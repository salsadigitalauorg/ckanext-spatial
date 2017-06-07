import re
import cgitb
import warnings
import urllib2
import sys
import logging
from string import Template
from urlparse import urlparse
from datetime import datetime
import uuid
import hashlib
import dateutil
import mimetypes


from pylons import config
from owslib import wms
import requests
from lxml import etree

from ckan import plugins as p
from ckan import model
from ckan.lib.helpers import json
from ckan import logic
from ckan.lib.navl.validators import not_empty
from ckan.lib.search.index import PackageSearchIndex

from ckanext.harvest.harvesters.base import HarvesterBase
from ckanext.harvest.model import HarvestObject

from ckanext.spatial.validation import Validators, all_validators
from ckanext.spatial.model import ISODocument
from ckanext.spatial.interfaces import ISpatialHarvester

log = logging.getLogger(__name__)

DEFAULT_VALIDATOR_PROFILES = ['iso19139']


def text_traceback():
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        res = 'the original traceback:'.join(
            cgitb.text(sys.exc_info()).split('the original traceback:')[1:]
        ).strip()
    return res


def guess_standard(content):
    lowered = content.lower()
    if '</gmd:MD_Metadata>'.lower() in lowered:
        return 'iso'
    if '</MD_Metadata>'.lower() in lowered:
        return 'iso'
    if '</gmi:MI_Metadata>'.lower() in lowered:
        return 'iso'
    if '</metadata>'.lower() in lowered:
        return 'fgdc'
    return 'unknown'


def guess_resource_format(url, use_mimetypes=True):
    '''
    Given a URL try to guess the best format to assign to the resource

    The function looks for common patterns in popular geospatial services and
    file extensions, so it may not be 100% accurate. It just looks at the
    provided URL, it does not attempt to perform any remote check.

    if 'use_mimetypes' is True (default value), the mimetypes module will be
    used if no match was found before.

    Returns None if no format could be guessed.

    '''
    url = url.lower().strip()

    resource_types = {
        # OGC
        'wms': ('service=wms', 'geoserver/wms', 'mapserver/wmsserver', 'com.esri.wms.Esrimap', 'service/wms'),
        'wfs': ('service=wfs', 'geoserver/wfs', 'mapserver/wfsserver', 'com.esri.wfs.Esrimap'),
        'wcs': ('service=wcs', 'geoserver/wcs', 'imageserver/wcsserver', 'mapserver/wcsserver'),
        'sos': ('service=sos',),
        'csw': ('service=csw',),
        # ESRI
        'kml': ('mapserver/generatekml',),
        'arcims': ('com.esri.esrimap.esrimap',),
        'arcgis_rest': ('arcgis/rest/services',),
    }

    for resource_type, parts in resource_types.iteritems():
        if any(part in url for part in parts):
            return resource_type

    file_types = {
        'kml' : ('kml',),
        'kmz': ('kmz',),
        'gml': ('gml',),
        'csv': ('csv',),
        'xls': ('xls', 'xlsx'),

    }

    for file_type, extensions in file_types.iteritems():
        if any(url.endswith(extension) for extension in extensions):
            return file_type

    resource_format, encoding = mimetypes.guess_type(url)
    if resource_format:
        return resource_format

    return None


class SpatialHarvester(HarvesterBase):

    _user_name = None

    _site_user = None

    source_config = {}

    force_import = False

    extent_template = Template('''
    {"type": "Polygon", "coordinates": [[[$xmin, $ymin], [$xmax, $ymin], [$xmax, $ymax], [$xmin, $ymax], [$xmin, $ymin]]]}
    ''')

    target_formats = list(set(map(lambda x: x.upper(), p.toolkit.aslist(config.get('ckanext.spatial.harvest.csw_harvested_formats',
                                                                                   'csv xls wms wfs wcs sos csw arcims arcgis_rest shp arcgrid kml zip')))))

    licenses = model.Package.get_license_register().values()

    ## IHarvester

    def validate_config(self, source_config):
        if not source_config:
            return source_config

        try:
            source_config_obj = json.loads(source_config)

            if 'validator_profiles' in source_config_obj:
                if not isinstance(source_config_obj['validator_profiles'], list):
                    raise ValueError('validator_profiles must be a list')

                # Check if all profiles exist
                existing_profiles = [v.name for v in all_validators]
                unknown_profiles = set(source_config_obj['validator_profiles']) - set(existing_profiles)

                if len(unknown_profiles) > 0:
                    raise ValueError('Unknown validation profile(s): %s' % ','.join(unknown_profiles))

            if 'default_tags' in source_config_obj:
                if not isinstance(source_config_obj['default_tags'],list):
                    raise ValueError('default_tags must be a list')

            if 'default_extras' in source_config_obj:
                if not isinstance(source_config_obj['default_extras'],dict):
                    raise ValueError('default_extras must be a dictionary')

            for key in ('override_extras'):
                if key in source_config_obj:
                    if not isinstance(source_config_obj[key],bool):
                        raise ValueError('%s must be boolean' % key)

        except ValueError, e:
            raise e

        return source_config

    ##

    ## SpatialHarvester

    organization_cache = {}

    def munge_title_to_name(self, name):
        '''Munge a package title into a package name.
        '''
        # convert spaces and separators
        name = re.sub('[ .:/,]', '-', name)
        # take out not-allowed characters
        name = re.sub('[^a-zA-Z0-9-_]', '', name).lower()
        # remove doubles
        name = re.sub('---', '-', name)
        name = re.sub('--', '-', name)
        name = re.sub('--', '-', name)
        # remove leading or trailing hyphens
        name = name.strip('-')[:99]
        return name

    def get_org(self, context, organization_title):
        organization_title_mapping = {'Commonwealth of Australia (Geoscience Australia)': 'GeoscienceAustralia',
                                      'Antarctic Climate and Ecosystems Cooperative Research Centre (ACE CRC)': 'commonwealthscientificandindustrialresearchorganisation',
                                      'Australian Bureau of Meteorology (BOM)': 'bureauofmeteorology',
                                      'Australian Bureau of Meteorology': 'bureauofmeteorology',
                                      'Bureau of Meteorology': 'bureauofmeteorology',
                                      'Australian Electoral Commission (AEC)': 'australianelectoralcommission',
                                      'Australian Government Department of Sustainability, Environment, Water, Population and Communities': 'departmentofenvironment',
                                      'Australian Government Department of the Environment': 'departmentofenvironment',
                                      'Australian Governement Department of the Environment and Water Resources': 'departmentofenvironment',
                                      'Department of the Environment': 'departmentofenvironment',
                                      'Antarctic CRC - The University of Tasmania': 'commonwealthscientificandindustrialresearchorganisation',
                                      'Australian Institute of Marine Science (AIMS)': 'Australian Institute of Marine Science',
                                      'AU/AADC > Australian Antarctic Data Centre, Australia': 'australianantarcticdivision',
                                      'ICSU/SCAR/SCAR-MARBIN/ANTABIF > Antarctic Biodiversity Information Facility, Marine Biodiversity Information Network, Scientific Committee on Antarctic Research, International Council for Science': 'australianantarcticdivision',
                                      'UQ/ENTOX > National Reserach Centre for Environmental Toxicology, University of Queensland, Australia': 'australianantarcticdivision',
                                      'WDC/WOUDC, TORONTO > World Data Center for Ozone and Ultraviolet Radiation, Toronto': 'australianantarcticdivision',
                                      'WDC/STS/IPS, SYDNEY > Ionospheric Prediction Service, World Data Centre for Solar Terrestrial Science, Sydney': 'australianantarcticdivision',
                                      'WDC/GEOMAGNETISM, EDINBURGH > World Data Center for Geomagnetism, Edinburgh': 'australianantarcticdivision',
                                      'UCAR/NCAR/HAO/CEDAR > Coupling, Energetics and Dynamics of Atmospheric Regions, High Altitude Observatory, National Center for Atmospheric Research, UCAR': 'australianantarcticdivision',
                                      'NASA/GSFC/SSED/CDDIS > Crustal Dynamics Data Information System, Solar System Exploration Division, Goddard Space Flight Center, NASA': 'australianantarcticdivision',
                                      'DOE/ORNL/ESD/CDIAC > Carbon Dioxide Information Analysis Center, Environmental Sciences Division, Oak Ridge National Laboratory, U. S. Department of Energy': 'australianantarcticdivision',
                                      'Commonwealth of Australia (Geoscience Australia, LOSAMBA)': 'GeoscienceAustralia',
                                      'Geoscience Australia (GA)': 'GeoscienceAustralia',
                                      'AU/GA > Geoscience Australia, Australia': 'GeoscienceAustralia',
                                      'Commonwealth Scientific and Industrial Research Organisation (CSIRO)': 'commonwealthscientificandindustrialresearchorganisation',
                                      'CSIRO Marine and Atmospheric Research (CMAR)': 'commonwealthscientificandindustrialresearchorganisation',
                                      'CSIRO Oceans & Atmosphere Flagship - Hobart': 'commonwealthscientificandindustrialresearchorganisation',
                                      'Department of Primary Industries NSW': 'NSW Department of Primary Industries',
                                      'Department of Industry and Investment (DII)': 'NSW Department of Primary Industries',
                                      'Department of Natural Resources and Mines, Queensland': 'Queensland Department of Natural Resources and Mines',
                                      'Derwent Estuary Program': 'Environment Protection Authority Tasmania',
                                      'ECOCEAN': 'commonwealthscientificandindustrialresearchorganisation',
                                      'eMarine Information Infrastructure (eMII)': 'commonwealthscientificandindustrialresearchorganisation',
                                      'Emergency Services GIS': 'Department of Primary Industries, Parks, Water and Environment (Tasmania)',
                                      'Fisheries NSW, Primary Industries': 'NSW Department of Primary Industries',
                                      'Flinders University, School of Chemistry, Physics and Earth Sciences': 'Flinders University',
                                      'Flinders University, School of Chemistry, Physics and Earth Sciences,': 'Flinders University',
                                      'Flinders University, School of Chemisty, Physics and Earth Sciences': 'Flinders University',
                                      'School of Chemistry, Physics and Earth Sciences (SoCPES), Flinders University': 'Flinders University',
                                      'School of Environment, Flinders University': 'Flinders University',
                                      'School of the Environment, Flinders University': 'Flinders University',
                                      'IMAS, University of Tasmania': 'Institute for Marine and Antarctic Studies',
                                      'Institute for Marine and Antarctic Studies (IMAS), University of Tasmania': 'Institute for Marine and Antarctic Studies',
                                      'Institute for Marine and Antarctic Studies (IMAS)': 'Institute for Marine and Antarctic Studies',
                                      'Land and Property Information': 'NSW Land and Property Information',
                                      'Land and Property Information-NSW': 'NSW Land and Property Information',
                                      'Marine Futures Project, The University of Western Australia (UWA)': 'University of Western Australia',
                                      'Marine Policy and Planning Branch, Department of Environment and Conservation': 'WA Department of Parks and Wildlife',
                                      'National Tidal Centre': 'bureauofmeteorology',
                                      'National Tidal Centre Unit': 'bureauofmeteorology',
                                      'AU/BOM/TARO > Tasmanian-Antarctica Regional Office, Bureau of Meteorology, Australia': 'bureauofmeteorology',
                                      'NIWA National Institute of Water & Atmospheric Research': 'NZ National Institute of Water & Atmospheric Research',
                                      'NSW Department of Environment, Climate Change and Water (DECCW)': 'NSW Office of Environment and Heritage',
                                      'DTIRIS Resources & Energy NSW': 'NSW Department of Trade and Investment, Regional Infrastructure and Services',
                                      'Office of Environment and Heritage': 'NSW Office of Environment and Heritage',
                                      'Office of Environment and Heritage (OEH)': 'NSW Office of Environment and Heritage',
                                      'Ocean Technology Group, University of Sydney': 'University of Sydney',
                                      'Discipline of Anatomy and Histology, The University of Sydney (USYD)': 'University of Sydney',
                                      'School of Geosciences, The University of Sydney (USYD)': 'University of Sydney',
                                      'Royal Australian Navy Hydrography and Metoc Branch': 'Royal Australian Navy',
                                      'Royal Australian Navy Hydrography and METOC Branch': 'Royal Australian Navy',
                                      'SARDI Aquatic Sciences': 'South Australian Research and Development Institute',
                                      'School of Environmental Science, Murdoch University': 'Murdoch University',
                                      'The Australian National University (ANU)': 'Australian National University',
                                      'Department of Earth and Marine Sciences (DEMS), The Australian National University (ANU) (Research School of Earth Sciences)': 'Australian National University',
                                      'Research School of Earth Sciences (RSES), The Australian National University (ANU)': 'Australian National University',
                                      'The University of Sydney': 'University of Sydney',
                                      'WA Department of Fisheries - Scientific Custodian': 'WA Department of Fisheries',
                                      'WA Department of Fisheries - Technical Custodian': 'WA Department of Fisheries',
                                      'Department of Transport': 'WA Department of Transport',
                                      'Department of Transport (WA)': 'WA Department of Transport',
                                      'Geological Survey Division, Department of Mines and Petroleum': 'WA Department of Mines and Petroleum',
                                      'School of Botany, The University of Melbourne': 'University of Melbourne',
                                      'Tasmanian Aquaculture and Fisheries Institute (TAFI)': 'Tasmanian Aquaculture and Fisheries Institute',
                                      'Western Australian Museum': 'Western Australian Museum (WAM)'
                                      }
        if organization_title in organization_title_mapping:
            organization_title = organization_title_mapping[organization_title]

        organization_id = self.munge_title_to_name(organization_title).lower()
        if organization_id not in self.organization_cache:
            try:
                self.organization_cache[organization_id] = p.toolkit.get_action('organization_show')(context, {
                    'id': organization_id, 'include_datasets': False})
            except:
                self.organization_cache[organization_id] = p.toolkit.get_action('organization_create')(context, {
                    'name': organization_id, 'title': organization_title})
        return self.organization_cache[organization_id]

    def get_package_dict(self, iso_values, harvest_object):
        '''
        Constructs a package_dict suitable to be passed to package_create or
        package_update. See documentation on
        ckan.logic.action.create.package_create for more details

        Extensions willing to modify the dict should do so implementing the
        ISpatialHarvester interface

            import ckan.plugins as p
            from ckanext.spatial.interfaces import ISpatialHarvester

            class MyHarvester(p.SingletonPlugin):

                p.implements(ISpatialHarvester, inherit=True)

                def get_package_dict(self, context, data_dict):

                    package_dict = data_dict['package_dict']

                    package_dict['extras'].append(
                        {'key': 'my-custom-extra', 'value': 'my-custom-value'}
                    )

                    return package_dict

        If a dict is not returned by this function, the import stage will be cancelled.

        :param iso_values: Dictionary with parsed values from the ISO 19139
            XML document
        :type iso_values: dict
        :param harvest_object: HarvestObject domain object (with access to
            job and source objects)
        :type harvest_object: HarvestObject

        :returns: A dataset dictionary (package_dict)
        :rtype: dict
        '''

        tags = []
        geospatial_topic = []
        if 'tags' in iso_values:
            for tagname in iso_values['tags']:
                for tag in tagname.replace(' - ', '|').split("|"):
                    tag = tag[:50] if len(tag) > 50 else tag
                    tags.append({'name': tag.strip()})

        if 'topic-category' in iso_values:
            for tagname in iso_values['topic-category']:
                for tag in tagname.replace(' - ', '|').split("|"):
                    tag = tag[:50] if len(tag) > 50 else tag
                    geospatial_topic.append({'name': tag.strip()})

        # Add default_tags from config
        default_tags = self.source_config.get('default_tags',[])
        if default_tags:
           for tag in default_tags:
              tags.append({'name': tag})

        package_dict = {
            'title': iso_values['title'],
            'notes': iso_values['abstract'] or iso_values['purpose'] + iso_values['lineage'],
            'tags': tags,
            'resources': [],
        }

        # We need to get the owner organization (if any) from the harvest
        # source dataset
        source_dataset = model.Package.get(harvest_object.source.id)
        if source_dataset.owner_org:
            package_dict['owner_org'] = source_dataset.owner_org

        # Package name
        package = harvest_object.package
        if package is None or package.title != iso_values['title']:
            name = self._gen_new_name(iso_values['title'])
            if not name:
                name = self._gen_new_name(str(iso_values['guid']))
            if not name:
                raise Exception('Could not generate a unique name from the title or the GUID. Please choose a more unique title.')
            package_dict['name'] = name
        else:
            package_dict['name'] = package.name

        extras = {
            'guid': harvest_object.guid,
            'spatial_harvester': True,
        }

        # Just add some of the metadata as extras, not the whole lot
        for name in [
            # Essentials
            'spatial-reference-system',
            'guid',
            # Usefuls
            'dataset-reference-date',
            'metadata-language',  # Language
            'metadata-date',  # Released
            'coupled-resource',
            'contact-email',
            'frequency-of-update',
            'spatial-data-service-type',
            'source',
            "dateStamp",
            "metadataStandard",
            "metadataStandardVersion",
        ]:
            extras[name] = iso_values[name]

        if len(iso_values.get('progress', [])):
            extras['progress'] = iso_values['progress'][0]
        else:
            extras['progress'] = ''

        if len(iso_values.get('resource-type', [])):
            extras['resource-type'] = iso_values['resource-type'][0]
        else:
            extras['resource-type'] = ''

        extras['licence'] = iso_values.get('use-constraints', '')

        def _extract_first_license_url(licences):
            for licence in licences:
                o = urlparse(licence)
                if o.scheme and o.netloc:
                    return licence
            return None

        if len(extras['licence']):
            license_url_extracted = _extract_first_license_url(extras['licence'])
            if license_url_extracted:
                extras['licence_url'] = license_url_extracted

        extras['access_constraints'] = iso_values.get('limitations-on-public-access', '')
        extras['use_constraints'] = iso_values.get('use-constraints', '')
        commons = iso_values.get('creative-commons', '')

        for l in self.licenses:
            if any([any([len(extras[y]) and x in ''.join(extras[y]) for y in ['use_constraints', 'access_constraints']]) or (commons and x in commons[0]) for x in [l.title, l.url or l.title]]):
                extras['licence'] = l.id
                package_dict['license_id'] = l.id
                extras['licence_url'] = l.url
                break
        else:
            extras['licence'] = "other"
            package_dict['license_id'] = "other"
            extras['licence_url'] = ""

        # Grpahic preview
        browse_graphic = iso_values.get('browse-graphic')
        if browse_graphic:
            browse_graphic = browse_graphic[0]
            extras['graphic-preview-file'] = browse_graphic.get('file')
            if browse_graphic.get('description'):
                extras['graphic-preview-description'] = browse_graphic.get('description')
            if browse_graphic.get('type'):
                extras['graphic-preview-type'] = browse_graphic.get('type')


        for key in ['temporal-extent-begin', 'temporal-extent-end']:
            if len(iso_values[key]) > 0:
                extras[key] = iso_values[key][0]

        # Save responsible organization roles
        extras['jurisdiction'] = 'Commonwealth of Australia'
        if iso_values['responsible-organisation']:
            responsible_org = None
            parties = {}
            for party in iso_values['responsible-organisation']:
                if party['organisation-name'] in parties:
                    if not party['role'] in parties[party['organisation-name']]:
                        parties[party['organisation-name']].append(party['role'])
                else:
                    parties[party['organisation-name']] = [party['role']]
            extras['responsible-party'] = [{'name': k, 'roles': v} for k, v in parties.iteritems()]
            for k, v in parties.iteritems():
                if 'custodian' in v or not responsible_org:
                    responsible_org = k
            context = {
                'model': model,
                'session': model.Session,
                'user': self._get_user_name(),
            }
            org = self.get_org(context, responsible_org)
            package_dict['owner_org'] = org['id']

        if len(iso_values['bbox']) > 0:
            bbox = iso_values['bbox'][0]
            extras['bbox-east-long'] = bbox['east']
            extras['bbox-north-lat'] = bbox['north']
            extras['bbox-south-lat'] = bbox['south']
            extras['bbox-west-long'] = bbox['west']

            try:
                xmin = float(bbox['west'])
                xmax = float(bbox['east'])
                ymin = float(bbox['south'])
                ymax = float(bbox['north'])
            except ValueError, e:
                self._save_object_error('Error parsing bounding box value: {0}'.format(str(e)),
                                    harvest_object, 'Import')
            else:
                # Construct a GeoJSON extent so ckanext-spatial can register the extent geometry

                # Some publishers define the same two corners for the bbox (ie a point),
                # that causes problems in the search if stored as polygon
                if xmin == xmax or ymin == ymax:
                    extent_string = Template('{"type": "Point", "coordinates": [$x, $y]}').substitute(
                        x=xmin, y=ymin
                    )
                    self._save_object_error('Point extent defined instead of polygon',
                                     harvest_object, 'Import')
                else:
                    extent_string = self.extent_template.substitute(
                        xmin=xmin, ymin=ymin, xmax=xmax, ymax=ymax
                    )

                extras['spatial'] = extent_string.strip()
                extras['spatial_coverage'] = extent_string.strip()
        else:
            log.debug('No spatial extent defined for this object')

        resource_locators = iso_values.get('resource-locator', []) +\
            iso_values.get('resource-locator-identification', [])

        if len(resource_locators):
            for resource_locator in resource_locators:
                url = resource_locator.get('url')
                if url and url.startswith('http') and not url.startswith(
                        'http://www.abs.gov.au/ausstats/abs@.nsf/Latestproducts/1297.0') \
                        and url not in ['http://www.abs.gov.au/AUSSTATS/abs@.nsf/DetailsPage/1297.01998?OpenDocument',
                                        'http://www.aodc.gov.au/', 'http://gcmd.nasa.gov/index.html',
                                        'http://aims.gov.au', 'http://www.aims.gov.au', 'http://www.aims.gov.au/adc']:
                    url = url.strip()
                    resource = {}
                    resource['format'] = guess_resource_format(url)

                    if 'name' not in resource and 'fname' in url:
                        fname = re.compile('fname=(.*)&')
                        resource['name'] = fname.search(url).group(1)
                        resource['format'] = guess_resource_format(resource['name'])
                    if 'kml' in url or '(kml)' in resource_locator['description']:
                        resource['format'] = 'kml'
                    if 'xhtml' in url:
                        resource['format'] = 'html'
                    if 'WMS applications' in resource_locator['description']:
                        resource['format'] = 'wms'
                    if 'WFS operations' in resource_locator['description']:
                        resource['format'] = 'wfs'
                    if 'xcel ' in resource_locator['description']:
                        resource['format'] = 'xls'
                    if 'csv ' in resource_locator['description'] or 'CSV ' in resource_locator['description']:
                        resource['format'] = 'csv'
                    if '(shp)' in resource_locator['description'] or 'shapefile' in resource_locator['description']:
                        resource['format'] = 'shp'
                    if '(ArcGIS-grid)' in resource_locator['description'] or '(ESRI ascii)' in resource_locator[
                        'description'] or 'ArcInfo ascii' in resource_locator['description']:
                        resource['format'] = 'arcgrid'
                    if resource['format'] == 'audio/basic':
                        resource['format'] = None
                    if resource['format'] == 'wms':
                        if 'name' in resource and ':' in resource['name'] and ' ' not in resource['name']:
                            resource['wms_layer'] = resource['name']
                        # Check if the service is a view service
                        test_url = url.split('?')[0] if '?' in url else url
                        try:
                            capabilities_url = wms.WMSCapabilitiesReader().capabilities_url(test_url)
                            res = urllib2.urlopen(capabilities_url, None, 10)
                            xml = res.read()

                            s = wms.WebMapService(test_url, xml=xml)
                            if isinstance(s.contents, dict) and s.contents != {}:
                                resource['verified'] = True
                                resource['verified_date'] = datetime.now().isoformat()
                                layers = list(s.contents)
                                if len(layers) == 1:
                                    resource['wms_layer'] = layers[0]
                                    bbox_values = list(s.contents[layers[0]].boundingBoxWGS84)
                                    bbox = {}
                                    bbox['minx'] = float(bbox_values[0])
                                    bbox['miny'] = float(bbox_values[1])
                                    bbox['maxx'] = float(bbox_values[2])
                                    bbox['maxy'] = float(bbox_values[3])
                                    # Construct a GeoJSON extent so ckanext-spatial can register the extent geometry
                                    extent_string = self.extent_template.substitute(
                                        xmin=bbox['minx'], ymin=bbox['miny'], xmax=bbox['maxx'], ymax=bbox['maxy']
                                    )
                                    extras['spatial'] = extent_string.strip()
                                    extras['spatial_coverage'] = extras['spatial']
                        except Exception, e:
                            log.debug('WMS check for %s failed with exception: %s' % (url, str(e)))

                    resource.update(
                        {
                            'url': url,
                            'name': resource.get('name') or resource_locator.get('name') or resource_locator.get(
                                'description') or url or p.toolkit._(
                                'Unnamed resource'),
                            'description': (resource_locator.get('description') if resource_locator.get(
                                'name') else None) or '',
                            'last_modified': iso_values['date-updated'] or '',
                            'resource_locator_protocol': resource_locator.get('protocol') or '',
                            'resource_locator_function': resource_locator.get('function') or '',
                        })
                    dupe = False
                    for r in package_dict['resources']:
                        if r['url'] == url:
                            dupe = True
                    if not dupe:
                        package_dict['resources'].append(resource)

        if iso_values['source'] and 'ga.gov.au' in iso_values['source']:
            package_dict['notes'] = package_dict['notes'] + "\n\nYou can also purchase hard copies of Geoscience Australia data and other products at http://www.ga.gov.au/products-services/how-to-order-products/sales-centre.html"

        # AGLS mapping
        if iso_values['source']:
            package_dict['url'] = iso_values['source']
        elif 'find.ga.gov.au' in harvest_object.source.url:
            package_dict['url'] = 'http://find.ga.gov.au/FIND/metadata-record/uuid/' + harvest_object.guid
        if iso_values['metadata-date']:
            extras['temporal_coverage'] = iso_values['metadata-date']
        if iso_values['dataset-reference-date'][0]['value']:
            extras['temporal_coverage'] = iso_values['dataset-reference-date'][0]['value']
        if iso_values['frequency-of-update']:
            extras['update_freq'] = iso_values['frequency-of-update']
        if iso_values['contact-email']:
            extras['contact_point'] = iso_values['contact-email']
        extras['data_state'] = 'inactive'

        # Add default_extras from config
        default_extras = self.source_config.get('default_extras',{})
        if default_extras:
           override_extras = self.source_config.get('override_extras',False)
           for key,value in default_extras.iteritems():
              log.debug('Processing extra %s', key)
              if not key in extras or override_extras:
                 # Look for replacement strings
                 if isinstance(value,basestring):
                    value = value.format(harvest_source_id=harvest_object.job.source.id,
                             harvest_source_url=harvest_object.job.source.url.strip('/'),
                             harvest_source_title=harvest_object.job.source.title,
                             harvest_job_id=harvest_object.job.id,
                             harvest_object_id=harvest_object.id)
                 extras[key] = value

        extras_as_dict = []
        for key, value in extras.iteritems():
            if isinstance(value, (list, dict)):
                extras_as_dict.append({'key': key, 'value': json.dumps(value)})
            else:
                extras_as_dict.append({'key': key, 'value': value})

        package_dict['extras'] = extras_as_dict

        return package_dict

    def transform_to_iso(self, original_document, original_format, harvest_object):
        '''
        DEPRECATED: Use the transform_to_iso method of the ISpatialHarvester
        interface
        '''
        self.__base_transform_to_iso_called = True
        return None

    def import_stage(self, harvest_object):

        context = {
            'model': model,
            'session': model.Session,
            'user': self._get_user_name(),
        }

        log = logging.getLogger(__name__ + '.import')
        log.debug('Import stage for harvest object: %s', harvest_object.id)

        if not harvest_object:
            log.error('No harvest object received')
            return False

        self._set_source_config(harvest_object.source.config)

        if self.force_import:
            status = 'change'
        else:
            status = self._get_object_extra(harvest_object, 'status')

        # Get the last harvested object (if any)
        previous_object = model.Session.query(HarvestObject) \
                          .filter(HarvestObject.guid==harvest_object.guid, HarvestObject.harvest_source_id==harvest_object.harvest_source_id) \
                          .filter(HarvestObject.current==True) \
                          .first()

        if status == 'delete':
            # Delete package
            context.update({
                'ignore_auth': True,
            })
            p.toolkit.get_action('package_delete')(context, {'id': harvest_object.package_id})
            log.info('Deleted package {0} with guid {1}'.format(harvest_object.package_id, harvest_object.guid))

            return True

        # Check if it is a non ISO document
        original_document = self._get_object_extra(harvest_object, 'original_document')
        original_format = self._get_object_extra(harvest_object, 'original_format')
        if original_document and original_format:
            #DEPRECATED use the ISpatialHarvester interface method
            self.__base_transform_to_iso_called = False
            content = self.transform_to_iso(original_document, original_format, harvest_object)
            if not self.__base_transform_to_iso_called:
                log.warn('Deprecation warning: calling transform_to_iso directly is deprecated. ' +
                         'Please use the ISpatialHarvester interface method instead.')

            for harvester in p.PluginImplementations(ISpatialHarvester):
                content = harvester.transform_to_iso(original_document, original_format, harvest_object)

            if content:
                harvest_object.content = content
            else:
                self._save_object_error('Transformation to ISO failed', harvest_object, 'Import')
                return False
        else:
            if harvest_object.content is None:
                self._save_object_error('Empty content for object {0}'.format(harvest_object.id), harvest_object, 'Import')
                return False

            # Validate ISO document
            is_valid, profile, errors = self._validate_document(harvest_object.content, harvest_object)
            if not is_valid:
                # If validation errors were found, import will stop unless
                # configuration per source or per instance says otherwise
                continue_import = p.toolkit.asbool(config.get('ckanext.spatial.harvest.continue_on_validation_errors', False)) or \
                    self.source_config.get('continue_on_validation_errors')
                if not continue_import:
                    return False

        # Parse ISO document
        try:

            iso_parser = ISODocument(harvest_object.content)
            iso_values = iso_parser.read_values()
        except Exception, e:
            self._save_object_error('Error parsing ISO document for object {0}: {1}'.format(harvest_object.id, str(e)),
                                    harvest_object, 'Import')
            return False

        # Flag previous object as not current anymore
        if previous_object and not self.force_import:
            previous_object.current = False
            previous_object.add()

        # Update GUID with the one on the document
        iso_guid = iso_values['guid']
        if iso_guid and harvest_object.guid != iso_guid:
            # First make sure there already aren't current objects
            # with the same guid
            existing_object = model.Session.query(HarvestObject.id) \
                            .filter(HarvestObject.guid==iso_guid) \
                            .filter(HarvestObject.current==True) \
                            .first()
            if existing_object:
                self._save_object_error('Object {0} already has this guid {1}'.format(existing_object.id, iso_guid),
                        harvest_object, 'Import')
                return False

            harvest_object.guid = iso_guid
            harvest_object.add()

        # Generate GUID if not present (i.e. it's a manual import)
        if not harvest_object.guid:
            m = hashlib.md5()
            m.update(harvest_object.content.encode('utf8', 'ignore'))
            harvest_object.guid = m.hexdigest()
            harvest_object.add()

        # Get document modified date
        try:
            metadata_modified_date = dateutil.parser.parse(iso_values['metadata-date'], ignoretz=True)
        except ValueError:
            self._save_object_error('Could not extract reference date for object {0} ({1})'
                        .format(harvest_object.id, iso_values['metadata-date']), harvest_object, 'Import')
            return False

        harvest_object.metadata_modified_date = metadata_modified_date
        harvest_object.add()


        # Build the package dict
        try:
            package_dict = self.get_package_dict(iso_values, harvest_object)
            for harvester in p.PluginImplementations(ISpatialHarvester):
                package_dict = harvester.get_package_dict(context, {
                    'package_dict': package_dict,
                    'iso_values': iso_values,
                    'xml_tree': iso_parser.xml_tree,
                    'harvest_object': harvest_object,
                })
        except Exception, e:
            log.debug('Attempt to retrieve package generated error: %r.' % e)
            package_dict = None

        if not package_dict:
            log.debug('No package dict returned, aborting import for object {0}'.format(harvest_object.id))
            return False

        def test_res(res):
            if 'format' in res and res.get('format', None) is not None:
                p_format = res['format'].split('/')[-1].upper()
                if any([t_format in p_format for t_format in self.target_formats]):
                    return res['format'].split('/')[-1]
            return None

        old_res = package_dict.get('resources', [])
        new_res = []
        for res in old_res:
            new_format = test_res(res)
            if new_format is not None:
                res['format'] = new_format
                new_res.append(res)

        package_dict['resources'] = new_res

        original_formats = set([x.get('format', '') for x in old_res])
        original_formats.discard('')
        original_formats.discard(None)
        if len(original_formats) > 0:
            log.debug('Analyzing resources with formats: {0}'.format(' '.join(original_formats)))
        else:
            log.debug('Package dict yields no resources with valid formats.')

        discarded_formats = set([x.get('format', '') for x in old_res if test_res(x) is None])
        discarded_formats.discard('')
        discarded_formats.discard(None)
        if len(discarded_formats) > 0:
            log.debug('Discarding resources with formats: {0}'.format(' '.join(discarded_formats)))

        if not package_dict['resources']:
            log.debug('Package dict returned no valid resources for object {0}'.format(harvest_object.id))

            # Delete package incase format selection has changed in the config
            if status == 'change':
                # Delete package
                context.update({
                    'ignore_auth': True,
                })
                try:
                    p.toolkit.get_action('package_delete')(context, {'id': harvest_object.package_id})
                    log.info('Deleted package {0} with guid {1}'.format(harvest_object.package_id, harvest_object.guid))
                except logic.NotFound:
                    log.info('Package {0} with guid {1} was not found, continuing...'.format(harvest_object.package_id, harvest_object.guid))
            return False

        # Create / update the package
        context.update({
           'extras_as_string': True,
           'api_version': '2',
           'return_id_only': True})

        if self._site_user and context['user'] == self._site_user['name']:
            context['ignore_auth'] = True


        # The default package schema does not like Upper case tags
        tag_schema = logic.schema.default_tags_schema()
        tag_schema['name'] = [not_empty, unicode]

        # Flag this object as the current one
        harvest_object.current = True
        harvest_object.add()

        if status == 'new':
            package_schema = logic.schema.default_create_package_schema()
            package_schema['tags'] = tag_schema
            context['schema'] = package_schema

            # We need to explicitly provide a package ID, otherwise ckanext-spatial
            # won't be be able to link the extent to the package.
            package_dict['id'] = unicode(uuid.uuid4())
            package_schema['id'] = [unicode]

            # Save reference to the package on the object
            harvest_object.package_id = package_dict['id']
            harvest_object.add()
            # Defer constraints and flush so the dataset can be indexed with
            # the harvest object id (on the after_show hook from the harvester
            # plugin)
            model.Session.execute('SET CONSTRAINTS harvest_object_package_id_fkey DEFERRED')
            model.Session.flush()

            try:
                package_id = p.toolkit.get_action('package_create')(context, package_dict)
                log.info('Created new package %s with guid %s', package_id, harvest_object.guid)
            except p.toolkit.ValidationError, e:
                self._save_object_error('Validation Error: %s' % str(e.error_summary), harvest_object, 'Import')
                return False

        elif status == 'change':

            # Check if the modified date is more recent
            if not self.force_import and previous_object and harvest_object.metadata_modified_date <= previous_object.metadata_modified_date:

                # Assign the previous job id to the new object to
                # avoid losing history
                harvest_object.harvest_job_id = previous_object.job.id
                harvest_object.add()

                # Delete the previous object to avoid cluttering the object table
                previous_object.delete()

                # Reindex the corresponding package to update the reference to the
                # harvest object
                if ((config.get('ckanext.spatial.harvest.reindex_unchanged', True) != 'False'
                    or self.source_config.get('reindex_unchanged') != 'False')
                    and harvest_object.package_id):
                    context.update({'validate': False, 'ignore_auth': True})
                    try:
                        package_dict = logic.get_action('package_show')(context,
                            {'id': harvest_object.package_id})
                    except p.toolkit.ObjectNotFound:
                        pass
                    else:
                        for extra in package_dict.get('extras', []):
                            if extra['key'] == 'harvest_object_id':
                                extra['value'] = harvest_object.id
                        if package_dict:
                            package_index = PackageSearchIndex()
                            package_index.index_package(package_dict)

                log.info('Document with GUID %s unchanged, skipping...' % (harvest_object.guid))
            else:
                package_schema = logic.schema.default_update_package_schema()
                package_schema['tags'] = tag_schema
                context['schema'] = package_schema

                package_dict['id'] = harvest_object.package_id
                package_dict['state'] = 'active'
                context.update({
                    'ignore_auth': True,
                })
                try:
                    package_id = p.toolkit.get_action('package_update')(context, package_dict)
                    log.info('Updated package %s with guid %s', package_id, harvest_object.guid)
                except p.toolkit.ValidationError, e:
                    self._save_object_error('Validation Error: %s' % str(e.error_summary), harvest_object, 'Import')
                    return False

        model.Session.commit()

        return True
    ##

    def _is_wms(self, url):
        '''
        Checks if the provided URL actually points to a Web Map Service.
        Uses owslib WMS reader to parse the response.
        '''
        try:
            capabilities_url = wms.WMSCapabilitiesReader().capabilities_url(url)
            res = urllib2.urlopen(capabilities_url, None, 10)
            xml = res.read()

            s = wms.WebMapService(url, xml=xml)
            return isinstance(s.contents, dict) and s.contents != {}
        except Exception, e:
            log.debug('WMS check for %s failed with exception: %s' % (url, str(e)))
        return False

    def _get_object_extra(self, harvest_object, key):
        '''
        Helper function for retrieving the value from a harvest object extra,
        given the key
        '''
        for extra in harvest_object.extras:
            if extra.key == key:
                return extra.value
        return None

    def _set_source_config(self, config_str):
        '''
        Loads the source configuration JSON object into a dict for
        convenient access
        '''
        if config_str:
            self.source_config = json.loads(config_str)
            #log.debug('Using config: %r', self.source_config)
        else:
            self.source_config = {}

    def _get_validator(self):
        '''
        Returns the validator object using the relevant profiles

        The profiles to be used are assigned in the following order:

        1. 'validator_profiles' property of the harvest source config object
        2. 'ckan.spatial.validator.profiles' configuration option in the ini file
        3. Default value as defined in DEFAULT_VALIDATOR_PROFILES
        '''
        if not hasattr(self, '_validator'):
            if hasattr(self, 'source_config') and self.source_config.get('validator_profiles', None):
                profiles = self.source_config.get('validator_profiles')
            elif config.get('ckan.spatial.validator.profiles', None):
                profiles = [
                    x.strip() for x in
                    config.get('ckan.spatial.validator.profiles').split(',')
                ]
            else:
                profiles = DEFAULT_VALIDATOR_PROFILES
            self._validator = Validators(profiles=profiles)

            # Add any custom validators from extensions
            for plugin_with_validators in p.PluginImplementations(ISpatialHarvester):
                custom_validators = plugin_with_validators.get_validators()
                for custom_validator in custom_validators:
                    if custom_validator not in all_validators:
                        self._validator.add_validator(custom_validator)


        return self._validator

    def _get_user_name(self):
        '''
        Returns the name of the user that will perform the harvesting actions
        (deleting, updating and creating datasets)

        By default this will be the internal site admin user. This is the
        recommended setting, but if necessary it can be overridden with the
        `ckanext.spatial.harvest.user_name` config option, eg to support the
        old hardcoded 'harvest' user:

           ckanext.spatial.harvest.user_name = harvest

        '''
        if self._user_name:
            return self._user_name

        context = {'model': model,
                   'ignore_auth': True,
                   'defer_commit': True, # See ckan/ckan#1714
                  }
        self._site_user = p.toolkit.get_action('get_site_user')(context, {})

        config_user_name = config.get('ckanext.spatial.harvest.user_name')
        if config_user_name:
            self._user_name = config_user_name
        else:
            self._user_name = self._site_user['name']

        return self._user_name

    def _get_content(self, url):
        '''
        DEPRECATED: Use _get_content_as_unicode instead
        '''
        url = url.replace(' ', '%20')
        http_response = urllib2.urlopen(url)
        return http_response.read()

    def _get_content_as_unicode(self, url):
        '''
        Get remote content as unicode.

        We let requests handle the conversion [1] , which will use the
        content-type header first or chardet if the header is missing
        (requests uses its own embedded chardet version).

        As we will be storing and serving the contents as unicode, we actually
        replace the original XML encoding declaration with an UTF-8 one.


        [1] http://github.com/kennethreitz/requests/blob/63243b1e3b435c7736acf1e51c0f6fa6666d861d/requests/models.py#L811

        '''
        url = url.replace(' ', '%20')
        response = requests.get(url, timeout=10)

        content = response.text

        # Remove original XML declaration
        content = re.sub('<\?xml(.*)\?>', '', content)

        # Get rid of the BOM and other rubbish at the beginning of the file
        content = re.sub('.*?<', '<', content, 1)
        content = content[content.index('<'):]

        return content

    def _validate_document(self, document_string, harvest_object, validator=None):
        '''
        Validates an XML document with the default, or if present, the
        provided validators.

        It will create a HarvestObjectError for each validation error found,
        so they can be shown properly on the frontend.

        Returns a tuple, with a boolean showing whether the validation passed
        or not, the profile used and a list of errors (tuples with error
        message and error lines if present).
        '''
        if not validator:
            validator = self._get_validator()

        document_string = re.sub('<\?xml(.*)\?>', '', document_string)

        try:
            xml = etree.fromstring(document_string)
        except etree.XMLSyntaxError, e:
            self._save_object_error('Could not parse XML file: {0}'.format(str(e)), harvest_object, 'Import')
            return False, None, []

        valid, profile, errors = validator.is_valid(xml)
        if not valid:
            log.error('Validation errors found using profile {0} for object with GUID {1}'.format(profile, harvest_object.guid))
            for error in errors:
                self._save_object_error(error[0], harvest_object, 'Validation', line=error[1])

        return valid, profile, errors
