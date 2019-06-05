#!/usr/bin/env python
# -*- coding: utf-8 -*-
# This file contains the code to audit, clean, process and load 
# the chosen subset of data from openstreetmap.org into csv files
# for subsequent loading into SQLite. It is part of the Udacity Data Wrangling Project

import xml.etree.cElementTree as ET
from collections import defaultdict
import re
import csv
import codecs
import urllib.request
from urllib.error import URLError, HTTPError

# ================================================== #
#               Variable definitions                 #
# ================================================== #

NODES_PATH = "nodes.csv"
NODE_TAGS_PATH = "nodes_tags.csv"
WAYS_PATH = "ways.csv"
WAY_NODES_PATH = "ways_nodes.csv"
WAY_TAGS_PATH = "ways_tags.csv"

LOWER_COLON = re.compile(r'^([a-z]|_)+:([a-z]|_)+')
PROBLEMCHARS = re.compile(r'[=\+/&<>;\'"\?%#$@\,\. \t\r\n]')

NODE_FIELDS = ['id', 'lat', 'lon', 'user', 'uid', 'version', 'changeset', 'timestamp']
NODE_TAGS_FIELDS = ['id', 'key', 'value', 'type']
WAY_FIELDS = ['id', 'user', 'uid', 'version', 'changeset', 'timestamp']
WAY_TAGS_FIELDS = ['id', 'key', 'value', 'type']
WAY_NODES_FIELDS = ['id', 'node_id', 'position']

#Define regular expressions to check tag types
street_type_re = re.compile(r'\S+\.?$', re.IGNORECASE)
postcode_re = re.compile(r'[A-Z]{2}[0-9]{1,2}(?:\s[0-9][A-Z]{2})?')
postcode_complete_re = re.compile(r'[A-Z]{2}[0-9]{1,2}\s[0-9][A-Z]{2}')

housenumber_digits_re = re.compile(r'(?:[i])?[0-9]{1,4}(?:[A-Z]{1})?', re.IGNORECASE)
housenumber_multiplenumbers_re = re.compile(r'([0-9]{1,4}[\,]){1,8}[0-9]{1,4}', re.IGNORECASE)
housenumber_digitstodigits_re = re.compile(r'[0-9]{1,4}[\-\;\,][?:\s]?[0-9]{1,4}(?:[A-Z]{1})?', re.IGNORECASE)
housenumber_unit_re = re.compile(r'Unit\s[0-9]{1,4}(?:\s)?(?:\,\s)?(?:[A-Z\s]{1,20})?', re.IGNORECASE)
housename_numbername_re = re.compile(r'[0-9]{1,4}[\s](?:[A-Z]{1,20}\s[A-Z]{1,20})?', re.IGNORECASE)

flatnumber_re = re.compile(r'Flat\s[0-9]{1,4}(?:\s)?(?:\,\s)?(?:[A-Z\s]{1,20})?', re.IGNORECASE)
invalid_phone_re = re.compile(r'[^0-9\+]')

# Define lists and dictionaries
street_types = defaultdict(int)
tag_types = []
country_types = defaultdict(int)
flat_types = defaultdict(list)
flats = []
flatnumbers = []
housename_types = defaultdict(list)
housenames = []
addrnames = []
house_name_tags = ["addr:housename", "addr:name"]
postcode_tags = ["addr:postcode", "old:addr:postcode", "postal_code"]
phone_tags = ["Phone", "phone", "contact:phone"]
types = set()
source_names = set()
invalid_websites = []
invalid_phones = []
postcodes = []
postcodes_incomplete = []
invalid_housenumbers = set()
interpolation = set()
cities = set()

# Mapping from old/erroneous values to clean values for tag keys and values 
street_mapping = { "ROAD": "Road",
                   "Rd": "Road"}
city_mapping = { "Easher": "Esher",
                 "Walton-on-Thamse": "Walton-on-Thames",
                 "Walton-On-Thames": "Walton-on-Thames",
                 "West Moseley": "West Molesey",
                 "CHERTSEY": "Chertsey",
                 "Sunbury": "Sunbury-on-Thames",
                 "Sunbury-On-Thames": "Sunbury-on-Thames",
                 "Surrey": "Molesey"
                 }

value_tag_correction_mapping = {"Council Offices": "addr:housename", "Padley": "addr:housename"}
tag_correction_mapping = {"addr:flat": "addr:flatnumber", "addr:name": "addr:housename"}
conditional_tag_correction_mapping = {"addr:housename": "addr:housenumber"}

# Other global variables
addTag = False
tagToAdd = {}

# ================================================== #
#               Clean/Update Tag Functions           #
# ================================================== #

# Generic update tag function, invoked for each tag
# to process/clean it before it is written to csv.
# Followed by tag key-specific update functions

def updateTag(tag):
    if is_flat_number(tag):   
        tag = update_flat_number(tag)
    elif is_house_name(tag):
        tag = update_house_name(tag)
    elif is_city_name(tag):
        tag = update_city_name(tag)
    elif is_street_name(tag):
        tag = update_street_name(tag)
    elif is_house_number(tag):
        tag = update_house_number(tag)
    elif is_phone(tag):
        tag = update_phone(tag)
    elif is_website(tag):
        tag = update_website(tag)
    return tag

def update_flat_number(tag):
    # Update tag key from mapping
    if tag.attrib['k'] in tag_correction_mapping:
            tag.attrib['k'] = tag_correction_mapping[tag.attrib['k']]
    return tag

def update_house_name(tag):
    global addTag
    global tagToAdd
    
    # Changing "addr:name" to "addr:housename"
    if tag.attrib['k'] in tag_correction_mapping:
        tag.attrib['k'] = tag_correction_mapping[tag.attrib['k']]

    # Checking for each kind of house number format
    # If format is of the form 6, or 8-10, then re-tag as house number instead of house name  
    m1 = housenumber_digitstodigits_re.fullmatch(tag.attrib['v']) or housenumber_digits_re.fullmatch(tag.attrib['v'])
    if m1:
        tag.attrib['k'] = "addr:housenumber"

    # If format is of the form Flat 7, then re-tag as flat number instead of house name
    m2 = flatnumber_re.fullmatch(tag.attrib['v'])
    if m2:
        tag.attrib['k'] = "addr:flatnumber"

    # If format is of the form 16 Danesfield Close, split into two tags:
    # house number with the value 16, and house name with the value Danesfield Close
    m3 = housename_numbername_re.fullmatch(tag.attrib['v'])
    if m3:
        housenumber = tag.attrib['v'].split()[0]
        addTag = True
        tagToAdd["addr:housenumber"] = housenumber

        # The only exception to adding the house name tag is if it contains "Street"
        # In this case, the addr:street will already carry the street name
        # so the extra house name tag will be redundant and is not required
        if tag.attrib['v'].split()[-1] == "Street":
            tag = None
        else:
           tag.attrib['v'] = ' '.join(tag.attrib['v'].split()[1:]) 
    return tag

def update_city_name(tag):
    city_name = tag.attrib['v']
    if city_name in city_mapping:
        tag.attrib['v'] = city_mapping[city_name]
    return tag

def update_street_name(tag):
    street_name = tag.attrib['v']
    lastword = street_name.split()[-1]

    # Replace last word in street name from street mapping if correction required 
    if lastword in street_mapping:
        street_name = street_name.replace(lastword, street_mapping[lastword])
        tag.attrib['v'] = street_name
    return tag

def update_house_number(tag):
    # Clean value and then replace from mapping dictionary if correction required  
    tag.attrib['v'] = tag.attrib['v'].replace(", ", ",")
    tag.attrib['v'] = tag.attrib['v'].replace(";", ",")
    if tag.attrib['v'] in value_tag_correction_mapping:
        tag.attrib['k'] = value_tag_correction_mapping[tag.attrib['v']]
    return tag

def update_phone(tag):
    # Clean out extraneous characters
    phone = tag.attrib['v']
    phone = phone.replace(" ", "")
    phone = phone.replace("(", "")
    phone = phone.replace(")", "")
    phone = phone.replace(".", "")

    phoneString = ""

    # Validate and correct each phone number
    # Turn into format: +44 <phone number minus inital 0>
    for phone_value in phone.split(";"):

        if phone_value.startswith("44"):
            phone_value = phone_value[2: len(phone_value)]

        if phone_value.startswith("+440"):
            phone_value = phone_value[3: len(phone_value)]
        
        if phone_value.startswith("0"):
            phone_value = phone_value[1: len(phone_value)]
        
        if not phone_value.startswith("+44"):
            phone_value = "+44" + phone_value

        phoneString = phoneString + phone_value + ";"

    phoneString = phoneString[0:len(phoneString) - 1]

    tag.attrib['v'] = phoneString

    return tag

def update_website(tag):
    # Prefix with http:// to make website definition uniform.
    # See write-up document on further idea on validating website
    website = tag.attrib['v']
    if not website.startswith("http://"):
        website = "http://" + website
    tag.attrib['v'] = website
    return tag


# Generic function to process the tags for node or way element
# Given a node or way element, returns a list of cleaned tags and values
def processTags(element):
    global addTag
    global tagToAdd
    tagDict = {}
    tags = []

    # Follows the logic from case study on Data Wrangling
    # if a tag contains problem characters or is empty because it is redundant, ignore
    elemid = int(element.attrib['id'])
    for tag in element.iter("tag"):
        tag = updateTag(tag)
        if tag is not None: 
            ekeyval = tag.attrib['k']
            keyval = ekeyval 
            etypeval = "regular"
            typeval = etypeval
            tagDict = {}
            if not PROBLEMCHARS.search(ekeyval):
                tagDict['id'] = elemid
                if LOWER_COLON.search(ekeyval):
                    colonPos = ekeyval.find(":")
                    typeval = ekeyval[0:colonPos]
                    keyval = ekeyval[colonPos + 1:len(ekeyval)]
                tagDict['key'] = keyval
                tagDict['value'] = tag.attrib['v']
                tagDict['type'] = typeval
                tags.append(tagDict)

    if addTag:
        tagDict = {}
        for key in tagToAdd.keys():
            ekeyval = key
            keyval = ekeyval 
            etypeval = "regular"
            typeval = etypeval
            if LOWER_COLON.search(key):
                colonPos = ekeyval.find(":")
                typeval = ekeyval[0:colonPos]
                keyval = ekeyval[colonPos+1:len(ekeyval)]
            tagDict['id'] = elemid
            tagDict['key'] = keyval
            tagDict['value'] = tagToAdd[key]
            tagDict['type'] = typeval
            if not any(d.get('key', None) == keyval for d in tags):
                tags.append(tagDict)
            
        addTag = False
        tagToAdd = {}

    return tags

# This function iteratively reads each XML element from file and shapes it into a Python dictionary
# It iterates through a node/way and then their tags one at a time,
# calls the update function to clean/process the tag as needed,
# then saves each cleaned tag as a key-value pair as a new dictionary entry.
# Five dictionaries are created: nodes, node_tags, way, way nodes, way tags
# This code is taken and adapted from the Openstreetmap case study
def shape_element(element, node_attr_fields=NODE_FIELDS, way_attr_fields=WAY_FIELDS,
                  problem_chars=PROBLEMCHARS, default_tag_type='regular'):

    node_attribs = {}
    way_attribs = {}
    way_nodes = []
    tags = []  # Handle secondary tags the same way for both node and way elements
    nodeTagDict = {}
    wayTagDict = {}
    wayNodeDict = {}

    if element.tag == 'node':
        nodeid = int(element.attrib['id'])
        node_attribs['id'] = nodeid
        node_attribs['user'] = element.attrib['user']
        node_attribs['uid'] = int(element.attrib['uid'])
        node_attribs['version'] = element.attrib['version']
        node_attribs['lat'] = float(element.attrib['lat'])
        node_attribs['lon'] = float(element.attrib['lon'])
        node_attribs['timestamp'] = element.attrib['timestamp']
        node_attribs['changeset'] = int(element.attrib['changeset'])

        tags = processTags(element)
        return {'node': node_attribs, 'node_tags': tags}

    elif element.tag == 'way':
        wayid = int(element.attrib['id'])
        way_attribs['id'] = wayid
        way_attribs['user'] = element.attrib['user']
        way_attribs['uid'] = int(element.attrib['uid'])
        way_attribs['version'] = element.attrib['version']
        way_attribs['changeset'] = element.attrib['changeset']
        way_attribs['timestamp'] = element.attrib['timestamp']
        
        pos = 0
        for pos, noderef in enumerate(element.iter("nd")):
            wayNodeDict = {}
            wayNodeDict["id"] = wayid
            wayNodeDict["node_id"] = int(noderef.attrib["ref"])
            wayNodeDict["position"] = pos
            way_nodes.append(wayNodeDict)

        tags = processTags(element)
        return {'way': way_attribs, 'way_nodes': way_nodes, 'way_tags': tags}


# ================================================== #
#               Audit Tag Functions                  #
# ================================================== #
# Section for auditing tags. One function for each tag to be audited.
# Results from manual inspection are in comments

# Main audit function
def audit():
    for event, elem in ET.iterparse(osm_file, events=("start",)):
        if elem.tag == "node" or elem.tag == "way":
            for tag in elem.iter("tag"):                    
                if tag.attrib['k'] not in tag_types:
                    tag_types.append(tag.attrib['k'])
                if is_country(tag):
                    audit_country(country_types, tag.attrib['v'])
                if is_flat_number(tag):
                    audit_flat(flat_types, tag)
                if is_house_name(tag):
                    audit_housename(housename_types, tag)
                if is_postcode(tag):
                    audit_postcode(postcodes, tag)
                if is_street_name(tag):
                    audit_street_type(street_types, tag.attrib['v'])
                if is_city_name(tag):
                    audit_city(cities, tag.attrib['v']) 
                if is_house_number(tag):
                    audit_house_number(invalid_housenumbers, tag.attrib['v'])
                if is_interpolation(tag):
                    audit_interpolation(interpolation, tag.attrib['v'])
                if is_phone(tag):
                    audit_phone(invalid_phones, tag.attrib['v'])
                if is_website(tag):
                    audit_website(invalid_websites, tag.attrib['v'])
                if is_source_name(tag):
                    audit_source_name(source_names, tag.attrib['v'])
                if is_type(tag):
                    audit_type(types, tag.attrib['v'])

def audit_city(cities, city_value):
    cities.add(city_value)
    #Auditing reveals some erroneous values, which are added to the cities dictionary to map to correct values

def audit_type(types, type_value):
    types.add(type_value)
    # Auditing reveals three distinct values: wheel_benders, coal_post, ha-ha. These appear to be valid values based on OpenStreetMap guidelines for type.
    # No cleanup required

def audit_source_name(source_names, source_name_value):
    source_names.add(source_name_value)
    # Auditing reveals no invalid values. No cleanup required

def audit_website(websites, website_value):
    pass
    # Commented lines below to speed up code execution
    '''try:
    #    if (urllib.request.urlopen(website_value).getcode()) == 200:
    #        pass
    #except (HTTPError, URLError):
        #print(website_value + ': The server couldn\'t fulfill the request.')
    #    invalid_websites.append(website_value)'''

    # Auditing the website reveals several websites that do not work. No cleanup required, but we can flag these.
    # As part of cleanup, we will only check if the value begins with http://, else we insert it

def audit_phone(phones, phone_value):
    mod_phone_value = phone_value.replace(" ", "")
    if len(mod_phone_value) < 10 or len(mod_phone_value) > 14 or invalid_phone_re.search(mod_phone_value):
        invalid_phones.append(phone_value)
    # This audit reveals 44 (0)208 941 7075, +44 01372 463533., 01932 780046;01932 783479 as invalid numbers.
    # Rules for updating are as follows:
    # (1) remove all spaces and ( and )
    # (2) if does not start with +44, insert +44
    # (3) if 0 after +44, remove trailing 0
    # (4) if multiple numbers separated by ; split and apply above rules to each
    # (5) can think of changing the "contact:phone" to "phone" tag. https://wiki.openstreetmap.org/wiki/Key:phone

def audit_street_type(street_types, street_name):
    m = street_type_re.search(street_name)
    if m:
        street_type = m.group()
        street_types[street_type] += 1
    # This audit revealed mostly recognisable street name endings, except for "Rd" and "ROAD" for "Road"
    # Accordingly, the street mapping was updated  
        
def audit_postcode(postcodes, postcode_tag):
    postcode_value = postcode_tag.attrib['v']
    m = postcode_complete_re.fullmatch(postcode_value)
    if m:
        postcodes.append(postcode_value)
    else:
        postcodes_incomplete.append(postcode_value)
    # This audit shows us that postcodes are all in valid format, but 11 of these are incomplete.
    # (contd.) They contain the partial postcode only, which denotes the postal code of the district

def audit_house_number(invalid_housenumbers, housenumber):
    m = housenumber_digits_re.fullmatch(housenumber) or housenumber_unit_re.fullmatch(housenumber) or housenumber_digitstodigits_re.fullmatch(housenumber) or housenumber_multiplenumbers_re.fullmatch(housenumber)
    if not m:
        invalid_housenumbers.add(housenumber)
    # This audit gives us 4 distinct instances of invalid housenumbers. Out of these, Whittets Ait is an exception.
    # It does not have a numeric house number and is a valid entry
    # Council Offices and Padley can be turned into housename
    # i can be recorded as invalid but we don't have information to replace it.
    # Turn semi-colon to comma, if space after comma, remove it.
        
def audit_interpolation(interpolation, interpolation_value):
    interpolation.add(interpolation_value)
    # This audit shows there are two valid values of interpolation: odd and even. No cleaning needed.

def audit_country(country_types, country_name):
    country_types[country_name] += 1
    # This audit shows us that there are 3 instances of "GB" and 1 instance of "UK".
    # These are unnecessary tags given we are examining an area in GB, so we will discard these when converting to csv

def audit_flat(flat_types, flat_tag):
    if (flat_tag.attrib['k'] == "addr:flat"):
        flats.append(flat_tag.attrib['v'])
    else:
        flatnumbers.append(flat_tag.attrib['v'])
    # This audit shows us that both tags are used to represent flat numbers. When converting to csv,
    # we will replace the "flat" tag with the more clearly named "flatnumber" tag

def audit_housename(housename_types, housename_tag):
    if (housename_tag.attrib['k'] == "addr:housename"):
        housenames.append(housename_tag.attrib['v'])
    else:
        addrnames.append(housename_tag.attrib['v'])
    # This audit shows us that both tags are used to represent house names. When converting to csv,
    # we will replace the only 2 "addr:name" tags with the more clearly named "addr:housename" tag
    # Some addr:housename tags contain numbers or are of the form number-number
    # These should be replaced by "addr:housenumber" tags if no "addr:housenumber" tag is present
    # Some addr:housename tags start with "Flat"
    # These should be replaced by "addr:flatnumber" tags if no "addr:flat" or "addr:flatnumber" is present
    # Some addr:housename tags start with "number name".
    # These should be replaced by "addr:housenumber" tags for the number part if house number tag does not exist. "addr:housename" should retain only non-number part
    # (contd.) If name ends with "Street", ignore because addr:street will be present.

# ================================================== #
#               Tag identification functions         #
# ================================================== #

def is_street_name(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "addr:street")

def is_type(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "type")

def is_source_name(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "source:name")

def is_website(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "contact:website")

def is_phone(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] in phone_tags) 

def is_country(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "addr:country")

def is_flat_number(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "addr:flat" or elem.attrib['k'] == "addr:flatnumber")

def is_house_name(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "addr:housename" or elem.attrib['k'] == "addr:name")

def is_postcode(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] in postcode_tags)
    # Note: Another similar attribute source:addr:postcode is not really a postcode
    # It is the name of the data source from where the postcode was obtained

def is_house_number(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "addr:housenumber")

def is_interpolation(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "addr:interpolation")

def is_city_name(elem):
    return (elem.tag == "tag") and (elem.attrib['k'] == "addr:city")

           
# ================================================== #
#               Helper Functions                     #
# ================================================== #

def print_sorted_dict(d):
    keys = d.keys()
    keys = sorted(keys, key=lambda s: s.lower())
    for k in keys:
        v = d[k]
        print ("%s: %s" % (k, v)) 

def get_element(osm_file, tags=('node', 'way', 'relation')):
    """Yield element if it is the right type of tag"""

    context = ET.iterparse(osm_file, events=('start', 'end'))
    _, root = next(context)
    for event, elem in context:
        if event == 'end' and elem.tag in tags:
            yield elem
            root.clear()


class UnicodeDictWriter(csv.DictWriter, object):
    """Extend csv.DictWriter to handle Unicode input"""

    def writerow(self, row):
        super(UnicodeDictWriter, self).writerow({
            k: (v.encode('utf-8') if isinstance(v, str) else v) for k, v in row.items()
        })

    def writerows(self, rows):
        for row in rows:
            self.writerow(row)


# ================================================== #
#               Load, clean, convert, store data     #
# ================================================== #
def process_map(file_in):
    """Iteratively process each XML element and write to csv(s)"""

    with codecs.open(NODES_PATH, 'w') as nodes_file, \
         codecs.open(NODE_TAGS_PATH, 'w') as nodes_tags_file, \
         codecs.open(WAYS_PATH, 'w') as ways_file, \
         codecs.open(WAY_NODES_PATH, 'w') as way_nodes_file, \
         codecs.open(WAY_TAGS_PATH, 'w') as way_tags_file:

        nodes_writer = UnicodeDictWriter(nodes_file, NODE_FIELDS, lineterminator='\n')
        node_tags_writer = UnicodeDictWriter(nodes_tags_file, NODE_TAGS_FIELDS, lineterminator='\n')
        ways_writer = UnicodeDictWriter(ways_file, WAY_FIELDS, lineterminator='\n')
        way_nodes_writer = UnicodeDictWriter(way_nodes_file, WAY_NODES_FIELDS, lineterminator='\n')
        way_tags_writer = UnicodeDictWriter(way_tags_file, WAY_TAGS_FIELDS, lineterminator='\n')

        nodes_writer.writeheader()
        node_tags_writer.writeheader()
        ways_writer.writeheader()
        way_nodes_writer.writeheader()
        way_tags_writer.writeheader()

        for element in get_element(file_in, tags=('node', 'way')):
            el = shape_element(element)
            if el:
                if element.tag == 'node':
                    nodes_writer.writerow(el['node'])
                    node_tags_writer.writerows(el['node_tags'])
                elif element.tag == 'way':
                    ways_writer.writerow(el['way'])
                    way_nodes_writer.writerows(el['way_nodes'])
                    way_tags_writer.writerows(el['way_tags'])


# ================================================== #
#               Main                                 #
# ================================================== #
if __name__ == '__main__':

    # Step 1: Audit (then manually inspect results)
    osm_file = open("map.osm", mode='r', encoding='utf-8')
    audit()
    osm_file.close()

    # Step 2: Load data, clean and write to csv 
    osm_file = open("map.osm", mode='r', encoding='utf-8')
    process_map(osm_file)
