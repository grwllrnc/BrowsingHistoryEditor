# -*- coding: utf-8 -*-

from collections import OrderedDict, Counter
import csv
from datetime import datetime, timedelta
import hashlib
import json
import os
import platform
import plistlib
import re
import shutil
import sqlite3
from subprocess import call
import sys
import time
import urllib
import uuid
import webbrowser
from flask import Flask, render_template, request, flash, url_for, redirect, Response, send_from_directory
import pyesedb
import vss
from werkzeug.utils import secure_filename


class BrowsingHistory(object):
    """A class to load, modify and export a *copy* of the web browsing history.

    Supported browsers:
    - Google Chrome
    - Firefox
    - Safari
    - Internet Explorer (>= 10) / Edge
    """
    def __init__(self):
        self.os = platform.system()
        self.os_release = platform.release()
        self.os_full = ' '.join([self.os, self.os_release])
        self._upload_dir = self._root_path('uploads')
        self._file_path = os.path.split(os.path.realpath(__file__))[0]
        self._browser_name = None
        self._browser_specs = None
        self._db = None
        self._min_date = self._min_date(num_days=60)
        self.date_range = None
        self.num_domains = None
        self.ready = self._state()
        self._domains = None
        self._keywords = None
        self._entries = None



    def _handle_platform(self):
        """Helper function to handle platform name.

        :return str: Platform name
        """
        if self.os in ['Linux', 'Darwin']:
            return self.os
        elif self.os == 'Windows':
            pat = re.compile(r'Windows\s\d{1,2}')
            match = re.findall(pat, self.os_full)
            if match:
                return match[0]


    def _build_path(self, _os):
        """Helper function to build and check the path to the browsing history.

        :param _os: Operation system
        :return str or boolean: path or False
        """
        if (self._browser_name == 'IE11' and self.os in ['Linux', 'Darwin']) or (self._browser_name == 'Safari' and self.os in ['Linux', 'Windows']):
            return False
        else:
            user = os.getlogin()
            for p in self._browser_specs['path'][_os]:
                if self._browser_name == 'Firefox':
                    # checking for profile name
                    pat = re.compile(r'\w+.default([\w\-\_\.]+)?')
                    if os.path.isdir(p.format(user)):
                        for item in os.listdir(p.format(user)):
                            if re.findall(pat, item):
                                profile_name = item
                                path = os.path.join(p.format(user), profile_name, self._browser_specs['file_name'][0])
                                if os.path.isfile(path):
                                    return path
                                else:
                                    continue
                else:
                    if os.path.isdir(p.format(user)):
                        for f in self._browser_specs['file_name']:
                            path = os.path.join(p.format(user), f)
                            if os.path.isfile(path):
                                return path
                            else:
                                continue
            return False



    def _create_db(self):
        """Creates an empty temporary sqlite database in the 'tmp' directory.

        :return: Database path or None
        """
        try:
            conn = sqlite3.connect('tmp/browsing_history.db')
            cur = conn.cursor()
            with open(self._root_path('data/schema.sql'), 'r') as sql_script:
                queries = sql_script.read()
            cur.executescript(queries)
            conn.commit()
        except BaseException:
            return None
        finally:
            cur.close()
            conn.close()
            return 'tmp/browsing_history.db'

    def _unique_id_generator(self):
        """Helper function to generate unique identifiers.

        :return: integer value
        """
        unique_id = 1
        while True:
            yield unique_id
            unique_id += 1

    def _extract_history_plist(self, pl):
        """Extracts Safari browsing history (History.plist) file.

        :param pl: File path (string)
        :return: Two lists of tuples
        """
        visits = []
        urls = []
        g = self._unique_id_generator()
        with open(pl, 'rb') as f:
            d = plistlib.load(f)
        for item in d['WebHistoryDates']:
            date = self._convert_timestamp(float(item['lastVisitedDate']), browser_name=self._browser_name, tz='utc')
            # Filter by url and minimum date
            if self._is_url(item['']) and date >= self._min_date:
                last_visit_date = date
                visit_date = last_visit_date
                url = item['']
                title = item['title']
                visit_count = item['visitCount']
                if 'redirectURLs' in item.keys():
                    redirect_urls = ' '.join(item['redirectURLs'])
                else:
                    redirect_urls = None
                url_id = next(g)
                _id = url_id
                urls.append((_id, last_visit_date, redirect_urls, title, url, visit_count))
                visits.append((url_id, visit_date))
            else:
                continue
        return urls, visits
    
    
    def _copy_webcachev01_dat(self, file_path):
        '''
        Creates a shadow copy of WebCacheVxx.dat and copies it into the upload folder.
        :param file_path: The file path of WebCacheVxx.dat
        :return: Boolean value
        '''
        # Adapted from sblosser's example code:
        # https://github.com/sblosser/pyshadowcopy
        # on 2017-07-31
        
        # Create a set that contains the LOCAL disks you want to shadow
        drv = file_path[0]
        local_drives = set()
        local_drives.add(drv)

        # Initialize the Shadow Copies
        try:
            sc = vss.ShadowCopy(local_drives)
            # An open and locked file we want to read
            locked_file = file_path
            shadow_path = sc.shadow_path(locked_file)
            try:
                shutil.copy(shadow_path, self._root_path('uploads'))
            except BaseException as e:
                print(e)
                sc.delete()
                return False
            finally:
                sc.delete()
                return True
        except BaseException:
            return False
    

    def _extract_webcachev01_dat(self, file_path):
        """Extracts data from WebCacheVxx.dat.
        
        :param str file_path: The file path of WebCacheVxx.dat
        :return lists urls, visits: Two lists of tuples
        """
        # Adapted from Jon Glass' blog:
        # http://jon.glass/blog/attempts-to-parse-webcachev01-dat/
        # on 2017-07-31
        if self._copy_webcachev01_dat(file_path):
            file_name = os.path.split(file_path)[1]
        elif 'WebCacheV01.dat' in os.listdir(self._upload_dir):
            file_name = 'WebCacheV01.dat'
        elif 'WebCacheV24.dat' in os.listdir(self._upload_dir):
            file_path = 'WebCacheV24.dat'
        else:
            return False
        visits = []
        urls = {}
        pat = re.compile(r'(?<=@)http[\w:\_\-/.]+')
        esedb_file = pyesedb.file()
        try:
            with open(os.path.join(self._root_path('uploads'), file_name), "rb") as f:
                esedb_file.open_file_object(f)
                containers_table = esedb_file.get_table_by_name("Containers")
                g = self._unique_id_generator()
                for i in range(0, containers_table.get_number_of_records()):
                    if containers_table.get_record(i).get_value_data_as_string(8) == 'History':
                        container_id = containers_table.get_record(i).get_value_data_as_integer(0)
                        history_table = esedb_file.get_table_by_name("Container_" + str(container_id))
                        for j in range(0, history_table.get_number_of_records()):
                            if history_table.get_record(j).is_long_value(17):
                                url = history_table.get_record(j).get_value_data_as_long_value(17).get_data_as_string()
                            else:
                                url = history_table.get_record(j).get_value_data_as_string(17)
                            date = self._convert_timestamp(history_table.get_record(j).get_value_data_as_integer(13), browser_name=self._browser_name, tz='utc')
                            # Filter by url and minimum date
                            if re.findall(pat, url) and date >= self._min_date:
                                url = re.findall(pat, url)[0]
                                if url not in urls.keys():
                                    unique_id = next(g)
                                    urls[url] = {}
                                    urls[url]['unique_id'] = unique_id
                                    urls[url]['access_count'] = history_table.get_record(j).get_value_data_as_integer(8)
                                    urls[url]['redirect_urls'] = history_table.get_record(j).get_value_data_as_string(22)
                                    entry_id = history_table.get_record(j).get_value_data_as_integer(0)
                                    accessed_time = date
                                    unique_entry_id = int(str(container_id) + str(unique_id))
                                    visits.append((accessed_time, unique_entry_id, urls[url]['unique_id']))
                                else:
                                    access_count = history_table.get_record(j).get_value_data_as_integer(8)
                                    if access_count > 0:
                                        urls[url]['access_count'] += access_count
                            else:
                                continue
                esedb_file.close()
                urls = [(value['access_count'], value['redirect_urls'], value['unique_id'], key) for key, value in
                        urls.items()]
            return urls, visits
        except PermissionError:
            return False
            

    def _import_data(self, file_path=None):
        """Imports data from a file into the database.
        
        :param file_path: The file path of the browsing history database file (e.g., sqlite database file or a plist property list file).
        :return: boolean value
        """
        if file_path:
            file_path = file_path
        else:
            file_path = self._build_path(self._handle_platform())
        if file_path:
            db_tables = tuple(self._browser_specs['tables'].keys())
            translate = self._load_json(self._root_path('data'), 'table_names')
            conn = False
            if self._browser_name == 'Safari':
                file_name = os.path.split(file_path)[1]
                if file_name == 'History.db':
                    safari8_tables = self._browser_specs['tables_s8']
                    db_tables = tuple(safari8_tables.keys())
                    if os.path.split(file_path)[0] != self._upload_dir:
                        try:
                            shutil.copy(file_path, self._root_path('uploads'))
                        except shutil.Error as e:
                            print(e)
                            return False
                        file_path = os.path.join(self._root_path('uploads'), file_name)
                    try:
                        conn = sqlite3.connect(file_path)
                    except sqlite3.OperationalError as e:
                        print(e)
                        return False
                else:
                    urls, visits = self._extract_history_plist(file_path)
            elif self._browser_name == 'IE11':
                try:
                    urls, visits = self._extract_webcachev01_dat(file_path)
                except TypeError:
                    return False
            elif self._browser_name == 'Chrome':
                if os.path.split(file_path)[0] != self._upload_dir:
                    try:
                        shutil.copy(file_path, self._root_path('uploads'))
                    except shutil.Error as e:
                        print(e)
                        return False
                    file_path = os.path.join(self._root_path('uploads'), self._browser_specs['file_name'][0])
                try:
                    conn = sqlite3.connect(file_path)
                except sqlite3.OperationalError as e:
                    print(e)
                    return False
            elif self._browser_name == 'Firefox':
                try:
                    conn = sqlite3.connect(file_path)
                except sqlite3.OperationalError as e:
                    print(e)
                    return False
            new_db = sqlite3.connect(self._db)
            new_db_cur = new_db.cursor()
            for table in db_tables:
                if conn and self._browser_name == 'Safari':
                    od = OrderedDict(sorted(safari8_tables[table].items(), key=lambda t: t[0]))
                else:
                    od = OrderedDict(sorted(self._browser_specs['tables'][table].items(), key=lambda t: t[0]))
                if conn:
                    conn.create_function('REGEXP', 2, self._regexp)
                    c = conn.cursor()
                    if translate[table] == 'visits':
                        if self._browser_name == 'Chrome':
                            q = "SELECT {0} FROM visits WHERE ((visits.visit_time/1000000)-11644473600) >= {1};".format(', '.join(od.keys()), self._min_date)
                        elif self._browser_name == 'Firefox':
                            q = "SELECT {0} FROM moz_historyvisits WHERE (visit_date/1000000) >= {1};".format(', '.join(od.keys()), self._min_date)
                        elif self._browser_name == 'Safari':
                            q = "SELECT {0} FROM history_visits WHERE (history_visits.visit_time + 978307200) >= {1};".format(', '.join(od.keys()), self._min_date)
                        else:
                            raise ValueError("Browser name {0} doesn't match.".format(self._browser_name))
                    else:
                        if self._browser_name == 'Chrome':
                            q = "SELECT {0} FROM urls, visits WHERE urls.id = visits.url AND ((visits.visit_time/1000000)-11644473600) >= {1} AND NOT REGEXP('^file:', urls.url);".format(', '.join(od.keys()), self._min_date)
                        elif self._browser_name == 'Firefox':
                            q = "SELECT {0} FROM moz_places, moz_historyvisits WHERE moz_places.id = moz_historyvisits.place_id AND (moz_historyvisits.visit_date/1000000) >= {1} AND NOT REGEXP('^file:///', moz_places.url);".format(', '.join(od.keys()), self._min_date)
                        elif self._browser_name == 'Safari':
                            q = "SELECT {0} FROM history_items, history_visits WHERE history_items.id = history_visits.history_item AND (history_visits.visit_time + 978307200) >= {1} AND NOT REGEXP('^file:', history_items.url);".format(', '.join(od.keys()), self._min_date)
                        else:
                            raise ValueError("Browser name {0} doesn't match.".format(self._browser_name))
                    rq = c.execute(q)
                    r = rq.fetchall()
                else:
                    if translate[table] == 'visits':
                        r = visits
                    else:
                        r = urls
                # Insert data into new database
                try:
                    if conn and self._browser_name == 'Safari':
                        placeholders = ', '.join(['?' for x in range(len(safari8_tables[table].values()))])
                    else:
                        placeholders = ', '.join(['?' for x in range(len(self._browser_specs['tables'][table].values()))])
                    query = 'INSERT OR IGNORE INTO {0} ({1}) VALUES ({2});'.format(translate[table], ', '.join(od.values()),
                                                                         placeholders)
                    new_db_cur.executemany(query, r)
                    new_db.commit()
                except sqlite3.OperationalError as e:
                    print('sqlite3.OperationalError: ', e)
                    return False
            if conn:
                c.close()
                conn.close()
            new_db_cur.close()
            new_db.close()
            return True
        else:
            return False

    def _regexp(self, p, s):
        pat = re.compile(p)
        if re.match(pat, s):
            return True
        else:
            return False

    def _load_json(self, path, name):
        """Helper function to load the json browser spec files.

        :param path: Path name
        :param name: File name (without file extension)
        :return: json object
        """
        with open('{0}.json'.format(os.path.join(path, name)), 'r') as file:
            return json.load(file)

    def _save_json(self, data, path, name):
        """Helper function to write json object to a json file.

        :param data: json object
        :param path: path name
        :param name: file name (without file extension)
        :return: nothing
        """
        with open('{0}.json'.format(os.path.join(path, name)), 'w') as file:
            json.dump(data, fp=file)

    def load(self, file_path=None, browser_name=None, min_date=None):
        """Loads the browsing history.
        
        :param str file_path: The file path of the browsing history
        :param str browser_name: The browser name
        :param min_date: The start date of the import
        :return: boolean value
        """
        self._db = self._create_db()
        if browser_name == None:
            self._browser_name = self._load_json('tmp', 'browser_name')['browser_name']
        else:
            self._browser_name = browser_name
            self._save_json({'browser_name': self._browser_name}, 'tmp', 'browser_name')
        self._browser_specs = self._load_json(self._root_path('data'), self._browser_name)
        if min_date:
            self._min_date = min_date
        if self._db:
            if file_path:
                status = self._import_data(file_path=file_path)
            else:
                status = self._import_data()
            if status:
                self.date_range = self._date_range()
                self.num_domains = len(self.visits(date=False, n=None, ascending=False, plot=False))
                self.ready = True
                return True
            else:
                return False

    def _state(self):
        """Helper function to keep track of the current state of the temporary database.

        :return: boolean value
        """
        db = 'tmp/browsing_history.db'
        if os.path.isfile(db):
            try:
                self._db = db
                self._browser_name = self._load_json('tmp', 'browser_name')['browser_name']
                self._browser_specs = self._load_json(self._root_path('data'), self._browser_name)
                self.date_range = self._date_range()
                self.num_domains = len(self.visits(date=False, n=None, ascending=False, plot=False))
                return True
            except TypeError:
                return False
        else:
            return False

    def _query(self, q):
        """Helper function to query the sqlite database.

        :param str q: Sqlite query
        :return: List of tuples
        """
        if self._db:
            with sqlite3.connect(self._db) as conn:  # connection to db
                c = conn.cursor()
                c.execute(q)
                return c.fetchall()
        else:
            return []


    def _update_db(self, x, kind='domains'):
        """Update function for the sqlite database.

        :param list x: URL ids
        :param str kind: What kind of data should be updated. domains (default), keywords, urls
        :return: nothing
        """
        #self.ready = False
        try:
            conn = sqlite3.connect(self._db)
            c = conn.cursor()
            if isinstance(x, str):
                if kind == 'keywords':
                    pat = re.compile(r'(?:\?q=|\?p=|\?query=|search?q=|\?q\d=|\&q\d=|\?k=|\?text=|\&q=|key=|\?search=|\&search=|\&searchTerm=|\?searchTerm=)([a-zA-Z0-9äöüïéàèáÜÄÖ\%\+\-\*\s]+)', re.IGNORECASE)
                    _ids = self._keywords[x]['ids']
                else:
                    _ids = self._domains[x]['ids']
            elif isinstance(x, list) and kind == 'urls':
                _ids = x
            else:
                raise ValueError('Input type unsupported: expects string or list')
            for i in _ids:
                entry = c.execute("SELECT url, rev_host FROM urls WHERE id = ?;", (i,)).fetchall()
                url = self._is_url(entry[0][0], r=True)
                if url:
                    hashed_url = self._hash_domain(url)
                    unique_id = '{0}-{1}-{2}'.format('anonymisiert', hashed_url, i)
                    if kind == 'keywords':
                        new_entry = re.sub(pat, unique_id, entry[0][0])
                        c.execute('UPDATE urls SET url = ?, title = ? WHERE id = ?;', (new_entry, '***', i))
                        conn.commit()
                    elif kind == 'urls':
                        domain = '{0}/{1}'.format(self._stem_url(entry[0][0]), '***')
                        c.execute('UPDATE urls SET url = ?, title = ?, redirect_urls = ? WHERE id = ?;', (domain, '***', '***', i))
                        conn.commit()
                    elif kind == 'domains':
                        c.execute('UPDATE urls SET url = ?, title = ?, rev_host = ?, redirect_urls = ? WHERE id = ?;', (unique_id, '***', '***', '***', i))
                        conn.commit()
                    else:
                        raise ValueError('{0} is not a valid kind.'.format(kind))
                else:
                    continue
        except sqlite3.OperationalError as e:
            print(e)
        finally:
            c.close()
            conn.close()


    def _date_conv(self, date):
        """Helper function to convert the date(s).

        :param date: string or list in %Y-%m-%d format
        :return: start (int), end (int), date (string)
        """
        if isinstance(date, list):
            date_str = 'between {0} and {1}'.format(date[0], date[1])
            t = int(time.mktime(datetime.strptime(date[0], "%Y-%m-%d").timetuple()) * 1000000)
            tk = int(time.mktime(datetime.strptime(date[1], "%Y-%m-%d").timetuple()) * 1000000)
        elif isinstance(date, str):
            date_str = 'on {0}'.format(date)
            t = int(time.mktime(datetime.strptime(date, "%Y-%m-%d").timetuple()))
            tk = datetime.strptime(date, "%Y-%m-%d") + timedelta(days=1)
            tk = int(time.mktime(tk.timetuple()) * 1000000)
        return t, tk, date_str

    def visits(self, date=False, n=25, ascending=False, plot=False):
        """Function to load all URLs from the database for a certain date or date range.

        :param str date: A date (e.g., '2016-10-15') or a date range as list (e.g., ['2016-10-15','2016-10-25'])
        :param int n: the number of websites that should be plotted, default = top 25; for all websites set n = None
        :param boolean ascending: order
        :param plot: boolean value
        :return: OrderedDict
        """
        if date:
            t, tk, date_str = self._date_conv(date)
        else:
            date_str = 'between {0} and {1}'.format(self.date_range[0], self.date_range[1])
        if date:
            visits = self._query(
                "SELECT url, visit_count, urls.id FROM urls, visits WHERE urls.id = visits.url_id AND visit_date >= {0} AND visit_date < {1};".format(
                    t, tk))
        else:
            visits = self._query("SELECT url, visit_count, urls.id FROM urls, visits WHERE urls.id = visits.url_id;")
        d = {}
        unique_id = set()
        for visit in visits:
            domain = self._stem_url(visit[0])
            count = visit[1]
            if domain not in d.keys():
                d[domain] = 0
            if visit[2] not in unique_id:
                unique_id.add(visit[2])
                d[domain] += count
        total_n = sum(d.values())
        if n == None:
            n = total_n
        if ascending == False:
            title = 'Top {0} visited websites {1} (n={2})'.format(n, date_str, total_n)
            od = OrderedDict(sorted(d.items(), key=lambda t: t[1])[-n:])
        else:
            title = 'Least {0} visited websites {1} (n={2})'.format(n, date_str, total_n)
            od = OrderedDict(sorted(d.items(), key=lambda t: t[1])[:n])
        source = {'x': list(od.keys()), 'y': list(od.values()),
                  'perc': [round((v / total_n) * 100, 2) for v in list(od.values())]}
        if plot == True:
            self._vbarplot(source, title)
        else:
            return od


    def entries(self, sort_by='date', q=None):
        """Function to load all entries from the database.

        :param str sort_by: Order. Domains or frequency
        :param str q: Search term
        :param stem_urls: Boolean value. Whether to return domains or urls
        :return: OrderedDict
        """
        d = {}
        if q == None:
            visits = self._query("SELECT urls.id, visit_date, url, visit_count FROM visits, urls WHERE visits.url_id = urls.id;")
        else:
            visits = self._query("SELECT urls.id, visit_date, url, visit_count FROM visits, urls WHERE visits.url_id = urls.id AND url LIKE '%{0}%';".format(q))
        # Filtering URLs only
        visits = [(e[0], self._get_date(e[1]), e[2], e[3], e[1]) for e in visits]
        # Sorting
        if sort_by == 'domains' or sort_by == None:
            visits = sorted(visits, key=lambda t: t[2])
        elif sort_by == 'frequency':
            visits = sorted(visits, key=lambda t: t[3], reverse=True)
        elif sort_by == 'date' or sort_by == None:
            visits = sorted(visits, key=lambda t: t[4], reverse=True)
        self._entries = visits
        return visits


    def select_domains(self, sort_by='domains', q=None, stem_urls=True):
        """Function to load all URLs from the database.

        :param str sort_by: Order. Domains or frequency
        :param str q: Search term
        :param boolean stem_urls: Whether to return domains or urls
        :return: OrderedDict
        """
        d = {}
        if q == None:
            visits = self._query("SELECT id, url, visit_count FROM urls;")
        else:
            visits = self._query("SELECT id, url, visit_count FROM urls WHERE url LIKE '%{0}%';".format(q))
        for visit in visits:
            if stem_urls:
                domain = self._stem_url(visit[1])
            else:
                domain = visit[1]
            count = visit[2]
            if domain in d.keys():
                d[domain]['ids'].append(visit[0])
            else:
                d[domain] = {'ids': [], 'count': 0}
                d[domain]['ids'].append(visit[0])
            d[domain]['count'] += count
        if sort_by == 'domains' or sort_by == None:
            od = OrderedDict(sorted(d.items(), key=lambda t: t[0]))
        elif sort_by == 'frequency':
            od = OrderedDict(sorted(d.items(), key=lambda t: t[1]['count'], reverse=True))
        self._domains = od
        return od
    

    def search_terms(self, sort_by='keywords', q=None):
        """Extracts search terms from urls in the database.

        :param str sort_by: specifies how the OrderedDict should be sorted. Default is keywords.
        :param str q: optional argument for a specific search term
        :return: OrderedDict
        """
        d = {}
        pat = re.compile(r'(?:\?q=|\?p=|\?query=|search?q=|\?q\d=|\&q\d=|\?k=|\?text=|\&q=|key=|\?search=|\&search=|\&searchTerm=|\?searchTerm=)([a-zA-Z0-9äöüïéàèáÜÄÖ\%\+\-\*\s\.\,]+)', re.IGNORECASE)
        if q:
            entries = self._query("SELECT id, url FROM urls WHERE url LIKE '%{0}%';".format(q))
        else:
            entries = self._query('SELECT id, url FROM urls;')
        for entry in entries:
            domain = self._stem_url(entry[1])
            matches = re.findall(pat, entry[1])
            if matches:
                for match in matches:
                    term = urllib.parse.unquote_plus(match)
                    if term not in d.keys():
                        d[term] = {'ids': [], 'count': 1, 'urls': [domain], 'match': match}
                        d[term]['ids'].append(entry[0])
                    else:
                        d[term]['ids'].append(entry[0])
                        d[term]['count'] += 1
                        if domain not in d[term]['urls']:
                            d[term]['urls'].append(domain)
        if sort_by == 'keywords' or sort_by == None:
            od = OrderedDict(sorted(d.items(), key=lambda t: t[0]))
        elif sort_by == 'frequency':
            od = OrderedDict(sorted(d.items(), key=lambda t: t[1]['count'], reverse=True))
        self._keywords = od
        return od


    def export(self):
        """Writes the browsing history to a CSV file.

        :return: Boolean value
        """
        data = self._query(
            "SELECT url_id, visits.id, url, title, rev_host, visit_count, typed, last_visit_date, redirect_urls, referrer, visit_date, visit_type FROM visits, urls WHERE visits.url_id = urls.id;")
        if data:
            data = [t + (self._browser_name, self.os_full) for t in data]
            header = ['url_id', 'visits_id', 'url', 'title', 'rev_host', 'visit_count', 'typed', 'last_visit_date',
                      'redirect_urls', 'referrer', 'visit_date', 'visit_type', 'browser', 'operation system']
            with open(os.path.join(self._file_path,'tmp', 'Export_Browserverlauf.csv'), 'w', encoding='utf-8') as f:
                writer = csv.writer(f, delimiter=';', lineterminator='\n')
                writer.writerow(header)
                writer.writerows(data)
            return True
        else:
            return False


    def _date_range(self):
        """Helper function.

        :return: Minimum and maximum date (timestamps)
        """
        min_date, max_date = self._query("SELECT min(visit_date), max(visit_date) FROM visits;")[0]
        if min_date and max_date:
            min_date = self._get_date(min_date)
            max_date = self._get_date(max_date)
            return (min_date, max_date)
        else:
            return (' ', ' ')


    def _hash_domain(self, domain):
        """Helper function to hash the domain.

        :param domain: Domain (string)
        :return: Hashed domain
        """
        salt = uuid.uuid4().hex
        return hashlib.sha256(salt.encode() + domain.encode()).hexdigest() + '-' + salt


    def _get_date(self, timestamp):
        """Helper function to convert timestamps into date strings.

        :param timestamp: Timestamp
        :return: Date string (e.g., '13.05.2014 08:34:45')
        """
        date = datetime.fromtimestamp(timestamp)
        return date.strftime('%d.%m.%Y %H:%M:%S')

        
    def _convert_timestamp(self, timestamp, browser_name=None, tz='utc'):
        """Helper function to convert different timestamps formats into date strings or POSIX timestamp.

        :param timestamp: Timestamp
        :return: POSIX timestamp (UTC)
        """
        if browser_name == 'Chrome':
            date = datetime(1601, 1, 1) + timedelta(microseconds=timestamp)
        elif browser_name == 'IE11':
            date = datetime(1601, 1, 1) + timedelta(microseconds=timestamp * 0.1)
        elif browser_name == 'Safari':
            date = datetime(2001, 1, 1) + timedelta(seconds=timestamp)
        elif browser_name == 'Firefox':
            date = datetime.fromtimestamp(timestamp / 1000000)
        else:
            date = datetime.fromtimestamp(timestamp)
        return date.timestamp()


    def _get_dto(self, timestamp):
        """Helper function to convert a timestamp to a datetime object

        :param timestamp: Timestamp
        :return: Datetime object
        """
        return datetime.fromtimestamp(timestamp / 1000000)


    def _min_date(self, num_days):
        """Helper function to determine the minimum date

        :param int num_days: Number days to go back in time
        :return: timestamp (UTC)
        """
        today = datetime.today()
        days = timedelta(num_days)
        min_date = today - days
        return min_date.timestamp()


    def _stem_url(self, url):
        """Helper function to stem URLs.

        :param str url: URL
        :return str: Domain
        """
        anonym_pattern = re.compile('anonymisiert-[\w]+\-[\w]+')
        stemmed_url = self._is_url(url, r=True)
        if stemmed_url:
            if stemmed_url[:4] == 'www.':
                return stemmed_url[4:]
            else:
                return stemmed_url
        else:
            # checking for domain made anonymous
            if re.findall(anonym_pattern, url):
                return re.findall(anonym_pattern, url)[0]
            else:
                # check if url is already stemmed
                if url[:-5:-1] == '***/':
                    return url[:-4]
                else:
                    return url
            

    def _is_url(self, url, r=False):
        """Helper function to check if a string is an URL.

        :param url: URL (string)
        :param r: Whether the URL should be return or not
        :return: URL (string) or boolean value
        """
        url_pattern = re.compile('(?<=\:\/\/)[a-z0-9\.\-\:]+')
        match = re.findall(url_pattern, url)
        if match:
            if r:
                return match[0]
            else:
                return True
        else:
            return False


    def _root_path(self, relative_path):
        """Helper function for path handling after bundling with pyinstaller.

        :param str: relative path
        """
        # Adapted from max' StackOverflow answer:
        # https://stackoverflow.com/questions/7674790/bundling-data-files-with-pyinstaller-onefile/13790741#13790741
        # on 2017-07-31
        try:
            base_path = sys._MEIPASS
        except Exception:
            base_path = os.path.abspath('.')
        return os.path.join(base_path, relative_path)



def root_path(relative_path):
    """Helper function for path handling after app bundling

    :param str: relative path
    """
    # Adapted from StackOverflow answer: https://stackoverflow.com/questions/7674790/bundling-data-files-with-pyinstaller-onefile/13790741#13790741; 2017-07-31
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath('.')
    return os.path.join(base_path, relative_path)

if not os.path.isdir(root_path('uploads')):
    os.mkdir(root_path('uploads'))

ALLOWED_EXTENSIONS = set(['sqlite', 'dat', 'plist', 'History', 'db'])
FILE_PATH = os.path.split(os.path.realpath(__file__))[0]

bh = BrowsingHistory()

app = Flask(__name__, root_path=root_path('.'))
app.secret_key = '8927-bdjbj20AWER$_'

#app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER


def allowed_file(filename):
    # Taken from Flask doc example: http://flask.pocoo.org/docs/0.12/ 
    if '.' in filename:
        return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS
    else:
        return filename in ALLOWED_EXTENSIONS

def _os_name(_os_full):
    pat = re.compile(r'(?<=Darwin\s)\d{1,2}')
    match = re.findall(pat, _os_full)
    if match:
        if match[0] == '10':
            return 'Mac OS X Snow Leopard'
        elif match[0] == '11':
            return 'Mac OS X Lion'
        elif match[0] == '12':
            return 'OS X Mountain Lion'
        elif match[0] == '13':
            return 'OS X Mavericks'
        elif match[0] == '14':
            return 'OS X Yosemite'
        elif match[0] == '15':
            return 'OS X El Capitan'
        elif match[0] == '16':
            return 'macOS Sierra'
        elif match[0] == '17':
            return 'macOS High Sierra'
    else:
        return _os_full

@app.route('/exit')
def shutdown_server():
    # Taken from Flask doc example: http://flask.pocoo.org/docs/0.12/ 
    func = request.environ.get('werkzeug.server.shutdown')
    if func is None:
        raise RuntimeError('Not running with the Werkzeug Server')
    func()
    return 'Das Programm wurde beendet. Sie können das Fenster schliessen.'


@app.route('/', methods=['GET', 'POST'])
def index():
    # Adapted from Flask doc example: http://flask.pocoo.org/docs/0.12/
    os_name = _os_name(bh.os_full)
    if request.method == 'GET':
        if request.args.get('load'):
            return render_template('index.html', os=os_name)
        elif request.args.get('notFound'):
            flash('Der Browserverlauf wurde nicht gefunden. Bitte wählen Sie die Datei manuell aus.')
            not_found = True
            return render_template('index.html', os=os_name)
        elif request.args.get('fileError'):
            flash('Die Datei konnte nicht gelesen werden.')
            not_found = True
            return render_template('index.html', os=os_name)
        else:
            if bh.ready:
                return redirect(url_for('dashboard'))
            else:
                return render_template('index.html', os=os_name)
    elif request.method == 'POST':
        browser_name = request.form.get('browser_name')
        if 'file' in request.files:
            
            # check if the post request has the file part
            if 'file' not in request.files:
                flash('No file part')
                return redirect(url_for('index', notFound=True, os=os_name))
            file = request.files['file']
            # if user does not select file, browser also
            # submit a empty part without filename
            if file.filename == '':
                flash('No selected file')
                return redirect(url_for('index', notFound=True, os=os_name))
            if file and allowed_file(file.filename):
                if len(os.listdir(root_path('uploads'))) >= 1:
                    for f in os.listdir(root_path('uploads')):
                        os.remove(os.path.join(root_path('uploads'), f))
                filename = secure_filename(file.filename)
                file.save(os.path.join(root_path('uploads'), filename))
                state = bh.load(file_path=os.path.join(root_path('uploads'), filename), browser_name=browser_name)
            else:
                return redirect(url_for('index', fileError=True, os=os_name))
        else:
            state = bh.load(browser_name=browser_name)
        if state:
            return redirect(url_for('dashboard'))
        else:
            return redirect(url_for('index', notFound=True, client=browser_name, os=os_name))

        
@app.route('/load')
def load():
    return redirect(url_for('index', load=True))

@app.route('/dashboard')
def dashboard():
    if bh.ready == False:
        return redirect(url_for('index'))
    else:
        date_range = bh.date_range
        num_domains = bh.num_domains
        browser_name = bh._browser_name
        top_10 = bh.visits(date = False, n = 10, ascending = False, plot = False)
        top_10 = OrderedDict(sorted(top_10.items(), key=lambda t: t[1], reverse=True))
        return render_template('dashboard.html', date_range=date_range, num_domains=num_domains, browser_name=browser_name, top_10=top_10)

@app.route('/select', methods=['GET', 'POST'])
def select():
    if request.method == 'POST':
        selection = request.form.getlist('check')
        for domain in selection:
            bh._update_db(domain, kind='domains')
        domains = bh.select_domains()
    elif request.method == 'GET':
        if request.args.get('sort') or request.args.get('q'):
            domains = bh.select_domains(sort_by=request.args.get('sort'), q=request.args.get('q'))
        else:
            domains = bh.select_domains()
    return render_template('select_domains.html', domains=domains)

@app.route('/search-terms', methods=['POST', 'GET'])
def search_terms():
    if request.method == 'POST':
        selection = request.form.getlist('check')
        for search_term in selection:
            bh._update_db(search_term, kind='keywords')
        search_terms = bh.search_terms()
    elif request.method == 'GET':
        if request.args.get('sort') or request.args.get('q'):
            search_terms = bh.search_terms(sort_by=request.args.get('sort'), q=request.args.get('q'))
        else:
            search_terms = bh.search_terms()
    return render_template('search_terms.html', search_terms=search_terms)


@app.route('/export')
def export():
    # Adapted from Flask doc example: http://flask.pocoo.org/docs/0.12/ 
    if bh.export():
        return send_from_directory(os.path.join(FILE_PATH, 'tmp'), 'Export_Browserverlauf.csv', as_attachment=True)
    else:
        flash('Export nicht möglich. Bitte laden Sie zuerst einen Browserverlauf.')
        return render_template('index.html', os=' '.join([bh.os, bh.os_release]))


@app.route('/log')
def get_log():
    # Adapted from Flask doc example: http://flask.pocoo.org/docs/0.12/
    if 'server.log' in os.listdir(os.path.join(FILE_PATH, 'tmp')):
        return send_from_directory(os.path.join(FILE_PATH, 'tmp'), 'server.log', as_attachment=True)
    else:
        flash('Es ist kein Log-File gefunden worden.')
        return render_template('index.html', os=' '.join([bh.os, bh.os_release]))


@app.route('/faqs')
def faqs():
    return render_template('faqs.html')


@app.route('/contact')
def contact():
    return render_template('contact.html')


@app.route('/entries', methods=['POST', 'GET'])
def list_entries():
    if request.method == 'GET':
        if request.args.get('sort') or request.args.get('q'):
            urls = bh.entries(sort_by=request.args.get('sort'), q=request.args.get('q'))
        else:
            urls = bh.entries()
    elif request.method == 'POST':
        selection = request.form.getlist('check')
        bh._update_db(selection, kind='urls')
        urls = bh.entries()
    return render_template('entries.html', domains=urls)


@app.errorhandler(404)
def page_not_found(e):
    return render_template('404.html'), 404


@app.errorhandler(405)
def page_not_found(e):
    return render_template('405.html'), 405


@app.errorhandler(500)
def page_not_found(e):
    return render_template('500.html'), 500


if __name__ == '__main__':
    print('STATUS: BrowsingHistoryEditor wird gestartet ...')
    if not app.debug:
        import logging
        from logging import FileHandler
        file_handler = FileHandler(os.path.join(FILE_PATH, 'tmp', 'server.log'))
        file_handler.setLevel(logging.WARNING)
        app.logger.addHandler(file_handler)
        logging.basicConfig(filename=os.path.join(FILE_PATH, 'tmp', 'server.log'), level=logging.DEBUG)
    webbrowser.open('http://localhost:5000', new=2)
    print('STATUS: BrowsingHistoryEditor läuft auf http://localhost:5000 (Drücken Sie CTRL+C, um das Programm zu beenden)')
    app.run(host='localhost', port=5000, debug=False)
