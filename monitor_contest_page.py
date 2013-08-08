#!python3.3
# encoding: utf-8
"""
File:        monitor_contest_page.py
Created:     Thursday,  8 August 2013
Author:      Sergey Vinokurov
Description:
"""

from __future__ import print_function, division

import re
import time
from urllib.request import urlopen
import urllib.parse as parse

import xml.dom.minidom as minidom

try:
    from BeautifulSoup import BeautifulSoup # For processing HTML
except ImportError:
    from bs4 import BeautifulSoup # python3+


SLEEP_TIME = 60 # seconds
URL = "http://icfpc2013.cloudapp.net/"

prev_news = None

while True:
    contents = urlopen(URL).read().decode("utf-8")
    soup = BeautifulSoup(contents)
    news_tags = soup.findAll(name = "div", attrs = { "class": ["news-body"] })
    news = set(sorted(map(lambda news_tag: news_tag.prettify(), news_tags)))
    if prev_news is not None and prev_news != news:
        print("got some news!")
        for new in set.difference(news, prev_news):
            print(new)
        print("-" * 80)

    prev_news = news
    time.sleep(SLEEP_TIME)


