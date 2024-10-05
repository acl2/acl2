FROM php:apache-bookworm

# Copyright (C) 2024 Andrew Walter
# Copyright (C) 2024 Yahya Sohail
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
#
# Original author:     Andrew Walter <me@atwalter.com>
# Contributing author: Yahya Sohail  <yahya@yahyasohail.com>

# This Docker image spins up a local instance of a web server to serve the web
# based ACL2 documentation and associated perl scripts.
#
# This is NOT production-quality, rather it is intended to make it easy to test
# any changes to the XDOC fancy viewer, the PHP based seo friendly XDOC manual,
# or the related Perl scripts.
#
# To use this image, you should first ensure that there is a built xdata.js
# file in this directory, and that you have Docker installed. Depending on your
# system configuration, you may need to prepend any Docker commands with
# `sudo`; see Docker's documentation for more info.
# Then, run the following commands:
# - `docker build . -t xdoc-local-server`
# - `docker run -p 8080:80 xdoc-local-server`
# This will result in the xdataget endpoint being available at
# localhost:8080/xdoc/xdataget.pl. You are free to choose a port other than
# 8080 to expose the xdataget.pl endpoint on - just make sure that 8080 is
# replaced with your desired port in the above and below commands/text.
#
# To get the manual to use this endpoint, modify the `XDATAGET` variable in the
# `config.js` file in the same directory as the manual's index.html file,
# setting it to "http://localhost:8080/xdoc/xdataget.pl".
#
# Additionally, the SEO friendly version of the manual is available at
# http://localhost:8080/xdoc/index-seo.php

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        perl \
        libdbi-perl \
        libdbd-sqlite3-perl \
        libcgi-pm-perl \
        libjson-xs-perl \
    && rm -rf /var/lib/apt/lists/* # remove cached apt files

# Get around CORS issues by allowing any origin to access this server.
RUN echo "LoadModule headers_module /usr/lib/apache2/modules/mod_headers.so\n\
Header set Access-Control-Allow-Origin \"*\"" >> /etc/apache2/apache2.conf
# Needed for CGI to work
RUN echo "LoadModule cgid_module /usr/lib/apache2/modules/mod_cgid.so\n\
<Directory "/var/www/html/xdoc">\n\
    Options +ExecCGI\n\
    AddHandler cgi-script .cgi .pl\n\
</Directory>" >> /etc/apache2/apache2.conf

COPY --chown=www-data:www-data . /var/www/html/xdoc
WORKDIR /var/www/html/xdoc
USER www-data
RUN perl xdata2sql.pl
RUN perl xdata2sql4seo.pl
RUN chmod +x xdataget.pl
