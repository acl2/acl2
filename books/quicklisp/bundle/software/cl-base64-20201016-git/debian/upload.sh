#!/bin/bash -e

dup cl-base64 -Ufiles.kpe.io -D/home/ftp/cl-base64 -su \
    -C"(umask 022; cd /srv/www/html/cl-base64; make install; find . -type d |xargs chmod go+rx; find . -type f | xargs chmod go+r)" $*
