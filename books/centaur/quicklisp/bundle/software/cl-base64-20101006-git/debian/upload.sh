#!/bin/bash -e

dup cl-base64 -Ufiles.b9.com -D/home/ftp/cl-base64 -C"(umask 022; /home/kevin/bin/remove-old-versions cl-base64 latest)" -su $*
