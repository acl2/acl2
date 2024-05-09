#!/bin/sh

mkdir cl-utilities-1.2.4
mkdir cl-utilities-1.2.4/doc
cp cl-utilities.asd package.sh collecting.lisp split-sequence.lisp expt-mod.lisp package.lisp compose.lisp extremum.lisp read-delimited.lisp test.lisp copy-array.lisp once-only.lisp rotate-byte.lisp with-unique-names.lisp README cl-utilities-1.2.4/
cp doc/collecting.html doc/expt-mod.html doc/read-delimited.html doc/with-unique-names.html doc/compose.html doc/extremum.html doc/rotate-byte.html doc/copy-array.html doc/index.html doc/split-sequence.html doc/once-only.html doc/style.css cl-utilities-1.2.4/doc/

rm -f cl-utilities-latest.tar.gz cl-utilities-latest.tar.gz.asc

tar -czvf cl-utilities-1.2.4.tar.gz cl-utilities-1.2.4/
ln -s ~/hacking/lisp/cl-utilities/cl-utilities-1.2.4.tar.gz ~/hacking/lisp/cl-utilities/cl-utilities-latest.tar.gz
gpg -b -a ~/hacking/lisp/cl-utilities/cl-utilities-1.2.4.tar.gz
ln -s ~/hacking/lisp/cl-utilities/cl-utilities-1.2.4.tar.gz.asc ~/hacking/lisp/cl-utilities/cl-utilities-latest.tar.gz.asc
rm -Rf cl-utilities-1.2.4/

scp cl-utilities-1.2.4.tar.gz pscott@common-lisp.net:/project/cl-utilities/public_html/cl-utilities-1.2.4.tar.gz
scp cl-utilities-1.2.4.tar.gz.asc pscott@common-lisp.net:/project/cl-utilities/public_html/cl-utilities-1.2.4.tar.gz.asc
scp cl-utilities-latest.tar.gz pscott@common-lisp.net:/project/cl-utilities/ftp/cl-utilities-1.2.4.tar.gz
scp cl-utilities-latest.tar.gz.asc pscott@common-lisp.net:/project/cl-utilities/ftp/cl-utilities-1.2.4.tar.gz.asc
scp cl-utilities-latest.tar.gz pscott@common-lisp.net:/project/cl-utilities/public_html/cl-utilities-latest.tar.gz
scp cl-utilities-latest.tar.gz.asc pscott@common-lisp.net:/project/cl-utilities/public_html/cl-utilities-latest.tar.gz.asc
