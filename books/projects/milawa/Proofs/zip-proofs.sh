#!/bin/sh

# zip-proofs.sh --- run this from the proofs directory after generating all of
# the proofs to generate the .tar.gz files, .zip files, and so on.

set -e

FILES=""
FILES="Sources/Proofs/user      Sources/Proofs/user.events   $FILES"
FILES="Sources/Proofs/level11   Sources/Proofs/level11.events   $FILES"
FILES="Sources/Proofs/level10   Sources/Proofs/level10.events   $FILES"
FILES="Sources/Proofs/level9    Sources/Proofs/level9.events    $FILES"
FILES="Sources/Proofs/level8    Sources/Proofs/level8.events    $FILES"
FILES="Sources/Proofs/level7    Sources/Proofs/level7.events    $FILES"
FILES="Sources/Proofs/level6    Sources/Proofs/level6.events    $FILES"
FILES="Sources/Proofs/level5    Sources/Proofs/level5.events    $FILES"
FILES="Sources/Proofs/level4    Sources/Proofs/level4.events    $FILES"
FILES="Sources/Proofs/level3    Sources/Proofs/level3.events    $FILES"
FILES="Sources/Proofs/level2    Sources/Proofs/level2.events    $FILES"
FILES="Sources/Proofs/logic     Sources/Proofs/logic.events     $FILES"
FILES="Sources/Proofs/utilities Sources/Proofs/utilities.events $FILES"

cd /u/jared/Milawa

echo "Making milawa-proofs.tar.gz"
time tar cf - $FILES | gzip --best -c - > Sources/Proofs/milawa-proofs.tar.gz
ls -lah Sources/Proofs/milawa-proofs.tar.gz

echo "Making milawa-proofs.tar.bz2"
time tar cf - $FILES | bzip2 --best > Sources/Proofs/milawa-proofs.tar.bz2
ls -lah Sources/Proofs/milawa-proofs.tar.bz2

echo "Making milawa-proofs.zip"
time zip -9 -q -r Sources/Proofs/milawa-proofs.zip $FILES
ls -lah Sources/Proofs/milawa-proofs.zip

echo "Making milawa-proofs.tar.7z"
time 7za a -mx9 Sources/Proofs/milawa-proofs.7z $FILES
ls -lah Sources/Proofs/milawa-proofs.7z


echo "All done."
echo "Summary of archives:"

du -hcs Sources/Proofs/milawa-proofs.tar.gz \
        Sources/Proofs/milawa-proofs.tar.bz2 \
        Sources/Proofs/milawa-proofs.7z \
        Sources/Proofs/milawa-proofs.zip


