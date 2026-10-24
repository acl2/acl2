#!/bin/sh

# zip-proofs.sh --- run this from the proofs directory after generating all of
# the proofs to generate the .tar.gz files, .zip files, and so on.

set -e

# Bundle the generated proofs.  Safe to run from anywhere: the script first
# moves to its own directory, which is where the proof subdirectories live.
#
#   ./zip-proofs.sh [basename]     (default basename: milawa-proofs)

cd "$(dirname "$0")"

out=${1:-milawa-proofs}

FILES=""
for level in utilities logic level2 level3 level4 level5 level6 level7 \
             level8 level9 level10 level11 user
do
    FILES="$FILES $level $level.events"
done

echo "Making $out.tar.gz"
time tar cf - $FILES | gzip --best -c - > "$out.tar.gz"
ls -lah "$out.tar.gz"

# The other formats are optional; make only the ones whose tool is installed.
if command -v bzip2 > /dev/null 2>&1; then
    echo "Making $out.tar.bz2"
    time tar cf - $FILES | bzip2 --best > "$out.tar.bz2"
    ls -lah "$out.tar.bz2"
fi

if command -v zip > /dev/null 2>&1; then
    echo "Making $out.zip"
    time zip -9 -q -r "$out.zip" $FILES
    ls -lah "$out.zip"
fi

if command -v 7za > /dev/null 2>&1; then
    echo "Making $out.7z"
    time 7za a -mx9 "$out.7z" $FILES > /dev/null
    ls -lah "$out.7z"
fi

echo "All done."
ls -lah "$out".*


