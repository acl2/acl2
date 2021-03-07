#!/bin/sh

# This script checks that only Matt Kaufmann has committed to files
# outside books/.  If others are to be included, update the first call
# of basecmd below.

if [ `basename $PWD` = devel ] ; then \
    echo "ERROR: Must not be in a devel directory." ; \
    exit 1 ; \
fi

export PAGER=cat

# Matt might update this when confident of purity since the indicated date.
export SINCE=2021-03-05

export basecmd="\
git log \
 --name-only \
 --pretty=oneline \
 --since $SINCE"

# Warning: Do not skip this fetch!  In particular, pull.sh relies on it.
echo "Executing git fetch --all"
git fetch --all
echo "-----"

$basecmd \
  --author='Matt Kaufmann <matthew.j.kaufmann@gmail.com>' \
  --author='Matt Kaufmann <kaufmann@wireless-10-147-200-122.public.utexas.edu>' \
  --author='Matt Kaufmann <kaufmann@horatio-123.cs.utexas.edu>' \
  --author='Matt Kaufmann <kaufmann@horatio-217.cs.utexas.edu>' \
  --author='Matt Kaufmann <kaufmann@horatio-168.cs.utexas.edu>' \
  --author='Matt Kaufmann <kaufmann@cs.utexas.edu>' \
  --author='MattKaufmann <matthew.j.kaufmann@gmail.com>' \
  --author='kaufmann <kaufmann@unknown58b035fde782.attlocal.net>' \
  --author='Matt Kaufmann <kaufmann@matts-mbp.attlocal.net>' \
  --author='Matt Kaufmann <kaufmann@Matts-MBP.attlocal.net>' \
  --author="Matt Kaufmann <kaufmann@Matts-MacBook-Pro.local>" \
  --author="Matt Kaufmann <kaufmann@Matts-MBP.home>" \
  --author="Matt Kaufmann <kaufmann@kestrel.edu>" \
  | grep -v '^[a-z0-9]\{40\}' \
  | grep -v '^books/' \
  > /tmp/git-log-matt.txt

$basecmd \
  | grep -v '^[a-z0-9]\{40\}' \
  | grep -v '^books/' \
  > /tmp/git-log-all.txt

export out_all=gitlog-all.txt

export diffcmd='diff /tmp/git-log-matt.txt /tmp/git-log-all.txt'
$diffcmd
if [ $? -ne 0 ] ; then \
    echo "-----"
    echo "ERROR: Someone committed to other than books/!" ; \
    echo "-----"
    git log --name-only --since $SINCE > $out_all
    echo "Search for the above file in $out_all."
    echo "If all is well, change SINCE in $0 to the date of the problem commit."
    exit 1 ; \
else
    echo "$0 PASSED."
fi
