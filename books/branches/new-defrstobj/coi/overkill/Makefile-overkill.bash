#!/bin/sh
#
# RAMS/Overkill System for Regression Testing
#
# File: make/Makefile-overkill.bash - This script calls upon Overkill to do a 
# parallel pcert of a SINGLE library.  It is called from Makefile.top when a 
# user types "make overkill".

source "$MAKEDIR/Makefile-okillprep.bash"

Debug "Checking host communication"
CheckOverkillHosts

Debug "Computing $MYDIR/.okill/HOSTS"
IFS=" "
for host in $HOSTS
do
  echo "$host" >> "$MYDIR/.okill/HOSTS"
done

Debug "Launching overkill executable"
$MAKEDIR/okill/overkill \
    -c "$MYDIR/.okill/COMMANDS" \
    -h "$MYDIR/.okill/HOSTS" \
    -l "$HOME/.overkill-results"

readonly RET=$?

Debug "Overkill is finished"
exit $RET
