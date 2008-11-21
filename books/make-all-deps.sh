#!/bin/bash


BOOK_DIRS=${BOOK_DIRS[*]:-`find * -type d | grep -v "\.svn" | grep -v workshops`}
SYSBOOKS_SKIP=no
SYSBOOKS_DIR=""

# Override the above assignments with the values in the local dep-params.sh, if exists
if [ -f dep-params.sh ] ; then source dep-params.sh ; fi

TARGET=`pwd`/Makefile-alldeps
BASE=`pwd`

case `uname` in
    Linux)    SED_FLG="-r" ;;
    Darwin)   SED_FLG="-E" ;;
    *)        SED_FLG="-r" ;;
esac


fixdotdots () {

    THE_PATH="$1";
    THE_NEW_PATH=`echo "$THE_PATH" | sed $SED_FLG -e 's!( |\/)[^/:]*\/\.\.\/!\1!'`
    if [ "$THE_PATH" == "$THE_NEW_PATH" ] ;
	then
	echo $THE_PATH;
    else
	fixdotdots "$THE_NEW_PATH";
    fi
}

fixdotdots_top () {
    lines=`cat $1`;
    IFS="
"
    for line in $lines ;
    do
      fixdotdots "$line";
    done
}
    

# Now walk through each one, make its Makefile-deps if not already made, and
# then add all the dependencies into the Makefile-alldeps in the main books dir.

echo "" > $TARGET
for d in ${BOOK_DIRS[*]}
do
    cd $d
	
    if [ ! -f Makefile ]
	then
	echo "Skipping $d since there is no Makefile there."
	cd $BASE
	continue
    fi

    make -s nothing > /dev/null 2>&1
    
    if [ ! -f Makefile-deps ]
	then
	echo "Skipping $d because Makefile-deps was not created."
	cd $BASE
	continue
    fi
	
    echo "# From $d/Makefile-deps" >> $TARGET
    cat Makefile-deps | grep -v "^#" | grep ":" \
	| sed $SED_FLG -e "s|(.*): (.*)|$d/\\1: $d/\\2|" | fixdotdots_top >> $TARGET
    
    if [ $SYSBOOKS_SKIP == no ] ; then
	echo "# From $d/Makefile-deps (system book comments)" >> $TARGET
	cat Makefile-deps | grep "^.*ACL2_SYSTEM_BOOKS.*" \
	    | sed $SED_FLG -e "s|# (.*):.*\(ACL2_SYSTEM_BOOKS\)/(.*)|$d/\\1: ${SYSBOOKS_DIR}\\2|" \
	    | fixdotdots_top >> $TARGET
    fi

    # BOZO maybe eventually add other stuff from the main Makefile if needed?
    echo "# From $d/Makefile" >> $TARGET
    cat Makefile | egrep -v "^[:BLANK:]" | egrep -v "^#" | egrep "^(.*)\.cert: (.*)" \
       | sed $SED_FLG -e "s|^(.*)\.cert: (.*)|$d/\\1.cert: $d/\\2|" | fixdotdots_top >> $TARGET

    cd $BASE
done


cat $TARGET | grep -v "#" | grep -v "^$" \
    | sed $SED_FLG -e "s|^(.*): .*$|\\1 \\\|" | sort --unique > Makefile-tmp

echo "" >> $TARGET
echo "" >> $TARGET
echo "BOOKS = \\" >> $TARGET
cat Makefile-tmp >> $TARGET
echo "" >> $TARGET
rm Makefile-tmp
