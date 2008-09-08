#!/bin/sh

# First, find all the directories with Makefiles that reference Makefile-deps

echo "Choosing subdirectories to consider."

DIRS=`find * -type d | grep -v "\.svn" | grep -v workshops`
TARGET=`pwd`/Makefile-alldeps
BASE=`pwd`


fixdotdots () {

    THE_PATH="$1";
    THE_NEW_PATH=`echo "$THE_PATH" | sed -r -e 's!( |\/)[^/:]*\/\.\.\/!\1!'`
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
for d in $DIRS
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
	| sed -r "s|(.*): (.*)|$d/\\1: $d/\\2|" | fixdotdots_top >> $TARGET
    
    echo "# From $d/Makefile-deps (system book comments)" >> $TARGET
    cat Makefile-deps | grep "^.*ACL2_SYSTEM_BOOKS.*" \
	| sed -r "s|# (.*):.*\(ACL2_SYSTEM_BOOKS\)/(.*)|$d/\\1: \\2|" | fixdotdots_top >> $TARGET
    
    # BOZO maybe eventually add other stuff from the main Makefile if needed?
    echo "# From $d/Makefile" >> $TARGET
    cat Makefile | egrep -v "^[:BLANK:]" | egrep -v "^#" | egrep "^(.*)\.cert: (.*)" \
       | sed -r "s|^(.*)\.cert: (.*)|$d/\\1.cert: $d/\\2|" | fixdotdots_top >> $TARGET

    cd $BASE
done


cat Makefile-alldeps | grep -v "#" | grep -v "^$" \
    | sed -r "s|^(.*): .*$|\\1 \\\|" | sort --unique > Makefile-tmp

echo "" >> $TARGET
echo "" >> $TARGET
echo "BOOKS = \\" >> $TARGET
cat Makefile-tmp >> $TARGET
echo "" >> $TARGET


# echo "rtl/rel4/support/rtlarr.cert: misc/total-order.cert"

# cat Makefile-alldeps | grep -v "#" | grep -v "^$" > makefile-tmp1

# lines=`cat makefile-tmp1`
# IFS="
# "
# for line in $lines ; do
#     echo $line | sed -r "s|^(.*): .*$|\\1 \\\|"
# done | sort --unique


#  >> Makefile-tmp

#  | sort --unique >> Makefile-tmp



# # Then the user should run something like this:       
    
# # make -f Makefile-big -j 8 ACL2=acl2





