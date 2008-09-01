#!/bin/sh

# First, find all the directories with Makefiles that reference Makefile-deps

echo "Choosing subdirectories to consider."

DIRS=`find * -type d | grep -v "\.svn" | grep -v workshops`
TARGET=`pwd`/Makefile-alldeps
BASE=`pwd`

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
    
    make -s Makefile-deps > /dev/null 2>&1
    
    if [ ! -f Makefile-deps ]
	then
	echo "Skipping $d becuase Makefile-deps was not created."
	cd $BASE
	continue
    fi
	
    echo "# From $d/Makefile-deps" >> $TARGET
    cat Makefile-deps | grep -v "^#" | grep ":" \
	| sed -r "s|(.*): (.*)|$d/\\1: $d/\\2|" >> $TARGET
    
    echo "# From $d/Makefile-deps (system book comments)" >> $TARGET
    cat Makefile-deps | grep "^.*ACL2_SYSTEM_BOOKS.*" \
	| sed -r "s|# (.*):.*\(ACL2_SYSTEM_BOOKS\)/(.*)|$d/\\1: \\2|" >> $TARGET
    
    # BOZO maybe eventually add other stuff from the main Makefile if needed?
    #echo "# From $d/Makefile" >> $TARGET
    #cat Makefile | grep -v "^[ \t].*#" | grep -v "^[\t]" | grep "(.*)\.cert: (.*)" \
    #   | sed -r "s|(.*)\.cert:(.*)|$d/\\1.cert: \\2|" >> $TARGET 

    cd $BASE
done

# Finally write out a Makefile-big that can be used to actually run this stuff.

echo "BOOKS = \\" > Makefile-big
cat Makefile-alldeps | grep -v "#" | grep -v "^$" | sed -r "s|(.*):.*|\\1 \\\|" | sort --unique >> Makefile-big
echo "" >> Makefile-big
echo "include Makefile-generic" >> Makefile-big
echo "include Makefile-alldeps" >> Makefile-big

echo "" >> Makefile-big

# Then the user should run something like this:       
    
# make -f Makefile-big -j 8 ACL2=acl2