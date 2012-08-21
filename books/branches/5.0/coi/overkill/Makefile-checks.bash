#!/bin/sh
#
# File: make/Makefile-checks.bash 
#
# Sanity checking routines for ensuring that variables have the proper formats
# and so forth, and for doing common grep/sed text parsing.  We expect that 
# this file should be included as follows:
#
# readonly SCRIPT="name of calling script"
# source $MAKEDIR/Makefile-checks.bash

readonly DEBUG
readonly QUIET
readonly NAME
readonly BOOKS
readonly LIBS
readonly MAKEDIR

# Debug Function
#
# Prints a single argument to the screen if DEBUG mode is enabled.  Attributes
# its message to the current $SCRIPT.

function Debug ()
{
    if [ -n "$DEBUG" ] 
    then
	echo "[$SCRIPT]: $1"
    fi
}

function DebugNewline ()
{
    if [ -n "$DEBUG" ] 
    then
	echo ""
    fi
}




# ParseLib Function
# 
# Check to ensure that our argument, $1, is a properly formed library name,
# e.g., :foo, and set two result variables:
#
#   LIB_UPPER becomes FOO
#   LIB_BOOKS becomes ACL2_FOO_BOOKS
function ParseLib () 
{    
    if [ "`echo $1 | egrep "^:[A-Za-z0-9_-]+$"`" ]
	then
	LIB_UPPER="`echo $1 | sed "s/://" | tr -t [:lower:] [:upper:]`"
	LIB_BOOKS="ACL2_`echo $LIB_UPPER`_BOOKS"
    else
	echo "
[$SCRIPT] Error in `pwd`

\"$1\" is not a valid library name.  Library names must be keyword symbols,
e.g., :lists or :bags, that consist of a colon followed only by letters, 
numbers, underscores, and hyphens.
"
	exit 1
    fi
}


# Do a quick sanity check on $NAME and set up NAME_UPPER and NAME_BOOKS

if [ -n "$NAME" ]
then
    ParseLib $NAME
    readonly NAME_UPPER=$LIB_UPPER
    readonly NAME_BOOKS=$LIB_BOOKS
else
    echo "
[$SCRIPT] Error in `pwd`

NAME is not set.

You can probably fix this problem by adding a line like \"NAME = :lists\" to 
your Makefile.
"
    exit 1
fi


# Do a quick sanity check on $LIBS and ensure that they are all syntactically
# in the format we expect them to be.

for lib in $LIBS
do
  ParseLib $lib
done


# Do a quick sanity check on $BOOKS and ensure that they are in the format
# we expect them to be -- namely, a string that has regular names separated
# by spaces.

if [ "`echo $BOOKS | egrep "^[ ]*([A-Za-z0-9_-]+[ ]*)+$"`" ]
then
    Debug "Books look ok: $BOOKS"
else
    echo "
[$SCRIPT] Error in `pwd`

BOOKS do not match the expected format.  We expect that books are a nonempty
list of names separated by spaces, wherein each name consists only of letters,
numbers, underscores, and hyphens.

BOOKS = $BOOKS
"
    exit 1
fi



# CheckBook Function   (yey for funny names)
# 
# This function ensures that its first argument, $1, is an entry in $BOOKS.
# If not, we cause an error.
function CheckBook() 
{
    IFS=" "
    for CheckBook_temp in `echo $BOOKS`
    do
        if [[ "$CheckBook_temp" == "$FILENAME" ]]
	    then return
	fi
    done
    
    echo "
[$SCRIPT] Error in `pwd`

We expected $1 to be a member of BOOKS, but it has not been found.  Perhaps
$1 needs to be added to BOOKS in your Makefile?
"
    exit 1
}



# CheckLib Function
# 
# This function ensures that its first argument, $1, is an entry in $LIBS.
# If not, we cause an error.  Note that this check is case insensitive.  We
# expect $1 to be of the form ":foo".
function CheckLib ()
{
    # First try to find it in our list of LIBS.
    IFS=" "
    for CheckLib_temp in `echo $LIBS`
    do
        if [[ "`echo $1 | tr -t [:lower:] [:upper:]`" == "`echo $CheckLib_temp | tr -t [:lower:] [:upper:]`" ]]
	    then return
	fi
    done

    # Next, see if it is SYSTEM.  If so, we know it.
    if [[ "`echo $1 | tr -t [:lower:] [:upper:]`" == ":SYSTEM" ]]
	then return
    fi

    # Otherwise, we fail.
    echo "
[$SCRIPT] Error in `pwd`

We expected $1 to be a member of LIBS, but it has not been found.  Perhaps
we have incorrectly scanned a :dir entry, or this library is not listed
in LIBS and needs to be?
"
    exit 1
}



# MangleFile Function  
#
# We expect that our argument is a filename, possibly including some
# directories.  We mangle it by turning all slashes into _slash_ and turning
# all periods into _dot_, and then uppercasing the entire thing.  The result
# is stored into MANGLEFILE.

function MangleFile ()
{
    MANGLEFILE=`echo $1 | sed "s/\//_slash_/g" | sed "s/\./_dot_/g" | tr -t [:lower:] [:upper:]`
    if [ `echo $MANGLEFILE | egrep "[^0-9A-Z_-]"` ]
    then
	echo "
[$SCRIPT] Error in `pwd`

Cannot mangle \"$1\" ($MANGLEFILE)

But this is not a valid mangling.  Perhaps the filename has illegal characters
in it?  The supported characters are letters, numbers, underscores, hyphens,
slashes, and periods.
"
	exit 1
    fi    
}


# CheckOverkill Function
#
# We ensure that the Overkill program is up to date (by running make on its
# executable), and then ensure that the program exists.

function CheckOverkill ()
{
    cd $MAKEDIR/okill; make -s; cd -

    if [ ! -f "$MAKEDIR/okill/overkill" ]
    then
	echo "
[$SCRIPT] Error: cannot find Overkill

I wasn't able to find the Overkill executable, and when I tried to recompile
it, it didn't get created.  Sorry, but you'll have to figure this one out on
your own.  (You should just be able to go into the Overkill directory, which
should be:
    $MAKEDIR/okill

And type \"make\", but that's what I did and it didn't work for me.  
Good luck!
"
	exit 1
    fi
}


function CheckOverkillHosts ()
{
    if [ -n "$MAKEDIR/HOSTS" ] 
	then
	HOSTS=`cat $MAKEDIR/HOSTS | grep -v "^#"`
	NUMHOSTS=$((`echo $HOSTS | wc -w`))
	if [ -n "$HOSTS" ]
	    then
	    echo "$NUMHOSTS machines will be utilized"
	    for host in $HOSTS
	      do
	      echo "   [$host] `rsh $host w | head -1 | sed "s/.*load/load/"`"
	      if [ $? -ne 0 ] 
		  then
		  echo "
[$SCRIPT] Error connecting to $host.  

I can't send a simple echo command over rsh to $host.  Maybe $host is 
misspelled, or not online?  You can comment the host out of the HOSTS 
file in the Make directory, or maybe try again?
"
		  exit 1
	      fi
	    done
	else
	    echo "
[$SCRIPT] HOSTS file is empty (or entirely comments)

Without hosts to do the work, what are we to do?  Please add some hosts
to the file HOSTS in the make directory, and try again!
"
	    exit 1
	fi	    
    else
	echo "
[$SCRIPT] Error: No HOSTS file found.

You will need to create a file called HOSTS in the Make directory, that
contains the hostnames for all of the machines you would like to use.
This is just a plain text file: one host per line, with comments allowed
using # at the beginning of commented lines.
"
	exit 1
    fi
}