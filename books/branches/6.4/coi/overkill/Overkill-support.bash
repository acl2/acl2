#!/bin/sh
#
# File: make/Overkill-support.bash
# Support functions for the Overkill system.


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
	HOSTS=`cat "$MAKEDIR/HOSTS" | sed "s/#.*//" | grep "[A-Za-z0-9]"`
	NUMHOSTS=$((`echo $HOSTS | wc -w`))
	if [ -n "$HOSTS" ]
	    then
	    echo "$NUMHOSTS machines will be utilized"
	    IFS="
"
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