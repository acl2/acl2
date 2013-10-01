#!/bin/sh
#
# RAMS/Overkill System for Regression Testing
#
# File: make/Makefile-pcert.bash - tries to create "pcert" files to indicate
# that a file will probably certify.
#
# Author: Jared Davis 

# Given some Lisp book, foo.lisp, we attempt to create a "Probably Certifies"
# file, foo.pcert, whose existence indicates that we think this file will not
# have any problems when (certify-book "foo") is executed.

# The reason that we are interested in .pcert files is that certify-book has a
# strict requirement that all included books must already be certified.  We
# have found that this is too time consuming when we have a large number of
# books to check, because it cannot be parallelized across many machines.

# But often, we don't care about the actual certificates -- we just want to
# know that the books would certify if we tried them out.  So, this script
# basically "emulates" a certify-book command, but without the restriction that
# included books must already be certified.

# Our intention is for the successful creation of a foo.pcert file will
# indicate exactly that a (certify-book "foo") command will succeed as long as
# all of the included books pass their certification.  The great thing about
# this is that we have effectively removed all dependencies between books, so
# we can farm out the .pcert generation process across a number of machines to
# make it fast.


# HACK: we accept either relative or absolute path names for FILENAME.

if [ "`echo $FILENAME | grep -v "^/"`" ] 
then
    FILENAME=$DIRECTORY/$FILENAME
fi

readonly DEBUG
readonly DIRECTORY
readonly FILENAME
readonly OUTLOG=$HOME/.overkill-results
readonly HOSTNAME



# We take an optional DEBUG parameter that, if set, means that we should print
# some debugging information.  Calls to the Debug and DebugNewLine functions
# will result in such messages.

function Debug () 
{
    if [ -n "$DEBUG" ] 
    then
	echo "[Makefile-pcert.bash]: $1"
    fi
}

function DebugNewline () 
{
    if [ -n "$DEBUG" ] 
    then
	echo ""
    fi
}




# We expect that a few variables will be set before invoking this script.  In
# other words, we expect this script to be invoked as follows:
#    "export ACL2=/blah/saved_acl2 ... ; sh Makefile-pcert.bash"

Debug "Checking required parameters..."

Debug "   Checking DIRECTORY"
if [ ! -d "$DIRECTORY" ]
then
    echo "[Makefile-pcert.bash]: Error with DIRECTORY"
    echo "We have been given: "
    echo "  DIRECTORY=\"$DIRECTORY\""
    echo "But this does not appear to be a directory."
    exit 1
fi

Debug "   Checking FILENAME"
if [ ! -e "$FILENAME.lisp" ]
then
    echo "[Makefile-pcert.bash]: Error with FILENAME"    
    echo "We have been given: "
    echo "  FILENAME=\"$FILENAME\""
    echo "But $FILENAME.lisp does not exist."
    exit 1
fi





# We also have various optional parameters.  If we are using the Overkill
# system to invoke this file, the additional parameters OUTLOG and HOSTNAME
# will be set.  If there is an OUTLOG, we will write messages to it using the
# OutputLog function.  This function takes a single parameters, the message to
# emit, and tags each message with the file we are working on and the host
# which is processing the file.

if [ -n "$OUTLOG" ]
then
    echo "Pending: $FILENAME ($HOSTNAME) `date +%s`" >> $OUTLOG
fi







# The process of building a .pcert file is somewhat complex.  We basically want
# to emulate the behavior of a session with certify-book.  We use the standard
# RAMS for loading "cert.acl2" and so forth, so this
# looks quite a lot like Makefile-generic.  We inhibit the output in our .pout
# files just as in regular .out files.

INHIBIT="(assign inhibit-output-lst (list (quote prove) (quote proof-tree) (quote warning) (quote observation) (quote event)))"


# The regular Makefile-generic creates some files, e.g., foo.workxxx and
# foo.out, and we have our own analogues which are foo.pwork foo.pout.  We also
# have two other files that we will need to create temporarily, namely the
# .plisp and .pcompat.lisp files.  These files might occasionally be left behind if
# the ACL2 process is killed before we properly delete them, but they will be
# cleaned away with a make clean.  Note: these files will also be left behind
# if DEBUG is set to true.

# "permanant" pcert artifacts
readonly PCERT=$FILENAME.pcert
readonly POUT=$FILENAME.pout

# "temporary" work files
readonly COMPAT=$FILENAME.pcompat
readonly TEST=$FILENAME.plisp
readonly WORK=$FILENAME.pwork


# To ensure that we are starting cleanly, we delete these files if they exist.

rm -f $WORK $COMPAT $TEST $POUT $PCERT


# The foo.pwork file is basically our version of the foo.workxxx file created
# by Makefile-generic.  Just as in Makefile-generic, we begin by providing an
# inhibit output list that cuts down on the volume of proof output and speeds
# things up, and we dump in the foo.acl2 or cert.acl2 if either exists in the
# usual manner.

echo "(acl2::value :q)" >> $WORK
echo "(in-package \"ACL2\")" >> $WORK
echo "(acl2::lp)" >> $WORK
echo $INHIBIT >> $WORK

if [ -f "$FILENAME.acl2" ]
then
    # We don't want to get the certify-book command, because we don't wish
    # to certify the book.  So, we use grep to remove it.
    grep -v "certify-book" $FILENAME.acl2 >> $WORK
elif [ -f "$DIRECTORY/cert.acl2" ]
then   
    cat $DIRECTORY/cert.acl2 >> $WORK
fi



# Our major idea is that "ld" does almost everything certify-book does, but
# without requiring the include-books to have been certified.  One problem with
# just using ld directly is that it does not include a local incompatibility
# check.  Fortunately, we can emulate this check using a simple include-book
# command.  We prefer to do this check first, even before the ld.

# But here's an issue: we need to know if our include-book is successful or
# not.  So, instead of trying to just include-book the lisp file, we will try
# to include a modified version of it.  The modification is simple: we just add
# to the very end of the file, the definition of a constant whose name surely
# will not be used anywhere else.

cat $FILENAME.lisp >> $COMPAT.lisp
echo "" >> $COMPAT.lisp
echo "(defconst ACL2::*overkill-victory-party-at-my-place-for-compat* t)" >> $COMPAT.lisp



# We instruct our .pwork file to try to include-book this .pcompat.lisp file.
# Either everything will work, or a local incompatibility will be detected.  If
# we succeed, we need to be sure that we can undo the include-book, so what we
# are going to do is go ahead and define a constant that will provide a
# convenient :ubt! target:

echo "(defconst ACL2::*overkill-undo-back-through-here-after-compat-check* t)" >> $WORK
echo "(include-book \"$COMPAT\")" >> $WORK


# We now see if our include-book command was successful.  To do this, we bounce
# down into common lisp and take a look at the victory party variable.

echo ":q" >> $WORK


# Now we check to see if the victory party variable is bound.  If so, we were
# successful and we just want to continue.  But if it is not bound, then we 
# have failed, and we need to quit early.

echo "(if (not (member 'ACL2_GLOBAL_ACL2::*OVERKILL-VICTORY-PARTY-AT-MY-PLACE-FOR-COMPAT* " >> $WORK
echo "                 (symbol-plist 'ACL2::*overkill-victory-party-at-my-place-for-compat*)))" >> $WORK

if [ -n "$OUTLOG" ]
then
    # we are supposed to log what is happening, so have ACL2 print to the 
    # output log that this book has failed.  We want to make sure the user
    # sees the reason that the build failed, so we print this four times.

    echo "    (progn (format t \"~%~%~%The local incompatibility check has failed!~%\")" >> $WORK
    echo "           (format t \"The local incompatibility check has failed!~%\")" >> $WORK
    echo "           (format t \"The local incompatibility check has failed!~%\")" >> $WORK
    echo "           (format t \"The local incompatibility check has failed!~%~%~%\")" >> $WORK
    echo "           (with-open-file" >> $WORK
    echo "             (ofile \"$OUTPUT\" :direction :output :if-exists :append)" >> $WORK
    echo "             (format ofile \"Failure: $FILENAME ($HOSTNAME)~%\"))" >> $WORK
    echo "           (good-bye))" >> $WORK

else

    # otherwise we just want to quit early.
    echo "    (progn (format t \"~%~%~%The local incompatibility check has failed!~%\")" >> $WORK
    echo "           (format t \"The local incompatibility check has failed!~%\")" >> $WORK
    echo "           (format t \"The local incompatibility check has failed!~%\")" >> $WORK
    echo "           (format t \"The local incompatibility check has failed!~%~%~%\")" >> $WORK
    echo "           (good-bye))" >> $WORK

fi

# On the other hand, if the symbol *is* bound, we will finish the if statement
# with a harmless nil, and continue our work.

echo "  nil)" >> $WORK



# If our WORK script gets this far, it has succeeded in the local incompatibility
# check and we can go ahead and go back into raw lisp, then undo back through our
# undo marker.

echo "(lp)" >> $WORK
echo ":ubt! ACL2::*overkill-undo-back-through-here-after-compat-check*" >> $WORK




# We are now ready for the "meat" of our test: ld'ing the file.  We need to 
# create another test file in the spirit of the compat file.  (We can't just 
# reuse the compatibility check file, becuase even after undoing the file the
# variable will still show up when we use the symbol-plist test.  Maybe we
# could undefine it or rebind it or something instead?)  So, for now we write
# a new file with a new constant that we can check.

cat $FILENAME.lisp >> $TEST
echo "" >> $TEST
echo "(defconst ACL2::*overkill-victory-party-at-my-place-for-ld* t)" >> $TEST


# We load the file using ld just as before, and then do our dance to see if we
# have gotten the global variable set.

echo "(ld \"$TEST\")" >> $WORK

echo ":q" >> $WORK
echo ":q" >> $WORK
echo ":q" >> $WORK


# At this point, we simply test our new variable.  If it is bound as we hope
# it should be, then we can create a .pcert file.

echo "(if (symbol-plist 'ACL2::*overkill-victory-party-at-my-place-for-ld*)" >> $WORK
echo "    (with-open-file" >> $WORK
echo "      (ofile \"$PCERT\" :direction :output :if-exists :supercede)" >> $WORK
echo "      (format ofile \"$PCERT created on `date`~%\")" >> $WORK
echo "      (format ofile \"ACL2=$ACL2~%\")" >> $WORK
echo "      (format ofile \"DIRECTORY=$DIRECTORY~%\")" >> $WORK
echo "      (format ofile \"FILENAME=$FILENAME~%\")" >> $WORK
echo "      (format ofile \"HOSTNAME=$HOSTNAME~%\")" >> $WORK
echo "      (format ofile \"OUTLOG=$OUTLOG~%\")" >> $WORK
echo "    )" >> $WORK
echo "  nil)" >> $WORK



# If we have an output log that we are supposed to write to, we will make the
# ACL2 image write its success or failure message there.

if [ -n "$OUTLOG" ]
then
    echo "(with-open-file" >> $WORK
    echo "  (ofile \"$OUTPUT\" :direction :output :if-exists :append)" >> $WORK
    echo "  (if (symbol-plist 'ACL2::*overkill-victory-party-at-my-place-for-ld*)" >> $WORK
    echo "      (format ofile \"Success: $FILENAME ($HOSTNAME)~%\")" >> $WORK
    echo "    (format ofile \"Failure: $FILENAME ($HOSTNAME)~%\")))" >> $WORK
fi


# Finally, our WORK script should always say goodbye.

echo "(good-bye)" >> $WORK




# Ok.  So at this point we have created a .pwork file that has our whole session
# for how to create .pcert files and write to the log if necessary, we have also
# created the temporary .pcompat.lisp and .plisp files that will be needed by
# the work script. 
# 
# At this point, we are going to actually invoke the script by firing off ACL2
# in the appropriate directory.  This will certainly create the .pout file, and
# will hopefully create a .pcert file.

cd $DIRECTORY; export TIME="%e seconds"; $ACL2 < $WORK > $POUT

# If we get this far, ACL2 has run to completion so we have our answer somewhere.
# We are now ready to delete the temporary files.

rm -f $WORK $TEST $COMPAT.lisp

# Now we will find out if the whole process was successful or not.

if [ -f $PCERT ]
then
    exit 0
else
    echo "**PCERT FAILED**"
    exit 1
fi

