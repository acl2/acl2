#!/bin/sh

##########

# Cheat sheet for using this file (a more conventional description
# follows):

# (1) Run fresh "everything" regression with ACL2_USELESS_RUNES=write
#     to regenerate @useless-runes.lsp files.  -- NOTE: file
#     books/projects/filesystems/oracle.lisp has take a very long time
#     to certify this way, perhaps adding as much as 4 hours to
#     regression time.  A note here formerly also said to consider
#     excluding projects/filesystems/abs-syscalls.lisp (which has
#     taken about 40 minutes to certify this way at UT CS).  So
#     consider using a command like the following.

#     (time make -j 30 -l 30 regression-everything-fresh ACL2_USELESS_RUNES=write ACL2=`pwd`/sbcl-saved_acl2 EXCLUDED_PREFIXES="projects/filesystems/oracle projects/filesystems/abs-syscalls") >& logs/make-regression-everything-sbcl-j-30-useless-runes-write-jul24.log&

# (2) Run ordinary "everything" regression, perhaps updating with git
#     first.

# (3) Check for failures, avoiding bad @useless-runes.lsp files by
#     editing or creating .acl2 files and removing those bad
#     @useless-runes.lsp files (using git rm for files that are under
#     git control).  For example:
#     ; cert-flags: ? t :useless-runes nil

# (4) Run the following in that same (top-level ACL2) directory, using
#     a full (absolute) pathname or directory-independent pathname
#     (e.g., "acl2" if that is really ~/bin/acl2) for <your_acl2>),
#     e.g., perhaps /projects/acl2/acl2/saved_acl2 rather than
#     saved_acl2:

#     ./bin/new-useless-runes-files.sh <your_acl2> tmp

# (5) After "cd books", run "git add" and "git rm" as suggested by the
#     output.

# (6) Commit, pull, commit, push.

##########

# Run

# ./bin/new-useless-runes-files.sh acl2 tmp

# in the main ACL2 directory (using any ACL2, but perhaps it's best to
# use the one just built).  That will create a temporary file, tmp, in
# the directory where this script is invoked; then it will execute
# that file in ACL2 to obtain suitable output at the shell, of the
# following form.  (Note that the temporary file, tmp, will then be
# deleted.)  It is up to the user to run "git add" and "git rm" on the
# files below (respectively); be sure to "cd books" first.

# @@@ Untracked @useless-runes.lsp files to be added:
# ("..." ... "...")
# @@@ Obsolete @useless-runes.lsp files (no corresponding books):
# ("..." ... "...")

if [ $# -ne 2 ] ; then
    echo "Usage: $0 <acl2_name> <output_file>"
    echo "       where <acl2_name> invokes ACL2 (possibly an alias)"
    exit 1
fi

ACL2=$1
outfile=`pwd`/$2

cd $(dirname $0)/../books

echo '(er-progn (set-inhibit-output-lst *valid-output-names*) (set-ld-prompt nil state) (value-triple :invisible))' > $outfile

echo '(defmacro my-print (s) (list (quote pprogn) (list (quote princ$) s (quote *standard-co*) (quote state)) (quote (newline *standard-co* state)) (quote (value :invisible))))' >> $outfile

echo '(defmacro quiet-assign (var form) `(pprogn (f-put-global (quote ,var) ,form state) (value :invisible)))' >> $outfile

echo '(defabbrev ur-fname (x)
  (let ((p (search *directory-separator-string* x :from-end t)))
    (if p
        (concatenate (quote string)
                     (subseq x 0 p)
                     #-non-standard-analysis "/.sys"
                     #+non-standard-analysis "/.sysr"
                     (subseq x p (length x))
                     "@useless-runes.lsp")
      (er hard? (quote ur-fname)
          "Unexpected error for ~x0 !"
          x))))' >> $outfile

echo "" >> $outfile

echo "(quiet-assign excluded-ur-books '(" >> $outfile

# Avoid books/top.lisp, which we have seen can generate no
# useless-runes anyhow.  If we ever include anything at the
# top leve of books/, we will read the (er hard? ...) above,
# and we'll have to figure out how to deal with that.
echo '"top"' >> $outfile

grep --include='*.acl2' -ri 'cert-flags.*useless-runes nil' . | sed 's+^[.]/\(.*\)[.]acl2:;.*$+"\1"+g' >> $outfile

echo "))" >> $outfile

echo "" >> $outfile

echo "(quiet-assign untracked-ur-books '(" >> $outfile

git ls-files . --exclude-standard --others | grep 'useless-runes.lsp$'  | sed 's+[.]sys/++g' | sed 's/\(.*\)@useless-runes[.]lsp/"\1"/g' >> $outfile

echo "))" >> $outfile

echo "" >> $outfile

echo '(my-print "@@@ Untracked @useless-runes.lsp files to be added:")' >> $outfile

echo "" >> $outfile

echo '(loop$ for x in (set-difference-equal (@ untracked-ur-books) (@ excluded-ur-books)) collect (ur-fname x))' >> $outfile

echo "" >> $outfile

echo "(quiet-assign all-books '(" >> $outfile

find . -name '*.lisp' -print | sed 's+^[.]/++g' | sed 's/^\(.*\)[.]lisp$/"\1"/g' | sort >> $outfile

echo "))" >> $outfile

echo "" >> $outfile

echo "(quiet-assign all-ur '(" >> $outfile

find . -name '*@useless-runes.lsp' -print | sed 's+[.]sys/++g' | sed 's+^[.]/++g' | sed 's/^\(.*\)@useless-runes[.]lsp$/"\1"/g' | sort >> $outfile

echo "))" >> $outfile

echo "" >> $outfile

echo '(my-print "@@@ Obsolete @useless-runes.lsp files (no corresponding books):")' >> $outfile

echo "" >> $outfile

echo '(loop$ for x in (set-difference-equal (@ all-ur) (@ all-books)) collect (ur-fname x))' >> $outfile

echo "" >> $outfile

echo "(quit)" >> $outfile

$ACL2 < $outfile

# rm $outfile

