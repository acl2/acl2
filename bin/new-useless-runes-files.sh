#!/bin/sh

# Run
#  new-useless-runes-files.sh acl2 tmp
# to create a temporary file, tmp, in the directory where this script is invoked,
# and then execute that file in ACL2 to obtain suitable output at the shell, of
# the following form.
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

echo "(quiet-assign excluded-ur-books '(" >> $outfile

grep --include='*.acl2' -ri 'cert-flags.*useless-runes nil' . | sed 's+^[.]/\(.*\)[.]acl2:;.*$+"\1"+g' >> $outfile

echo "))" >> $outfile

echo "" >> $outfile

echo "(quiet-assign untracked-ur-books '(" >> $outfile

git ls-files . --exclude-standard --others | grep 'useless-runes.lsp$' | sed 's/\(.*\)@useless-runes[.]lsp/"\1"/g' >> $outfile

echo "))" >> $outfile

echo "" >> $outfile

echo '(my-print "@@@ Untracked @useless-runes.lsp files to be added:")' >> $outfile

echo '(loop$ for x in (set-difference-equal (@ untracked-ur-books) (@ excluded-ur-books)) collect (concatenate (quote string) x "@useless-runes.lsp"))' >> $outfile

echo "(quiet-assign all-books '(" >> $outfile

find . -name '*.lisp' -print | sed 's+^[.]/++g' | sed 's/^\(.*\)[.]lisp$/"\1"/g' | sort >> $outfile

echo "))" >> $outfile

echo "" >> $outfile

echo "(quiet-assign all-ur '(" >> $outfile

find . -name '*@useless-runes.lsp' -print | sed 's+^[.]/++g' | sed 's/^\(.*\)@useless-runes[.]lsp$/"\1"/g' | sort >> $outfile

echo "))" >> $outfile

echo "" >> $outfile

echo '(my-print "@@@ Obsolete @useless-runes.lsp files (no corresponding books):")' >> $outfile

echo '(loop$ for x in (set-difference-equal (@ all-ur) (@ all-books)) collect (concatenate (quote string) x "@useless-runes.lsp"))' >> $outfile

echo "(quit)" >> $outfile

$ACL2 < $outfile

rm $outfile
