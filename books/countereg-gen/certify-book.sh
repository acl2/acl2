#! /bin/sh

if [ "$ACL2" ]; then
    if [ '!' -x "$ACL2" ]; then
	echo "the ACL2 environment variable must point to an ACL2 executable."
	exit 1
    fi
else
    export ACL2=acl2
fi

cd "`dirname "${1}"`" || exit 2

TARGET="`basename "${1}" .lisp`"

if [ '!' -e "${TARGET}.lisp" ]; then
	echo "<first argument>.lisp is the file to be certified."
	exit 3
fi

(
 echo "(value :q)" &&
 echo "(progn (lp) (good-bye))" &&
 echo "(set-ld-error-action :return state)" &&
 if [ -e "${TARGET}.acl2" ]; then
   cat "${TARGET}.acl2"
 else
   echo "(certify-book \"${TARGET}\" ? t :skip-proofs-okp t :defaxioms-okp t :ttags :all)"
 fi) | "$ACL2"

test "${TARGET}.cert" -nt "${TARGET}.lisp"
