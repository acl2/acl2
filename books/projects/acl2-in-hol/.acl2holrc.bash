if [ "$ACL2_SYSTEM_BOOKS" = "" ] ; then \
    echo "ERROR: Need to define ACL2_SYSTEM_BOOKS to invoke books/projects/acl2-in-hol/tests/doit ." ;\
    echo "       See books/projects/acl2-in-hol/.acl2holrc.bash ." ;\
    exit 1 ;\
fi

# Note: ACL2 is needed for lisp/book-essence.bash.
if [ "$ACL2" = "" ] ; then
    pushd "${ACL2_SYSTEM_BOOKS}/.." > /dev/null ; export ACL2=`pwd`/saved_acl2 ; popd > /dev/null ;\
fi

# Get the pathname for the executable, (since for example $ACL2 could
# be a command like "acl2" that is on the path and is a symbolic link,
# and a test "-x $ACL2" wouldn fail in that case):
myacl2=`which "$ACL2"` 2> /dev/null

if [ "$myacl2" = "" ] ; then \
    echo "ERROR: Need to define ACL2 to invoke books/projects/acl2-in-hol/tests/doit," ;\
    echo "       because $ACL2 does not invoke an acl2 executable." ;\
    exit 1 ;\
fi

export ACL2_HOL=${ACL2_SYSTEM_BOOKS}/projects/acl2-in-hol
export ACL2_HOL_LISP=${ACL2_HOL}/lisp
