if [ "$ACL2_SYSTEM_BOOKS" = "" ] ; then \
    echo "ERROR: Need to define ACL2_SYSTEM_BOOKS to invoke books/projects/acl2-in-hol/tests/doit ." ;\
    echo "       See books/projects/acl2-in-hol/.acl2holrc.bash ." ;\
    exit 1 ;\
fi

# Note: ACL2 is needed for lisp/book-essence.csh.
if [ "$ACL2" = "" ] ; then
    pushd "${ACL2_SYSTEM_BOOKS}/.." > /dev/null ; export ACL2=`pwd`/saved_acl2 ; popd > /dev/null ;\
fi

if [ ! `which acl2` ] ; then \
    echo "ERROR: Need to define ACL2 to invoke books/projects/acl2-in-hol/tests/doit," ;\
    echo "       because $ACL2 does not invoke an acl2 executable." ;\
    exit 1 ;\
fi

export ACL2_HOL=${ACL2_SYSTEM_BOOKS}/projects/acl2-in-hol
export ACL2_HOL_LISP=${ACL2_HOL}/lisp
