# Editable variable, ACL2_SRC:
# It is OK to specify ACL2_SRC on the command line, e.g., to run tests/doit
# from the directory of this .acl2holrc.bash file:

# (cd tests ; \
#  export ACL2_SRC=/Users/kaufmann/acl2/acl2 ;\
#  source ../.acl2holrc.bash ;\
#  ./doit)

# But careful; you need to define the ACL2 variable as well if
# your executable is not saved_acl2.  For example:

# (cd tests ; \
#  export ACL2_SRC=/Users/kaufmann/acl2/acl2 ;\
#  export ACL2=${ACL2_SRC}/sbcl-saved_acl2 ;\
#  source ../.acl2holrc.bash ;\
#  ./doit)

if [ "${ACL2_SRC}" = "" ] ; then \
    echo "Need to define ACL2_SRC; see books/projects/acl2-in-hol/.acl2holrc.bash" ; \
    exit 1 ; \
fi

if [ "${ACL2}" = "" ] ; then \
    export ACL2=${ACL2_SRC}/saved_acl2 ; \
fi
export ACL2_HOL=${ACL2_SRC}/books/projects/acl2-in-hol
export ACL2_SYSTEM_BOOKS=${ACL2_SRC}/books
export ACL2_HOL_LISP=${ACL2_HOL}/lisp
