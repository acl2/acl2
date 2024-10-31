# Editable variable: It is OK to specify this on the command line,
# e.g., to run tests/doit:

# (export ACL2_SRC=/Users/kaufmann/acl2/acl2 ; ./doit)

# But careful; you need to define the ACL2 variable as well if
# your executable is not saved_acl2.  For example:

# (export ACL2_SRC=/Users/kaufmann/acl2/acl2 ; \
#  export ACL2=${ACL2_SRC}/sbcl-saved_acl2 ;\
#  ./doit)

if [ "${ACL2_SRC}" = "" ] ; then \
    echo "Need to define ACL2_SRC; see books/projects/hol-acl2/.acl2holrc.bash" ; \
    exit 1 ; \
fi

# export ACL2_SRC=/Users/kaufmann/acl2/acl2

if [ "${ACL2_SRC}" = "" ] ; then \
    export ACL2=${ACL2_SRC}/saved_acl2 ; \
fi
export ACL2_HOL=${ACL2_SRC}/books/projects/hol-acl2
export ACL2_SYSTEM_BOOKS=${ACL2_SRC}/books
export ACL2_HOL_LISP=${ACL2_HOL}/lisp
