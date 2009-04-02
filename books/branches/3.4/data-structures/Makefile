include ../Makefile-generic

# We need to exclude define-structures-package.lisp from BOOKS.

BOOKS = array1 \
        list-defuns list-defthms \
        utilities deflist list-theory \
        set-defuns set-defthms set-theory \
        alist-defuns alist-defthms \
        defalist alist-theory \
        structures \
        number-list-defuns number-list-defthms number-list-theory

# Dependencies:

array1.cert: array1.lisp

list-defuns.cert: list-defuns.lisp

list-defthms.cert: list-defthms.lisp
list-defthms.cert: list-defuns.cert
list-defthms.cert: ../arithmetic/equalities.cert

utilities.cert: utilities.lisp
utilities.cert: utilities.acl2

deflist.cert: deflist.lisp
deflist.cert: list-defuns.cert
deflist.cert: utilities.cert
deflist.cert: list-defthms.cert
deflist.cert: deflist.acl2

list-theory.cert: list-theory.lisp
list-theory.cert: list-defuns.cert
list-theory.cert: list-defthms.cert
list-theory.cert: deflist.cert

set-defuns.cert: set-defuns.lisp

set-defthms.cert: set-defthms.lisp
set-defthms.cert: set-defuns.cert

set-theory.cert: set-theory.lisp
set-theory.cert: set-defuns.cert
set-theory.cert: set-defthms.cert

alist-defuns.cert: alist-defuns.lisp

alist-defthms.cert: alist-defthms.lisp
alist-defthms.cert: alist-defuns.cert
alist-defthms.cert: list-defuns.cert
alist-defthms.cert: set-defuns.cert
alist-defthms.cert: ../arithmetic/equalities.cert
alist-defthms.cert: set-defthms.cert

defalist.cert: defalist.lisp
defalist.cert: alist-defuns.cert
defalist.cert: list-defuns.cert
defalist.cert: utilities.cert
defalist.cert: defalist.acl2

alist-theory.cert: alist-theory.lisp
alist-theory.cert: alist-defuns.cert
alist-theory.cert: alist-defthms.cert
alist-theory.cert: defalist.cert

structures.cert: structures.lisp
structures.cert: utilities.cert
structures.cert: structures.acl2

number-list-defuns.cert: number-list-defuns.lisp
number-list-defuns.cert: list-defuns.cert

number-list-defthms.cert: number-list-defthms.lisp
number-list-defthms.cert: number-list-defuns.cert
number-list-defthms.cert: deflist.cert

number-list-theory.cert: number-list-theory.lisp
number-list-theory.cert: number-list-defuns.cert
number-list-theory.cert: number-list-defthms.cert
