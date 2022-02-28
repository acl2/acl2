(in-package "ACL2")

(defpkg "TYPES"
  (append '(acl2::val acl2::met)
          *acl2-exports*
          *common-lisp-symbols-from-main-lisp-package*))

(defpkg "PICK-A-POINT"
  '(equal
    not
    nil
    t
    and
    nth
    if
    iff
    list
    exit
    quit
    let
    let*
    +
    <
    <=
    len
    local
    consp
    car
    cdr
    defstub
    defun
    defthm
    defthmd
    defmacro
    implies
    &key
    encapsulate
    include-book
    in-theory
    in-conclusion-check
    ))
