; Written by John Cowles
; Copyright/License: See the LICENSE file in this directory.

(in-package "ACL2")

(defconst *cowles-package-symbols*
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*

; The following symbols are useful for documentation.  For potentially useful
; information about that, see:
; http://code.google.com/p/acl2-books/issues/detail?id=4

             '(arithmetic
               cowles
               abelian-semigroups
               abelian-groups
               commutative-rings
               defxdoc
               defsection
               rewrite
               ))
   '(zero)))

(defpkg "ACL2-CRG" *cowles-package-symbols*)
(defpkg "ACL2-AGP" *cowles-package-symbols*)
(defpkg "ACL2-ASG" *cowles-package-symbols*)

(include-book "std/portcullis" :dir :system)
