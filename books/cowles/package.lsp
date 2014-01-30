; Written by John Cowles
; Copyright/License: See the LICENSE file in this directory.

(in-package "ACL2")

(defconst *cowles-package-symbols*
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*
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
