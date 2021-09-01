;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau <ckcuong@cs.utexas.edu>
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

(include-book "std/strings/istrprefixp" :dir :system)

;; ======================================================================

(defpkg "ADE"
  (union-eq
   '(a b c d e f g h i j k l m n o p q r s t u v w x y z

       add-to-ruleset
       associativity-of-append

       b*
       bash
       bash-fn
       bool-fix

       def-gl-thm
       def-ruleset
       define
       definline
       defopener
       disable*

       e/d*
       enable*
       explode

       find-lemmas

       include-raw

       list-fix
       logext

       make-flag
       make-list-ac-removal
       mod-zero

       nonlinearp-default-hint

       pos-listp
       prefixp
       prefixp-of-cons-left
       prefixp-when-equal-lengths
       proof-by-arith

       repeat
       rev

       signed-byte-p
       suffixp

       take-of-len-free
       take-of-take-split
       take-of-too-many
       take-redefinition

       unsigned-byte-p

       zp-open

       str::basic-nat-to-dec-chars
       str::iprefixp
       str::istrprefixp
       str::nat-to-dec-chars
       str::natstr)

   (union-eq *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)))

;; ======================================================================
