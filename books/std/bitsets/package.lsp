; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

(include-book "std/osets/portcullis" :dir :system)

(defconst *bitset-exports*
  '(bitsets
    bitset-singleton
    bitset-insert
    bitset-list
    bitset-list*
    bitset-delete
    bitset-union
    bitset-intersect
    bitset-difference
    bitset-memberp
    bitset-intersectp
    bitset-subsetp
    bitset-cardinality
    bitset-members

    equal-bitsets-by-membership
    bitset-witnessing
    bitset-equal-witnessing
    bitset-equal-instancing
    bitset-equal-example
    bitset-fns
    
    sbitsets
    sbitsetp
    sbitset-fix
    sbitset-members
    sbitset-singleton
    sbitset-union
    sbitset-intersect
    sbitset-difference
    ))

(defconst *bitsets-pkg-symbols*
  (set-difference-eq
   (union-eq sets::*sets-exports*
             *bitset-exports*
             *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*
             '(*bitset-exports*
               std
               std/util
               std/bitsets
               osets
               __function__
               raise
               define
               defrule
               defsection
               defxdoc
               defwitness
               definstantiate
               defexample
               include-raw
               witness
               xdoc
               assert!
               b*
               progn$

               enable*
               disable*
               e/d*

               rev

               arith-equiv-forwarding
               lnfix
               lifix
               lbfix
               nat-equiv
               int-equiv

               logbitp-mismatch
               equal-by-logbitp
               logbitp-hyp
               logbitp-lhs
               logbitp-rhs

               a b c d e f g h i j k l m n o p q r s t u v w x y z

               ))

   '(union delete find map intersectp
           enable disable e/d)))

(defpkg "BITSETS" *bitsets-pkg-symbols*)

