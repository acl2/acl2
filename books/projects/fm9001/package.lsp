;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; August 2016

;; ======================================================================

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "FM9001"
  (union-eq
   '(a b c d e f g h i j k l m n o p q r s t u v w x y z

       b*
       bash
       bash-fn
       bool-fix

       def-gl-thm
       def-ruleset
       define
       definline
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

       nonlinearp-default-hint

       pos-listp
       prefixp
       prefixp-of-cons-left
       prefixp-when-equal-lengths
       proof-by-arith

       repeat
       rev

       signed-byte-p

       take-of-len-free
       take-of-take-split
       take-of-too-many
       take-redefinition

       unsigned-byte-p

       zp-open)

   (union-eq *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)))

;; ======================================================================
