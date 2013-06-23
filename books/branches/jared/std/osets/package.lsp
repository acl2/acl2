; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public Lic-
; ense along with this program; if not, write to the Free Soft- ware
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")

(defpkg "INSTANCE"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))


(defpkg "COMPUTED-HINTS"
  (union-eq '(mfc-ancestors
	      mfc-clause
	      string-for-tilde-@-clause-id-phrase
	      INSTANCE::instance-rewrite)
            *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))

(defpkg "SETS"
  (set-difference-equal
   (union-eq '(defsection
               defxdoc
               definline
               definlined
               lexorder
               lnfix
               <<
               <<-irreflexive
               <<-transitive
               <<-asymmetric
               <<-trichotomy
               <<-implies-lexorder
               fast-<<
               fast-lexorder
               COMPUTED-HINTS::rewriting-goal-lit
               COMPUTED-HINTS::rewriting-conc-lit
               def-ruleset
               def-ruleset!
               add-to-ruleset
               ;; To make Sets::Osets print as just Osets in the XDOC index
               osets)
             *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)

; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (intersectp was added to *acl2-exports*).]

   '(union delete find map intersectp
           enable disable e/d)))

#!SETS
(defconst *sets-exports*
  ;; This just contains the user-level set functions, and a couple of theroems
  ;; that frequently need to be enabled/disabled.
  '(<<
    setp
    empty
    sfix
    head
    tail
    insert
    in
    subset
    delete
    union
    intersect
    ;; intersectp -- we leave this out because of the existing ACL2 function
    ;; called intersectp.
    difference
    cardinality
    mergesort
    ;; A couple of theorems that frequently need to be enabled/disabled.
    double-containment
    pick-a-point-subset-strategy
    ))
