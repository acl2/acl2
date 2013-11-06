; Arithmetic-2 Library
; Copyright (C) 1999 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; mini-theories.lisp
;;
;;
;; This book contains a couple of rules which don't seem to fit
;; anywhere else.  They are sometimes useful, however, and
;; their existence should be kept im mind.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "../pass1/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some proofs of linear equalities don't work when presented as
;; equalities.  This lemma allows you to state the equality as
;; an equality rewrite rule, but breaks the equality apart for
;; the proof.
;;
;; Try the following lemma with and without
;; rewrite-linear-equalities-to-iff to see what is meant by the
;; above paragraph:

#|(defthm <-*-0
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (equal (< (* x y) 0)
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< x 0)
                          (< 0 y))))))|#

;; The same technique is sometimes needed for other boolean
;; operators.


(defthm rewrite-linear-inequalities-to-iff
   (equal (equal (< w x) (< y z))
          (iff (< w x) (< y z))))

(in-theory (disable rewrite-linear-inequalities-to-iff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I put this lemma here because it makes me unhappy to have it
;; anywhere else.  It serves as a reminder that type-set does
;; not execute anything when relieving hypotheses.  This lack
;; has irritated me at times.

; Matt K. change for v2-9: Now that terms are kept in quote-normal form, the
; following is illegal because the term translates to T.
#|
(defthm hack-minus-1
  (not (integerp (* 1/2 -1)))
  :rule-classes :type-prescription)
|#
