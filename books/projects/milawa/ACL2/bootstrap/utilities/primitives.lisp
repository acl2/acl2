; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "primitives-6")

(defmacro %cdr-induction (x)
  `(%induct (rank ,x)
            ((not (consp ,x))
             nil)
            ((consp ,x)
             (((,x (cdr ,x)))))))

(defmacro %cdr-cdr-induction (x y)
  `(%induct (rank ,x)
            ((or (not (consp ,x))
                 (not (consp ,y)))
             nil)
            ((and (consp ,x)
                  (consp ,y))
             (((,x (cdr ,x))
               (,y (cdr ,y)))))))

(defmacro %cdr-cdr-cdr-induction (x y z)
  `(%induct (rank ,x)
            ((or (not (consp ,x))
                 (not (consp ,y))
                 (not (consp ,z)))
             nil)
            ((and (consp ,x)
                  (consp ,y)
                  (consp ,z))
             (((,x (cdr ,x))
               (,y (cdr ,y))
               (,z (cdr ,z)))))))

(defmacro %four-cdrs-induction (a b c d)
  `(%induct (rank ,a)
            ((or (not (consp ,a))
                 (not (consp ,b))
                 (not (consp ,c))
                 (not (consp ,d)))
             nil)
            ((and (consp ,a)
                  (consp ,b)
                  (consp ,c)
                  (consp ,d))
             (((,a (cdr ,a))
               (,b (cdr ,b))
               (,c (cdr ,c))
               (,d (cdr ,d)))))))

(defmacro %dec-induction (a)
  `(%induct (nfix ,a)
            ((zp ,a)
             nil)
            ((not (zp ,a))
             (((,a (- ,a 1)))))))

(defmacro %dec-dec-induction (a b)
  `(%induct (nfix ,a)
            ((or (zp ,a)
                 (zp ,b))
             nil)
            ((and (not (zp ,a))
                  (not (zp ,b)))
             (((,a (- ,a '1))
               (,b (- ,b '1)))))))

(defmacro %sub-induction (a b)
  `(%induct (nfix ,a)
            ((zp ,b)
             nil)
            ((and (not (zp ,b))
                  (< ,a ,b))
             nil)
            ((and (not (zp ,b))
                  (not (< ,a ,b)))
             (((,a (- ,a ,b))
               (,b ,b))))))

(defmacro %car-cdr-induction (x)
  `(%induct (rank ,x)
            ((not (consp ,x))
             nil)
            ((consp ,x)
             (((,x (car ,x)))
              ((,x (cdr ,x)))))))


(%ensure-exactly-these-rules-are-missing
 "../../utilities/primitives"
 ;; These should be missing because we don't want to add extra axioms for
 ;; them yet.
; DEFINITION-OF-BITWISE-NTH
; DEFINITION-OF-BITWISE-XOR
; DEFINITION-OF-BITWISE-OR
; DEFINITION-OF-BITWISE-AND
; DEFINITION-OF-BITWISE-SHR
; DEFINITION-OF-BITWISE-SHL
; DEFINITION-OF-EXPT
; DEFINITION-OF-MOD
; DEFINITION-OF-FLOOR
; DEFINITION-OF-*
 ;; This is only needed to tell ACL2 to use ord< as its wfr.
 ORD<-IS-WELL-FOUNDED
 ;; This is only needed to tell ACL2 to use car-cdr-elim automatically; we
 ;; use the %car-cdr-elim tactic instead
 CAR-CDR-ELIM

 ;; BOZO why is this rule missing?
 ;; Aah, it ought to be local in the ACL2 file but we forgot to keep it local. Stupid us.
 ;; Relocalize it in the ACL2 file and get rid of it from this list.
 NATURAL-LESS-THAN-ONE-IS-ZERO

 ;; This isn't part of the logic.
; UNBOUNDED-RANK

 ;; This one was added to account for changes in ACL2 6.2.
 EQUAL-OF-CONS-REWRITE-CONSTANTS
 )


(%save-events "primitives.events")