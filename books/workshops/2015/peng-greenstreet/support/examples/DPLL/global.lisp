;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;; There are two files for the proof of recurrence model of the
;; DPLL: global.lisp, DPLL_functions.lisp and DPLL_theorems.lisp.
;; global.lisp
;; global.lisp defines global variables that are repeatedly
;; called in a lot of the functions.

(in-package "ACL2")
;; (defconst *g1* 1/3200)
(defconst *g2* (- (/ 1/3200 5)))
(defconst *ccode* 1)
(defconst *Kt* 4/5)
(defconst *N* 1)
(defconst *fref* 1)
(defconst *alpha* 1)
(defconst *beta* 1)
(defconst *f0* 1)
(defconst *vcenter* 1)
;; (defconst *v0* 1)

; Define intermediate variables
(defun equ-c (v0)
  (- (* *f0* (+ 1 (* *alpha* v0)) (/ (* *beta* *N* *fref*)))
     (/ *beta*)))
(defun gamma ()
  (- 1 *Kt*))
;;(defun gamma () (/ 1 2))
(defun mu ()
  (/ *f0* (* *N* *fref*)))
(defun m (n v0 g1)
 (- (/ (equ-c v0) g1) n))
;; (defun m-constraint (n v0 g1)
;;   (and (> m (- (- (/ (equ-c v0) g1) n) 1))
;;        (< m (- (/ (equ-c v0) g1) n))))
(defun dv0 ()
  (* -2 *g2*))
