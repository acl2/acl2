; A utility to term a DAG or term into a DAG.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-term-into-dag-basic")
(include-book "kestrel/utilities/translate" :dir :system)

;; Returns (mv erp dag-or-quotep).
(defun dag-or-term-to-dag-basic (item wrld)
  (declare (xargs :mode :program)) ;; because this calls translate-term
  (if (eq nil item) ; we assume nil is the constant nil, not an empty DAG
      (mv (erp-nil) *nil*)
    (if (weak-dagp item)
        (mv (erp-nil) item) ;already a DAG
      ;; translate the given form to obtain a pseudo-term and then make that into a DAG:
      (make-term-into-dag-basic (translate-term item 'dag-or-term-to-dag wrld)
                                nil))))

;; Returns (mv erp dag-or-quotep).  This variant has no invariant-risk because
;; it calls make-term-into-dag-basic-unguarded, which has no invariant-risk.
(defun dag-or-term-to-dag-basic-unguarded (item wrld)
  (declare (xargs :mode :program)) ;; because this calls translate-term
  (if (eq nil item) ; we assume nil is the constant nil, not an empty DAG
      (mv (erp-nil) *nil*)
    (if (weak-dagp item)
        (mv (erp-nil) item) ;already a DAG
      ;; translate the given form to obtain a pseudo-term and then make that into a DAG:
      (make-term-into-dag-basic-unguarded (translate-term item 'dag-or-term-to-dag wrld)
                                          nil))))

;; Returns the dag-or-quotep.  Does not return erp.
(defun dag-or-term-to-dag-basic! (item wrld)
  (declare (xargs :mode :program)) ;; because this depends on translate-term
  (mv-let (erp dag-or-quotep)
    (dag-or-term-to-dag-basic item wrld)
    (if erp
        (er hard? 'dag-or-term-to-dag-basic! "Error converting term into DAG.")
      dag-or-quotep)))
