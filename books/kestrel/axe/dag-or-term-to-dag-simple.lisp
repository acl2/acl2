; A utility to convert a DAG or term into a DAG.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This version does not handle embedded dags, resolve ifs, or evaluate ground terms.
;; See also dag-or-term-to-dag-basic.lisp

(include-book "make-term-into-dag-simple")

;; ITEM is a dag or an (untranslated) term.  If a term, it is converted to a dag (or quotep).
;; Returns (mv erp dag-or-quotep).
;; Can throw an error if translation of the term fails.
(defun dag-or-term-to-dag-simple (item wrld)
  (declare (xargs :mode :program)) ;; because this calls translate-term
  (if (eq nil item) ; we assume nil is the constant nil, not an empty DAG
      (mv (erp-nil) *nil*)
    (if (weak-dagp item)
        (mv (erp-nil) item) ;already a DAG
      ;; translate the given item to obtain a pseudo-term and then make that into a DAG:
      (make-term-into-dag-simple (translate-term item 'dag-or-term-to-dag wrld)))))

;; Uncomment if needed:
;; ;; Returns (mv erp dag-or-quotep).  This variant has no invariant-risk because
;; ;; it calls make-term-into-dag-simple-unguarded, which has no invariant-risk.
;; (defun dag-or-term-to-dag-simple-unguarded (item wrld)
;;   (declare (xargs :mode :program)) ;; because this calls translate-term
;;   (if (eq nil item) ; we assume nil is the constant nil, not an empty DAG
;;       (mv (erp-nil) *nil*)
;;     (if (weak-dagp item)
;;         (mv (erp-nil) item) ;already a DAG
;;       ;; translate the given item to obtain a pseudo-term and then make that into a DAG:
;;       (make-term-into-dag-simple-unguarded (translate-term item 'dag-or-term-to-dag wrld)))))
