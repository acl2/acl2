; Utilities to make terms into dag-arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This version does not handle embedded dags, resolve ifs, or evaluate ground terms.
;; See also make-term-into-dag-array-basic.lisp.

(include-book "merge-term-into-dag-array-simple")

(local (in-theory (disable posp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where nodenum-or-quotep is
;; equivalent to the TERM passed in.
(defund make-term-into-dag-array-simple (term dag-array-name dag-parent-array-name)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp dag-array-name)
                              (symbolp dag-parent-array-name))))
  (b* ((slack-amount 1000) ; why 1000?
       ;; Start with an empty dag:
       ((mv dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (empty-dag-array-with-name slack-amount dag-array-name dag-parent-array-name))
       ((mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (merge-term-into-dag-array-simple term
                                          nil ;initial var-replacement-alist
                                          dag-array
                                          dag-len
                                          dag-parent-array
                                          dag-constant-alist dag-variable-alist
                                          dag-array-name dag-parent-array-name))
       ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
    (mv (erp-nil) nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))

(defthm wf-dagp-of-make-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (not (mv-nth 0 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
           (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name)
             (declare (ignore erp nodenum-or-quotep))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :in-theory (enable make-term-into-dag-array-simple))))

(defthm pseudo-dag-arrayp-after-make-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (not (mv-nth 0 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
           (pseudo-dag-arrayp dag-array-name
                              (mv-nth 2 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))
                              (mv-nth 3 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
  :hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-simple)
           :in-theory (disable wf-dagp-of-make-term-into-dag-array-simple))))

(defthm natp-of-mv-nth-3-of-make-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (not (mv-nth 0 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
           (natp (mv-nth 3 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-simple)
           :in-theory (disable wf-dagp-of-make-term-into-dag-array-simple))))

(defthm <-of-mv-nth-3-of-make-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (not (mv-nth 0 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
           (<= (mv-nth 3 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))
               *max-1d-array-length*))
  :hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-simple)
           :in-theory (disable wf-dagp-of-make-term-into-dag-array-simple))))

(defthm posp-of-mv-nth-3-of-make-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                ;; returns a nodenum, not a quotep:
                (not (consp (mv-nth 1 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
           (posp (mv-nth 3 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (make-term-into-dag-array-simple
                                   merge-terms-into-dag-array-simple)
                                  (posp)))))

(defthm dargp-of-mv-nth-1-of-make-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
           (dargp (mv-nth 1 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (make-term-into-dag-array-simple
                                   merge-terms-into-dag-array-simple)
                                  (posp natp dargp)))))

;; We use consp as the normal forma
(defthm myquotep-of-mv-nth-1-of-make-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name))))
           (equal (myquotep (mv-nth 1 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name)))
                  (consp (mv-nth 1 (make-term-into-dag-array-simple term dag-array-name dag-parent-array-name)))))
  :hints (("Goal" :use dargp-of-mv-nth-1-of-make-term-into-dag-array-simple
           :in-theory (disable dargp-of-mv-nth-1-of-make-term-into-dag-array-simple))))

;;;
;;; make-terms-into-dag-array-simple
;;;

;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where nodenums-or-quoteps are
;; equivalent to the TERMS passed in.
(defund make-terms-into-dag-array-simple (terms dag-array-name dag-parent-array-name)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (symbolp dag-array-name)
                              (symbolp dag-parent-array-name))))
  ;; todo: call empty-dag-array
  (merge-terms-into-dag-array-simple terms
                                     nil ;initial var-replacement-alist
                                     (make-empty-array dag-array-name 1000) ;fixme why 1000?
                                     0 ;initial dag-len
                                     (make-empty-array dag-parent-array-name 1000)
                                     nil ;empty dag-constant-alist
                                     (empty-dag-variable-alist)
                                     dag-array-name dag-parent-array-name
                                     ))

(defthm wf-dagp-of-make-terms-into-dag-array-simple
  (implies (and (pseudo-term-listp terms)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (not (mv-nth 0 (make-terms-into-dag-array-simple terms dag-array-name dag-parent-array-name))))
           (mv-let (erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-terms-into-dag-array-simple terms dag-array-name dag-parent-array-name)
             (declare (ignore erp nodenums-or-quoteps))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :in-theory (enable make-terms-into-dag-array-simple))))

(defthm bounded-darg-listp-of-mv-nth-1-of-make-terms-into-dag-array-simple
  (implies (and (pseudo-term-listp terms)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (not (mv-nth 0 (make-terms-into-dag-array-simple terms dag-array-name dag-parent-array-name))))
           (bounded-darg-listp (mv-nth 1 (make-terms-into-dag-array-simple terms dag-array-name dag-parent-array-name))
                               (mv-nth 3 (make-terms-into-dag-array-simple terms dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable make-terms-into-dag-array-simple))))

(defthm true-listp-of-mv-nth-1-of-make-terms-into-dag-array-simple
  (implies (and (pseudo-term-listp terms)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (not (mv-nth 0 (make-terms-into-dag-array-simple terms dag-array-name dag-parent-array-name))))
           (true-listp (mv-nth 1 (make-terms-into-dag-array-simple terms dag-array-name dag-parent-array-name))))
  :hints (("Goal" :in-theory (enable make-terms-into-dag-array-simple))))
