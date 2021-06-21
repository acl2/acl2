; Utilities to make terms into dags
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The functions in this book use the basic evaluator to evaluate ground terms.

(include-book "merge-term-into-dag-array-basic")

;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where nodenums-or-quoteps are
;; equivalent to the TERMS passed in.
(defund make-terms-into-dag-array-basic (terms dag-array-name dag-parent-array-name interpreted-function-alist)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (symbolp dag-array-name)
                              (symbolp dag-parent-array-name)
                              (interpreted-function-alistp interpreted-function-alist))))
  (merge-terms-into-dag-array-basic terms
                                    nil ;initial var-replacement-alist
                                    (make-empty-array dag-array-name 1000) ;fixme why 1000?
                                    0 ;initial dag-len
                                    (make-empty-array dag-parent-array-name 1000)
                                    nil  ;empty dag-constant-alist
                                    nil  ;empty dag-variable-alist
                                    dag-array-name dag-parent-array-name
                                    interpreted-function-alist))

(defthm wf-dagp-of-make-terms-into-dag-array-basic
  (implies (and (pseudo-term-listp terms)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (make-terms-into-dag-array-basic terms dag-array-name dag-parent-array-name interpreted-function-alist))))
           (mv-let (erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-terms-into-dag-array-basic terms dag-array-name dag-parent-array-name interpreted-function-alist)
             (declare (ignore erp nodenums-or-quoteps))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :in-theory (enable make-terms-into-dag-array-basic))))

(defthm all-dargp-less-than-of-mv-nth-1-of-make-terms-into-dag-array-basic
  (implies (and (pseudo-term-listp terms)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (make-terms-into-dag-array-basic terms dag-array-name dag-parent-array-name interpreted-function-alist))))
           (all-dargp-less-than (mv-nth 1 (make-terms-into-dag-array-basic terms dag-array-name dag-parent-array-name interpreted-function-alist))
                                (mv-nth 3 (make-terms-into-dag-array-basic terms dag-array-name dag-parent-array-name interpreted-function-alist))))
  :hints (("Goal" :in-theory (enable make-terms-into-dag-array-basic))))

(defthm true-listp-of-mv-nth-1-of-make-terms-into-dag-array-basic
  (implies (and (pseudo-term-listp terms)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (make-terms-into-dag-array-basic terms dag-array-name dag-parent-array-name interpreted-function-alist))))
           (true-listp (mv-nth 1 (make-terms-into-dag-array-basic terms dag-array-name dag-parent-array-name interpreted-function-alist))))
  :hints (("Goal" :in-theory (enable make-terms-into-dag-array-basic))))

;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array
;; dag-constant-alist dag-variable-alist), where nodenum-or-quotep is
;; equivalent to the TERM passed in.
(defund make-term-into-dag-array-basic (term dag-array-name dag-parent-array-name interpreted-function-alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp dag-array-name)
                              (symbolp dag-parent-array-name)
                              (interpreted-function-alistp interpreted-function-alist))))
  (b* (((mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (merge-term-into-dag-array-basic term
                                         nil ;initial var-replacement-alist
                                         (make-empty-array dag-array-name 1000) ;fixme why 1000?
                                         0 ;initial dag-len
                                         (make-empty-array dag-parent-array-name 1000)
                                         nil  ;empty dag-constant-alist
                                         nil  ;empty dag-variable-alist
                                         dag-array-name dag-parent-array-name
                                         interpreted-function-alist))
       ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
    (mv (erp-nil) nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))

(defthm wf-dagp-of-make-term-into-dag-array-basic
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
           (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist)
             (declare (ignore erp nodenum-or-quotep))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :in-theory (enable make-term-into-dag-array-basic))))

(defthm pseudo-dag-arrayp-after-make-term-into-dag-array-basic
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
           (pseudo-dag-arrayp dag-array-name
                              (mv-nth 2 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))
                              (mv-nth 3 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
  :hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-basic)
           :in-theory (disable wf-dagp-of-make-term-into-dag-array-basic))))

(defthm natp-of-mv-nth-3-of-make-term-into-dag-array-basic
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
           (natp (mv-nth 3 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-basic)
           :in-theory (disable wf-dagp-of-make-term-into-dag-array-basic))))

(defthm <-of-mv-nth-3-of-make-term-into-dag-array-basic
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
           (< (mv-nth 3 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))
              2147483647))
  :hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-basic)
           :in-theory (disable wf-dagp-of-make-term-into-dag-array-basic))))

(defthm posp-of-mv-nth-3-of-make-term-into-dag-array-basic
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                ;; returns a nodenum, not a quotep:
                (not (consp (mv-nth 1 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
           (posp (mv-nth 3 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (make-term-into-dag-array-basic
                                   merge-terms-into-dag-array-basic)
                                  (posp)))))

(defthm dargp-of-mv-nth-1-of-make-term-into-dag-array-basic
  (implies (and (pseudo-termp term)
                (symbolp dag-array-name)
                (symbolp dag-parent-array-name)
                (interpreted-function-alistp interpreted-function-alist)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
           (dargp (mv-nth 1 (make-term-into-dag-array-basic term dag-array-name dag-parent-array-name interpreted-function-alist))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (make-term-into-dag-array-basic
                                   merge-terms-into-dag-array-basic)
                                  (posp natp dargp)))))

;;;
;;; make-term-into-dag-basic
;;;

;; Returns (mv erp dag-or-quotep).  Returns the DAG as a list but uses arrays to do the work.
(defund make-term-into-dag-basic (term interpreted-function-alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (interpreted-function-alistp interpreted-function-alist))
                  :guard-hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-basic
                                                        (dag-array-name 'make-term-into-dag-basic-array)
                                                        (dag-parent-array-name 'make-term-into-dag-basic-parent-array))
                                 :in-theory (disable wf-dagp-of-make-term-into-dag-array-basic)))))
  (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (make-term-into-dag-array-basic term 'make-term-into-dag-basic-array 'make-term-into-dag-basic-parent-array interpreted-function-alist)
    (declare (ignore dag-parent-array dag-constant-alist dag-variable-alist))
    (if erp
        (mv erp nil)
      (if (consp nodenum-or-quotep) ; check for quotep
          (mv (erp-nil) nodenum-or-quotep)
        (mv (erp-nil) (array-to-alist 'make-term-into-dag-basic-array dag-array dag-len))))))

(local
 (defthm equal-of-quote-and-car-when-dargp
   (implies (dargp x)
            (equal (equal 'quote (car x))
                   (consp x)))))

(defthm make-term-into-dag-basic-return-type
  (implies (and (pseudo-termp term)
                (interpreted-function-alistp interpreted-function-alist)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-basic term interpreted-function-alist))))
           (or (pseudo-dagp (mv-nth 1 (make-term-into-dag-basic term interpreted-function-alist)))
               (myquotep (mv-nth 1 (make-term-into-dag-basic term interpreted-function-alist)))))
  :hints (("Goal" :in-theory (e/d (make-term-into-dag-basic) (natp)))))

(defthm pseudo-dagp-of-mv-nth-1-of-make-term-into-dag-basic
  (implies (and (pseudo-termp term)
                (interpreted-function-alistp interpreted-function-alist)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-basic term interpreted-function-alist)))
                (not (myquotep (mv-nth 1 (make-term-into-dag-basic term interpreted-function-alist)))))
           (pseudo-dagp (mv-nth 1 (make-term-into-dag-basic term interpreted-function-alist))))
  :hints (("Goal" :use (:instance make-term-into-dag-basic-return-type)
           :in-theory (disable make-term-into-dag-basic-return-type))))

(defthm <-of-len-of-mv-nth-1-of-make-term-into-dag-basic
  (implies (and (pseudo-termp term)
                (interpreted-function-alistp interpreted-function-alist)
                ;; no error:
                (not (mv-nth 0 (make-term-into-dag-basic term interpreted-function-alist)))
                (not (myquotep (mv-nth 1 (make-term-into-dag-basic term interpreted-function-alist)))))
           (< (len (mv-nth 1 (make-term-into-dag-basic term interpreted-function-alist)))
              2147483647))
  :hints (("Goal" :in-theory (enable make-term-into-dag-basic))))

;; Returns (mv erp dag-or-quotep).  Returns the DAG as a list but uses arrays to do the work.
;; This wrapper has no invariant risk because it has a guard of t.
(defund make-term-into-dag-basic-unguarded (term interpreted-function-alist)
  (declare (xargs :guard t))
  (if (not (and (pseudo-termp term)
                (interpreted-function-alistp interpreted-function-alist)))
      (prog2$ (er hard? 'make-term-into-dag-basic-unguarded "Bad input.")
              (mv (erp-t) nil))
    (make-term-into-dag-basic term interpreted-function-alist)))

;; Returns the dag-or-quotep.  Does not return erp.
(defund make-term-into-dag-basic! (term interpreted-function-alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (interpreted-function-alistp interpreted-function-alist))
                  :guard-hints (("Goal" :use (:instance wf-dagp-of-make-term-into-dag-array-basic
                                                        (dag-array-name 'make-term-into-dag-basic-array)
                                                        (dag-parent-array-name 'make-term-into-dag-basic-parent-array))
                                 :in-theory (disable wf-dagp-of-make-term-into-dag-array-basic)))))
  (mv-let (erp dag-or-quotep)
    (make-term-into-dag-basic term interpreted-function-alist)
    (if erp
        (er hard? 'make-term-into-dag-basic "Error making term into dag.")
      dag-or-quotep)))
