; Index for variable nodes in DAGs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The dag-variable-alist is an index into the dag that maps expressions that
;; are variables to their nodenums.  Since these nodes have no children, we
;; cannot use the parent-array to find them.  The entries in the
;; dag-variable-alist should be sorted by decreasing nodenum.

;; (include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)

(local (in-theory (disable natp)))

;dup: pull out into a book about bounded-alists?
;; (defthm <-of-lookup-equal-when-all-<-of-strip-cdrs
;;   (implies (and (all-< (strip-cdrs alist) dag-len)
;;                 (lookup-equal expr alist))
;;            (< (lookup-equal expr alist) dag-len)))

;;;
;;; dag-variable-alistp
;;;

;; TODO: Add the constraints that the keys are all unique and the vals are all unique?
(defund dag-variable-alistp (alist)
  (declare (xargs :guard t))
  (and (symbol-alistp alist)
       (nat-listp (strip-cdrs alist))))

(defthm dag-variable-alistp-forward-to-alist
  (implies (dag-variable-alistp alist)
           (alistp alist))
  :hints (("Goal" :in-theory (enable dag-variable-alistp))))

(defthm dag-variable-alistp-forward-to-nat-listp-of-strip-cdrs
  (implies (dag-variable-alistp alist)
           (nat-listp (strip-cdrs alist)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dag-variable-alistp))))

(defthm dag-variable-alistp-forward-symbol-alistp
  (implies (dag-variable-alistp alist)
           (symbol-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dag-variable-alistp))))

;; (defthm integerp-of-lookup-equal-when-dag-variable-alistp
;;   (implies (dag-variable-alistp dag-variable-alist)
;;            (iff (integerp (lookup-equal var dag-variable-alist))
;;                 (lookup-equal var dag-variable-alist)))
;;   :hints (("Goal" :in-theory (enable  dag-variable-alistp))))

;; (defthm nonneg-of-lookup-equal-when-dag-variable-alistp
;;   (implies (dag-variable-alistp dag-variable-alist)
;;            (<= 0 (lookup-equal var dag-variable-alist)))
;;   :hints (("Goal" :in-theory (enable  dag-variable-alistp))))

(defthm dag-variable-alistp-of-cons-of-cons
  (equal (dag-variable-alistp (cons (cons var nodenum) alist))
         (and (symbolp var)
              (natp nodenum)
              (dag-variable-alistp alist)))
  :hints (("Goal" :in-theory (enable dag-variable-alistp))))

(defthm all-<-of-strip-cdrs-of-0-when-dag-variable-alistp
  (implies (dag-variable-alistp dag-variable-alist)
           (equal (all-< (strip-cdrs dag-variable-alist) 0)
                  (not (consp dag-variable-alist))))
  :hints (("Goal" :in-theory (enable dag-variable-alistp))))

(local
 (defthm natp-of-lookup-equal-when-dag-variable-alistp
   (implies (dag-variable-alistp dag-variable-alist)
            (iff (natp (lookup-equal var dag-variable-alist))
                 (assoc-equal var dag-variable-alist)))
   :hints (("Goal" :in-theory (enable assoc-equal dag-variable-alistp nat-listp)))))

;; todo: can we make rules like this local, now that we have a more abstract interface?
(local
 (defthmd natp-of-cdr-of-assoc-equal-when-dag-variable-alistp
   (implies (dag-variable-alistp dag-variable-alist)
            (iff (natp (cdr (assoc-equal var dag-variable-alist)))
                 (assoc-equal var dag-variable-alist)))
   :hints (("Goal" :in-theory (enable assoc-equal dag-variable-alistp nat-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Might change soon to use fast alists
(defund-inline add-to-dag-variable-alist (var nodenum dag-variable-alist)
  (declare (xargs :guard (and (symbolp var)
                              (natp nodenum)
                              (dag-variable-alistp dag-variable-alist))))
  (acons-fast var nodenum dag-variable-alist))

(defthm dag-variable-alistp-of-add-to-dag-variable-alist
  (equal (dag-variable-alistp (add-to-dag-variable-alist var nodenum dag-variable-alist))
         (and (symbolp var)
              (natp nodenum)
              (dag-variable-alistp dag-variable-alist)))
  :hints (("Goal" :in-theory (enable add-to-dag-variable-alist))))

;; todo: breaks the abstraction
(defthm strip-cdrs-of-add-to-dag-variable-alist
  (equal (strip-cdrs (add-to-dag-variable-alist var nodenum dag-variable-alist))
         (cons nodenum (strip-cdrs dag-variable-alist)))
  :hints (("Goal" :in-theory (enable add-to-dag-variable-alist))))

;; todo: breaks the abstraction
(defthm strip-cars-of-add-to-dag-variable-alist
  (equal (strip-cars (add-to-dag-variable-alist var nodenum dag-variable-alist))
         (cons var (strip-cars dag-variable-alist)))
  :hints (("Goal" :in-theory (enable add-to-dag-variable-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Might change soon to use fast alists
(defund-inline lookup-in-dag-variable-alist (var dag-variable-alist)
  (declare (xargs :guard (and (symbolp var)
                              (dag-variable-alistp dag-variable-alist))))
  (lookup-eq var dag-variable-alist))

(defthm lookup-in-dag-variable-alist-type
  (implies (dag-variable-alistp dag-variable-alist)
           (or (null (lookup-in-dag-variable-alist var dag-variable-alist))
               (natp (lookup-in-dag-variable-alist var dag-variable-alist))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable lookup-in-dag-variable-alist))))

;; (defthm lookup-in-dag-variable-alist-iff
;;   (implies (and (member-equal var (strip-cars dag-variable-alist))
;;                 (dag-variable-alistp dag-variable-alist))
;;            (lookup-in-dag-variable-alist var dag-variable-alist))
;;   :hints (("Goal" :in-theory (enable lookup-in-dag-variable-alist
;;                                      dag-variable-alistp))))

(defthm natp-of-lookup-in-dag-variable-alist
  (implies (and (member-equal var (strip-cars dag-variable-alist))
                (dag-variable-alistp dag-variable-alist))
           (natp (lookup-in-dag-variable-alist var dag-variable-alist)))
  :hints (("Goal" :in-theory (enable lookup-in-dag-variable-alist
                                     dag-variable-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; bounded-dag-variable-alistp
;;;

;; Recognize a dag-variable-alist all of whose cdrs are nodenums less than the dag-len.
(defund bounded-dag-variable-alistp (alist dag-len)
  (declare (xargs :guard (natp dag-len)))
  (and (dag-variable-alistp alist)
       (all-< (strip-cdrs alist) dag-len)))

(defthm bounded-dag-variable-alistp-forward-to-dag-variable-alistp
  (implies (bounded-dag-variable-alistp alist dag-len)
           (dag-variable-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp))))

(defthm bounded-dag-variable-alistp-monotone
  (implies (and (bounded-dag-variable-alistp alist dag-len1)
                (<= dag-len1 dag-len2))
           (bounded-dag-variable-alistp alist dag-len2))
  :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp))))

(defthm bounded-dag-variable-alistp-of-nil
  (bounded-dag-variable-alistp nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp))))

(defthm <-of-lookup-in-dag-variable-alist-when-bounded-dag-variable-alistp
  (implies (and (bounded-dag-variable-alistp alist dag-len)
                (lookup-in-dag-variable-alist var alist))
           (< (lookup-in-dag-variable-alist var alist) dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp dag-variable-alistp lookup-in-dag-variable-alist))))

(local
 (defthm <-of-cdr-of-assoc-equal-when-bounded-dag-variable-alistp
   (implies (and (bounded-dag-variable-alistp alist dag-len)
                 (assoc-equal var alist))
            (< (cdr (assoc-equal var alist)) dag-len))
   :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp dag-variable-alistp)))))

(defthm bounded-dag-variable-alistp-of-add-to-dag-variable-alist
  (equal (bounded-dag-variable-alistp (add-to-dag-variable-alist var nodenum alist) dag-len)
         (and (symbolp var)
              (natp nodenum)
              (< nodenum dag-len)
              (bounded-dag-variable-alistp alist dag-len)))
  :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp))))
