; Index for variable nodes in DAGs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The dag-variable-alist is an index into the dag that node expressions that
;; are variables to their nodenums.  Since these nodes have no children, we
;; cannot use the parent-array to find them.  The entries in the
;; dag-variable-alist should be sorted by decreasing nodenum.

(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)

;dup: pull out into a book about bounded-alists?
(defthm <-of-lookup-equal-when-all-<-of-strip-cdrs
  (implies (and (all-< (strip-cdrs alist) dag-len)
                (lookup-equal expr alist))
           (< (lookup-equal expr alist) dag-len)))

;;;
;;; dag-variable-alistp
;;;

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

(defthm integerp-of-lookup-equal-when-dag-variable-alistp
  (implies (dag-variable-alistp dag-variable-alist)
           (iff (integerp (lookup-equal var dag-variable-alist))
                (lookup-equal var dag-variable-alist)))
  :hints (("Goal" :in-theory (enable  dag-variable-alistp))))

(defthm nonneg-of-lookup-equal-when-dag-variable-alistp
  (implies (dag-variable-alistp dag-variable-alist)
           (<= 0 (lookup-equal var dag-variable-alist)))
  :hints (("Goal" :in-theory (enable  dag-variable-alistp))))

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

(defthmd natp-of-lookup-equal-when-dag-variable-alistp
  (implies (dag-variable-alistp dag-variable-alist)
           (iff (natp (lookup-equal var dag-variable-alist))
                (assoc-equal var dag-variable-alist)))
  :hints (("Goal" :in-theory (enable assoc-equal dag-variable-alistp nat-listp))))

(defthmd natp-of-cdr-of-assoc-equal-when-dag-variable-alistp
  (implies (dag-variable-alistp dag-variable-alist)
           (iff (natp (cdr (assoc-equal var dag-variable-alist)))
                (assoc-equal var dag-variable-alist)))
  :hints (("Goal" :in-theory (enable assoc-equal dag-variable-alistp nat-listp))))

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

;todo: replace with a designated lookup operation for dag-variable-alists
(defthm <-of-lookup-equal-when-bounded-dag-variable-alistp
  (implies (and (bounded-dag-variable-alistp alist dag-len)
                (lookup-equal var alist))
           (< (lookup-equal var alist) dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp dag-variable-alistp))))

(defthm <-of-cdr-of-assoc-equal-when-bounded-dag-variable-alistp
  (implies (and (bounded-dag-variable-alistp alist dag-len)
                (assoc-equal var alist))
           (< (cdr (assoc-equal var alist)) dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp dag-variable-alistp))))

(defthm bounded-dag-variable-alistp-of-cons-of-cons
  (equal (bounded-dag-variable-alistp (cons (cons var nodenum) alist) dag-len)
         (and (symbolp var)
              (natp nodenum)
              (< nodenum dag-len)
              (bounded-dag-variable-alistp alist dag-len)))
  :hints (("Goal" :in-theory (enable bounded-dag-variable-alistp))))
