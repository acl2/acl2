; Index for constant nodes in DAGs
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

;; The dag-constant-alist is an index into the dag that node expressions that
;; are constants, including calls of 0-ary functions, to their nodenums. Since
;; these nodes have no children, we cannot use the parent-array to find them.
;; The entries in the dag-constant-alist should be sorted by decreasing
;; nodenum.

(include-book "no-atoms")
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)

;;;
;;; dag-constant-alistp
;;;

;strengthen
(defund dag-constant-alistp (alist)
  (declare (xargs :guard t))
  (and (alistp alist)
       (nat-listp (strip-cdrs alist))))

(defthm rational-listp-of-strip-cdrs-when-dag-constant-alistp
  (implies (dag-constant-alistp alist)
           (rational-listp (strip-cdrs alist)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dag-constant-alistp))))

(defthm dag-constant-alistp-forward-to-alistp
  (implies (dag-constant-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dag-constant-alistp))))

(defthm integerp-of-lookup-equal-when-dag-constant-alistp
  (implies (dag-constant-alistp dag-constant-alist)
           (iff (integerp (lookup-equal expr dag-constant-alist))
                (lookup-equal expr dag-constant-alist)))
  :hints (("Goal" :in-theory (enable  dag-constant-alistp))))

(defthm nonneg-of-lookup-equal-when-dag-constant-alistp
  (implies (dag-constant-alistp dag-constant-alist)
           (<= 0 (lookup-equal expr dag-constant-alist)))
  :hints (("Goal" :in-theory (enable  dag-constant-alistp))))

(defthm dag-constant-alistp-of-cons-of-cons
  (equal (dag-constant-alistp (cons (cons expr nodenum) alist))
         (and (natp nodenum)
              (dag-constant-alistp alist)))
  :hints (("Goal" :in-theory (enable dag-constant-alistp))))

;;;
;;; bounded-dag-constant-alistp
;;;

;; Recognize a dag-constant-alist all of whose cdrs are nodenums less than the dag-len.
(defund bounded-dag-constant-alistp (alist dag-len)
  (declare (xargs :guard (natp dag-len)))
  (and (dag-constant-alistp alist)
       (all-< (strip-cdrs alist) dag-len)))

(defthm bounded-dag-constant-alistp-forward-to-dag-constant-alistp
  (implies (bounded-dag-constant-alistp alist dag-len)
           (dag-constant-alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp))))

(defthm bounded-dag-constant-alistp-monotone
  (implies (and (bounded-dag-constant-alistp alist dag-len1)
                (<= dag-len1 dag-len2))
           (bounded-dag-constant-alistp alist dag-len2))
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp))))

(defthm bounded-dag-constant-alistp-of-nil
  (bounded-dag-constant-alistp nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp))))

;todo: replace with a designated lookup operation for dag-constant-alists
(defthm <-of-lookup-equal-when-bounded-dag-constant-alistp
  (implies (and (bounded-dag-constant-alistp alist dag-len)
                (lookup-equal expr alist))
           (< (lookup-equal expr alist) dag-len))
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp dag-constant-alistp))))

(defthm bounded-dag-constant-alistp-of-cons-of-cons
  (equal (bounded-dag-constant-alistp (cons (cons expr nodenum) alist) dag-len)
         (and (natp nodenum)
              (< nodenum dag-len)
              (bounded-dag-constant-alistp alist dag-len)))
  :hints (("Goal" :in-theory (enable bounded-dag-constant-alistp))))
