; Tracking equalities involving nodenums
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

;; See also node-replacement-alist-for-context.

(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "all-dargp-less-than")

;; A node-replacement-alist maps nodenums to things (nodenums or quoteps) to
;; which they are known to be equal.  The mapping is represented by a list of
;; pairs of the form (<nodenum> . <nodenum-or-quotep>).
(defund node-replacement-alistp (pairs dag-len)
  (declare (xargs :guard (natp dag-len)))
  (and (alistp pairs)
       (all-natp (strip-cars pairs))
       (all-< (strip-cars pairs) dag-len)
       (all-dargp-less-than (strip-cdrs pairs) dag-len)))

(defthm node-replacement-alistp-of-nil
  (node-replacement-alistp nil dag-len)
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

(defthm node-replacement-alistp-forward-to-eqlable-alistp
  (implies (node-replacement-alistp pairs dag-len)
           (eqlable-alistp pairs))
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

(defthm node-replacement-alistp-forward-to-alistp
  (implies (node-replacement-alistp pairs dag-len)
           (alistp pairs))
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

(defthm node-replacement-alistp-monotone
  (implies (and (node-replacement-alistp pairs dag-len2)
                (<= dag-len2 dag-len))
           (node-replacement-alistp pairs dag-len))
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

;; Kept disabled most of the time, for speed
(defthmd dargp-less-than-of-cdr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp pairs dag-len)
                (<= dag-len bound)
                (assoc-equal nodenum pairs))
           (dargp-less-than (cdr (assoc-equal nodenum pairs)) bound))
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

;; Kept disabled most of the time, for speed
(defthmd dargp-of-cdr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp pairs dag-len)
                (<= dag-len bound)
                (assoc-equal nodenum pairs))
           (dargp (cdr (assoc-equal nodenum pairs))))
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

;; Uses consp as the normal form.
;; Kept disabled most of the time, for speed
(defthmd myquotep-of-cdr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp pairs dag-len)
                (assoc-equal nodenum pairs))
           (equal (myquotep (cdr (assoc-equal nodenum pairs)))
                  (consp (cdr (assoc-equal nodenum pairs)))))
  :hints (("Goal"
           :use (:instance dargp-of-cdr-of-assoc-equal
                           (var nodenum)
                           (alist pairs))
           :in-theory (e/d (node-replacement-alistp) (dargp-of-cdr-of-assoc-equal)))))

(defthmd natp-of-cdr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp pairs dag-len)
                (assoc-equal nodenum pairs))
           (equal (natp (cdr (assoc-equal nodenum pairs)))
                  (not (consp (cdr (assoc-equal nodenum pairs))))))
  :hints (("Goal"
           :use (:instance dargp-of-cdr-of-assoc-equal
                           (var nodenum)
                           (alist pairs))
           :in-theory (e/d (node-replacement-alistp) (dargp-of-cdr-of-assoc-equal)))))

;; Kept disabled most of the time, for speed
(defthmd consp-of-assoc-equal-when-node-replacement-alistp
  (implies (and (assoc-equal tree node-replacement-alist)
                (node-replacement-alistp node-replacement-alist dag-len))
           (consp (assoc-equal tree node-replacement-alist)))
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

(defthm node-replacement-alistp-of-cons-and-cons
  (equal (node-replacement-alistp (cons (cons lhs rhs) acc) dag-len)
         (and (node-replacement-alistp acc dag-len)
              (natp lhs)
              (< lhs dag-len)
              (dargp-less-than rhs dag-len)))
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

;; Separate so we can profile it
(defund assoc-in-node-replacement-alist (nodenum node-replacement-alist)
  (declare (xargs :guard (and (natp nodenum)
                              (alistp node-replacement-alist)
                              ;; can't call this unless dag-len is passed in:
                              ;; (node-replacement-alistp node-replacement-alist dag-len)
                              )))
  (assoc nodenum node-replacement-alist))
