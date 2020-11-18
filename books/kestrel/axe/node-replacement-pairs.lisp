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

;; See also node-replacement-pairs-for-context.

(include-book "dags")

 ;pairs of the form (<nodenum> . <nodenum-or-quotep>)
;; TODO: Rename to node-replacement-alist?
(defund node-replacement-pairsp (pairs dag-len)
  (declare (xargs :guard (natp dag-len)))
  (and (alistp pairs)
       (all-natp (strip-cars pairs))
       (all-< (strip-cars pairs) dag-len)
       (all-dargp-less-than (strip-cdrs pairs) dag-len)))

(defthm node-replacement-pairsp-of-nil
  (node-replacement-pairsp nil dag-len)
  :hints (("Goal" :in-theory (enable node-replacement-pairsp))))

(defthm node-replacement-pairsp-forward-to-eqlable-alistp
  (implies (node-replacement-pairsp pairs dag-len)
           (eqlable-alistp pairs))
  :hints (("Goal" :in-theory (enable node-replacement-pairsp))))

(defthm node-replacement-pairsp-forward-to-alistp
  (implies (node-replacement-pairsp pairs dag-len)
           (alistp pairs))
  :hints (("Goal" :in-theory (enable node-replacement-pairsp))))

(defthm node-replacement-pairsp-monotone
  (implies (and (node-replacement-pairsp pairs dag-len2)
                (<= dag-len2 dag-len))
           (node-replacement-pairsp pairs dag-len))
  :hints (("Goal" :in-theory (enable node-replacement-pairsp))))

;; Kept disabled most of the time, for speed
(defthmd dargp-less-than-of-cdr-of-assoc-equal-when-node-replacement-pairsp
  (implies (and (node-replacement-pairsp pairs dag-len)
                (<= dag-len bound)
                (assoc-equal nodenum pairs))
           (dargp-less-than (cdr (assoc-equal nodenum pairs)) bound))
  :hints (("Goal" :in-theory (enable node-replacement-pairsp))))

;; Kept disabled most of the time, for speed
(defthmd dargp-of-cdr-of-assoc-equal-when-node-replacement-pairsp
  (implies (and (node-replacement-pairsp pairs dag-len)
                (<= dag-len bound)
                (assoc-equal nodenum pairs))
           (dargp (cdr (assoc-equal nodenum pairs))))
  :hints (("Goal" :in-theory (enable node-replacement-pairsp))))

;; Uses consp as the normal form.
;; Kept disabled most of the time, for speed
(defthmd myquotep-of-cdr-of-assoc-equal-when-node-replacement-pairsp
  (implies (and (node-replacement-pairsp pairs dag-len)
                (assoc-equal nodenum pairs))
           (equal (myquotep (cdr (assoc-equal nodenum pairs)))
                  (consp (cdr (assoc-equal nodenum pairs)))))
  :hints (("Goal"
           :use (:instance dargp-of-cdr-of-assoc-equal
                           (var nodenum)
                           (alist pairs))
           :in-theory (e/d (node-replacement-pairsp) (dargp-of-cdr-of-assoc-equal)))))

(defthmd natp-of-cdr-of-assoc-equal-when-node-replacement-pairsp
  (implies (and (node-replacement-pairsp pairs dag-len)
                (assoc-equal nodenum pairs))
           (equal (natp (cdr (assoc-equal nodenum pairs)))
                  (not (consp (cdr (assoc-equal nodenum pairs))))))
  :hints (("Goal"
           :use (:instance dargp-of-cdr-of-assoc-equal
                           (var nodenum)
                           (alist pairs))
           :in-theory (e/d (node-replacement-pairsp) (dargp-of-cdr-of-assoc-equal)))))

;; Kept disabled most of the time, for speed
(defthmd consp-of-assoc-equal-when-node-replacement-pairsp
  (implies (and (assoc-equal tree node-replacement-pairs)
                (node-replacement-pairsp node-replacement-pairs dag-len))
           (consp (assoc-equal tree node-replacement-pairs)))
  :hints (("Goal" :in-theory (enable node-replacement-pairsp))))

(defthm node-replacement-pairsp-of-cons-and-cons
  (equal (node-replacement-pairsp (cons (cons lhs rhs) acc) dag-len)
         (and (node-replacement-pairsp acc dag-len)
              (natp lhs)
              (< lhs dag-len)
              (dargp-less-than rhs dag-len)))
  :hints (("Goal" :in-theory (enable node-replacement-pairsp))))

;; Separate so we can profile it
(defun assoc-in-node-replacement-pairs (nodenum node-replacement-pairs)
  (declare (xargs :guard (and (natp nodenum)
                              ;;(node-replacement-pairsp node-replacement-pairs)
                              (alistp node-replacement-pairs)
                              )))
  (assoc nodenum node-replacement-pairs))
