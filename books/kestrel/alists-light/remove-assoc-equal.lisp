; A lightweight book about the built-in function remove-assoc-equal
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Grant Jurgensen (grant@kestrel.edu)
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book previously introduced an equivalent function called clear-key.

(in-theory (disable remove-assoc-equal))

;; Changed param names to match std
(defthm alistp-of-remove-assoc-equal
  (implies (alistp x)
           (alistp (remove-assoc-equal a x)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm true-listp-of-remove-assoc-equal-type
  (implies (true-listp alist)
           (true-listp (remove-assoc-equal x alist)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm len-of-remove-assoc-equal-linear
  (<= (len (remove-assoc-equal x alist))
      (len alist))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm len-of-remove-assoc-equal-when-assoc-equal-linear
  (implies (assoc-equal x alist)
           (< (len (remove-assoc-equal x alist))
              (len alist)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm len-of-remove-assoc-equal-when-not-assoc-equal
  (implies (and (not (assoc-equal x alist))
                ;; Some hyp is needed here. Consider x = 'nil and alist = '(nil):
                (or (alistp alist) x) ; perhaps reorder the disjuncts?
                )
           (equal (len (remove-assoc-equal x alist))
                  (len alist)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal assoc-equal))))

(defthm acl2-count-of-remove-assoc-equal-linear
  (<= (acl2-count (remove-assoc-equal x alist))
      (acl2-count alist))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm acl2-count-of-remove-assoc-equal-when-assoc-equal-linear
  (implies (assoc-equal x alist)
           (< (acl2-count (remove-assoc-equal x alist))
              (acl2-count alist)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm acl2-count-of-remove-assoc-equal-when-not-assoc-equal
  (implies (and (not (assoc-equal x alist))
                ;; Some hyp is needed here. Consider x = 'nil and alist = '(nil):
                (alistp alist))
           (equal (acl2-count (remove-assoc-equal x alist))
                  (acl2-count alist)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm remove-assoc-equal-when-not-member-equal-of-strip-cars
  (implies (not (member-equal x (strip-cars alist)))
           (equal (remove-assoc-equal x alist)
                  (true-list-fix alist)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm remove-assoc-equal-when-not-assoc-equal
  (implies (and (not (assoc-equal x alist))
                (alistp alist))
           (equal (remove-assoc-equal x alist)
                  alist))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthmd remove-assoc-equal-when-not-assoc-equal-gen
  (implies (and (not (assoc-equal x alist))
                (or (alistp alist) x))
           (equal (remove-assoc-equal x alist)
                  (true-list-fix alist)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal true-list-fix))))

(defthm remove-assoc-equal-when-not-consp-cheap
  (implies (not (consp alist))
           (equal (remove-assoc-equal x alist)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; A loop stopper is introduced implicitly
(defthm remove-assoc-equal-of-remove-assoc-equal
  (equal (remove-assoc-equal x1 (remove-assoc-equal x2 alist))
         (remove-assoc-equal x2 (remove-assoc-equal x1 alist)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

;; idempotence
(defthm remove-assoc-equal-of-remove-assoc-equal-same
  (equal (remove-assoc-equal x (remove-assoc-equal x alist))
         (remove-assoc-equal x alist))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm assoc-equal-of-remove-assoc-equal
  (equal (assoc-equal x1 (remove-assoc-equal x2 alist))
         (if (equal x1 x2)
             nil
           (assoc-equal x1 alist)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

;; Changed param names to match std
(defthm strip-cars-of-remove-assoc-equal
  (equal (strip-cars (remove-assoc-equal a x))
         (remove-equal a (strip-cars x)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))

(defthm remove-assoc-equal-of-append
  (equal (remove-assoc-equal x (append alist1 alist2))
         (append (remove-assoc-equal x alist1)
                 (remove-assoc-equal x alist2)))
  :hints (("Goal" :in-theory (enable remove-assoc-equal))))
