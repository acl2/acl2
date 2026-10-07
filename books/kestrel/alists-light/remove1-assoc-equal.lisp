; A lightweight book about the built-in function remove1-assoc-equal
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also remove-assoc-equal.lisp, which removes all pairs with the given key.

(local (include-book "assoc-equal"))

(in-theory (disable remove1-assoc-equal))

(defthm remove1-assoc-equal-when-not-consp-cheap
  (implies (not (consp alist))
           (equal (remove1-assoc-equal key alist)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm remove1-assoc-equal-of-cons
  (equal (remove1-assoc-equal key (cons pair alist))
         (if (equal key (car pair))
             alist
           (cons pair (remove1-assoc-equal key alist))))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

;; todo: non-standard param name is to match std
(defthm alistp-of-remove1-assoc-equal
  (implies (alistp x)
           (alistp (remove1-assoc-equal key x)))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm true-listp-of-remove1-assoc-equal-type
  (implies (true-listp alist)
           (true-listp (remove1-assoc-equal key alist)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm len-of-remove1-assoc-equal-linear
  (<= (len (remove1-assoc-equal key alist))
      (len alist))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm len-of-remove1-assoc-equal-when-assoc-equal
  (implies (assoc-equal key alist)
           (equal (len (remove1-assoc-equal key alist))
                  (+ -1 (len alist))))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm len-of-remove1-assoc-equal-when-not-assoc-equal
  (implies (and (not (assoc-equal key alist))
                ;; Some hyp is needed here. Consider key = 'nil and alist = '(nil):
                (or (alistp alist) key))
           (equal (len (remove1-assoc-equal key alist))
                  (len alist)))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal assoc-equal))))

(defthm acl2-count-of-remove1-assoc-equal-linear
  (<= (acl2-count (remove1-assoc-equal key alist))
      (acl2-count alist))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm acl2-count-of-remove1-assoc-equal-when-assoc-equal-linear
  (implies (assoc-equal key alist)
           (< (acl2-count (remove1-assoc-equal key alist))
              (acl2-count alist)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm remove1-assoc-equal-when-not-assoc-equal
  (implies (and (not (assoc-equal key alist))
                (alistp alist))
           (equal (remove1-assoc-equal key alist)
                  alist))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm remove1-assoc-equal-when-not-member-equal-of-strip-cars
  (implies (not (member-equal key (strip-cars alist)))
           (equal (remove1-assoc-equal key alist)
                  (true-list-fix alist)))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

;; Removing one pair with a given key does not affect lookups of other keys.
(defthm assoc-equal-of-remove1-assoc-equal-diff
  (implies (not (equal key1 key2))
           (equal (assoc-equal key1 (remove1-assoc-equal key2 alist))
                  (assoc-equal key1 alist)))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

;; If there are no duplicate keys, removing the (unique) pair with a given key
;; means that key is no longer bound.
(defthm assoc-equal-of-remove1-assoc-equal-same
  (implies (no-duplicatesp-equal (strip-cars alist))
           (equal (assoc-equal key (remove1-assoc-equal key alist))
                  nil))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal
                                     member-equal-of-strip-cars-when-assoc-equal))))

(defthm strip-cars-of-remove1-assoc-equal
  (equal (strip-cars (remove1-assoc-equal key alist))
         (remove1-equal key (strip-cars alist)))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm remove1-assoc-equal-of-append
  (implies (alistp alist1) ; needed, e.g., if key is nil and alist1 contains an atom
           (equal (remove1-assoc-equal key (append alist1 alist2))
                  (if (assoc-equal key alist1)
                      (append (remove1-assoc-equal key alist1) alist2)
                    (append alist1 (remove1-assoc-equal key alist2)))))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))

(defthm remove1-assoc-equal-of-remove1-assoc-equal
  (equal (remove1-assoc-equal key1 (remove1-assoc-equal key2 alist))
         (remove1-assoc-equal key2 (remove1-assoc-equal key1 alist)))
  :hints (("Goal" :in-theory (enable remove1-assoc-equal))))
