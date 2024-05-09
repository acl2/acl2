; Axe rules about lists
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

(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/memberp-def" :dir :system)
(include-book "kestrel/lists-light/nth-to-unroll" :dir :system)
(include-book "kestrel/lists-light/prefixp-def" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "axe-syntax")
(include-book "known-booleans")
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(add-known-boolean prefixp)

(def-constant-opener memberp)

(defthmd consp-of-cons
  (consp (cons a x)))

;;Only needeed for Axe.
(defthmd equal-of-cons-alt
  (implies (syntaxp (not (and (quotep x)
                              (quotep y))))
           (equal (equal z (cons x y))
                  (and (consp z)
                       (equal x (car z))
                       (equal y (cdr z))))))

;; Only needeed for Axe, since ACL2 knows this by type-prescription.
(defthmd true-listp-of-repeat
  (true-listp (repeat n x)))

;; Only needeed for Axe, since ACL2 knows this by type-prescription.
(defthmd true-listp-of-firstn
  (true-listp (firstn n x)))

;; Only needeed for Axe, since ACL2 knows this by type-prescription.
(defthmd true-listp-of-true-list-fix2
  (true-listp (true-list-fix x)))

;; Only needeed for Axe, since ACL2 knows this by type-prescription.
(defthmd equal-of-nil-and-len
  (not (equal nil (len x))))

;; Only needeed for Axe, since ACL2 knows this by type-prescription.
(defthmd consp-of-update-nth
  (consp (update-nth key val l)))

;; Only needeed for Axe, since ACL2 knows this by type-prescription.
(defthmd not-equal-of-nil-and-update-nth
  (not (equal nil (update-nth key val l))))

;; Only needeed for Axe, since ACL2 knows this by type-prescription.
(defthmd not-equal-of-update-nth-and-nil
  (not (equal (update-nth key val l) nil)))

;We also have equal-of-car-and-nth-of-0, so this variant is just for Axe.
;This helps when we don't want to commit to either form.
(defthmd equal-of-nth-of-0-and-car
  (equal (equal (nth 0 x) (car x))
         t))

(defthmd integerp-of-len
  (integerp (len x)))

(defthmd acl2-numberp-of-len
  (acl2-numberp (len x)))

;; could be used outside axe, but we have better rules for fix
;; deprecate: use fix-when-acl2-numberp and acl2-numberp-of-len
(defthmd fix-of-len
  (equal (fix (len x))
         (len x)))

(defthmd len-equal-impossible
  (implies (and (syntaxp (quotep k))
                (not (natp k)))
           (equal (equal k (len x))
                  nil)))

;rename
(defthmd len-non-negative
  (not (< (len x) 0)))

(defthmd booleanp-of-memberp
  (booleanp (memberp a x)))

(defthmd equal-of-append-arg1
  (equal (equal (append y z) x)
         (and (<= (len y) (len x))
              (equal (take (len y) x)
                     (true-list-fix y))
              (equal (nthcdr (len y) x) z)))
  :hints (("Goal" :use (:instance equal-of-append)
           :in-theory (disable equal-of-append))))

;; Only needed for Axe
(defthmd booleanp-of-items-have-len
  (booleanp (items-have-len n lst)))

;; Only needed for Axe
(defthmd booleanp-of-all-true-listp
  (booleanp (all-true-listp x)))

;; Permuted, for Axe only
(defthmd consp-when-len-equal-constant-alt
  (implies (and (equal free (len x))
                (syntaxp (quotep free)))
           (equal (consp x)
                  (< 0 free)))
  :hints (("Goal" :in-theory (enable len))))

;mostly for axe
(defthmd equal-of-cons-when-quotep
  (implies (syntaxp (quotep k))
           (equal (equal k (cons x y))
                  (and (consp k)
                       (equal x (car k))
                       (equal y (cdr k))))))

;or just turn equals around?
;only needed for axe
(defthmd equal-of-cons-when-quotep-alt
  (implies (syntaxp (quotep k))
           (equal (equal (cons x y) k)
                  (and (consp k)
                       (equal x (car k))
                       (equal y (cdr k))))))

;; We don't usually unroll NTH (preferring to turn it into BV-ARRAY-READ), but
;; we do when the list is a 2-D array, since we have no suppported operators for
;; 2-D arrays.
;; TODO: If N is a BVCAT term, we could split the list in half for each bit.
(defthmd nth-becomes-nth-to-unroll-for-2d-array
  (implies (and (syntaxp (quotep l))
                (true-list-listp l) ; not just an array of numbers
                (natp n)
                (< n (len l)))
           (equal (nth n l)
                  (nth-to-unroll n 0 (+ -1 (len l)) l)))
  :hints (("Goal" :use (:instance nth-becomes-nth-to-unroll-helper
                                  (low 0)
                                  (high (+ -1 (len l)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd prefixp-when-longer-work-hard
  (implies (work-hard (< (len x) (len y)))
           (equal (prefixp y x)
                  nil))
  :hints (("Goal" :in-theory (enable prefixp))))

(defthmd prefixp-when-not-shorter-work-hard
  (implies (work-hard (<= (len x) (len y)))
           (equal (prefixp y x)
                  (equal (true-list-fix x) (true-list-fix y))))
  :hints (("Goal" :in-theory (enable prefixp))))

(defthmd true-listp-subst-rule
  (implies (equal x (take free free2))
           (equal (true-listp x)
                  t)))

(defthmd true-listp-of-take
  (true-listp (take n x)))
