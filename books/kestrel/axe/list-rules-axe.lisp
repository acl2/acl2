; Axe rules about lists
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

(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/lists-light/memberp-def" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;;Only needeed for Axe.
(defthm equal-of-cons-alt
  (implies (syntaxp (not (and (quotep x)
                              (quotep y))))
           (equal (equal z (cons x y))
                  (and (consp z)
                       (equal x (car z))
                       (equal y (cdr z))))))

(defthm true-listp-of-repeat
  (true-listp (repeat n x)))

;only useful for Axe since ACL2 knows this by types
(defthmd equal-of-nil-and-len
  (equal (equal nil (len x))
         nil))

;We also have equal-of-car-and-nth-of-0, so this variant is just for Axe.
;This helps when we don't want to commit to either form.
(defthmd equal-of-nth-of-0-and-car
  (equal (equal (nth 0 x) (car x))
         t))

;only needed by axe since ACL2 knows this by type reasoning
(defthm consp-of-update-nth
  (consp (update-nth key val l)))

(defthm integerp-of-len
  (integerp (len x)))

;rename
(defthm len-non-negative
  (not (< (len x) 0)))

(defthm booleanp-of-memberp
  (booleanp (memberp a x)))

(defthm member-equal-of-nil
  (equal (member-equal a nil)
         nil))

(defthm equal-of-append-arg1
  (equal (equal (append y z) x)
         (and (<= (len y) (len x))
              (equal (take (len y) x)
                     (true-list-fix y))
              (equal (nthcdr (len y) x) z)))
  :hints (("Goal" :use (:instance equal-of-append)
           :in-theory (disable equal-of-append))))

(def-constant-opener memberp)

;; Only needed for Axe
(defthm booleanp-of-items-have-len
  (booleanp (items-have-len n lst)))

;; Only needed for Axe
(defthm booleanp-of-all-true-listp
  (booleanp (all-true-listp x)))

;; Permuted, for Axe only
(defthmd consp-when-len-equal-constant-alt
  (implies (and (equal free (len x))
                (syntaxp (quotep free)))
           (equal (consp x)
                  (< 0 free)))
  :hints (("Goal" :in-theory (e/d (len) ()))))

;mostly for axe
(defthmd acl2::equal-of-cons-when-quotep
  (implies (syntaxp (quotep k))
           (equal (equal k (cons x y))
                  (and (consp k)
                       (equal x (car k))
                       (equal y (cdr k))))))

;or just turn equals around?
;only needed for axe
(defthmd acl2::equal-of-cons-when-quotep-alt
  (implies (syntaxp (quotep k))
           (equal (equal (cons x y) k)
                  (and (consp k)
                       (equal x (car k))
                       (equal y (cdr k))))))
