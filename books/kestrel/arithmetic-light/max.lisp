; A lightweight book about the built-in function max.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable max))

(defthm max-commutative
  (implies (and (acl2-numberp x) ; note that (max t 0) <> (max 0 t)
                (acl2-numberp y))
           (equal (max x y)
                  (max y x)))
  :hints (("Goal"
           :cases ((acl2-numberp x))
           :in-theory (enable max))))

;; Consider what MAX-COMMUTATIVE would do to the RHS of len-update-nth
;; before MAX is opened.  It can make the resulting IF harder to resolve.
(theory-invariant (incompatible (:rewrite max-commutative) (:definition max))
                  :error nil
                  :key consider-disabling-max-commutative-when-max-is-enabled)

(defthm max-associative
  (equal (max (max x y) z)
         (max x (max y z)))
  :hints (("Goal" :in-theory (enable max))))

(defthm max-commutative-2
  (implies (and (acl2-numberp x) ; note that (max t 0) <> (max 0 t)
                (acl2-numberp y))
           (equal (max x (max y z))
                  (max y (max x z))))
  :hints (("Goal" :in-theory (enable max))))

(defthm max-same
  (equal (max x x)
         x)
  :hints (("Goal" :in-theory (enable max))))

(defthm max-same-2
  (equal (max x (max x y))
         (max x y))
  :hints (("Goal" :in-theory (enable max))))

(defthmd max-when-<=-1
  (implies (<= x y)
           (equal (max x y)
                  y))
  :hints (("Goal" :in-theory (enable max))))

(defthmd max-when-<=-2
  (implies (and (<= y x)
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (max x y)
                  x))
  :hints (("Goal" :in-theory (enable max))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm <-of-max-arg1
  (equal (< (max x y) z)
         (and (< x z)
              (< y z)))
  :hints (("Goal" :in-theory (enable max))))

;; In case we disable <-of-max-arg1
(defthm not-<-of-max-when-<-arg1-arg1
  (implies (<= z x)
           (not (< (max x y) z))))

;; In case we disable <-of-max-arg1
(defthm not-<-of-max-when-<-arg1-arg2
  (implies (<= z y)
           (not (< (max x y) z))))

;; In case we disable <-of-max-arg1
(defthm not-<-of-max-same-arg1-arg1
  (not (< (max x y) x))
  :hints (("Goal" :in-theory (enable max))))

;; In case we disable <-of-max-arg1
(defthm not-<-of-max-same-arg1-arg2
  (not (< (max x y) y))
  :hints (("Goal" :in-theory (enable max))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm <-of-max-arg2
  (equal (< z (max x y))
         (or (< z x)
             (< z y)))
  :hints (("Goal" :in-theory (enable max))))

;; In case we disable <-of-max-arg2
(defthm <-of-max-when-<-arg1
  (implies (< z x)
           (< z (max x y))))

;; In case we disable <-of-max-arg2
(defthm <-of-max-when-<-arg2
  (implies (< z y)
           (< z (max x y))))

;; In case we disable <-of-max-arg2
(defthm <-of-max-same-arg2-arg1
  (equal (< x (max x y))
         (< x y))
  :hints (("Goal" :in-theory (enable max))))

;; In case we disable <-of-max-arg2
(defthm <-of-max-same-arg2-arg2
  (equal (< y (max x y))
         (< y x))
  :hints (("Goal" :in-theory (enable max))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm acl2-numberp-of-max
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (acl2-numberp (max x y))))

(defthm acl2-numberp-of-max-when-<-of-0
  (implies (< 0 x)
           (acl2-numberp (max x y)))
  :hints (("Goal" :in-theory (enable max))))

(defthm integerp-of-max
  (implies (and (integerp x)
                (integerp y))
           (integerp (max x y))))

(defthm equal-of-max-same-arg1
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (equal x (max x y))
                  (<= y x)))
  :hints (("Goal" :in-theory (enable max))))

(defthm equal-of-max-same-arg2
  (equal (equal y (max x y))
         (<= x y))
  :hints (("Goal" :in-theory (enable max))))


(defthm <=-of-max-same-arg1-linear
  (<= x (max x y))
  :rule-classes :linear)

(defthm <=-of-max-same-arg2-linear
  (<= y (max x y))
  :rule-classes :linear)
