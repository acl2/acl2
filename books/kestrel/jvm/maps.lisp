; More rules about maps
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/maps/maps" :dir :system)

;; TODO: Move this stuff to ../maps/.

;move
(defthm s-nil-becomes-clr
  (equal (s a nil r)
         (clr a r))
  :hints (("Goal" :in-theory (e/d (clr) (s==r)))))

(theory-invariant (incompatible (:rewrite s-nil-becomes-clr) (:definition clr)))

(defthm rkeys-of-clr
  (equal (rkeys (clr key r))
         (set::delete key (rkeys r)))
  :hints (("Goal"  :DO-NOT '(preprocess)
           :in-theory (e/d (clr) (S-NIL-BECOMES-CLR ;looped
                                  s==r
                                  )))))

(in-theory (disable key-list)) ;fixme move up

;bozo expensive?
;use iff?
(defthm not-clr-when-not-s
  (implies (not (s a val r))
           (not (clr a r)))
  :hints (("Goal" ;:do-not-preprocess
           :cases (val)
           :in-theory (e/d (clr) (s==r s-nil-becomes-clr)))))

;move
(defthm s-iff
  (iff (s a v r)
       (or v (clr a r))))

;if a is nil, it could be made into a clr
(defthm equal-of-nil-of-s-and-s
  (implies (and v2
                (not (equal a a2)))
           (equal (equal nil (s a v (s a2 v2 r)))
                  nil)))

(defthm clr-non-nil-when-g-of-some-other-address-is-non-nil
  (implies (and (equal (g a1 val) value)
                value ;is not nil
                (not (equal a1 a2)))
           (clr a2 val))
  :hints (("Goal" :in-theory (disable G-OF-CLR)
           :use (:instance G-OF-CLR (R  val) (A2  A2) (A1  A1)))))
