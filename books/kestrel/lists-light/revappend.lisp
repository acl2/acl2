; A lightweight book about the built-in function revappend.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that it may be helpful, instead of reasoning about revappend, to get
;; rid of it in favor of rev or reverse-list.

(local (include-book "append"))
(local (include-book "butlast"))
(local (include-book "true-list-fix"))
(local (include-book "take"))

(in-theory (disable revappend))

(defthm car-of-revappend
  (equal (car (revappend x y))
         (if (consp x)
             (car (last x))
           (car y)))
  :hints (("Goal" :in-theory (enable revappend))))

(defthm consp-of-revappend
  (equal (consp (revappend x y))
         (or (consp x)
             (consp y)))
  :hints (("Goal" :in-theory (enable revappend))))

(defthm revappend-iff
  (iff (revappend x y)
       (or (consp x)
           y))
  :hints (("Goal" :in-theory (enable revappend))))

(defthm revappend-of-append-arg2
  (equal (revappend x (append acc y))
         (append (revappend x acc) y))
  :hints (("Goal" :in-theory (enable revappend append))))

;makes the acc nil
(defthmd revappend-normalize-acc
  (implies (syntaxp (not (equal y *nil*)))
           (equal (revappend x y)
                  (append (revappend x nil) y)))
  :hints (("Goal" :use (:instance revappend-of-append-arg2 (acc nil))
           :in-theory (disable revappend-of-append-arg2))))

(defthm revappend-of-append-arg1
  (equal (revappend (append x y) z)
         (append (revappend y nil)
                 (revappend x z)))
  :hints (("subgoal *1/1" :in-theory (enable revappend revappend-normalize-acc))
          ("Goal" :induct (revappend x z)
           :in-theory (enable revappend ;revappend-normalize-acc
                              ))))

(defthm true-list-fix-of-revappend
  (equal (true-list-fix (revappend x y))
         (revappend x (true-list-fix y)))
  :hints (("Goal" :in-theory (enable true-list-fix revappend))))

(defthm true-listp-of-revappend
  (equal (true-listp (revappend x y))
         (true-listp y))
  :hints (("Goal" :in-theory (enable revappend))))

;matches the version in books/std/lists/revappend.lisp
(defthm len-of-revappend
  (equal (len (revappend x y))
         (+ (len x) (len y)))
  :hints (("Goal" :in-theory (enable revappend))))

(defthm revappend-of-nil-arg1
  (equal (revappend nil acc)
         acc)
  :hints (("Goal" :in-theory (enable revappend))))

(defthm revappend-of-singleton-arg1
  (equal (revappend (list a) acc)
         (cons a acc))
  :hints (("Goal" :in-theory (enable revappend))))

(defthm revappend-of-cons
  (equal (revappend (cons a x) acc)
         (append (revappend x nil)
                 (list a)
                 acc))
  :hints (("Goal" :use (:instance revappend-of-append-arg1 (x (list a)) (y x) (z acc))
           :in-theory (disable revappend-of-append-arg1))))

(defthm revappend-of-revappend
  (equal (revappend (revappend x nil) nil)
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm revappend-of-true-list-fix-arg1
  (equal (revappend (true-list-fix x) y)
         (revappend x y))
  :hints (("Goal" :expand (revappend (true-list-fix x) y)
           :in-theory (e/d (revappend) (true-list-fix)))))

(defthm cdr-of-revappend
  (equal (cdr (revappend x y))
         (if (consp x)
             (revappend (butlast x 1) y)
           (cdr y)))
  :hints (("Goal" :in-theory (enable revappend butlast))))
