; A lightweight book about the built-in operation /.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "times"))
(local (include-book "../library-wrappers/arithmetic-inequalities"))

;; Exported in times-and-divides.lisp
(local
 (defthm *-of-/-same
   (equal (* x (/ x))
          (if (equal 0 (fix x))
              0
            1))))

(defthm /-of-/
  (equal (/ (/ x))
         (fix x)))

(defthm equal-of-/-constant
  (implies (syntaxp (quotep k))
           (equal (equal k (/ x))
                  (and (acl2-numberp k)
                       (equal (fix x) (/ k))))))

(defthm <-of-/-and-constant-1
  (implies (and (syntaxp (quotep k))
                (< 0 k)
                (rationalp k)
                (rationalp y))
           (equal (< k (/ y))
                  (and (not (<= y 0))
                       (< y (/ k)))))
  :hints (("Goal" :cases ((< y 0)
                          (equal y 0)
                          (< k (/ y)))
           :in-theory (disable <-of-*-and-*-cancel)
           :use (:instance <-of-*-and-*-cancel
                           (x1 k)
                           (x2 (/ y))
                           (y y)))))

(defthm <-of-/-and-constant-2
  (implies (and (syntaxp (quotep k))
                (< 0 k)
                (rationalp k)
                (rationalp y))
           (equal (< (/ y) k)
                  (or (<= y 0)
                      (< (/ k) y))))
  :hints (("Goal" :cases ((< y 0)
                          (equal y 0)
                          (< (/ y) k)))))

(defthm <-of-/
  (implies (rationalp x)
           (equal (< 0 (/ x))
                  (< 0 x)))
  :hints (("Goal" :cases ((equal x 0)
                          (< 0 x))
           :in-theory (disable <-of-*-and-*-cancel)
           :use (:instance <-of-*-and-*-cancel
                           (x1 0)
                           (x2 (/ x))
                           (y (- x))))))


    ;gen
(defthm <-of-/-and-/
  (implies (and (< 0 x)
                (< 0 y)
                (rationalp x)
                (rationalp y))
           (equal (< (/ x) (/ y))
                  (< y x)))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (x1 (/ y))
                                  (x2 (/ X))
                                  (y (* x y)))
           :in-theory (disable <-of-*-and-*-cancel))))

(defthm <=-of-/-linear
  (implies (and (<= x0 x)
                (< 0 x)
                (< 0 x0)
                (rationalp x)
                (rationalp x0))
           (<= (/ x) (/ x0)))
  :rule-classes :linear)
