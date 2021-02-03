; A lightweight book about the built-in operations + and -.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that DISTRIBUTIVITY-OF-MINUS-OVER-+ and INVERSE-OF-+ are built in to
;; ACL2.

(defthm +-of-+-of---same
  (equal (+ x (- x) y)
         (fix y)))

(defthm equal-of-0-and-+-of--
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (equal 0 (+ x (- y)))
                  (equal x y))))

(defthm equal-of-0-and-+-of---alt
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (equal 0 (+ (- y) x))
                  (equal x y))))

(defthm <-of-+-of---and-0-arg2
  (equal (< (+ x (- y)) 0)
         (< x y))
  :hints (("Goal" :cases ((< x y)))))

(defthm <-of-+-of---and-0-arg1
  (equal (< (+ (- x) y) 0)
         (< y x))
  :hints (("Goal" :cases ((< y x)))))
