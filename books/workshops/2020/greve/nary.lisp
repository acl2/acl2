;;
;; Copyright (C) 2020, David Greve
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
;;
(in-package "ACL2")

(include-book "coi/nary/nary-mod" :dir :system)
(local (include-book "coi/util/rewrite-equiv" :dir :system))

(defun mod-ctx (x a)
  (mod x a))

(in-theory (disable mod))

(encapsulate
    ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm mod-mod
    (equal (mod (mod x n) n)
           (mod x n)))

  (defthm mod-zp
    (equal (mod 0 n) 0))
  
  )
  
(local (in-theory (enable nary::mod-rules)))

(def::context (mod-ctx x a)
  :hyps (and (integerp x)
             (integerp a)))

(defthm mod-ctx-mod-ctx
  (equal (mod-ctx (mod-ctx x a) a)
         (mod-ctx x a)))

(defthm mod-n-of-mod-n-reduction
  (equal (mod-ctx (mod x n) n)
         (mod-ctx x n)))

(defthmd mod-mod-congruence
  (implies
   (and
    (integerp x)
    (integerp n)
    (nary::bind-context
     (equal a (mod-ctx x n))))
   (equal (mod x n)
          (mod a n))))

(defthmd mod-+-congruence
  (implies
   (and
    (integerp a)
    (integerp b)
    (integerp n)
    (nary::bind-context
     (equal x (mod-ctx a n))
     (equal y (mod-ctx b n))))
   (equal (mod-ctx (+ a b) n)
          (mod-ctx (+ x y) n)))
  :hints ((rewrite-equiv-hint)))

(defthmd mod-*-congruence
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp n)
    (nary::bind-context
     (equal a (mod-ctx x n))
     (equal b (mod-ctx y n))))
   (equal (mod-ctx (* x y) n)
          (mod-ctx (* a b) n))))

(defthmd mod---congruence
  (implies
   (and
    (integerp x)
    (integerp n)
    (nary::bind-context
     (equal a (mod-ctx x n))))
   (equal (mod-ctx (- x) n)
          (mod-ctx (- a) n))))

(defthmd mod-n-of-n-reduction
  (equal (mod-ctx n n)
         (mod-ctx 0 n)))

(in-theory (disable mod-ctx))

(in-theory
 (enable
  mod-n-of-mod-n-reduction
  mod-n-of-n-reduction
  mod---congruence
  mod-+-congruence
  mod-*-congruence
  ))
