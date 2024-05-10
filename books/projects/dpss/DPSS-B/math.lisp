;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "util")

(local (include-book "arithmetic-5/top" :dir :system))

;; (defthm rationalp-rfix
;;   (rationalp (rfix x))
;;   :rule-classes :type-prescription)

;; (defthm rfix-rationalp
;;   (implies
;;    (rationalp x)
;;    (equal (rfix x) x))
;;   :hints (("Goal" :in-theory (enable rfix))))

;; (defthm rfix-rfix
;;   (equal (rfix (rfix x))
;;          (rfix x))
;;   :hints (("Goal" :in-theory (enable rfix))))

;; (in-theory (disable rfix))

(defun merge-1 (x a)
  (if (not (consp a)) (list x)
    (if (equal x (car a)) a
      (cons (car a) (merge-1 x (cdr a))))))

(defun merge-2 (a b)
  (if (not (consp a)) b
    (merge-2 (cdr a) (merge-1 (car a) b))))

(defun find-recips (expr)
  (case-match expr
    ((`binary-+ x y)
     (merge-2 (find-recips x)
              (find-recips y)))
    ((`binary-* x y)
     (merge-2 (find-recips x)
              (find-recips y)))
    ((`unary-/ x) (list x))
    ((`quote r) (let ((d (denominator r)))
                  (if (equal d 1) nil (list `(quote ,d)))))
    (& nil)))

(defun choose-recip (exprs)
  (if (not (consp exprs)) nil
    (acons 'x (car exprs) nil)))

(defthmd remove-reciporicals-<
  (implies
   (and
    (bind-free (choose-recip (merge-2 (find-recips a) (find-recips b))) (x))
    (rationalp x)
    (not (equal x 0))
    (equal c (double-rewrite (* x a)))
    (equal d (double-rewrite (* x b))))
   (equal (< a b)
          (if (< 0 x) (< c d) (< d c)))))

(defthmd remove-reciporicals-=
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (bind-free (choose-recip (merge-2 (find-recips a) (find-recips b))) (x))
    (rationalp x)
    (not (equal x 0))
    (equal c (double-rewrite (* x a)))
    (equal d (double-rewrite (* x b))))
   (iff (equal a b)
        (equal c d))))
