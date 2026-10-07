; Proof of correctness of get-conjuncts
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-conjuncts")
(include-book "kestrel/evaluators/if-eval" :dir :system)
(include-book "make-conjunction-from-list")

;; The conjuncts all evaluate to true exactly when TERM does.
(defthm all-eval-to-true-with-if-eval-of-get-conjuncts
  (iff (all-eval-to-true-with-if-eval (get-conjuncts term) a)
       (if-eval term a))
  :hints (("Goal" :in-theory (enable get-conjuncts))))

;; Conjoining the conjuncts gives back something equivalent to TERM.
(defthm if-eval-of-conjoin-of-get-conjuncts
  (iff (if-eval (conjoin (get-conjuncts term)) a)
       (if-eval term a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm if-eval-of-make-conjunction-from-list-of-append
   (implies (consp lst2)
            (equal (if-eval (make-conjunction-from-list (append lst1 lst2)) a)
                   (if (if-eval (make-conjunction-from-list lst1) a)
                       (if-eval (make-conjunction-from-list lst2) a)
                     nil)))
   :hints (("Goal" :in-theory (enable make-conjunction-from-list)))))

;; Here we have EQUAL, not just IFF, because make-conjunction-from-list doesn't
;; take liberties like CONJOIN does.
(defthm if-eval-of-make-conjunction-from-list-of-get-conjuncts
  (equal (if-eval (make-conjunction-from-list (get-conjuncts term)) a)
         (if-eval term a))
  :hints (("Goal" :in-theory (enable get-conjuncts make-conjunction-from-list))))
