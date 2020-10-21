; A lightweight book about the built-in function cons.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The syntaxp hyp means this rule does not fire if (cons x y) is a constant
;; (ACL2 can match (cons x y) with a quoted constant!).
(defthm equal-of-cons
  (implies (syntaxp (not (and (quotep x)
                              (quotep y))))
           (equal (equal (cons x y) z)
                  (and (consp z)
                       (equal x (car z))
                       (equal y (cdr z))))))

(defthm equal-of-cons-and-cons
  (equal (equal (cons a x) (cons b y))
         (and (equal a b) (equal x y))))

;; Param names changed to match std
(defthm true-listp-of-cons
  (equal (true-listp (cons a x))
         (true-listp x))
  :hints (("Goal" :cases ((true-listp x)))))
