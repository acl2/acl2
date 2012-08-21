; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

(in-package "ACL2")
(include-book "lite")

(qs-subset-mode t)

(encapsulate
 (((f *) => *))
 (local (defun f (x)
          (declare (ignore x))
          t))
 (defthm normp-of-f
   (normp (f x))))



(defthm test-q-and-macro-basic
  (implies (normp x)
           (and (equal (q-and) t)
                (equal (q-and x) x)))
  :rule-classes nil)

(defthm test-q-and-macro-lazy-2
  (implies (norm-listp (list x y))
           (and (equal (q-binary-and x y)     (q-ite-fn x y nil))
                (equal (q-and x y)            (q-binary-and x y))
                (equal (q-and (f x) y)        (q-binary-and (f x) y))
                (equal (q-and x (f y))        (q-binary-and x (f y)))
                (equal (q-and (f x) (f y))    (q-binary-and (f x) (f y)))))
  :rule-classes nil)

(defthm test-q-and-macro-lazy-3
  (implies (norm-listp (list x y z))
           (and (equal (q-and x y z)                (q-binary-and x (q-binary-and y z)))
                (equal (q-and (f x) y z)            (q-binary-and (f x) (q-binary-and y z)))
                (equal (q-and x (f y) z)            (q-binary-and x (q-binary-and (f y) z)))
                (equal (q-and x y (f z))            (q-binary-and x (q-binary-and y (f z))))
                (equal (q-and (f x) (f y) z)        (q-binary-and (f x) (q-binary-and (f y) z)))
                (equal (q-and x (f y) (f z))        (q-binary-and x (q-binary-and (f y) (f z))))
                (equal (q-and (f x) y (f z))        (q-binary-and (f x) (q-binary-and y (f z))))
                (equal (q-and (f x) (f y) (f z))    (q-binary-and (f x) (q-binary-and (f y) (f z))))))
  :rule-classes nil)





(defthm test-q-or-macro-basic
  (implies (normp x)
           (and (equal (q-or) nil)
                (equal (q-or x) x)))
  :rule-classes nil)

(defthm test-q-or-macro-lazy-2
  (implies (norm-listp (list x y))
           (and (equal (q-binary-or x y)     (q-ite-fn x t y))
                (equal (q-or x y)            (q-binary-or x y))
                (equal (q-or (f x) y)        (q-binary-or (f x) y))
                (equal (q-or x (f y))        (q-binary-or x (f y)))
                (equal (q-or (f x) (f y))    (q-binary-or (f x) (f y)))))
  :rule-classes nil)

(defthm test-q-or-macro-lazy-3
  (implies (norm-listp (list x y z))
           (and (equal (q-or x y z)                (q-binary-or x (q-binary-or y z)))
                (equal (q-or (f x) y z)            (q-binary-or (f x) (q-binary-or y z)))
                (equal (q-or x (f y) z)            (q-binary-or x (q-binary-or (f y) z)))
                (equal (q-or x y (f z))            (q-binary-or x (q-binary-or y (f z))))
                (equal (q-or (f x) (f y) z)        (q-binary-or (f x) (q-binary-or (f y) z)))
                (equal (q-or x (f y) (f z))        (q-binary-or x (q-binary-or (f y) (f z))))
                (equal (q-or (f x) y (f z))        (q-binary-or (f x) (q-binary-or y (f z))))
                (equal (q-or (f x) (f y) (f z))    (q-binary-or (f x) (q-binary-or (f y) (f z))))))
  :rule-classes nil)




(defthm test-q-implies-macro-lazy-2
  (implies (norm-listp (list x y))
           (and (equal (q-implies-fn x y)         (q-ite-fn x y t))
                (equal (q-implies x y)            (q-implies-fn x y))
                (equal (q-implies (f x) y)        (q-implies-fn (f x) y))
                (equal (q-implies x (f y))        (q-implies-fn x (f y)))
                (equal (q-implies (f x) (f y))    (q-implies-fn (f x) (f y)))))
  :rule-classes nil)

(defthm test-q-or-c2-macro-lazy-2
  (implies (norm-listp (list x y))
           (and (equal (q-or-c2-fn x y)         (q-ite-fn y x t))
                (equal (q-or-c2 x y)            (q-or-c2-fn x y))
                (equal (q-or-c2 (f x) y)        (q-or-c2-fn (f x) y))
                (equal (q-or-c2 x (f y))        (q-or-c2-fn x (f y)))
                (equal (q-or-c2 (f x) (f y))    (q-or-c2-fn (f x) (f y)))))
  :rule-classes nil)

(defthm test-q-and-c1-macro-lazy-2
  (implies (norm-listp (list x y))
           (and (equal (q-and-c1-fn x y)         (q-ite-fn (q-not x) y nil))
                (equal (q-and-c1 x y)            (q-and-c1-fn x y))
                (equal (q-and-c1 (f x) y)        (q-and-c1-fn (f x) y))
                (equal (q-and-c1 x (f y))        (q-and-c1-fn x (f y)))
                (equal (q-and-c1 (f x) (f y))    (q-and-c1-fn (f x) (f y)))))
  :rule-classes nil)

(defthm test-q-and-c2-macro-lazy-2
  (implies (norm-listp (list x y))
           (and (equal (q-and-c2-fn x y)         (q-ite-fn x (q-not y) nil))
                (equal (q-and-c2 x y)            (q-and-c2-fn x y))
                (equal (q-and-c2 (f x) y)        (q-and-c2-fn (f x) y))
                (equal (q-and-c2 x (f y))        (q-and-c2-fn x (f y)))
                (equal (q-and-c2 (f x) (f y))    (q-and-c2-fn (f x) (f y)))))
  :rule-classes nil)




(defthm test-q-iff-macro-lazy-2
  (implies (norm-listp (list x y))
           (and (equal (q-binary-iff x y)        (q-binary-and (q-implies-fn x y)
                                                               (q-implies-fn y x)))
                (equal (q-iff x y)               (q-binary-iff x y))
                (equal (q-iff (f x) y)           (q-binary-iff (f x) y))
                (equal (q-iff x (f y))           (q-binary-iff x (f y)))
                (equal (q-iff (f x) (f y))       (q-binary-iff (f x) (f y)))))
  :rule-classes nil)

(defthm test-q-iff-macro-lazy-3
  (implies (norm-listp (list x y z))
           (and (equal (q-iff x y z)                (q-binary-and (q-binary-iff x y)
                                                                  (q-binary-iff x z)))
                (equal (q-iff (f x) y z)            (q-binary-and (q-binary-iff (f x) y)
                                                                  (q-binary-iff (f x) z)))
                (equal (q-iff x (f y) z)            (q-binary-and (q-binary-iff x (f y))
                                                                  (q-binary-iff x z)))
                (equal (q-iff x y (f z))            (q-binary-and (q-binary-iff x y)
                                                                  (q-binary-iff x (f z))))
                (equal (q-iff (f x) (f y) z)        (q-binary-and (q-binary-iff (f x) (f y))
                                                                  (q-binary-iff (f x) z)))
                (equal (q-iff x (f y) (f z))        (q-binary-and (q-binary-iff x (f y))
                                                                  (q-binary-iff x (f z))))
                (equal (q-iff (f x) y (f z))        (q-binary-and (q-binary-iff (f x) y)
                                                                  (q-binary-iff (f x) (f z))))
                (equal (q-iff (f x) (f y) (f z))    (q-binary-and (q-binary-iff (f x) (f y))
                                                                  (q-binary-iff (f x) (f z))))))
  :rule-classes nil)



(defthm test-q-xor-macro-2
  (implies (norm-listp (list x y z))
           (and (equal (q-binary-xor x y)   (q-ite-fn x
                                                      (q-ite-fn y nil t)
                                                      (q-ite-fn y t nil)))
                (equal (q-xor (f x) y)    (q-binary-xor (f x) y))
                (equal (q-xor x (f y))    (q-binary-xor x (f y)))))
  :rule-classes nil)

(defthm test-q-xor-macro-3
  (implies (norm-listp (list x y z))
           (and (equal (q-xor x y z)                (q-binary-xor x (q-binary-xor y z)))
                (equal (q-xor (f x) y z)            (q-binary-xor (f x) (q-binary-xor y z)))
                (equal (q-xor x (f y) z)            (q-binary-xor x (q-binary-xor (f y) z)))
                (equal (q-xor x y (f z))            (q-binary-xor x (q-binary-xor y (f z))))
                (equal (q-xor (f x) (f y) z)        (q-binary-xor (f x) (q-binary-xor (f y) z)))
                (equal (q-xor x (f y) (f z))        (q-binary-xor x (q-binary-xor (f y) (f z))))
                (equal (q-xor (f x) y (f z))        (q-binary-xor (f x) (q-binary-xor y (f z))))
                (equal (q-xor (f x) (f y) (f z))    (q-binary-xor (f x) (q-binary-xor (f y) (f z))))))
  :rule-classes nil)
