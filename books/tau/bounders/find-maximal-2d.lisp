; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore, December 20, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Toy: Finding the Maximal Value of a Function over a Pair of Integer Intervals

; To recertify:
; (certify-book "find-maximal-2d")

; Abstract:  Given

; FMLA : integerp x integerp --> integerp.

; maximize (fmla x y), where lox <= x <= hix and loy <= y <= hiy.  See
; find-minimal-2d.lisp for the original development.

(in-package "ACL2")

(encapsulate ((fmla (x y) t))
             (local (defun fmla (x y) (* x y)))
             (defthm integerp-fmla
               (implies (and (integerp x)
                             (integerp y))
                        (integerp (fmla x y)))
               :rule-classes :type-prescription))

(defun find-maximal2 (x loy hiy max)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hiy)) (ifix loy)))))
  (cond
   ((not (and (integerp loy)
              (integerp hiy)))
    max)
   ((> loy hiy) max)
   (t (find-maximal2
       x
       (+ 1 loy) hiy
       (if (or (null max)
               (> (fmla x loy) max))
           (fmla x loy)
           max)))))

(defun find-maximal1 (lox hix loy hiy max)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hix)) (ifix lox)))))
  (cond
   ((not (and (integerp lox)
              (integerp hix)))
    max)
   ((> lox hix) max)
   (t (find-maximal1
       (+ 1 lox) hix
       loy hiy
       (find-maximal2 lox loy hiy max)))))

(defun find-maximal (lox hix loy hiy)
  (find-maximal1 lox hix loy hiy nil))

(defthm find-maximal2-increases
  (implies (and max
                (integerp x))
           (>= (find-maximal2 x loy hiy max) max))
  :rule-classes :linear)

(defthm integerp-find-maximal2
  (implies (and (integerp x)
                (integerp loy)
                (integerp hiy)
                (or (null max) (integerp max)))
           (equal (integerp (find-maximal2 x loy hiy max))
                  (if (null max)
                      (<= loy hiy)
                      t))))

(defthm non-nil-find-maximal2
  (implies (and (integerp x)
                (integerp loy)
                (integerp hiy))
           (iff (find-maximal2 x loy hiy max)
                (or max (<= loy hiy)))))

(defthm find-maximal1-increases
  (implies (and max
                (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy))
           (>= (find-maximal1 lox hix loy hiy max) max))
  :rule-classes :linear)

(defthm integerp-find-maximal1
  (implies (and (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy)
                (or (null max) (integerp max)))
           (equal (integerp (find-maximal1 lox hix loy hiy max))
                  (if (null max)
                      (and (<= lox hix)
                           (<= loy hiy))
                      t))))

(defun above-all2 (max x loy hiy)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hiy)) (ifix loy)))))
  (cond
   ((not (and (integerp loy)
              (integerp hiy)))
    t)
   ((> loy hiy) t)
   ((>= max (fmla x loy))
    (above-all2 max x (+ 1 loy) hiy))
   (t nil)))

(defun above-all1 (max lox hix loy hiy)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hix)) (ifix lox)))))
  (cond
   ((not (and (integerp lox)
              (integerp hix)))
    t)
   ((> lox hix) t)
   ((above-all2 max lox loy hiy)
    (above-all1 max (+ 1 lox) hix loy hiy))
   (t nil)))

(defthm above-all2-find-maximal2
  (implies (and (integerp x)
                (integerp loy)
                (integerp hiy)
                (or (null xxx) (integerp xxx)))
           (above-all2 (find-maximal2 x loy hiy xxx) x loy hiy)))

; This is a lemma not found in the 1D case...

(defthm above-all2-trans
  (implies (and (>= max1 max2)
                (above-all2 max2 x loy hiy))
           (above-all2 max1 x loy hiy))
  :rule-classes nil)

(defthm above-all1-find-maximal1
  (implies (and (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy)
                (or (null xxx) (integerp xxx)))
           (above-all1 (find-maximal1 lox hix loy hiy xxx) lox hix loy hiy))
  :hints (("Goal" :induct (find-maximal1 lox hix loy hiy xxx))
          ("Subgoal *1/2"
           :use
           ((:instance above-all2-trans
                       (x LOX)
                       (max1 (FIND-MAXIMAL1 (+ 1 LOX)
                                            HIX
                                            LOY HIY
                                            (FIND-MAXIMAL2 LOX LOY HIY XXX)))
                       (max2 (FIND-MAXIMAL2 LOX LOY HIY XXX)))))))

(defthm above-all2-is-a-universal-quantifier
  (implies (and (above-all2 max x loy hiy)
                (integerp x)
                (integerp loy)
                (integerp hiy)
                (integerp y)
                (<= loy y)
                (<= y hiy))
           (>= max (fmla x y)))
  :rule-classes :linear)

(defthm above-all1-is-a-universal-quantifier
  (implies (and (above-all1 max lox hix loy hiy)
                (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy)
                (integerp x)
                (<= lox x)
                (<= x hix)
                (integerp y)
                (<= loy y)
                (<= y hiy))
           (>= max (fmla x y)))
  :rule-classes nil)

(defthm find-maximal-correct
  (implies (and (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy)
                (integerp x)
                (<= lox x)
                (<= x hix)
                (integerp y)
                (<= loy y)
                (<= y hiy))
           (and (integerp (find-maximal lox hix loy hiy))
                (>= (find-maximal lox hix loy hiy)
                    (fmla x y))))
  :hints (("Goal" :use (:instance above-all1-is-a-universal-quantifier
                                  (max (find-maximal lox hix loy hiy)))))
  :rule-classes nil)






