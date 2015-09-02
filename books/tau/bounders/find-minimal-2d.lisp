; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore, December 20, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Toy: Finding the Minimal Value of a Function over a Pair of Integer Intervals

; To recertify:
; (certify-book "find-minimal-2d")

; Abstract:  This is like find-minimal-1d.lisp except it deals with a
; dyadic function over pairs of integers,

; FMLA : integerp x integerp --> integerp.

; We wish to minimize (fmla x y), where lox <= x <= hix and loy <= y <= hiy.

(in-package "ACL2")

(encapsulate ((fmla (x y) t))
             (local (defun fmla (x y) (* x y)))
             (defthm integerp-fmla
               (implies (and (integerp x)
                             (integerp y))
                        (integerp (fmla x y)))
               :rule-classes :type-prescription))

; Find-minimal initializes the accumulator to nil and calls find-minimal1.
; Find-minimal1 calls find-minimal2 for each x between lox and hix,
; accumulating the results.  Find-minimal2 takes a given x and maps y from loy
; to hiy and for each y accumulates (minimizes wrt min) the values of (fmla x
; y).

(defun find-minimal2 (x loy hiy min)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hiy)) (ifix loy)))))
  (cond
   ((not (and (integerp loy)
              (integerp hiy)))
    min)
   ((> loy hiy) min)
   (t (find-minimal2
       x
       (+ 1 loy) hiy
       (if (or (null min)
               (< (fmla x loy) min))
           (fmla x loy)
           min)))))

(defun find-minimal1 (lox hix loy hiy min)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hix)) (ifix lox)))))
  (cond
   ((not (and (integerp lox)
              (integerp hix)))
    min)
   ((> lox hix) min)
   (t (find-minimal1
       (+ 1 lox) hix
       loy hiy
       (find-minimal2 lox loy hiy min)))))

; This is the wrapper that initializes the running minimal, min, to nil.  But
; all our lemmas except the last will be about the two recursive functions
; above.

(defun find-minimal (lox hix loy hiy)
  (find-minimal1 lox hix loy hiy nil))

(defthm find-minimal2-decreases
  (implies (and min
                (integerp x))
           (<= (find-minimal2 x loy hiy min) min))
  :rule-classes :linear)

(defthm integerp-find-minimal2
  (implies (and (integerp x)
                (integerp loy)
                (integerp hiy)
                (or (null min) (integerp min)))
           (equal (integerp (find-minimal2 x loy hiy min))
                  (if (null min)
                      (<= loy hiy)
                      t))))

; Unlike the 1d case, in the 2d case the accumulator can take on the value not
; just nil or the integer value of the formula but the value of find-minimal2.
; So we must show it is generally non-nil too.

(defthm non-nil-find-minimal2
  (implies (and (integerp x)
                (integerp loy)
                (integerp hiy))
           (iff (find-minimal2 x loy hiy min)
                (or min (<= loy hiy)))))

(defthm find-minimal1-decreases
  (implies (and min
                (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy))
           (<= (find-minimal1 lox hix loy hiy min) min))
  :rule-classes :linear)

(defthm integerp-find-minimal1
  (implies (and (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy)
                (or (null min) (integerp min)))
           (equal (integerp (find-minimal1 lox hix loy hiy min))
                  (if (null min)
                      (and (<= lox hix)
                           (<= loy hiy))
                      t))))

(defun below-all2 (min x loy hiy)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hiy)) (ifix loy)))))
  (cond
   ((not (and (integerp loy)
              (integerp hiy)))
    t)
   ((> loy hiy) t)
   ((<= min (fmla x loy))
    (below-all2 min x (+ 1 loy) hiy))
   (t nil)))

(defun below-all1 (min lox hix loy hiy)
  (declare (xargs :measure (nfix (- (+ 1 (ifix hix)) (ifix lox)))))
  (cond
   ((not (and (integerp lox)
              (integerp hix)))
    t)
   ((> lox hix) t)
   ((below-all2 min lox loy hiy)
    (below-all1 min (+ 1 lox) hix loy hiy))
   (t nil)))

(defthm below-all2-find-minimal2
  (implies (and (integerp x)
                (integerp loy)
                (integerp hiy)
                (or (null xxx) (integerp xxx)))
           (below-all2 (find-minimal2 x loy hiy xxx) x loy hiy)))

; This is a lemma not found in the 1D case...

(defthm below-all2-trans
  (implies (and (<= min1 min2)
                (below-all2 min2 x loy hiy))
           (below-all2 min1 x loy hiy))
  :rule-classes nil)

; The lemma above contains the free variable min2 and there is no good way to
; choose it, that is, instances of neither of the hypotheses above appear in
; the subgoal below to which the lemma applies.  The lemma must be applied in
; Subgoal *1/2 of the theorem below.  The lemma's first hypothesis will be
; established the theorem find-minimal1-decreases above.  The lemma's second
; hypothesis will be established by below-all2-find-minimal2.  Since both
; hypotheses are established by lemmas and contain the free variable, I could
; see no more elegant way to proceed than to use an explicit hint, below, to
; use the desired instance of below-all2-trans.

(defthm below-all1-find-minimal1
  (implies (and (integerp lox)
                (integerp hix)
                (integerp loy)
                (integerp hiy)
                (or (null xxx) (integerp xxx)))
           (below-all1 (find-minimal1 lox hix loy hiy xxx) lox hix loy hiy))
  :hints (("Goal" :induct (find-minimal1 lox hix loy hiy xxx))
          ("Subgoal *1/2"
           :use
           ((:instance below-all2-trans
                       (x LOX)
                       (min1 (FIND-MINIMAL1 (+ 1 LOX)
                                            HIX
                                            LOY HIY
                                            (FIND-MINIMAL2 LOX LOY HIY XXX)))
                       (min2 (FIND-MINIMAL2 LOX LOY HIY XXX)))))))

(defthm below-all2-is-a-universal-quantifier
  (implies (and (below-all2 min x loy hiy)
                (integerp x)
                (integerp loy)
                (integerp hiy)
                (integerp y)
                (<= loy y)
                (<= y hiy))
           (<= min (fmla x y)))
  :rule-classes :linear)

(defthm below-all1-is-a-universal-quantifier
  (implies (and (below-all1 min lox hix loy hiy)
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
           (<= min (fmla x y)))
  :rule-classes nil)

; Again, note that we have free-variables above, and the hypothesis containing
; them will be established by a lemma when the theorem above is applied.
; Therefore, I make the theorem above rule-classes nil and :use it explicitly
; in the proof below.

(defthm find-minimal-correct
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
           (and
            (integerp (find-minimal lox hix loy hiy))
            (<= (find-minimal lox hix loy hiy)
                (fmla x y))))

  :hints (("Goal" :use (:instance below-all1-is-a-universal-quantifier
                                  (min (find-minimal lox hix loy hiy)))))
  :rule-classes nil)






