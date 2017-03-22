; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book supports Section 2.1.1 of the paper
; "Meta-extract: Using Existing Facts in Meta-reasoning"
; by Matt Kaufmann and Sol Swords.

(in-package "ACL2")

(defevaluator nthmeta-ev nthmeta-ev-lst
  ((typespec-check ts x)
   (nth n x)
   (car x)))

(defun nth-symbolp-metafn (term mfc state)
  (declare (xargs :stobjs state))
  (case-match term
    (('nth n x)
     (if (equal (mfc-ts n mfc state :forcep nil)
                *ts-symbol*)
         (list 'car x)
       term))
    (& term)))

(defthm nth-symbolp-meta
    (implies (nthmeta-ev (meta-extract-contextual-fact `(:typeset ,(cadr term))
                                                       mfc
                                                       state)
                         a)
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (nth-symbolp-metafn term mfc state) a)))
    :rule-classes ((:meta :trigger-fns (nth))))

(defstub foo (x) t)

(defthm nth-foo
  (implies (symbolp (foo x))
           (equal (nth (foo x) y) (car y)))
  :hints (("Goal" :in-theory '(nth-symbolp-meta))))
