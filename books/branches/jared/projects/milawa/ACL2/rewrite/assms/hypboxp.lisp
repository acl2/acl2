; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "../../clauses/basic")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(definlined rw.hypboxp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (logic.term-listp (car x))
       (logic.term-listp (cdr x))
       (true-listp (car x))
       (true-listp (cdr x))))

(definlined rw.hypbox (left right)
  (declare (xargs :guard (and (logic.term-listp left)
                              (logic.term-listp right)
                              (true-listp left)
                              (true-listp right))))
  (cons left right))

(definlined rw.hypbox->left (x)
  (declare (xargs :guard (rw.hypboxp x)))
  (car x))

(definlined rw.hypbox->right (x)
  (declare (xargs :guard (rw.hypboxp x)))
  (cdr x))

(encapsulate
 ()
 (local (in-theory (enable rw.hypboxp
                           rw.hypbox
                           rw.hypbox->left
                           rw.hypbox->right)))

 (defthm booleanp-of-rw.hypboxp
   (equal (booleanp (rw.hypboxp x))
          t))

 (defthm forcing-rw.hypboxp-of-rw.hypbox
   (implies (force (and (logic.term-listp left)
                        (logic.term-listp right)
                        (true-listp left)
                        (true-listp right)))
            (equal (rw.hypboxp (rw.hypbox left right))
                   t)))

 (defthm rw.hypbox->left-of-rw.hypbox
   (equal (rw.hypbox->left (rw.hypbox left right))
          left))

 (defthm rw.hypbox->right-of-rw.hypbox
   (equal (rw.hypbox->right (rw.hypbox left right))
          right))

 (defthm forcing-logic.term-listp-of-rw.hypbox->left
   (implies (force (rw.hypboxp x))
            (equal (logic.term-listp (rw.hypbox->left x))
                   t)))

 (defthm forcing-logic.term-listp-of-rw.hypbox->right
   (implies (force (rw.hypboxp x))
            (equal (logic.term-listp (rw.hypbox->right x))
                   t)))

 (defthm forcing-true-listp-of-rw.hypbox->left
   (implies (force (rw.hypboxp x))
            (equal (true-listp (rw.hypbox->left x))
                   t)))

 (defthm forcing-true-listp-of-rw.hypbox->right
   (implies (force (rw.hypboxp x))
            (equal (true-listp (rw.hypbox->right x))
                   t)))

 (defthm forcing-equal-of-rw.hypbox-one
   (implies (force (rw.hypboxp x))
            (equal (equal x (rw.hypbox left right))
                   (and (equal left (rw.hypbox->left x))
                        (equal right (rw.hypbox->right x))))))

 (defthm forcing-equal-of-rw.hypbox-two
   (implies (force (rw.hypboxp x))
            (equal (equal (rw.hypbox left right) x)
                   (and (equal left (rw.hypbox->left x))
                        (equal right (rw.hypbox->right x)))))))


(definlined rw.hypbox-atblp (x atbl)
  (declare (xargs :guard (and (rw.hypboxp x)
                              (logic.arity-tablep atbl))))
  (and (logic.term-list-atblp (rw.hypbox->left x) atbl)
       (logic.term-list-atblp (rw.hypbox->right x) atbl)))

(encapsulate
 ()
 (local (in-theory (enable rw.hypbox-atblp)))

 (defthm booleanp-of-rw.hypbox-atblp
   (equal (booleanp (rw.hypbox-atblp x atbl))
          t))

 (defthm forcing-rw.hypbox-atblp-of-quote-nil
   (equal (rw.hypbox-atblp '(nil) atbl)
          t))

 (defthm forcing-logic.term-list-atblp-of-rw.hypbox->left
   (implies (force (rw.hypbox-atblp x atbl))
            (equal (logic.term-list-atblp (rw.hypbox->left x) atbl)
                   t)))

 (defthm forcing-logic.term-list-atblp-of-rw.hypbox->right
   (implies (force (rw.hypbox-atblp x atbl))
            (equal (logic.term-list-atblp (rw.hypbox->right x) atbl)
                   t)))

 (defthm forcing-rw.hypbox-atblp-of-rw.hypbox
   (implies (force (and (logic.term-list-atblp left atbl)
                        (logic.term-list-atblp right atbl)))
            (equal (rw.hypbox-atblp (rw.hypbox left right) atbl)
                   t)))

 (defthm rw.hypbox-atblp-of-nil
   (equal (rw.hypbox-atblp nil atbl)
          t)))





(definlined rw.hypbox-formula (x)
  (declare (xargs :guard (and (rw.hypboxp x)
                              (or (rw.hypbox->left x)
                                  (rw.hypbox->right x)))))
  (let ((left  (rw.hypbox->left x))
        (right (rw.hypbox->right x)))
    (cond ((and left right)
           (logic.por (clause.clause-formula left)
                      (clause.clause-formula right)))
          (left
           (clause.clause-formula left))
          (right
           (clause.clause-formula right))
          (t nil))))

(defthm forcing-logic.formulap-of-rw.hypbox-formula
  (implies (force (and (rw.hypboxp x)
                       (or (rw.hypbox->left x)
                           (rw.hypbox->right x))))
           (equal (logic.formulap (rw.hypbox-formula x))
                  t))
  :hints(("Goal" :in-theory (enable rw.hypbox-formula))))

(defthm forcing-logic.formula-atblp-of-rw.hypbox-formula
  (implies (force (and (rw.hypboxp x)
                       (rw.hypbox-atblp x atbl)
                       (or (rw.hypbox->left x)
                           (rw.hypbox->right x))))
           (equal (logic.formula-atblp (rw.hypbox-formula x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.hypbox-formula))))



(deflist rw.hypbox-listp (x)
  (rw.hypboxp x)
  :guard t
  :elementp-of-nil nil)

(deflist rw.hypbox-list-atblp (x atbl)
  (rw.hypbox-atblp x atbl)
  :guard (and (rw.hypbox-listp x)
              (logic.arity-tablep atbl))
  :elementp-of-nil t)




(defund logic.true-term-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (logic.termp (car x))
           (logic.true-term-listp (cdr x)))
    (not x)))

(defthm logic.true-term-listp-removal
  (equal (logic.true-term-listp x)
         (and (true-listp x)
              (logic.term-listp x)))
  :hints(("Goal" :in-theory (enable logic.true-term-listp))))

(defund rw.faster-hypboxp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (logic.true-term-listp (car x))
       (logic.true-term-listp (cdr x))))

(defthm rw.faster-hypboxp-removal
  (equal (rw.faster-hypboxp x)
         (rw.hypboxp x))
  :hints(("Goal" :in-theory (enable rw.faster-hypboxp rw.hypboxp))))
