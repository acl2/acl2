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
(include-book "hypboxp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund rw.slow-hypbox-arities (x)
  (declare (xargs :guard (rw.hypboxp x)))
  (app (logic.slow-term-list-arities (rw.hypbox->left x))
       (logic.slow-term-list-arities (rw.hypbox->right x))))

(defund rw.hypbox-arities (x acc)
  (declare (xargs :guard (and (rw.hypboxp x)
                              (true-listp acc))))
  (logic.term-list-arities (rw.hypbox->left x)
                           (logic.term-list-arities (rw.hypbox->right x)
                                                    acc)))

(defthm true-listp-of-rw.hypbox-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.hypbox-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.hypbox-arities))))

(defthm rw.hypbox-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.hypbox-arities x acc)
                  (app (rw.slow-hypbox-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.hypbox-arities
                                    rw.slow-hypbox-arities))))

(defthm rw.slow-hypbox-arities-correct
  (implies (force (rw.hypboxp x))
           (equal (logic.arities-okp (rw.slow-hypbox-arities x) atbl)
                  (rw.hypbox-atblp x atbl)))
  :hints(("Goal"
          :in-theory (e/d (rw.slow-hypbox-arities
                           rw.hypbox-atblp)
                          ((:executable-counterpart acl2::force))))))

(definlined rw.fast-hypbox-atblp (x atbl)
  (declare (xargs :guard (and (rw.hypboxp x)
                              (logic.arity-tablep atbl))))
  (logic.fast-arities-okp (rw.hypbox-arities x nil) atbl))

(defthm rw.fast-hypbox-atblp-removal
  (implies (and (force (rw.hypboxp x))
                (force (mapp atbl)))
           (equal (rw.fast-hypbox-atblp x atbl)
                  (rw.hypbox-atblp x atbl)))
  :hints(("Goal" :in-theory (enable rw.fast-hypbox-atblp))))






(defund rw.slow-hypbox-list-arities (x)
  (declare (xargs :guard (rw.hypbox-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (rw.slow-hypbox-list-arities (cdr x))
           (rw.slow-hypbox-arities (car x)))
    nil))

(defund rw.hypbox-list-arities (x acc)
  (declare (xargs :guard (and (rw.hypbox-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.hypbox-list-arities (cdr x)
                              (rw.hypbox-arities (car x) acc))
    acc))

(defthm true-listp-of-rw.hypbox-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.hypbox-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.hypbox-list-arities))))

(defthm rw.hypbox-list-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.hypbox-list-arities x acc)
                  (app (rw.slow-hypbox-list-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.hypbox-list-arities
                                    rw.slow-hypbox-list-arities))))

(defthm rw.slow-hypbox-list-arities-correct
  (implies (force (rw.hypbox-listp x))
           (equal (logic.arities-okp (rw.slow-hypbox-list-arities x) atbl)
                  (rw.hypbox-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.hypbox-list-atblp x atbl)
                   (rw.slow-hypbox-list-arities x)))))

