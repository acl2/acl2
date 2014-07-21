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
(include-book "terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(deflist logic.all-functionsp (x)
  (logic.functionp x)
  :elementp-of-nil nil
  :guard (logic.term-listp x))

(defprojection :list (logic.strip-function-names x)
               :element (logic.function-name x)
               :guard (and (logic.term-listp x)
                           (logic.all-functionsp x))
               :nil-preservingp t)

(defthm forcing-logic.function-symbol-listp-of-logic.strip-function-names
  (implies (and (force (logic.term-listp x))
                (force (logic.all-functionsp x)))
           (equal (logic.function-symbol-listp (logic.strip-function-names x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


(defprojection :list (logic.strip-function-args x)
               :element (logic.function-args x)
               :guard (and (logic.term-listp x)
                           (logic.all-functionsp x))
               :nil-preservingp t)

(defthm forcing-logic.term-list-listp-of-logic.strip-function-args
  (implies (and (force (logic.term-listp x))
                (force (logic.all-functionsp x)))
           (equal (logic.term-list-listp (logic.strip-function-args x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atblp-of-logic.strip-function-args
  (implies (and (force (logic.term-list-atblp x atbl))
                (force (logic.all-functionsp x)))
           (equal (logic.term-list-list-atblp (logic.strip-function-args x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-true-list-listp-of-logic.strip-function-args
  (implies (and (force (logic.term-listp x))
                (force (logic.all-functionsp x)))
           (equal (true-list-listp (logic.strip-function-args x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-listp-of-strip-firsts-when-all-lens-2
  (implies (and (logic.all-functionsp x)
                (logic.term-listp x)
                (all-equalp 2 (strip-lens (logic.strip-function-args x))))
           (equal (logic.term-listp (strip-firsts (logic.strip-function-args x)))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-listp-of-strip-seconds-when-all-lens-2
  (implies (and (logic.all-functionsp x)
                (logic.term-listp x)
                (all-equalp 2 (strip-lens (logic.strip-function-args x))))
           (equal (logic.term-listp (strip-seconds (logic.strip-function-args x)))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-atblp-of-strip-firsts-when-all-lens-2
  (implies (and (logic.all-functionsp x)
                (all-equalp 2 (strip-lens (logic.strip-function-args x)))
                (force (logic.term-listp x))
                (force (logic.term-list-atblp x atbl)))
           (equal (logic.term-list-atblp (strip-firsts (logic.strip-function-args x)) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-atblp-of-strip-seconds-when-all-lens-2
  (implies (and (logic.all-functionsp x)
                (all-equalp 2 (strip-lens (logic.strip-function-args x)))
                (force (logic.term-listp x))
                (force (logic.term-list-atblp x atbl)))
           (equal (logic.term-list-atblp (strip-seconds (logic.strip-function-args x)) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(encapsulate
 ()
 (local (in-theory (disable equal-of-logic.function-rewrite)))
 (defprojection
   :list (logic.function-list name x)
   :element (logic.function name x)
   :guard (and (logic.function-namep name)
               (logic.term-list-listp x)
               (true-list-listp x))))

(defthm forcing-logic.term-listp-of-logic.function-list
  (implies (and (force (logic.function-namep name))
                (force (logic.term-list-listp x))
                (force (true-list-listp x)))
           (equal (logic.term-listp (logic.function-list name x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-logic.function-list
  (implies (and (force (logic.function-namep name))
                (force (logic.term-list-list-atblp x atbl))
                (force (all-equalp (cdr (lookup name atbl)) (strip-lens x))))
           (equal (logic.term-list-atblp (logic.function-list name x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.all-functionsp-of-logic.function-list
  (implies (and (force (logic.function-namep name))
                (force (logic.term-list-listp x))
                (force (true-list-listp x)))
           (equal (logic.all-functionsp (logic.function-list name x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.strip-function-names-of-logic.function-list
  (implies (and (force (logic.function-namep name))
                (force (logic.term-list-listp x))
                (force (true-list-listp x)))
           (equal (logic.strip-function-names (logic.function-list name x))
                  (repeat name (len x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.strip-function-args-of-logic.function-list
  (implies (and (force (logic.function-namep name))
                (force (logic.term-list-listp x))
                (force (true-list-listp x)))
           (equal (logic.strip-function-args (logic.function-list name x))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))



(defthm forcing-logic.term-listp-list-of-list2-list
  (implies (and (force (logic.term-listp x))
                (force (logic.term-listp y)))
           (equal (logic.term-list-listp (list2-list x y))
                  t))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm forcing-logic.term-list-atblp-list-of-list2-list
  (implies (and (force (logic.term-list-atblp x atbl))
                (force (logic.term-list-atblp y atbl)))
           (equal (logic.term-list-list-atblp (list2-list x y) atbl)
                  t))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

