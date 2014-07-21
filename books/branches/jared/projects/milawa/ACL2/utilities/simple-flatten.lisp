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
(include-book "list-list-fix")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund slow-simple-flatten (x)
  ;; Computes (simple-flatten x) very inefficiently.  There's no reason to ever
  ;; use this function.
  (declare (xargs :guard t))
  (if (consp x)
      (app (car x)
           (slow-simple-flatten (cdr x)))
    nil))

(defthm slow-simple-flatten-when-not-consp
  (implies (not (consp x))
           (equal (slow-simple-flatten x)
                  nil))
  :hints(("Goal" :in-theory (enable slow-simple-flatten))))

(defthm slow-simple-flatten-of-cons
  (equal (slow-simple-flatten (cons a x))
         (app a (slow-simple-flatten x)))
  :hints(("Goal" :in-theory (enable slow-simple-flatten))))

(defund fast-simple-flatten$ (x acc)
  ;; Computes (revappend (simple-flatten x) acc).  This is cheaper than calling
  ;; simple-flatten, saveing you one "fast-rev" call and the associated
  ;; consing.
  (declare (xargs :guard (true-listp acc)))
  (if (consp x)
      (fast-simple-flatten$ (cdr x)
                            (revappend (car x) acc))
    acc))


(defund simple-flatten (x)
  ;; Does one level of list flattening.  This won't flatten a whole tree, it'll
  ;; just condense a two-level "list of lists" into a regular, one-level list.
  ;; It takes two linear passes of consing.
  (declare (xargs :guard t))
  (fast-rev (fast-simple-flatten$ x nil)))

(defthmd lemma-for-definition-of-simple-flatten
  (implies (true-listp acc)
           (equal (fast-simple-flatten$ x acc)
                  (app (rev (slow-simple-flatten x)) acc)))
  :hints(("Goal" :in-theory (enable fast-simple-flatten$))))

(defthmd definition-of-simple-flatten
  (equal (simple-flatten x)
         (if (consp x)
             (app (car x)
                  (simple-flatten (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable simple-flatten
                                    lemma-for-definition-of-simple-flatten))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition simple-flatten))))

(defthm simple-flatten-when-not-consp
  (implies (not (consp x))
           (equal (simple-flatten x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-simple-flatten))))

(defthm simple-flatten-of-cons
  (equal (simple-flatten (cons a x))
         (app a (simple-flatten x)))
  :hints(("Goal" :in-theory (enable definition-of-simple-flatten))))

(defthm true-listp-of-simple-flatten
  (equal (true-listp (simple-flatten x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm simple-flatten-of-list-fix
  (equal (simple-flatten (list-fix x))
         (simple-flatten x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm simple-flatten-of-app
  (equal (simple-flatten (app x y))
         (app (simple-flatten x) (simple-flatten y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm simple-flatten-of-list-list-fix
  (equal (simple-flatten (list-list-fix x))
         (simple-flatten x))
  :hints(("Goal" :induct (cdr-induction x))))



(defthm forcing-fast-simple-flatten$-removal
  (implies (force (true-listp acc))
           (equal (fast-simple-flatten$ x acc)
                  (app (rev (simple-flatten x)) acc)))
  :hints(("Goal" :in-theory (enable fast-simple-flatten$))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition fast-simple-flatten$))))




(defun fast-simple-flatten-of-domain$ (x acc)
  ;; Calculates (revappend (simple-flatten (domain x)) acc) in a single,
  ;; tail-recursive linear pass.
  (declare (xargs :guard (and (mapp x)
                              (true-listp acc))))
  (if (consp x)
      (fast-simple-flatten-of-domain$ (cdr x)
                                      (revappend (car (car x)) acc))
    acc))

(defthm fast-simple-flatten-of-domain$-removal
  (implies (force (true-listp acc))
           (equal (fast-simple-flatten-of-domain$ x acc)
                  (app (rev (simple-flatten (domain x))) acc))))



(defun fast-simple-flatten-of-range$ (x acc)
  ;; Calculates (revappend (simple-flatten (range x)) acc) in a single,
  ;; tail-recursive linear pass.
  (declare (xargs :guard (and (mapp x)
                              (true-listp acc))))
  (if (consp x)
      (fast-simple-flatten-of-range$ (cdr x)
                                     (revappend (cdr (car x)) acc))
    acc))

(defthm fast-simple-flatten-of-range$-removal
  (implies (force (true-listp acc))
           (equal (fast-simple-flatten-of-range$ x acc)
                  (app (rev (simple-flatten (range x))) acc))))

