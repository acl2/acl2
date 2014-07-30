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
(include-book "proofp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; We introduce some fused operations for greater efficiency.  IMO the compiler
;; should be smart enough to do this, but IRL it isn't.  I guess TANSTAAFL,
;; after all.

(defund logic.=rhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-atomicp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (logic.=rhs (logic.conclusion (car x)))
            (logic.=rhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.=rhses-of-strip-conclusions-removal
  (equal (logic.=rhses-of-strip-conclusions x)
         (logic.=rhses (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.=rhses-of-strip-conclusions))))



(defund logic.=lhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-atomicp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (logic.=lhs (logic.conclusion (car x)))
            (logic.=lhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.=lhses-of-strip-conclusions-removal
  (equal (logic.=lhses-of-strip-conclusions x)
         (logic.=lhses (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.=lhses-of-strip-conclusions))))




(defund logic.vrhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (logic.vrhs (logic.conclusion (car x)))
            (logic.vrhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.vrhses-of-strip-conclusions-removal
  (equal (logic.vrhses-of-strip-conclusions x)
         (logic.vrhses (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.vrhses-of-strip-conclusions))))


(defund logic.vlhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (logic.vlhs (logic.conclusion (car x)))
            (logic.vlhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.vlhses-of-strip-conclusions-removal
  (equal (logic.vlhses-of-strip-conclusions x)
         (logic.vlhses (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.vlhses-of-strip-conclusions))))


(defund logic.=lhses-of-vrhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x))))))
  (if (consp x)
      (cons (logic.=lhs (logic.vrhs (logic.conclusion (car x))))
            (logic.=lhses-of-vrhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.=lhses-of-vrhses-of-strip-conclusions-removal
  (equal (logic.=lhses-of-vrhses-of-strip-conclusions x)
         (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
  :hints(("Goal" :in-theory (enable logic.=lhses-of-vrhses-of-strip-conclusions))))


(defund logic.=rhses-of-vrhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x))))))
  (if (consp x)
      (cons (logic.=rhs (logic.vrhs (logic.conclusion (car x))))
            (logic.=rhses-of-vrhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.=rhses-of-vrhses-of-strip-conclusions-removal
  (equal (logic.=rhses-of-vrhses-of-strip-conclusions x)
         (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
  :hints(("Goal" :in-theory (enable logic.=rhses-of-vrhses-of-strip-conclusions))))




(defund logic.all-atomicp-of-strip-conclusions (x)
  (declare (xargs :guard (logic.appeal-listp x)))
  (if (consp x)
      (and (equal (logic.fmtype (logic.conclusion (car x))) 'pequal*)
           (logic.all-atomicp-of-strip-conclusions (cdr x)))
    t))

(defthm logic.all-atomicp-of-strip-conclusions-removal
  (equal (logic.all-atomicp-of-strip-conclusions x)
         (logic.all-atomicp (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.all-atomicp-of-strip-conclusions))))



(defund logic.all-disjunctionsp-of-strip-conclusions (x)
  (declare (xargs :guard (logic.appeal-listp x)))
  (if (consp x)
      (and (equal (logic.fmtype (logic.conclusion (car x))) 'por*)
           (logic.all-disjunctionsp-of-strip-conclusions (cdr x)))
    t))

(defthm logic.all-disjunctionsp-of-strip-conclusions-removal
  (equal (logic.all-disjunctionsp-of-strip-conclusions x)
         (logic.all-disjunctionsp (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.all-disjunctionsp-of-strip-conclusions))))


(defund logic.all-atomicp-of-vrhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x)))))
  (if (consp x)
      (and (equal (logic.fmtype (logic.vrhs (logic.conclusion (car x)))) 'pequal*)
           (logic.all-atomicp-of-vrhses-of-strip-conclusions (cdr x)))
    t))

(defthm logic.all-atomicp-of-vrhses-of-strip-conclusions-removal
  (equal (logic.all-atomicp-of-vrhses-of-strip-conclusions x)
         (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x))))
  :hints(("Goal" :in-theory (enable logic.all-atomicp-of-vrhses-of-strip-conclusions))))
