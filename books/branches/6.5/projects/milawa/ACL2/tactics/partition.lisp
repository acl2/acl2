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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defprojection :list (rev-lists x)
               :element (rev x)
               :guard t
               :nil-preservingp t)

(defthm rev-lists-of-rev-lists
  (equal (rev-lists (rev-lists x))
         (list-list-fix x))
  :hints(("Goal" :induct (cdr-induction x))))




(defund fast-app-lists$ (x acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp x)
      (fast-app-lists$ (cdr x)
                       (revappend (car x) acc))
    acc))

(definlined app-lists (x)
  (fast-rev (fast-app-lists$ x nil)))

(defund slow-app-lists (x)
  (if (consp x)
      (app (car x)
           (slow-app-lists (cdr x)))
    nil))

(defthm slow-app-lists-when-not-consp
  (implies (not (consp x))
           (equal (slow-app-lists x)
                  nil))
  :hints(("Goal" :in-theory (enable slow-app-lists))))

(defthm slow-app-lists-of-cons
  (equal (slow-app-lists (cons a x))
         (app a
              (slow-app-lists x)))
  :hints(("Goal" :in-theory (enable slow-app-lists))))

(defthm true-listp-of-slow-app-lists
  (equal (true-listp (slow-app-lists x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm slow-app-lists-of-list-fix
  (equal (slow-app-lists (list-fix x))
         (slow-app-lists x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm slow-app-lists-of-app
  (equal (slow-app-lists (app x y))
         (app (slow-app-lists x)
              (slow-app-lists y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-of-slow-app-lists
  (equal (rev (slow-app-lists x))
         (slow-app-lists (rev (rev-lists x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm slow-app-lists-of-list-list-fix
  (equal (slow-app-lists (list-list-fix x))
         (slow-app-lists x))
  :hints(("Goal" :induct (cdr-induction x))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (true-listp acc)
                   (equal (fast-app-lists$ x acc)
                          (app (slow-app-lists (rev (rev-lists x)))
                               acc)))
          :hints(("Goal" :in-theory (enable fast-app-lists$)))))

 (local (defthm lemma2
          (equal (app-lists x)
                 (slow-app-lists x))
          :hints(("Goal" :in-theory (enable app-lists)))))

 (defthmd definition-of-app-lists
   (equal (app-lists x)
          (if (consp x)
              (app (car x)
                   (slow-app-lists (cdr x)))
            nil))
   :rule-classes :definition))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition app-lists))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition fast-app-lists$))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition slow-app-lists))))

(defthm app-lists-when-not-consp
  (implies (not (consp x))
           (equal (app-lists x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-app-lists))))

(defthm app-lists-of-cons
  (equal (app-lists (cons a x))
         (app a (app-lists x)))
  :hints(("Goal" :in-theory (enable definition-of-app-lists))))

(defthm true-listp-of-app-lists
  (equal (true-listp (app-lists x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm app-lists-of-list-fix
  (equal (app-lists (list-fix x))
         (app-lists x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm app-lists-of-app
  (equal (app-lists (app x y))
         (app (app-lists x)
              (app-lists y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-of-app-lists
  (equal (rev (app-lists x))
         (app-lists (rev (rev-lists x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm app-lists-of-list-list-fix
  (equal (app-lists (list-list-fix x))
         (app-lists x))
  :hints(("Goal" :induct (cdr-induction x))))




(defund fast-sum-list (x acc)
  (declare (xargs :guard (natp acc)))
  (if (consp x)
      (fast-sum-list (cdr x) (+ (car x) acc))
    acc))

(definlined sum-list (x)
  (fast-sum-list x 0))

(defund slow-sum-list (x)
  (if (consp x)
      (+ (car x)
         (slow-sum-list (cdr x)))
    0))

(encapsulate
 ()
 (local (defthm lemma
          (implies (force (natp acc))
                   (equal (fast-sum-list x acc)
                          (+ (slow-sum-list x) acc)))
          :hints(("Goal" :in-theory (enable fast-sum-list
                                            slow-sum-list)))))

 (defthmd definition-of-sum-list
   (equal (sum-list x)
          (if (consp x)
              (+ (car x)
                 (sum-list (cdr x)))
            0))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable slow-sum-list sum-list)))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition sum-list))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition fast-sum-list))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition slow-sum-list))))

(defthm sum-list-when-not-consp
  (implies (not (consp x))
           (equal (sum-list x)
                  0))
  :hints(("Goal" :in-theory (enable definition-of-sum-list))))

(defthm sum-list-of-cons
  (equal (sum-list (cons a x))
         (+ a (sum-list x)))
  :hints(("Goal" :in-theory (enable definition-of-sum-list))))

(defthm natp-of-sum-list
  (equal (natp (sum-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm sum-list-of-list-fix
  (equal (sum-list (list-fix x))
         (sum-list x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm sum-list-of-app
  (equal (sum-list (app x y))
         (+ (sum-list x) (sum-list y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm sum-list-of-rev
  (equal (sum-list (rev x))
         (sum-list x))
  :hints(("Goal" :induct (cdr-induction x))))



(defthm len-of-restn
  ;; BOZO move to utilities
  (equal (len (restn n x))
         (- (len x) n))
  :hints(("Goal" :in-theory (enable restn))))

(defthm len-of-firstn
  ;; BOZO move to utilities
  (equal (len (firstn n x))
         (min n (len x)))
  :hints(("Goal" :in-theory (enable firstn))))


(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defund partition (lens x)
   ;; Split x into sublists by their lengths.
   ;; BOZO it would be a good idea to improve this function's efficiency, e.g.,
   ;; tail recursion, a combined firstn/restn with no list-fixing, etc.
   (declare (xargs :guard (and (nat-listp lens)
                               (equal (sum-list lens) (len x)))))
   (if (consp lens)
       (cons (firstn (car lens) x)
             (partition (cdr lens) (restn (car lens) x)))
     nil)))

(defthm partition-when-not-consp
  (implies (not (consp lens))
           (equal (partition lens x)
                  nil))
  :hints(("Goal" :in-theory (enable partition))))

(defthm partition-of-cons
  (equal (partition (cons len lens) x)
         (cons (firstn len x)
               (partition lens (restn len x))))
  :hints(("Goal" :in-theory (enable partition))))

;; I'm just going to be sloppy and enable partition when I need its induction
;; scheme.

(defthm partition-of-list-fix-one
  (equal (partition (list-fix lens) x)
         (partition lens x))
  :hints(("Goal" :in-theory (enable partition))))

(defthm partition-of-list-fix-two
  (equal (partition lens (list-fix x))
         (partition lens x))
  :hints(("Goal" :in-theory (enable partition))))

(defthm true-listp-of-partition
  (equal (true-listp (partition lens x))
         t)
  :hints(("Goal" :in-theory (enable partition))))

(encapsulate
 ()
 (local (defthm lemma
          ;; BOZO add to arithmetic?
          (implies (and (not (zp b))
                        (not (< a x)))
                   (equal (equal (+ a b) x)
                          nil))))

 (defthm forcing-app-lists-of-partition
   (implies (force (equal (sum-list lens) (len x)))
            (equal (app-lists (partition lens x))
                   (list-fix x)))
   :hints(("Goal"
           :in-theory (enable partition)
           :induct (partition lens x)))))

(defthm partition-of-strip-lens-of-app-lists
  (equal (partition (strip-lens x) (app-lists x))
         (list-list-fix x))
  :hints(("Goal"
          :induct (cdr-induction x))))

(defthm partition-of-strip-lens-of-app-lists-free
  (implies (equal lens (strip-lens x))
           (equal (partition lens (app-lists x))
                  (list-list-fix x))))

(defthm partition-of-simple-flatten
  (equal (partition (strip-lens x) (simple-flatten x))
         (list-list-fix x))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable partition))))