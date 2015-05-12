; SVEX - Symbolic, Vector-Level Hardware Description Library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SVEX")

(include-book "4vec")
(include-book "evaluator")
(include-book "std/misc/two-nats-measure" :dir :system)
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (acl2::ruletable-delete-tags! acl2::listp-rules (:osets :duplicated-members)))

;; Motivating example 1:
;; Suppose we have something like
;; wire [7:0] a;
;; wire [7:0] b;
;; assign a =  b | { a[6:0], 1'b0 };
;; This looks like a loop, but is actually legitimate at the bit level --
;; each a[i] equals | b[i:0].

;; How would we process this to a fixpoint?
;; If we expand a as-is, we get something like
;; assign a = b | { ( b | { a[6:0], 1'b0 } )[6:0], 1'b0 }
;; and we could just keep doing this forever.  What we'd like is for one such
;; expansion to give us something that's now in terms of a[5:0], the next in
;; terms of a[4:0], until we eliminate a from the formula altogether.

;; First, it helps if we explicitly put a size on our original formula.
;; Let's also write a[6:0] as trunc(7, a).
;; assign a = trunc(8, b | { trunc(7, a), 1'b0 });
;; We can push the trunc inside the OR and the concatenation:
;; assign a = trunc(8, b) | { trunc(7, trunc(7, a)), 1'b0 }
;; and simplify the trunc-of-trunc:
;; assign a = trunc(8, b) | { trunc(7, a), 1'b0 }
;; Now if we expand a and again push the trunc(7, ) inside, we get
;; assign a = trunc(8, b) | { trunc(7, trunc(8, b) | { trunc(7, a), 1'b0 } ), 1'b0 }
;; assign a = trunc(8, b) | { trunc(7, trunc(8, b)) | { trunc(6, trunc(7, a)), 1'b0 } ), 1'b0 }
;; simplify the trunc-of-trunc:
;; assign a = trunc(8, b) | { trunc(7, b) | { trunc(6, a), 1'b0 } ), 1'b0 }
;; and expanding more:
;; assign a = trunc(8, b) |
;;            { trunc(7, b) |
;;              { trunc(6, b) |
;;                { trunc(5, b) |
;;                  {trunc(4, b) |
;;                    { trunc(3, b) |
;;                      { trunc(2, b) |
;;                        { trunc(1, b) | 1'b0
;;                         , 1'b0 }
;;                       , 1'b0 }
;;                     , 1'b0 }
;;                   , 1'b0 }
;;                 , 1'b0 }
;;               , 1'b0 }
;;             , 1'b0 }

;; Another way of accomplishing this might be to just keep track of a care
;; mask.  Then, we can use a stylized kind of rule to say how we can update
;; that context as we go down into arguments of functions, e.g.:

(defxdoc 4vmask
  :parents (svex)
  :short "Bitmasks indicating the relevant bits of SVEX expressions.")

(defxdoc svmask.lisp :parents (4vmask))
(local (xdoc::set-default-parents svmask.lisp))


(define 4vmask-p (x)
  (integerp x)
  ///
  (defthm 4vmask-p-compound-recognizer
    (equal (4vmask-p x) (integerp x))
    :rule-classes :compound-recognizer))



(define 4vmask-fix ((x 4vmask-p))
  :returns (xx 4vmask-p :rule-classes (:rewrite :type-prescription))
  (mbe :logic (if (4vmask-p x) x -1)
       :exec x)
  ///
  (defthm 4vmask-fix-when-4vmask-p
    (implies (4vmask-p x)
             (equal (4vmask-fix x) x)))

  (fty::deffixtype 4vmask :pred 4vmask-p :fix 4vmask-fix :equiv 4vmask-equiv
    :define t :forward t))

(define 4vec-mask ((mask 4vmask-p) (x 4vec-p))
  :returns (xx 4vec-p)
  (b* ((mask (mbe :logic (4vmask-fix mask) :exec mask))
       ((4vec x) x))
    (4vec (logior (lognot mask) x.upper)
          (logand mask x.lower)))
  ///
  (fty::deffixequiv 4vec-mask)

  ;; (defthm svobj-p-of-4vec-mask
  ;;   (svobj-p (4vec-mask mask x))
  ;;   :hints(("Goal" :in-theory (enable svobj-p))))

  (defthm 4vec-mask-idempotent
    (equal (4vec-mask mask (4vec-mask mask x))
           (4vec-mask mask x)))

  (defthm 4vec-mask-minus-1
    (equal (4vec-mask -1 x)
           (4vec-fix x))
    :hints(("Goal" :in-theory (enable 4vec-mask 4vec-equiv))))

  (defthm 4vec-mask-zero
    (equal (4vec-mask 0 x)
           (4vec-x))
    :hints(("Goal" :in-theory (enable 4vec-mask 4vec-equiv)))))

(fty::deflist 4vmasklist :elt-type 4vmask-p :true-listp t)

(define 4veclist-mask ((masks 4vmasklist-p) (x 4veclist-p))
  :returns (xx 4veclist-p)
  (if (atom x)
      nil
    (if (atom masks)
        (mbe :logic (4veclist-fix x) :exec x)
      (cons (4vec-mask (car masks) (car x))
            (4veclist-mask (cdr masks) (cdr x)))))
  ///
  (fty::deffixequiv 4veclist-mask)

  (defthm len-of-4veclist-mask
    (equal (len (4veclist-mask masks x))
           (len x))))


(fty::defalist 4vmask-alist :key-type svar :val-type 4vmask-p :true-listp t)

(define 4vmask-assoc ((k svar-p)
                      (x 4vmask-alist-p))
  :prepwork ((local (in-theory (enable ; 4vmask-alist-p-when-consp
                                4vmask-alist-p))))
  :guard-hints (("goal" :in-theory (enable 4vmask-fix)))
  :returns (val 4vmask-p :rule-classes :type-prescription
                :hints(("Goal" :in-theory (enable 4vmask-alist-fix))))
  (mbe :logic (4vmask-fix (cdr (hons-assoc-equal (svar-fix k) (4vmask-alist-fix x))))
       :exec (let ((look (assoc-equal (svar-fix k) (4vmask-alist-fix x))))
                (if look (cdr look) -1)))
  ///
  (fty::deffixequiv 4vmask-assoc
    :hints(("Goal" :in-theory (enable 4vmask-alist-fix))))

  (defthm 4vmask-assoc-of-nil
    (equal (4vmask-assoc k nil) -1)))


(define 4vmask-acons ((k svar-p)
                      (v 4vmask-p)
                      (x 4vmask-alist-p))
  :prepwork ((local (in-theory (enable 4vmask-alist-p))))
  :returns (xx 4vmask-alist-p)
  (mbe :logic (cons (cons (svar-fix k) (4vmask-fix v))
                    (4vmask-alist-fix x))
       :exec (acons k v x))
  ///
  (fty::deffixequiv 4vmask-acons)

  (defthm 4vmask-assoc-of-4vmask-acons
    (equal (4vmask-assoc j (4vmask-acons k v x))
           (if (svar-equiv j k)
               (4vmask-fix v)
             (4vmask-assoc j x)))
    :hints(("Goal" :in-theory (enable 4vmask-assoc)))))


(define 4vmask-subsumes ((x 4vmask-p) (y 4vmask-p))
  ;; checks that x has a superset of bits set that y has
  (b* ((x (mbe :logic (4vmask-fix x) :exec x))
       (y (mbe :logic (4vmask-fix y) :exec y)))
    (eql 0 (logand (lognot x) y)))
  ///
  (fty::deffixequiv 4vmask-subsumes)

  (defthm 4vmask-subsumes-implies-masks-equal
    (implies (and (4vmask-subsumes m1 m2)
                  (equal (4vec-mask m1 x) (4vec-mask m1 y)))
             (equal (equal (4vec-mask m2 x) (4vec-mask m2 y))
                    t))
    :hints(("Goal" :in-theory (enable 4vec-mask))
           (acl2::logbitp-reasoning :prune-examples nil)))

  (defthmd 4vmask-subsumes-neg-1-implies-fixes
    (implies (and (4vmask-subsumes m1 -1)
                  (equal (4vec-mask m1 x) (4vec-mask m1 y)))
             (equal (equal (4vec-fix x) (4vec-fix y))
                    t))
    :hints(("Goal" :use ((:instance 4vmask-subsumes-implies-masks-equal
                          (m2 -1)))
            :in-theory (disable 4vmask-subsumes-implies-masks-equal))))

  (defthm 4vmask-subsumes-trans-1
    (implies (and (4vmask-subsumes a b)
                  (4vmask-subsumes b c))
             (4vmask-subsumes a c))
    :hints ((acl2::logbitp-reasoning)))

  (defthm 4vmask-subsumes-trans-2
    (implies (and (4vmask-subsumes b c)
                  (4vmask-subsumes a b))
             (4vmask-subsumes a c))
    :hints ((acl2::logbitp-reasoning)))

  (defthm 4vmask-subsumes-self
    (4vmask-subsumes x x)))

(define 4vmasklist-subsumes ((x 4vmasklist-p) (y 4vmasklist-p))
  :measure (+ (len x) (len y))
  (if (and (atom x) (atom y))
      t
    (and (4vmask-subsumes (if (consp x) (car x) -1)
                          (if (consp y) (car y) -1))
         (4vmasklist-subsumes (cdr x) (cdr y))))
  ///
  (fty::deffixequiv 4vmasklist-subsumes)

  (local (defun ind (x y m1 m2)
           (declare (xargS :measure (+ (len m1) (len m2))))
           (if (and (atom m1) (atom m2))
               (list x y)
             (ind (cdr x) (cdr y) (cdr m1) (cdr m2)))))

  (defthm 4vmasklist-subsumes-implies-masks-equal
    (implies (and (4vmasklist-subsumes m1 m2)
                  (equal (4veclist-mask m1 x) (4veclist-mask m1 y)))
             (equal (equal (4veclist-mask m2 x) (4veclist-mask m2 y))
                    t))
    :hints(("Goal" :in-theory (enable 4vmask-subsumes-neg-1-implies-fixes
                                      4veclist-mask
                                      4veclist-fix)
            :induct (ind x y m1 m2))))

  (defthm 4vmasklist-subsumes-self
    (4vmasklist-subsumes x x)
    :hints (("goal" :induct (len x)))))


(define 4vmask-union ((x 4vmask-p) (y 4vmask-p))
  :returns (u 4vmask-p :rule-classes :type-prescription)
  (logior (mbe :logic (4vmask-fix x) :exec x)
          (mbe :logic (4vmask-fix y) :exec y))
  ///
  (fty::deffixequiv 4vmask-union)

  (local (in-theory (enable 4vmask-subsumes)))

  (defthm 4vmask-subsumes-of-4vmask-union-1
    (4vmask-subsumes (4vmask-union x y) x)
    :hints ((acl2::logbitp-reasoning)))

  (defthm 4vmask-subsumes-of-4vmask-union-2
    (4vmask-subsumes (4vmask-union x y) y)
    :hints ((acl2::logbitp-reasoning))))
