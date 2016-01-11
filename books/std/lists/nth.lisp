; Nth Lemmas
; Copyright (C) 2011-2013 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "list-defuns")
(include-book "abstract")
(local (include-book "rev"))
(local (include-book "append"))
(local (include-book "take"))

(local (defthm commutativity-2-of-+
         (equal (+ x (+ y z))
                (+ y (+ x z)))))

(local (defthm fold-consts-in-+
         (implies (and (syntaxp (quotep x))
                       (syntaxp (quotep y)))
                  (equal (+ x (+ y z)) (+ (+ x y) z)))))

(local (defthm distributivity-of-minus-over-+
         (equal (- (+ x y)) (+ (- x) (- y)))))


(defthm nth-when-atom
  (implies (atom x)
           (equal (nth n x)
                  nil)))

(defthm nth-when-zp
  (implies (zp n)
           (equal (nth n x)
                  (car x))))

(defthm nth-of-nil
  (equal (nth n nil)
         nil))

(defthm nth-of-list-fix
  (equal (nth n (list-fix x))
         (nth n x)))

(defthm nth-of-nfix
  (equal (nth (nfix n) x)
         (nth n x)))

(defthm member-of-nth
  (implies (< (nfix n) (len x))
           (member (nth n x) x)))

(defthmd nth-when-too-large
  ;; Matt Kaufmann reported that this lemma got expensive in one of his books,
  ;; so we now disable it by default and instead leave enabled a -cheap rule
  ;; with a backchain limit.
  (implies (<= (len x) (nfix n))
           (equal (nth n x)
                  nil)))

(defthm nth-when-too-large-cheap
  (implies (<= (len x) (nfix n))
           (equal (nth n x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm nth-of-append
  (equal (nth n (append x y))
         (if (< (nfix n) (len x))
             (nth n x)
           (nth (- n (len x)) y))))

(defthm nth-of-revappend
  (equal (nth n (revappend x y))
         (if (< (nfix n) (len x))
             (nth (- (len x) (+ 1 (nfix n))) x)
           (nth (- n (len x)) y))))

(defthm nth-of-rev
  (equal (nth n (rev x))
         (if (< (nfix n) (len x))
             (nth (- (len x) (+ 1 (nfix n))) x)
           nil)))

(defthm nth-of-reverse
  (equal (nth n (reverse x))
         (if (< (nfix n) (len x))
             (nth (- (len x) (+ 1 (nfix n))) x)
           nil)))

(defthm nth-of-take
  (equal (nth i (take n l))
         (if (< (nfix i) (min (nfix n) (len l)))
             (nth i l)
           nil)))

(defthm nth-of-make-list-ac
  (equal (nth n (make-list-ac m val acc))
         (if (< (nfix n) (nfix m))
             val
           (nth (- n (nfix m)) acc))))

(encapsulate
 ()
 (local (defun my-induct (n m)
          (if (zp m)
              (list n m)
            (my-induct (- n 1) (- m 1)))))

 (defthm nth-of-repeat
   (equal (nth n (repeat m a))
          (if (< (nfix n) (nfix m))
              a
            nil))
   :hints(("Goal"
           :induct (my-induct n m)
           :in-theory (enable repeat)))))

(defthm nth-of-nthcdr
  (equal (nth n (nthcdr m x))
         (nth (+ (nfix n) (nfix m)) x)))

(defthm nth-of-last
  (equal (nth n (last x))
         (if (zp n)
             (car (last x))
           nil)))

(defthm nth-of-butlast
  (equal (nth n (butlast x m))
         (if (< (nfix n) (- (len x) (nfix m)))
             (nth n x)
           nil)))




;; Generic rules about nth of element-lists, projections
(def-listp-rule element-p-of-nth-when-element-list-p-when-nil-element
  (implies (and (element-p nil)
                (element-list-p x))
           (element-p (nth n x)))
  :requirement (and element-p-of-nil simple)
  :name element-p-of-nth-when-element-list-p
  :body (implies (element-list-p x)
                    (element-p (nth n x))))

(def-listp-rule element-p-of-nth-when-element-list-p-when-nil-unknown
  (implies (and (element-list-p x)
                (< (nfix n) (len x)))
           (element-p (nth n x)))
  :requirement (and (not element-p-of-nil)
                    simple
                    (not not-element-p-of-nil))
  :name element-p-of-nth-when-element-list-p)

(def-listp-rule element-p-of-nth-when-element-list-p-when-nil-not-element-non-negated
  (implies (and (not (element-p nil))
                (element-list-p x))
           (iff (element-p (nth n x))
                (< (nfix n) (len x))))
  :requirement (and not-element-p-of-nil
                    simple
                    (not negatedp))
  :name element-p-of-nth-when-element-list-p
  :body (implies (element-list-p x)
                 (iff (element-p (nth n x))
                      (< (nfix n) (len x)))))

(def-listp-rule element-p-of-nth-when-element-list-p-when-nil-not-element-negated
  (implies (and (not (element-p nil))
                (element-list-p x))
           (iff (non-element-p (nth n x))
                (<= (len x) (nfix n))))
  :requirement (and not-element-p-of-nil
                    simple
                    negatedp)
  :name element-p-of-nth-when-element-list-p
  :body (implies (element-list-p x)
                 (iff (non-element-p (nth n x))
                      (<= (len x) (nfix n)))))


(def-projection-rule nth-of-elementlist-projection-when-nil-preservingp
  (implies (equal (element-xformer nil) nil)
           (equal (nth n (elementlist-projection x))
                  (element-xformer (nth n x))))
  :requirement nil-preservingp
  :name nth-of-elementlist-projection
  :body (equal (nth n (elementlist-projection x))
               (element-xformer (nth n x))))

(def-projection-rule nth-of-elementlist-projection-when-not-nil-preservingp
  (equal (nth n (elementlist-projection x))
         (and (< (nfix n) (len x))
              (element-xformer (nth n x))))
  :requirement (not nil-preservingp)
  :name nth-of-elementlist-projection)


(def-listfix-rule nth-of-element-list-fix-when-nil-element
  (implies (element-p nil)
           (equal (nth n (element-list-fix x))
                  (element-fix (nth n x))))
  :requirement element-p-of-nil
  :name nth-of-element-list-fix
  :body (equal (nth n (element-list-fix x))
               (element-fix (nth n x))))

(def-listfix-rule nth-of-element-list-fix-unless-nil-element
  (equal (nth n (element-list-fix x))
         (and (< (nfix n) (len x))
              (element-fix (nth n x))))
  :requirement (not element-p-of-nil)
  :name nth-of-element-list-fix)


;; No rule about update-nth, because nth-update-nth is an ACL2 builtin.


(encapsulate
 (((equal-by-nths-hyp) => *)
  ((equal-by-nths-lhs) => *)
  ((equal-by-nths-rhs) => *))
 (local (defun equal-by-nths-hyp () nil))
 (local (defun equal-by-nths-lhs () nil))
 (local (defun equal-by-nths-rhs () nil))
 (defthmd equal-by-nths-constraint
   (implies (and (equal-by-nths-hyp)
                 (natp n)
                 (< n (len (equal-by-nths-lhs))))
            (equal (nth n (equal-by-nths-lhs))
                   (nth n (equal-by-nths-rhs))))))

(local (defun nth-badguy (x y)
         (cond ((or (not (consp x))
                    (not (consp y)))
                0)
               ((equal (car x) (car y))
                (+ 1 (nth-badguy (cdr x) (cdr y))))
               (t
                0))))

(local (defthm nth-badguy-bounded
         (<= (nth-badguy x y) (len x))
         :rule-classes :linear))

(local (defthm nth-badguy-is-bad
         (implies (and (equal (len x) (len y))
                       (not (equal (nth-badguy x y) (len x))))
                  (not (equal (nth (nth-badguy x y) x)
                              (nth (nth-badguy x y) y))))))

(local (defthm nth-badguy-is-equality
         (implies (and (equal (len x) (len y))
                       (true-listp x)
                       (true-listp y))
                  (equal (equal (nth-badguy x y) (len x))
                         (equal x y)))))

(local (in-theory (disable nth-badguy-is-equality
                           nth-badguy-is-bad
                           nth-badguy)))

(defthm equal-by-nths
  (implies (and (equal-by-nths-hyp)
                (true-listp (equal-by-nths-lhs))
                (true-listp (equal-by-nths-rhs)))
           (equal (equal (equal-by-nths-lhs) (equal-by-nths-rhs))
                  (equal (len (equal-by-nths-lhs)) (len (equal-by-nths-rhs)))))
  :hints(("Goal"
          :use ((:instance nth-badguy-is-equality
                           (x (equal-by-nths-lhs))
                           (y (equal-by-nths-rhs)))
                (:instance nth-badguy-is-bad
                           (x (equal-by-nths-lhs))
                           (y (equal-by-nths-rhs)))
                (:instance equal-by-nths-constraint
                           (n (nth-badguy (equal-by-nths-lhs) (equal-by-nths-rhs))))))))


;; Computed hint.  For now we'll assume that we're trying to prove an equality
;; which is the conclusion of the goal, and that the rest of the goal is hyps
;; that we might need.
(defun equal-by-nths-hint-fn (clause)
  (declare (xargs :mode :program))
  (b* ((lit (car (last clause)))
       ((unless (and (consp lit)
                     (eq (car lit) 'equal)))
        nil)
       (hyps (dumb-negate-lit-lst (butlast clause 1)))
       ((list x y) (cdr lit)))
    `(:use ((:functional-instance
             equal-by-nths
             (equal-by-nths-lhs (lambda () ,x))
             (equal-by-nths-rhs (lambda () ,y))
             (equal-by-nths-hyp (lambda () (and . ,hyps))))))))

(defmacro equal-by-nths-hint ()
  '(equal-by-nths-hint-fn clause))

(defthm acl2-count-of-nth-linear
  ;; Added by Alessandro Coglio (coglio@kestrel.edu), Kestrel Institute.
  (implies (consp x)
           (< (acl2-count (nth i x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-of-nth-linear-weak
  ;; Added by Alessandro Coglio (coglio@kestrel.edu), Kestrel Institute.
  (<= (acl2-count (nth i x))
      (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-of-nth-rewrite
  ;; Added by Alessandro Coglio (coglio@kestrel.edu), Kestrel Institute.
  (equal (< (acl2-count (nth i x))
            (acl2-count x))
         (or (consp x)
             (> (acl2-count x) 0))))
