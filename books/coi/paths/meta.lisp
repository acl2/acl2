; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

(in-package "CPATH")
(include-book "../lists/basic")
(include-book "../lists/map-cons")
(include-book "../syntax/syntax")
(include-book "../util/mv-nth")
(local (include-book "../util/iff"))

;; jcd - changing this to path, speeds things up a lot (~100 seconds) and
;; separates paths from graphs.
(include-book "path")

;; jcd - moved to :lists/map-cons
;; (defun map-cons (a list)
;;   (declare (type t a list))
;;   (if (consp list)
;;       (cons (cons a (car list))
;;             (map-cons a (cdr list)))
;;     nil))

;; jcd - moved to :lists/basic
;; (defun appendx (x y)
;;   (declare (type t x y))
;;   (if (consp x)
;;       (cons (car x) (appendx (cdr x) y))
;;     y))

;; jcd - we use mbe now, no need for this rule
;; (defthm appendx-is-append
;;   (equal (appendx x y)
;;          (append x y)))

;  1.36          12.00
;  CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-MEMBERSHIP-DECONSTRUCTION

;jcd Trying this. -ews
(local (in-theory (disable not-dominates-from-diverge-one
                           not-dominates-from-diverge-two)))

;; Normalization: assume that (append (cons a b) list) = (cons a (append b list))
;; (for quoted (cons a b) terms, too)

(in-theory
 (disable
  LENS-<-WHEN-DOMINATES-BUT-NOT-CONG
  NOT-DOMINATES-FROM-<-OF-LEN-AND-LEN
  DOMINATES-WHEN-LENS-EQUAL
;; jcd - Cheapened this, going to try leaving it enabled
;;   DOMINATES-WHEN-NOT-DIVERGE-AND-NOT-DOMINATES
  DOMINATES-ASYMMETRIC
  DOMINATES-TRANSITIVE-TWO
  dominates-means-not-diverge
  dominates-means-not-diverge-alt
  ))

(in-theory
 (enable
  BAG::APPEND-COMMUTATIVE-INSIDE-PERM
  ))

(local (in-theory (disable syn::open-len)))

(defun syn::ts-consp (term fact)
  (declare (type (satisfies acl2::type-alist-entryp) fact)
           (xargs :guard-hints (("goal" :in-theory (enable acl2::type-alist-entryp)))))
  (let ((ts     (cadr fact))
        (tsterm (car  fact)))
    (and (or (not (= (logand ts acl2::*ts-proper-cons*) acl2::*ts-empty*))
             (not (= (logand ts acl2::*ts-improper-cons*) acl2::*ts-empty*)))
         (equal term tsterm))))

(defun sudo-len (term)
  (declare (type t term))
  (if (syn::consp term)
      (1+ (sudo-len (syn::cdr term)))
    (if (syn::appendp term)
        (1+ (sudo-len (syn::arg 2 term)))
      (if (syn::quotep term)
          1
        0))))

(defthm integerp-sudo-len
  (integerp (sudo-len term))
  :rule-classes (:rewrite :type-prescription))

(defthm sudo-len-linear
  (<= 0 (sudo-len ter))
  :rule-classes (:linear))

(defun equal-len (path1 path2)
  (declare (type t path1 path2))
  (cond
   ((and (syn::quotep path1)
         (syn::quotep path2))
    (equal (len (syn::dequote path1))
           (len (syn::dequote path2))))
   ((and (syn::consp path1)
         (syn::consp path2))
    (equal-len (syn::cdr path1)
               (syn::cdr path2)))
   ((and (syn::appendp path1)
         (syn::appendp path2))
    (and (equal-len (syn::arg 1 path1) (syn::arg 1 path2))
         (equal-len (syn::arg 2 path1) (syn::arg 2 path2))))
   (t (equal path1 path2))))

(defthm equal-len-identity
  (equal-len x x))

(defun syntax-quote-diverge (path1 path2)
  (declare (type t path1 path2))
  (if (consp path1)
      (cond
       ((syn::consp path2)
        (let ((v (syn::car path2)))
          (or (and (syn::quotep v)
                   (not (equal (car path1) (syn::dequote v)))
                   (syn::true))
              (syntax-quote-diverge (cdr path1) (syn::cdr path2)))))
       ((syn::quotep path2)
        (and (diverge path1 (syn::dequote path2))
             (syn::true)))
       (t nil))
    nil))

(defthm syntax-quote-diverge-implies-quote-true
  (implies
   (syntax-quote-diverge path1 path2)
   (equal (syntax-quote-diverge path1 path2) (syn::true))))

(defthm syntax-quote-diverge-implies-diverge
  (implies
   (syntax-quote-diverge x1 t2)
   (diverge x1 (syn::eval t2 a)))
  :hints (("goal" :in-theory (enable diverge-append-len-equal))))

(defun syntax-diverge (path1 path2)
  (declare (type t path1 path2))
  (cond
   ((syn::quotep path1)
    (syntax-quote-diverge (syn::dequote path1) path2))
   ((syn::quotep path2)
    (syntax-quote-diverge (syn::dequote path2) path1))
   ((and (syn::consp path1)
         (syn::consp path2))
    (let ((car1 (syn::car path1))
          (car2 (syn::car path2)))
      (if (and (syn::quotep car1)
               (syn::quotep car2)
               (not (equal (syn::dequote car1)
                           (syn::dequote car2))))
          (syn::true)
        (syntax-diverge (syn::cdr path1) (syn::cdr path2)))))
   ((and (syn::appendp path1)
         (syn::appendp path2))
    (let ((arg11 (syn::arg 1 path1))
          (arg12 (syn::arg 1 path2)))
      (and (equal arg11 arg12)
           (syntax-diverge (syn::arg 2 path1) (syn::arg 2 path2)))))
   (t nil)))

(defthm syntax-diverge-implies-diverge
  (implies
   (syntax-diverge t1 t2)
   (diverge (syn::eval t1 a) (syn::eval t2 a)))
  :hints (("goal" :in-theory (enable syn::open-nth diverge-append-len-equal))))

(defun remove-common-prefix (path1 path2)
  (declare (type t path1 path2))
  (if (and (consp path1)
           (consp path2))
      (if (equal (car path1) (car path2))
          (remove-common-prefix (cdr path1) (cdr path2))
        (mv path1 path2))
    (mv nil nil)))

(defthm remove-common-prefix-identity
  (and
   (equal (v0 (remove-common-prefix x x)) nil)
   (equal (v1 (remove-common-prefix x x)) nil)))

(defun syntax-quote-remove-common-prefix (path1 path2)
  (declare (type t path1 path2))
  (if (consp path1)
      (cond
       ((syn::consp path2)
        (let ((v (syn::car path2)))
          (if (and (syn::quotep v)
                   (equal (car path1) (syn::dequote v)))
              (syntax-quote-remove-common-prefix (cdr path1) (syn::cdr path2))
            (mv path1 path2))))
       ((syn::quotep path2)
        (met ((path1 path2) (remove-common-prefix path1 (syn::dequote path2)))
             (mv path1 (syn::enquote path2))))
       (t
        (mv path1 path2)))
    (mv path1 path2)))

(defthm pseudo-termp-syntax-quote-remove-common-prefix
  (implies
   (and
    (pseudo-termp y))
   (pseudo-termp (v1 (syntax-quote-remove-common-prefix x y))))
  :hints (("goal" :in-theory (enable pseudo-termp))))

(defthm diverge-remove-common-prefix-noop
  (equal (diverge (v0 (remove-common-prefix t1 t2))
                  (v1 (remove-common-prefix t1 t2)))
         (diverge t1 t2)))

(defthm syntax-quote-diverge-syntax-quote-remove-common-prefix-noop
  (equal (syntax-quote-diverge (v0 (syntax-quote-remove-common-prefix t1 t2))
                               (v1 (syntax-quote-remove-common-prefix t1 t2)))
         (syntax-quote-diverge t1 t2)))

(defun syntax-remove-common-prefix (path1 path2)
  (declare (type t path1 path2))
  (cond
   ((syn::quotep path1)
    (met ((path1 path2) (syntax-quote-remove-common-prefix (syn::dequote path1) path2))
         (mv (syn::enquote path1) path2)))
   ((syn::quotep path2)
    (met ((path2 path1) (syntax-quote-remove-common-prefix (syn::dequote path2) path1))
         (mv path1 (syn::enquote path2))))
   ((and (syn::consp path1)
         (syn::consp path2))
    (let ((car1 (syn::car path1))
          (car2 (syn::car path2)))
      (if (equal car1 car2)
          (syntax-remove-common-prefix (syn::cdr path1) (syn::cdr path2))
        (mv path1 path2))))
   ((and (syn::appendp path1)
         (syn::appendp path2))
    (let ((arg11 (syn::arg 1 path1))
          (arg12 (syn::arg 1 path2)))
      (if (equal arg11 arg12)
          (syntax-remove-common-prefix (syn::arg 2 path1) (syn::arg 2 path2))
        (mv path1 path2))))
   ((equal path1 path2)
    (mv (syn::nil) (syn::nil)))
   (t (mv path1 path2))))

(defthm pseudo-termp-syntax-remove-common-prefix
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp y))
   (and (pseudo-termp (v0 (syntax-remove-common-prefix x y)))
        (pseudo-termp (v1 (syntax-remove-common-prefix x y)))))
  :hints (("goal" :in-theory (enable pseudo-termp))))

(defthmd syntax-diverge-commute
  (equal (syntax-diverge x y)
         (syntax-diverge y x))
  :rule-classes ((:rewrite :loop-stopper ((y x)))))

(defthm syntax-diverge-syntax-remove-common-prefix-noop
  (equal (syntax-diverge (v0 (syntax-remove-common-prefix t1 t0))
                         (v1 (syntax-remove-common-prefix t1 t0)))
         (syntax-diverge t1 t0))
  :hints (("goal" :in-theory (e/d (syntax-diverge-commute)
                                  (;for efficiency:
                                   SYN::OPEN-LEN
                                   SYNTAX-QUOTE-DIVERGE)))))

(defun syntax-diverge-wrapper (term)
  (declare (type t term))
  (if (syn::funcall 'diverge 2 term)
      (let ((arg1 (syn::arg 1 term))
            (arg2 (syn::arg 2 term)))
        (met ((arg1 arg2) (syntax-remove-common-prefix arg1 arg2))
             (let ((hit (syntax-diverge arg1 arg2)))
               (if hit
                   hit
                 term))))
    term))

(defthm equal-len-implies-equal-len
  (implies
   (equal-len t1 t2)
   (iff (equal (len (syn::eval t1 a))
               (len (syn::eval t2 a)))
        t))
  :hints (("goal" :in-theory (enable syn::open-nth))))

(defthm syntax-diverge-implies-eval-commute
  (implies
   (syntax-diverge t1 t2)
   (equal (diverge (syn::eval t1 a) (syn::eval t2 a))
          (syn::eval (syntax-diverge t1 t2) a)))
  :hints (("goal" :in-theory (enable diverge-append-len-equal))))

(syn::extend-eval diverge-eval
 (
  (diverge x y)
  ))

(syn::defevthm diverge-eval syntax-diverge-implies-eval-commute
  (implies
   (syntax-diverge t1 t2)
   (equal (diverge (diverge-eval t1 a) (diverge-eval t2 a))
          (diverge-eval (syntax-diverge t1 t2) a))))

(defthmd *meta*-syntax-diverge
  (iff (diverge-eval term a)
       (diverge-eval (syntax-diverge-wrapper term) a))
  :hints (("goal" :in-theory (enable syn::open-nth)))
  :rule-classes ((:meta :trigger-fns (diverge))))

;; Syntactic tail domination ..

(defun true-p (x)
  (declare (type t x)
           (ignore x))
  t)

(defun remove-prefix (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (if (and (consp x)
               (equal (car prefix) (car x)))
          (remove-prefix (cdr prefix) (cdr x))
        (mv nil nil))
    (mv t x)))

(defun v0-remove-prefix (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (if (and (consp x)
               (equal (car prefix) (car x)))
          (v0-remove-prefix (cdr prefix) (cdr x))
        nil)
    t))

(defun v1-remove-prefix (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (if (and (consp x)
               (equal (car prefix) (car x)))
          (v1-remove-prefix (cdr prefix) (cdr x))
        nil)
    x))

(defthm v0-remove-prefix-reduction
  (equal (v0 (remove-prefix prefix x))
         (v0-remove-prefix prefix x)))

(defcong list::equiv equal
  (v0-remove-prefix prefix x) 2)

(defthm v1-remove-prefix-reduction
  (equal (v1 (remove-prefix prefix x))
         (v1-remove-prefix prefix x)))

(defcong list::equiv list::equiv
  (v1-remove-prefix prefix x) 2)

(defthm list-fix-v1-remove-prefix
  (equal (list::fix (v1-remove-prefix prefix x))
         (v1-remove-prefix prefix (list::fix x))))

(defthm v0-remove-prefix-append
  (equal (v0-remove-prefix (append x y) z)
         (and (v0-remove-prefix x z)
              (v0-remove-prefix y (v1-remove-prefix x z)))))

(defthm v1-remove-prefix-append
  (equal (v1-remove-prefix (append x y) z)
         (and
          (v0-remove-prefix x z)
          (v1-remove-prefix y (v1-remove-prefix x z)))))

(defthm not-v0-implies-nil-v1-remove-prefix
  (implies
   (not (v0-remove-prefix x y))
   (equal (v1-remove-prefix x y) nil)))

#|
(defignore syntax-quote-remove-prefix bag::a (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (cond
       ((syn::consp x)
        (let ((v (syn::car x)))
          (if (and (syn::quotep v)
                   (equal (car pefix) (syn::dequote v)))
              (syntax-quote-x-remove-prefix (cdr prefix) (syn::cdr x))
            (mv nil nil))))
       ((syn::quotep x)
        (remove-prefix prefix (syn::dequote x)))
       (t (mv nil nil)))
    (mv (syn::null x) nil)))

(defirrelevant syntax-quote-remove-prefix 2 bag::a (px prefix x)
  )

(defignore v0-syntax-quote-remove-prefix bag::a (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (cond
       ((syn::consp x)
        (let ((v (syn::car x)))
          (if (and (syn::quotep v)
                   (equal (car pefix) (syn::dequote v)))
              (v0-syntax-quote-x-remove-prefix (cdr prefix) (syn::cdr x))
            nil)))
       ((syn::quotep x)
        (v0-remove-prefix prefix (syn::dequote x)))
       (t nil))
    (syn::null x)))

(defirrelevant v0-syntax-quote-remove-prefix 2 bag::a (px prefix x)
  )

(defignore v1-syntax-quote-remove-prefix bag::a (prefix x)
  (declare (type t prefix x))
  (if (consp prefix)
      (cond
       ((syn::consp x)
        (let ((v (syn::car x)))
          (if (and (syn::quotep v)
                   (equal (car pefix) (syn::dequote v)))
              (v1-syntax-quote-x-remove-prefix (cdr prefix) (syn::cdr x))
            nil)))
       ((syn::quotep x)
        (v1-remove-prefix prefix (syn::dequote x)))
       (t nil))
    nil))

(defirrelevant v1-syntax-quote-remove-prefix 2 bag::a (px prefix x)
  )

(defthm v0-to-v0-syntax-quote-remove-prefix
  (equal (v0 (syntax-quote-remove-prefix prefix x))
         (v0-syntax-quote-remove-prefix prefix x)))

(defthm v1-to-v1-syntax-quote-remove-prefix
  (equal (v1 (syntax-quote-remove-prefix prefix x))
         (v1-syntax-quote-remove-prefix prefix x)))

(defcong list::equiv equal
  (v0-syntax-remove-prefix prefix x) 2)

(defcong list::equiv list::equiv
  (v1-syntax-quote-remove-prefix prefix x) 2)

(defthm list-fix-v1-syntax-quote-remove-prefix
  (equal (list::fix (v1-syntax-quote-remove-prefix prefix x))
         (v1-syntax-quote-remove-prefix prefix (list::fix x))))

(defthm not-v0-implies-nil-v1-syntax-quote-remove-prefix
  (implies
   (not (v0-syntax-quote-remove-prefix x y))
   (equal (v1-syntax-quote-remove-prefix x y) nil)))

#+joe
(defignore syntax-remove-prefix bag::a (prefix x)
  (declare (type t prefix x))
  (cond
   ((syn::consp prefix)
    (if (and (syn::consp x)
             (equal (syn::car prefix) (syn::car x)))
        (syntax-remove-prefix (syn::cdr prefix) (syn::cdr x))
      (mv nil nil)))
   ((syn::appendp prefix)
    (if (and (syn::appendp x)
             (equal (syn::arg 1 prefix) (syn::arg 1 x)))
        (syntax-remove-prefix (syn::arg 2 prefix) (syn::arg 2 x))
      (mv nil nil)))
   ((syn::quotep prefix)
    (syntax-quote-remmove-prefix (syn::dequote prefix) x))
   (t (mv nil nil))))

|#

(defun tail-p (x y)
  (declare (type t x y))
  (or (list::equiv x y)
      (and (consp y)
           (tail-p x (cdr y)))))

(defthm v1-remove-prefix-is-tail-x
  (implies
   (v0-remove-prefix prefix x)
   (tail-p (v1-remove-prefix prefix x) x)))

(defthm tail-p-implies
  (implies
   (tail-p x y)
   (<= (len x) (len y)))
  :rule-classes (:linear :rewrite))






#+joe
(defignore syntax-alist-quote-remove-prefix bag::a (prefix x)
  (if (consp x)
      (if (consp prefix)
          (let ((key (caar prefix))
                (val (cdar prefix)))
            (case key
                  (:cons
                   (if (equal (car x) val)
                       (syntax-alist-quote-remove-prefix prefix x)
                     (mv nil nil)))
                  (:append
                   (met ((hit rest) (syntax-
                        (equal (syn::arg 1 x) val)
                        (syntax-prefixed-tail-dominator-p (syn::arg 2 x) (cdr prefix) y)))
                  (:quote
                   (if (syn::quotep y)
                       (prefixed-tail-dominator-p (syn::dequote x) val (syn::dequote y))
                     (syntax-quote-quote-prefixed-tail-dominator-p x val y)))
                  (t nil)))
        x)
    nil))))

#|

;; DAG - I have removed this line of thinking.  It just doesn't make any sense
;; .. if x is a quoted constant, then the prefix would have to be quoted as
;; well.

(defignore syntax-quote-remove-prefix bag::a (prefix x)
  (declare (type t prefix x))
  (cond
   ((syn::consp prefix)
    (let ((v (syn::car prefix)))
      (if (and (syn::quotep v)
               (consp x)
               (equal (car x) (syn::dequote v)))
          (syntax-quote-remove-prefix (syn::cdr prefix) (cdr x))
        (mv nil nil))))
   ((syn::appendp prefix)
    (met ((hit rest) (syntax-quote-remove-prefix (syn::arg 1 prefix) x))
         (if (not hit) (mv nil nil)
           (syntax-quote-remove-prefix (syn::arg 2 prefix) rest))))
   ((syn::quotep prefix)
    (remove-prefix (syn::dequote prefix) x))
   (t (mv nil nil))))

(defirrelevant syntax-quote-remove-prefix 2 bag::a (prefix x)
  )

(defthmd list-fix-commutes-over-syntax-quote-remove-prefix
  (implies
   (syntaxp (symbolp x))
   (and
    (equal (list::fix (v1 (syntax-quote-remove-prefix prefix x)))
           (v1 (syntax-quote-remove-prefix prefix (list::fix x))))
    (equal (v0 (syntax-quote-remove-prefix prefix x))
           (v0 (syntax-quote-remove-prefix prefix (list::fix x)))
           ))))

(defignore v0-syntax-quote-remove-prefix bag::a (prefix x)
  (declare (type t prefix x))
  (cond
   ((syn::consp prefix)
    (let ((v (syn::car prefix)))
      (if (and (syn::quotep v)
               (consp x)
               (equal (car x) (syn::dequote v)))
          (v0-syntax-quote-remove-prefix (syn::cdr prefix) (cdr x))
        nil)))
   ((syn::appendp prefix)
    (met ((hit rest) (syntax-quote-remove-prefix (syn::arg 1 prefix) x))
         (if (not hit) nil
           (v0-syntax-quote-remove-prefix (syn::arg 2 prefix) rest))))
   ((syn::quotep prefix)
    (v0-remove-prefix (syn::dequote prefix) x))
   (t nil)))

(defirrelevant v0-syntax-quote-remove-prefix 1 bag::a (prefix x)
  :hints (("goal" :in-theory (enable syntax-quote-remove-prefix-irrelevant))))

(defignore v1-syntax-quote-remove-prefix bag::a (prefix x)
  (declare (type t prefix x))
  (cond
   ((syn::consp prefix)
    (let ((v (syn::car prefix)))
      (if (and (syn::quotep v)
               (consp x)
               (equal (car x) (syn::dequote v)))
          (v1-syntax-quote-remove-prefix (syn::cdr prefix) (cdr x))
        nil)))
   ((syn::appendp prefix)
    (met ((hit rest) (syntax-quote-remove-prefix (syn::arg 1 prefix) x))
         (if (not hit) nil
           (v1-syntax-quote-remove-prefix (syn::arg 2 prefix) rest))))
   ((syn::quotep prefix)
    (v1-remove-prefix (syn::dequote prefix) x))
   (t nil)))

(defirrelevant v1-syntax-quote-remove-prefix 1 bag::a (prefix x)
  :hints (("goal" :in-theory (enable syntax-quote-remove-prefix-irrelevant))))

(defthm v0-syntax-quote-remove-prefix-reduction
  (equal (v0 (syntax-quote-remove-prefix prefix x))
         (v0-syntax-quote-remove-prefix prefix x)))

(defthm v1-syntax-quote-remove-prefix-reduction
  (equal (v1 (syntax-quote-remove-prefix prefix x))
         (v1-syntax-quote-remove-prefix prefix x)))

(defthmd vx-list-fix-commutes-over-syntax-quote-remove-prefix
  (implies
   (syntaxp (symbolp x))
   (and
    (equal (list::fix (v1-syntax-quote-remove-prefix prefix x))
           (v1-syntax-quote-remove-prefix prefix (list::fix x)))
    (equal (v0-syntax-quote-remove-prefix prefix x)
           (v0-syntax-quote-remove-prefix prefix (list::fix x)))))
  :hints (("goal" :use (:instance list-fix-commutes-over-syntax-quote-remove-prefix))))

(defcong list::equiv list::equiv
  (v1-syntax-quote-remove-prefix-fn a prefix x) 3
  :hints (("goal" :in-theory '(list::equiv
                               vx-list-fix-commutes-over-syntax-quote-remove-prefix
                               ))))

(defcong list::equiv equal
  (v0-syntax-quote-remove-prefix-fn a prefix x) 3
  :hints (("goal" :in-theory '(list::equiv
                               vx-list-fix-commutes-over-syntax-quote-remove-prefix
                               ))))

(defthm not-v0-implies-nil-v1-syntax-quote-remove-prefix
  (implies
   (not (v0-syntax-quote-remove-prefix prefix x))
   (equal (v1-syntax-quote-remove-prefix prefix x) nil)))

(defthm v0-syntax-quote-remove-prefix-implies-v2-cong
  (implies
   (v0-syntax-quote-remove-prefix prefix x)
   (and (list::equiv (v1-syntax-quote-remove-prefix prefix x)
                         (v1-remove-prefix (syn::eval prefix bag::a) x))
        (v0-remove-prefix (syn::eval prefix bag::a) x)))
  :hints (("goal" :induct (syntax-quote-remove-prefix prefix x))))

#+joe
(defignore syntax-remove-term (term x)
  ..)

#+joe
(defignore syntax-remove-prefix (prefix x)
  )
|#

(defignore syntax-quote-dominates-p bag::a (x y)
  (declare (type t x y)
           (xargs :measure (acl2-count y)))
  (if (consp x)
      (cond
       ((syn::consp y)
        (let ((v (syn::car y)))
          (and
           (syn::quotep v)
           (equal (car x) (syn::dequote v))
           (syntax-quote-dominates-p (cdr x) (syn::cdr y)))))
       #+joe
       ((syn::appendp y)
        (met ((hit rest) (syntax-quote-remove-prefix x (syn::arg 1 y) x))
             (and hit (syntax-quote-dominates-p rest (syn::arg 2 y)))))
       ((syn::quotep y)
        (dominates x (syn::dequote y)))
       (t
        nil))
    t))

(defirrelevant syntax-quote-dominates-p 1 bag::a (x y)
  :hints (("goal" :in-theory (enable ;v0-syntax-quote-remove-prefix-irrelevant
                                     ;v1-syntax-quote-remove-prefix-irrelevant
                                     ))))

(defthmd dominates-append-2
  (equal (dominates x (append y z))
         (or (dominates x y)
             (and
              (v0-remove-prefix y x)
              (dominates (v1-remove-prefix y x) z))))
  :hints (("goal" :in-theory (enable dominates))))

(defthm syntax-quote-dominates-implies-dominates
  (implies
   (syntax-quote-dominates-p x y)
   (dominates x (syn::eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable dominates
                                     dominates-append-2))))

(defignore show-syntax-consp-from-alist bag::a (term type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist)
           (xargs :guard-hints (("goal" :in-theory (enable acl2::type-alistp)))))
  (if (endp type-alist)
      nil
    (let ((entry (car type-alist)))
      (or (syn::ts-consp term entry)
          (show-syntax-consp-from-alist term (cdr type-alist))))))

(defirrelevant show-syntax-consp-from-alist 1 bag::a (term type-alist)
  )

(defignore hyp-for-show-syntax-consp-from-alist bag::a (term type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist)
           (xargs :guard-hints (("goal" :in-theory (enable acl2::type-alistp)))))
  (if (endp type-alist)
      nil
    (let ((entry (car type-alist)))
      (or (and (syn::ts-consp term entry)
               `(consp ,term))
          (hyp-for-show-syntax-consp-from-alist term (cdr type-alist))))))

(defirrelevant hyp-for-show-syntax-consp-from-alist 1 bag::a (term type-alist)
  )

(defthm pseudo-termp-hyp-for-show-syntax-consp-from-alist
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-consp-from-alist term type-alist))))

(defthm show-syntax-consp-from-alist-to-hyp-for
  (iff (show-syntax-consp-from-alist term type-alist)
       (hyp-for-show-syntax-consp-from-alist term type-alist)))

(defthm show-syntax-consp-from-alist-works
  (implies
   (and
    (hyp-for-show-syntax-consp-from-alist x type-alist)
    (syn::eval (hyp-for-show-syntax-consp-from-alist x type-alist) bag::a))
   (consp (syn::eval x bag::a)))
  :rule-classes (:rewrite :forward-chaining))

;; DAG -- This could be improved by checking each append term for
;; consp.

(defignored show-syntax-consp bag::a (term type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist))
  (or (syn::consp-rec term)
      (show-syntax-consp-from-alist term type-alist)))

(defirrelevant show-syntax-consp 1 bag::a (term type-alist)
  :hints (("goal" :in-theory (enable
                              show-syntax-consp
                              hyp-for-show-syntax-consp-from-alist-irrelevant
                              ))))

(defignored hyp-for-show-syntax-consp bag::a (term type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist))
  (if (syn::consp-rec term) (syn::true)
    (hyp-for-show-syntax-consp-from-alist term type-alist)))

(defirrelevant hyp-for-show-syntax-consp 1 bag::a (term type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-syntax-consp
                              hyp-for-show-syntax-consp-from-alist-irrelevant
                              ))))

(defthm show-syntax-consp-to-hyp-for
  (iff (show-syntax-consp term type-alist)
       (hyp-for-show-syntax-consp term type-alist))
  :hints (("goal" :in-theory (enable
                              show-syntax-consp
                              hyp-for-show-syntax-consp
                              ))))

(defthm pseudo-termp-hyp-for-show-syntax-consp
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-consp term type-alist)))
  :hints (("goal" :in-theory (enable
                              hyp-for-show-syntax-consp
                              ))))

(defthm show-syntax-consp-works
  (implies
   (and
    (hyp-for-show-syntax-consp term type-alist)
    (syn::eval (hyp-for-show-syntax-consp term type-alist) bag::a))
   (consp (syn::eval term bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-syntax-consp
                              ))))

(defignore show-syntax-dominates-p bag::a (flg x y type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp x)
    (and (syn::consp y)
         (equal (syn::car x) (syn::car y))
         (show-syntax-dominates-p t (syn::cdr x) (syn::cdr y) type-alist)))
   ((syn::appendp x)
    (and (syn::appendp y)
         (equal (syn::arg 1 x) (syn::arg 1 y))
         (show-syntax-dominates-p (or flg (show-syntax-consp (syn::arg 1 x) type-alist))
                                  (syn::arg 2 x) (syn::arg 2 y) type-alist)))
   ((syn::quotep x)
    (let ((x (syn::dequote x)))
      (and (or flg (consp x)) (syntax-quote-dominates-p x y))))
   ((syn::appendp y)
    (and (equal x (syn::arg 1 y))
         (or flg (show-syntax-consp x type-alist))))
   (t
    (and
     (equal x y)
     (or flg (show-syntax-consp x type-alist))))))

(defcong iff iff
  (show-syntax-dominates-p-fn a flg x y type-alist)
  2)

(defirrelevant show-syntax-dominates-p 1 bag::a (flg x y type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-syntax-consp-irrelevant
                              show-syntax-consp-irrelevant
                              syntax-quote-dominates-p-irrelevant
                              ))))

(defignore hyp-for-show-syntax-dominates-p bag::a (flg x y type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp x)
    (and (syn::consp y)
         (equal (syn::car x) (syn::car y))
         (hyp-for-show-syntax-dominates-p t (syn::cdr x) (syn::cdr y) type-alist)))
   ((syn::appendp x)
    (and (syn::appendp y)
         (equal (syn::arg 1 x) (syn::arg 1 y))
         (let ((hyp (if flg (syn::true)
                      (hyp-for-show-syntax-consp (syn::arg 1 x) type-alist))))
           (if hyp (syn::and hyp
                             (hyp-for-show-syntax-dominates-p t (syn::arg 2 x) (syn::arg 2 y) type-alist))
             (hyp-for-show-syntax-dominates-p nil (syn::arg 2 x) (syn::arg 2 y) type-alist)))))
   ((syn::quotep x)
    (let ((x (syn::dequote x)))
      (and (or flg (consp x))
           (syntax-quote-dominates-p x y)
           (syn::true))))
   ((syn::appendp y)
    (and (equal x (syn::arg 1 y))
         (or (and flg (syn::true))
             (hyp-for-show-syntax-consp x type-alist))))
   (t
    (and (equal x y)
         (or (and flg (syn::true))
             (hyp-for-show-syntax-consp x type-alist))))))

(defcong iff iff
  (hyp-for-show-syntax-dominates-p-fn a flg x y type-alist)
  2)

(defirrelevant hyp-for-show-syntax-dominates-p 1 bag::a (flg x y type-alist)
  :hints (("goal" :in-theory (enable
                       hyp-for-show-syntax-consp-irrelevant
                       syntax-quote-dominates-p-irrelevant
                       ))))

(defthm show-syntax-dominates-p-to-hyp-for
  (iff (show-syntax-dominates-p flg x y type-alist)
       (hyp-for-show-syntax-dominates-p flg x y type-alist))
  :hints (("goal" :induct (hyp-for-show-syntax-dominates-p-fn bag::a flg x y type-alist))))

(defthm pseudo-termp-hyp-for-show-syntax-dominates-p
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-dominates-p flg x y type-alist)))
  :hints (("goal" :in-theory (enable syn::open-nth))))

(defun contains (symbol term)
  (declare (type t symbol term))
  (if (consp term)
      (if (consp (car term))
          (or (contains symbol (car term))
              (contains symbol (cdr term)))
        (or (equal symbol (car term))
            (contains symbol (cdr term))))
    (equal symbol term)))

(defthmd syntax-domination-implies-domination
  (implies
   (and
    (hyp-for-show-syntax-dominates-p flg x y type-alist)
    (syntaxp (contains 'syn::eval logical-x))
    (equal (syn::eval x bag::a) logical-x))
   (dominates logical-x (syn::eval y bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth))))

(defthm syntax-domination-implies-domination-helper
  (implies
   (hyp-for-show-syntax-dominates-p flg x y type-alist)
   (dominates (syn::eval x bag::a) (syn::eval y bag::a)))
  :hints (("goal" :in-theory (enable syntax-domination-implies-domination))))

(defthmd syntax-domination-implies-consp
  (implies
   (and
    (hyp-for-show-syntax-dominates-p flg x y type-alist)
    (syn::eval (hyp-for-show-syntax-dominates-p flg x y type-alist) bag::a)
    (syntaxp (contains 'syn::eval logical-x))
    (not flg)
    (equal logical-x (syn::eval x bag::a)))
   (consp logical-x))
  :hints (("goal" :in-theory (enable SYN::CONJOIN syn::open-nth))))

(defun tail-dominates-p (x y)
  (declare (type t x y))
  (cond
   ((consp x)
    (or (dominates x y)
        (tail-dominates-p (cdr x) y)))
   (t nil)))

(defun tail-dominates (x y)
  (declare (type t x y))
  (cond
   ((consp x)
    (met ((hit prefix) (tail-dominates (cdr x) y))
         (let ((dom (dominates x y)))
           (if (or hit dom)
               (mv t (cons (cons dom (car x)) prefix))
             (mv nil nil)))))
   (t (mv nil nil))))

(defthm booleanp-v0-tail-dominates
  (booleanp (v0 (tail-dominates x y))))

(defmacro wf-prefix (prefix)
  `(alistp ,prefix))

(defthm wf-prefix-v1-tail-dominates
  (wf-prefix (v1 (tail-dominates val v))))

(defthm v0-tail-dominates-to-tail-dominates-p
  (equal (v0 (tail-dominates x y))
         (tail-dominates-p x y)))

(defun prefixes (prefix)
  (declare (type (satisfies alistp) prefix))
  (if (consp prefix)
      (let ((list (list::map-cons (cdar prefix) (prefixes (cdr prefix)))))
        (if (caar prefix) (cons nil list)
          list))
    nil))

;; jcd removing this for list::map-cons
;; (defthm non-consp-memberp-map-cons
;;   (implies
;;    (not (consp x))
;;    (not (list::memberp x (map-cons a z)))))

(defthm consp-prefixes-v1-tail-dominates
  (implies
   (v0 (tail-dominates x y))
   (consp (prefixes (v1 (tail-dominates x y))))))

(defun true-listp-list (list)
  (declare (type t list))
  (if (consp list)
      (and (true-listp (car list))
           (true-listp-list (cdr list)))
    (null list)))

(defthm true-listp-car-true-listp-list
  (implies
   (true-listp-list list)
   (true-listp (car list))))

(defthm true-listp-list-prefixes
  (true-listp-list (prefixes list)))

(defun prefixed-tail-dominator-p (x prefix y)
  (declare (type t x prefix y))
  (and (consp x)
       (if (consp prefix)
           (and (equal (car prefix) (car x))
                (prefixed-tail-dominator-p (cdr x) (cdr prefix) y))
         (dominates x y))))

(defthm not-consp-y-not-prefixed-tail-dominator-p
  (implies
   (not (consp y))
   (not (prefixed-tail-dominator-p x prefix y))))

(defun list-prefixed-tail-dominator-p (x prefixes y)
  (declare (type t x prefixes y))
  (if (consp prefixes)
      (or (prefixed-tail-dominator-p x (car prefixes) y)
          (list-prefixed-tail-dominator-p x (cdr prefixes) y))
    nil))

(defthm not-consp-y-not-list-prefixed-tail-dominator-p
  (implies
   (not (consp y))
   (not (list-prefixed-tail-dominator-p x prefix y))))

(defthm not-consp-x-not-list-prefixed-tail-dominator-p
  (implies
   (not (consp x))
   (not (list-prefixed-tail-dominator-p x prefix y))))

(defthm list-prefixed-tail-dominator-p-from-memberp-prefixed-tail-dominator-p
  (implies
   (and
    (prefixed-tail-dominator-p x prefix y)
    (list::memberp prefix prefixes))
   (list-prefixed-tail-dominator-p x prefixes y)))

#+joe
(defthm list-prefixed-tail-dominator-p-from-memberp-prefixed-tail-dominator-membership
  (implies
   (and
    (prefixed-tail-dominator-p x prefix y)
    (list::memberp prefix prefixes))
   (list::memberp prefix (list-prefixed-tail-dominator-p x prefixes y))))

(defthm prefixed-tail-dominator-p-implies-len
  (implies
   (prefixed-tail-dominator-p x prefix y)
   (< (len prefix) (len x)))
  :rule-classes (:forward-chaining))

(defthm consp-dominates-implies-tail-dominates-p
  (implies
   (and
    (consp x)
    (dominates x y))
   (tail-dominates-p x y)))

(defthm not-consp-not-tail-dominates-p
  (implies
   (not (consp y))
   (not (tail-dominates-p x y))))

(defthm not-tail-dominates-p-implies-nil-prefix
  (implies
   (not (tail-dominates-p x y))
   (equal (v1 (tail-dominates x y)) nil)))

(defthm tail-dominates-append
  (implies
   (tail-dominates-p x z)
   (tail-dominates-p (append y x) z))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (append y x))))

(defun wf-syntax-prefix (prefix)
  (declare (type t prefix))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (and (consp entry)
             (case (car entry)
                   (:cons
                    (wf-syntax-prefix (cdr prefix)))
                   (:append
                    (wf-syntax-prefix (cdr prefix)))
                   (:quote
                    (and (null (cdr prefix))
                         (true-listp (cdr entry))))
                   (t
                    nil))))
    (null prefix)))

(defthm wf-syntax-prefix-implies-true-listp
  (implies
   (wf-syntax-prefix prefix)
   (true-listp prefix))
  :rule-classes (:rewrite :forward-chaining))

(defun s2l (prefix a)
  (declare (type (satisfies wf-syntax-prefix) prefix))
  (if (consp prefix)
      (let ((entry (car prefix)))
        (case (car entry)
              (:cons
               (cons (syn::eval (cdr entry) a)
                     (s2l (cdr prefix) a)))
              (:append
               (list::appendx (syn::eval (cdr entry) a)
                              (s2l (cdr prefix) a)))
              (:quote
               (cdr entry))
              (t
               nil)))
    nil))

(defthm true-listp-s2l
  (implies
   (wf-syntax-prefix pre)
   (true-listp (s2l pre a))))

(defignore syntax-quote-tail-dominates bag::a (x y)
  (declare (type t x y))
  (if (consp x)
      (if (syntax-quote-dominates-p x y)
          (mv t nil)
        (met ((hit prefix) (syntax-quote-tail-dominates (cdr x) y))
             (if hit (mv t (cons (cons :cons (syn::enquote (car x))) prefix))
               (mv nil nil))))
    (mv nil nil)))

(defirrelevant syntax-quote-tail-dominates 1 bag::a (x y)
  :hints (("goal" :in-theory (enable syntax-quote-dominates-p-irrelevant
                                     ))))

(defthm wf-syntax-prefix-syntax-quote-tail-dominates
  (wf-syntax-prefix (v1 (syntax-quote-tail-dominates x y))))

(defthm syntax-quote-tail-dominates-implies-tail-dominates
  (implies
   (v0 (syntax-quote-tail-dominates x y))
   (tail-dominates-p x (syn::eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable syntax-domination-implies-consp
                                     syntax-domination-implies-domination))))

(defthmd not-consp-membership-implies-dominates
  (implies (and (not (consp pre))
                (list::memberp pre (prefixes (v1 (tail-dominates x y)))))
           (dominates x y)))

;; jcd removing this for list::map-cons
;; (defthm memberp-x-map-cons
;;   (equal (list::memberp x (map-cons a y))
;;          (and (consp x)
;;               (equal (car x) a)
;;               (list::memberp (cdr x) y))))

(defthmd memberp-not-consp-prefixes
  (implies
   (not (consp pre))
   (equal (list::memberp pre (prefixes (val 1 (tail-dominates x y))))
          (and (null pre) (consp x) (dominates x y))))
  :hints (("goal" :in-theory (enable list::memberp
                                     not-consp-membership-implies-dominates)
           :expand (tail-dominates x y))))

(defthm s2l-membership-in-syntax-quote-tail-dominates
  (implies
   (v0 (syntax-quote-tail-dominates x y))
   (list::memberp (s2l (v1 (syntax-quote-tail-dominates x y)) bag::a)
                 (prefixes (v1 (tail-dominates x (syn::eval y bag::a))))))
  :hints (("goal" :induct (syntax-quote-tail-dominates-fn bag::a x y))
          (and acl2::stable-under-simplificationp
               `(:in-theory
                 (enable
                  memberp-not-consp-prefixes
                  syntax-domination-implies-domination
                  syntax-domination-implies-consp
                  memberp-not-consp-prefixes
                  )))))

(defignore show-syntax-tail-dominates bag::a (x y type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp x)
    (if (show-syntax-dominates-p t x y type-alist)
        (mv t nil)
      (met ((hit prefix) (show-syntax-tail-dominates (syn::cdr x) y type-alist))
           (if hit (mv t (cons (cons :cons (syn::car x)) prefix))
             (mv nil nil)))))
   ((syn::appendp x)
    (if (show-syntax-dominates-p nil x y type-alist)
        (mv t nil)
      (met ((hit prefix) (show-syntax-tail-dominates (syn::arg 2 x) y type-alist))
           (if hit (mv t (cons (cons :append (syn::arg 1 x)) prefix))
             (mv nil nil)))))
   ((syn::quotep x)
    (if (syn::quotep y)
        (met ((hit prefix) (tail-dominates (syn::dequote x) (syn::dequote y)))
             (if hit (mv t (list (cons :quote (car (prefixes prefix)))))
               (mv nil nil)))
      (syntax-quote-tail-dominates (syn::dequote x) y)))
   (t
    (mv (show-syntax-dominates-p nil x y type-alist) nil))))

(defirrelevant show-syntax-tail-dominates 2 bag::a (x y type-alist)
  :hints (("goal" :in-theory (enable
                              syntax-quote-tail-dominates-irrelevant
                              show-syntax-dominates-p-irrelevant
                              hyp-for-show-syntax-dominates-p-irrelevant
                              ))))

(defignore hyp-for-show-syntax-tail-dominates bag::a (x y type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp x)
    (or (hyp-for-show-syntax-dominates-p t x y type-alist)
        (hyp-for-show-syntax-tail-dominates (syn::cdr x) y type-alist)))
   ((syn::appendp x)
    (or (hyp-for-show-syntax-dominates-p nil x y type-alist)
        (hyp-for-show-syntax-tail-dominates (syn::arg 2 x) y type-alist)))
   ((syn::quotep x)
    (if (syn::quotep y)
        (and (tail-dominates-p (syn::dequote x) (syn::dequote y))
             (syn::true))
      (met ((hit rest) (syntax-quote-tail-dominates (syn::dequote x) y))
           (declare (ignore rest))
           (and hit
                (syn::true)))))
   (t
    (hyp-for-show-syntax-dominates-p nil x y type-alist))))

(defirrelevant hyp-for-show-syntax-tail-dominates 1 bag::a (x y type-alist)
  :hints (("goal" :in-theory (enable
                              syntax-quote-tail-dominates-irrelevant
                              hyp-for-show-syntax-dominates-p-irrelevant
                              ))))

(defthm show-syntax-tail-dominates-to-hyp-for
  (iff (v0 (show-syntax-tail-dominates x y type-alist))
       (hyp-for-show-syntax-tail-dominates x y type-alist)))

(defthm pseduo-termp-hyp-for-show-syntax-tail-dominates
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-tail-dominates x y type-alist))))

(defthm wf-syntax-prefix-show-syntax-tail-dominates
  (wf-syntax-prefix (v1 (show-syntax-tail-dominates x y type-alist))))

#+joe
(defthm tail-dominates-p-from-dominates
  (implies
   (dominates x y)
   (tail-dominates-p x y)))

(defthm show-syntax-tail-dominates-implies-tail-dominates
  (implies
   (and
    (hyp-for-show-syntax-tail-dominates x y type-alist)
    (syn::eval (hyp-for-show-syntax-tail-dominates x y type-alist) bag::a))
   (tail-dominates-p (syn::eval x bag::a) (syn::eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable syn::open-nth
                                     syn::conjoin
                                     syntax-domination-implies-consp
                                     syntax-domination-implies-domination))))

(defthm memberp-prefixes-implies-memberp-prefixes-append
  (implies
   (list::memberp list (prefixes (v1 (tail-dominates x y))))
   (list::memberp (append z list) (prefixes (v1 (tail-dominates (append z x) y)))))
  :hints (("goal" :induct (len z)
           :in-theory (enable binary-append))))

(defthm s2l-membership-in-prefixes
  (implies
   (and
    (hyp-for-show-syntax-tail-dominates x y type-alist)
    (syn::eval (hyp-for-show-syntax-tail-dominates x y type-alist) bag::a))
   (list::memberp (s2l (v1 (show-syntax-tail-dominates x y type-alist)) bag::a)
                  (prefixes (v1 (tail-dominates (syn::eval x bag::a) (syn::eval y bag::a))))))
  :hints (("goal"
           :in-theory (e/d
                       (syn::open-nth
                        syn::conjoin
                        syn::open-len

                        syntax-domination-implies-domination
                        syntax-domination-implies-consp
                        memberp-not-consp-prefixes

                        )
                       ( ;jcd (:REWRITE CONSP-NON-NULL-TRUE-LIST)
                        (:REWRITE WF-SYNTAX-PREFIX-IMPLIES-TRUE-LISTP)
                        (:DEFINITION TRUE-LISTP)
                        (:REWRITE SYN::CONSP-REC-IMPLIES-CONSP)
                        (:DEFINITION SYN::CONSP-REC)
                        ;(:REWRITE list::EQUAL-OF-BOOLEANS-REWRITE)
                        (:rewrite acl2::equal-booleans-reducton)
                        (:REWRITE list::EQUAL-CAR-DIFFERENTIAL)
                        (:REWRITE list::CONSP-APPEND)
                        (:REWRITE list::CDR-APPEND)
                        (:REWRITE list::APPEND-OF-NON-CONSP-ONE)
                        (:TYPE-PRESCRIPTION SYN::CONSP-REC)
                        SYNTAX-QUOTE-DOMINATES-P-FN
                        TAIL-DOMINATES-P
                        SYNTAX-QUOTE-TAIL-DOMINATES-FN
                        DOMINATES-SAME-LEN-CHEAP

                        ))
           :induct (show-syntax-tail-dominates-fn bag::a x y type-alist))
          ))

(defignore syntax-quote-quote-prefixed-tail-dominator-p bag::a (x prefix y)
  (declare (type t x prefix y))
  (and (consp x)
       (if (consp prefix)
           (and (equal (car prefix) (car x))
                (syntax-quote-quote-prefixed-tail-dominator-p (cdr x) (cdr prefix) y))
         (syntax-quote-dominates-p x y))))

#+joe
(defignore syntax-quote-alist-prefixed-tail-dominator-p bag::a (x prefix y)
  (declare (type (satisfies wf-syntax-prefix) prefix))
  (and (consp x)
       (if (consp prefix)
           (let ((key (caar prefix))
                 (val (cdar prefix)))
             (case key
                   (:cons
                    (and (equal (car x) val)
                         (syntax-quote-alist-prefixed-tail-dominator-p (cdr x) (cdr prefix) y)))
                   (:append
                    (and (syn::appendp x)
                         (equal (syn::arg 1 x) val)
                         (syntax-prefixed-tail-dominator-p (syn::arg 2 x) (cdr prefix) y)))
                   (:quote
                    (if (syn::quotep y)
                        (prefixed-tail-dominator-p (syn::dequote x) val (syn::dequote y))
                      (syntax-quote-quote-prefixed-tail-dominator-p x val y)))
                   (t nil)))
         (syntax-quote-dominates-p x y))))

(defirrelevant syntax-quote-quote-prefixed-tail-dominator-p 1 bag::a (x prefix y)
  :hints (("goal" :in-theory (enable syntax-quote-dominates-p-irrelevant))))

(defthm syntax-quote-quote-prefixed-tail-dominator-p-implies-prefixed-tail-dominator
  (implies
   (syntax-quote-quote-prefixed-tail-dominator-p x prefix y)
   (prefixed-tail-dominator-p x prefix (syn::eval y bag::a)))
  :hints (("goal" :in-theory (enable syntax-domination-implies-consp
                                     syntax-domination-implies-domination)))
  :rule-classes (:rewrite :forward-chaining))

(defignore show-syntax-prefixed-tail-dominator-p bag::a (x prefix y type-alist)
  (declare (type (satisfies wf-syntax-prefix) prefix)
           (type (satisfies acl2::type-alistp) type-alist))
  (if (consp prefix)
      (let ((key (caar prefix))
            (val (cdar prefix)))
        (case key
              (:cons
               (and (syn::consp x)
                    (equal (syn::car x) val)
                    (show-syntax-prefixed-tail-dominator-p (syn::cdr x) (cdr prefix) y type-alist)))
              (:append
               (and (syn::appendp x)
                    (equal (syn::arg 1 x) val)
                    (show-syntax-prefixed-tail-dominator-p (syn::arg 2 x) (cdr prefix) y type-alist)))
              (:quote
               (and (syn::quotep x)
                    (if (syn::quotep y)
                        (prefixed-tail-dominator-p (syn::dequote x) val (syn::dequote y))
                      (syntax-quote-quote-prefixed-tail-dominator-p (syn::dequote x) val y))))
              (t nil)))
    (show-syntax-dominates-p nil x y type-alist)))

(defirrelevant show-syntax-prefixed-tail-dominator-p 1 bag::a (x prefix y type-alist)
  :hints (("goal" :in-theory (enable
                              show-syntax-dominates-p-irrelevant
                              hyp-for-show-syntax-dominates-p-irrelevant
                              syntax-quote-quote-prefixed-tail-dominator-p-irrelevant
                              ))))

(defignore hyp-for-show-syntax-prefixed-tail-dominator-p bag::a (x prefix y type-alist)
  (declare (type (satisfies wf-syntax-prefix) prefix)
           (type (satisfies acl2::type-alistp) type-alist))
  (if (consp prefix)
      (let ((key (caar prefix))
            (val (cdar prefix)))
        (case key
              (:cons
               (and (syn::consp x)
                    (equal (syn::car x) val)
                    (hyp-for-show-syntax-prefixed-tail-dominator-p (syn::cdr x) (cdr prefix) y type-alist)))
              (:append
               (and (syn::appendp x)
                    (equal (syn::arg 1 x) val)
                    (hyp-for-show-syntax-prefixed-tail-dominator-p (syn::arg 2 x) (cdr prefix) y type-alist)))
              (:quote
               (and (syn::quotep x)
                    (if (syn::quotep y)
                        (prefixed-tail-dominator-p (syn::dequote x) val (syn::dequote y))
                      (syntax-quote-quote-prefixed-tail-dominator-p (syn::dequote x) val y))
                    (syn::true)))
              (t nil)))
    (hyp-for-show-syntax-dominates-p nil x y type-alist)))

(defirrelevant hyp-for-show-syntax-prefixed-tail-dominator-p 1 bag::a (x prefix y type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-syntax-dominates-p-irrelevant
                              syntax-quote-quote-prefixed-tail-dominator-p-irrelevant
                              ))))

(defthm show-syntax-prefixed-tail-dominator-p-to-hyp-for
  (iff (show-syntax-prefixed-tail-dominator-p x prefix y type-alist)
       (hyp-for-show-syntax-prefixed-tail-dominator-p x prefix y type-alist)))

(defthm pseudo-termp-hyp-for-show-syntax-prefixed-tail-dominator-p
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-show-syntax-prefixed-tail-dominator-p x prefix y type-alist))))

(defthm prefixed-tail-dominator-p-append
  (implies
   (and
    (prefixed-tail-dominator-p x y z)
    (equal w k))
   (prefixed-tail-dominator-p (append w x) (append k y) z))
  :hints (("goal" :induct (list::len-len-induction w k))))

#+joe
(defthm list-prefixed-tail-dominator-p-append
  (implies
   (and
    (list-prefixed-tail-dominator-p x y z)
    (equal w k))
   (list-prefixed-tail-dominator-p (append w x) (map-append k y) z))
  :hints (("goal" :induct (list::len-len-induction w k))))

(defun len-len-len-induction (x y z)
  (if (and (consp x)
           (consp y)
           (consp z))
      (len-len-len-induction (cdr x) (cdr y) (cdr z))
    (list x y z)))

;; I don't think this helps ..

(defcong list::equiv equal
  (prefixed-tail-dominator-p x prefix y)
  2
  :hints (("goal" :induct (len-len-len-induction x prefix list::prefix-equiv))))

#+joe
(defcong list::equiv equal
  (list-prefixed-tail-dominator-p x prefix y)
  2
  :hints (("goal" :induct (len-len-len-induction x prefix list::prefix-equiv))))

(defthm show-syntax-prefixed-tail-dominator-p-implies-prefixed-tail-dominator
  (implies
   (and
    (hyp-for-show-syntax-prefixed-tail-dominator-p x prefix y type-alist)
    (syn::eval (hyp-for-show-syntax-prefixed-tail-dominator-p x prefix y type-alist) bag::a))
   (prefixed-tail-dominator-p (syn::eval x bag::a) (s2l prefix bag::a) (syn::eval y bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth
                                     syn::conjoin
                                     syntax-domination-implies-consp
                                     syntax-domination-implies-domination)))
  :rule-classes (:rewrite :forward-chaining))

(defthm prefixed-tail-dominator-membership-implies-prefixed-tail-dominator
  (implies
   (list::memberp pre (prefixes (v1 (tail-dominates x y))))
   (prefixed-tail-dominator-p x pre y))
  :hints (("goal" :in-theory (enable list::memberp)
           :induct (list::len-len-induction pre x))))

(defthm prefixed-tail-dominator-membership-implies-tail-dominates-p
  (implies
   (list::memberp pre (prefixes (v1 (tail-dominates x y))))
   (tail-dominates-p x y))
  :hints (("goal" :in-theory (enable list::memberp)))
  :rule-classes (:rewrite :forward-chaining))

(defthm prefixed-tail-dominator-p-implies-v0-tail-dominates
  (implies
   (prefixed-tail-dominator-p x pre y)
   (and (v0 (tail-dominates x y))
        (tail-dominates-p x y)))
  :rule-classes (:rewrite :forward-chaining))

(defthm list-prefixed-tail-dominator-p-implies-v0-tail-dominates
  (implies
   (list-prefixed-tail-dominator-p x pre y)
   (and (v0 (tail-dominates x y))
        (tail-dominates-p x y)))
  :rule-classes (:rewrite :forward-chaining))

(defthm prefixed-tail-dominator-implies-membership-tail-dominates
  (implies
   (prefixed-tail-dominator-p x pre y)
   (equal (list::memberp pre (prefixes (v1 (tail-dominates x y))))
          (true-listp pre)))
  :hints (("goal" :in-theory (enable list::memberp)
           :induct (list::len-len-induction pre x))))

(defthm show-syntax-prefixed-tail-dominator-p-implies-memberp
  (implies
   (and
    (hyp-for-show-syntax-prefixed-tail-dominator-p x pre y type-alist)
    (syn::eval (hyp-for-show-syntax-prefixed-tail-dominator-p x pre y type-alist) bag::a)
    (wf-syntax-prefix pre))
   (list::memberp (s2l pre bag::a) (prefixes (v1 (tail-dominates (syn::eval x bag::a) (syn::eval y bag::a))))))
  :hints (("goal" :in-theory '(true-listp-s2l
                               show-syntax-prefixed-tail-dominator-p-implies-prefixed-tail-dominator
                               prefixed-tail-dominator-implies-membership-tail-dominates
                               ))))

(defun contains-prefixed-tail-dominator-p (list pre x)
  (declare (type t x pre list))
  (if (consp list)
      (or (prefixed-tail-dominator-p (car list) pre x)
          (contains-prefixed-tail-dominator-p (cdr list) pre x))
    nil))

(defthm contains-prefixed-tail-dominator-p-membership-reduction
  (implies
   (list::memberp v list)
   (equal (contains-prefixed-tail-dominator-p list pre y)
          (or (prefixed-tail-dominator-p v pre y)
              (contains-prefixed-tail-dominator-p (bag::remove-1 v list) pre y))))
  :hints (("goal" :in-theory (enable list::memberp
                                     bag::remove-1)
           :induct (len list))))

#+joe
(defthm not-prefixed-tail-dominator-p-remove-1-reduction
  (implies
   (not (list-prefixed-tail-dominator-p x pre y))
   (equal (contains-prefixed-tail-dominator-p (bag::remove-1 x list) pre y)
          (contains-prefixed-tail-dominator-p list pre y)))
  :hints (("goal" :in-theory (enable bag::remove-1))))

#+joe
(defthm membership-reduction
  (implies
   (and
    (list::memberp x list)
    (prefixed-tail-dominator-p x pre y))
   (contains-prefixed-tail-dominator-p list pre y))
  :hints (("goal" :in-theory (enable list::memberp))))

(defcong bag::perm equal
  (contains-prefixed-tail-dominator-p list pre x)
  1
  :hints (("goal" :induct (bag::perm list bag::list-equiv)
           :in-theory (enable bag::perm))
          (and
           acl2::stable-under-simplificationp
           `(:cases ((list-prefixed-tail-dominator-p (car list) pre x))))))

(defthm contains-prefixed-tail-dominator-p-append-2
  (implies
   (contains-prefixed-tail-dominator-p list pre x)
   (contains-prefixed-tail-dominator-p (append y list) pre x))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (binary-append y list))))

(defthm contains-prefixed-tail-dominator-p-append-1
  (implies
   (contains-prefixed-tail-dominator-p z pre x)
   (contains-prefixed-tail-dominator-p (append z a) pre x)))

(defun contains-list-prefixed-tail-dominator-p (list prefixes x)
  (declare (type t x prefixes list))
  (if (consp list)
      (or (list-prefixed-tail-dominator-p (car list) prefixes x)
          (contains-list-prefixed-tail-dominator-p (cdr list) prefixes x))
    nil))

(local (in-theory (disable LIST-PREFIXED-TAIL-DOMINATOR-P)))

(defthm contains-list-prefixed-tail-dominator-p-membership-reduction
  (implies
   (list::memberp v list)
   (equal (contains-list-prefixed-tail-dominator-p list prefixes x)
          (or (list-prefixed-tail-dominator-p v prefixes x)
              (contains-list-prefixed-tail-dominator-p (bag::remove-1 v list) prefixes x))))
  :hints (("goal" :in-theory (enable list::memberp
                                     bag::remove-1)
           :induct (len list))))

(defcong bag::perm equal
  (contains-list-prefixed-tail-dominator-p list prefixes x)
  1
  :hints (("goal" :in-theory (enable bag::perm)
           :induct (bag::perm list bag::list-equiv))))

(defthm contains-list-prefixed-tail-dominator-p-append-2
  (implies
   (contains-list-prefixed-tail-dominator-p list pre x)
   (contains-list-prefixed-tail-dominator-p (append y list) pre x))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (binary-append y list))))

(defthm contains-list-prefixed-tail-dominator-p-append-1
  (implies
   (contains-list-prefixed-tail-dominator-p z pre x)
   (contains-list-prefixed-tail-dominator-p (append z a) pre x)))

(defthmd member-contains-prefixed-tail-dominator-p-implies-contains-list-prefixed-tail-dominator-p
  (implies
   (and
    (contains-prefixed-tail-dominator-p list pre x)
    (list::memberp pre prefixes))
   (contains-list-prefixed-tail-dominator-p list prefixes x))
  :hints (("goal" :in-theory (enable list::memberp))))

(in-theory
 (disable
  NOT-CONSP-MEMBERSHIP-IMPLIES-DOMINATES
  MEMBERP-NOT-CONSP-PREFIXES
  PREFIXED-TAIL-DOMINATOR-IMPLIES-MEMBERSHIP-TAIL-DOMINATES
  ))

(defignore syntax-quote-contains-prefixed-tail-dominator bag::a (list pre n x)
  (declare (type (integer 0 *) n)
           (type (satisfies wf-syntax-prefix) pre))
  (if (consp list)
      (let ((z (car list)))
        (let ((m (len z)))
          (or (and (< n m) (syntax-quote-quote-prefixed-tail-dominator-p z pre x))
              (syntax-quote-contains-prefixed-tail-dominator (cdr list) pre n x))))
    nil))

(defirrelevant syntax-quote-contains-prefixed-tail-dominator 1 bag::a (list pre n x)
  :hints (("goal" :in-theory (enable syntax-quote-quote-prefixed-tail-dominator-p-irrelevant
                                     ))))

(defthm syntax-quote-contains-prefixed-tail-dominator-implies-contains-prefixed-tail-dominator-p
  (implies
   (syntax-quote-contains-prefixed-tail-dominator list pre n x)
   (contains-prefixed-tail-dominator-p list pre (syn::eval x bag::a)))
  :rule-classes (:rewrite :forward-chaining))

;; DAG - finish this function to fix problem identified below

#+joe
(defignore syntax-quote-contains-prefixed-tail-dominator bag::a (list pre n x)
  )

(defignore syntax-contains-prefixed-tail-dominator bag::a (list pre n x type-alist)
  (declare (type (satisfies wf-syntax-prefix) pre)
           (type (satisfies acl2::type-alistp) type-alist)
           (type (integer 0 *) n))
  (cond
   ((syn::consp list)
    (let ((z (syn::car list)))
      (let ((m (sudo-len z)))
        (or (and (<= n m) (show-syntax-prefixed-tail-dominator-p z pre x type-alist))
            (syntax-contains-prefixed-tail-dominator (syn::cdr list) pre n x type-alist)))))
   ((syn::appendp list)
    (syntax-contains-prefixed-tail-dominator (syn::arg 2 list) pre n x type-alist))
   ((syn::quotep list)
    (and (syn::quotep x) ;; DAG: We should not require this here ..
         (consp pre)
         (equal (caar pre) :quote)
         (let ((prefix (cdar pre)))
           (contains-prefixed-tail-dominator-p (syn::dequote list) prefix (syn::dequote x)))))
   (t nil)))

(defirrelevant syntax-contains-prefixed-tail-dominator 1 bag::a (list pre n x type-alist)
  :hints (("goal" :in-theory (enable
                              show-syntax-prefixed-tail-dominator-p-irrelevant
                              hyp-for-show-syntax-prefixed-tail-dominator-p-irrelevant
                              ))))

(defignore hyp-for-syntax-contains-prefixed-tail-dominator bag::a (list pre n x type-alist)
  (declare (type (satisfies wf-syntax-prefix) pre)
           (type (satisfies acl2::type-alistp) type-alist)
           (type (integer 0 *) n))
  (cond
   ((syn::consp list)
    (let ((z (syn::car list)))
      (let ((m (sudo-len z)))
        (or (and (<= n m) (hyp-for-show-syntax-prefixed-tail-dominator-p z pre x type-alist))
            (hyp-for-syntax-contains-prefixed-tail-dominator (syn::cdr list) pre n x type-alist)))))
   ((syn::appendp list)
    (hyp-for-syntax-contains-prefixed-tail-dominator (syn::arg 2 list) pre n x type-alist))
   ((syn::quotep list)
    (and (syn::quotep x) ;; DAG: We should not require this here ..
         (consp pre)
         (equal (caar pre) :quote)
         (let ((prefix (cdar pre)))
           (contains-prefixed-tail-dominator-p (syn::dequote list) prefix (syn::dequote x)))
         (syn::true)))
   (t nil)))

(defirrelevant hyp-for-syntax-contains-prefixed-tail-dominator 1 bag::a (list pre n x type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-syntax-prefixed-tail-dominator-p-irrelevant
                              ))))

(defthm syntax-contains-prefixed-tail-dominator-to-hyp-for
  (iff (syntax-contains-prefixed-tail-dominator list pre n x type-alist)
       (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist)))

(defthm pseudo-termp-hyp-for-syntax-contains-prefixed-tail-dominator
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist))))

(defthm syntax-contains-prefixed-tail-dominator-implies-contains-prefixed-tail-dominator-p
  (implies
   (and
    (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist)
    (syn::eval (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist) bag::a))
   (contains-prefixed-tail-dominator-p (syn::eval list bag::a) (s2l pre bag::a) (syn::eval x bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth syn::conjoin)))
  :rule-classes (:rewrite :forward-chaining))

(defthm member-syntax-contains-prefixed-tail-dominator-p-implies-contains-list-prefixed-tail-dominator-p
  (implies
   (and
    (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist)
    (syn::eval (hyp-for-syntax-contains-prefixed-tail-dominator list pre n x type-alist) bag::a)
    (list::memberp (s2l pre bag::a) prefixes))
   (contains-list-prefixed-tail-dominator-p (syn::eval list bag::a) prefixes (syn::eval x bag::a)))
  :hints (("goal" :use (:instance member-contains-prefixed-tail-dominator-p-implies-contains-list-prefixed-tail-dominator-p
                                  (list (syn::eval list bag::a))
                                  (pre  (s2l pre bag::a))
                                  (x    (syn::eval x bag::a))
                                  (prefixes prefixes)))))

(defund tail-dominator-body (val rest x y)
  (declare (type t x y))
  (met ((hit prex) (tail-dominates val x))
       (or (and hit (contains-list-prefixed-tail-dominator-p rest (prefixes prex) y))
           (met ((hit prey) (tail-dominates val y))
                (and hit (contains-list-prefixed-tail-dominator-p rest (prefixes prey) x))))))

(defthm list-prefixed-tail-dominator-p-map-cons
  (equal (list-prefixed-tail-dominator-p w (list::map-cons a list) y)
         (and (consp w)
              (equal (car w) a)
              (list-prefixed-tail-dominator-p (cdr w) list y)))
  :hints (("goal" :in-theory (enable LIST-PREFIXED-TAIL-DOMINATOR-P)
           :induct (len list))))

(defun tail-dominator-body-body (v w x y)
  (met ((hitx prex) (tail-dominates v x))
       (met ((hity prey) (tail-dominates v y))
            (or (and hitx (list-prefixed-tail-dominator-p w (prefixes prex) y))
                (and hity (list-prefixed-tail-dominator-p w (prefixes prey) x))))))

(defun tail-dominator-body-rec (val rest x y)
  (if (consp rest)
      (or (tail-dominator-body-body val (car rest) x y)
          (tail-dominator-body-rec val (cdr rest) x y))
    nil))

(defthm tail-dominator-boody-to-tail-dominator-body-rec
  (equal (tail-dominator-body val rest x y)
         (tail-dominator-body-rec val rest x y))
  :hints (("goal" :in-theory (enable tail-dominator-body)
           :induct (len rest))))

(in-theory
 (disable
  tail-dominator-body
  ))

(defun tail-dominator-body-body-rec (w v x y)
  (if (and (consp w)
           (consp v))
      (or (and (dominates w x)
               (dominates v y))
          (and (dominates v x)
               (dominates w y))
          (and (equal (car w) (car v))
               (tail-dominator-body-body-rec (cdr w) (cdr v) x y)))
    nil))

(defthm open-tail-dominates
  (implies
   (consp x)
   (equal (tail-dominates x y)
          (met ((hit prefix)
                (tail-dominates (cdr x) y))
               (let ((dom (dominates x y)))
                    (if (or hit dom)
                        (mv t (cons (cons dom (car x)) prefix))
                        (mv nil nil)))))))

(defthm tail-dominator-body-body-is-tail-dominator-body-body-rec
  (equal (tail-dominator-body-body w v x y)
         (tail-dominator-body-body-rec w v x y))
  :hints (("Goal" :in-theory (e/d (LIST-PREFIXED-TAIL-DOMINATOR-P)
                                  ( TAIL-DOMINATES ;efficiency
                                      CONSP-PREFIXES-V1-TAIL-DOMINATES
                                      STRICTLY-DOMINATES-IMPLIES-DOMINATES
                                      ;LIST::MV-NTH-TO-VAL
                                      ;LIST-PREFIXED-TAIL-DOMINATOR-P
                                      ;TAIL-DOMINATES-P
                                      ))))
  )

(defthm tail-dominator-body-body-commutes-first-2
  (equal (tail-dominator-body-body-rec v w x y)
         (tail-dominator-body-body-rec w v x y)))

(defthm tail-dominator-body-body-commutes-last-2
  (equal (tail-dominator-body-body-rec v w x y)
         (tail-dominator-body-body-rec v w y x)))

(defthm tail-dominator-body-commutes-last-2
  (equal (tail-dominator-body-rec val rest x y)
         (tail-dominator-body-rec val rest y x)))

(in-theory
 (disable
  tail-dominator-body-body
  ))

(defthm tail-dominator-body-rec-membership-reduction
  (implies
   (list::memberp v rest)
   (equal (tail-dominator-body-rec val rest x y)
          (or (tail-dominator-body-body-rec val v x y)
              (tail-dominator-body-rec val (bag::remove-1 v rest) x y))))
  :hints (("goal" :in-theory (enable list::memberp
                                     bag::remove-1)
           :induct (len rest))))

(defcong bag::perm equal
  (tail-dominator-body-rec val rest x y)
  2
  :hints (("goal" :in-theory (enable bag::perm)
           :induct (bag::perm rest bag::rest-equiv))))

(defun contains-unique-prefixed-tail-dominators (list x y)
  (declare (type t list x y))
  (if (consp list)
      (let ((rest (cdr list))
            (val  (car list)))
        (or (tail-dominator-body val rest x y)
            (contains-unique-prefixed-tail-dominators rest x y)))
    nil))

(defthm contains-unique-prefixed-tail-dominators-membership-deconstruction
  (implies
   (list::memberp v list)
   (equal (contains-unique-prefixed-tail-dominators list x y)
          (or (tail-dominator-body v (bag::remove-1 v list) x y)
              (contains-unique-prefixed-tail-dominators (bag::remove-1 v list) x y))))
  :hints (("goal" :in-theory (enable bag::remove-1))))

(defcong bag::perm equal
  (contains-unique-prefixed-tail-dominators list x y)
  1
  :hints (("goal" :in-theory (enable bag::perm)
           :induct (bag::perm list bag::list-equiv))))

(defthm contains-unique-prefixed-tail-dominators-commutes
  (equal (contains-unique-prefixed-tail-dominators list x y)
         (contains-unique-prefixed-tail-dominators list y x)))

(defthm contains-unique-prefixed-tail-dominators-append-1
  (implies
   (contains-unique-prefixed-tail-dominators list x y)
   (contains-unique-prefixed-tail-dominators (append z list) x y))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (binary-append z list))))

(defthm contains-unique-prefixed-tail-dominators-append-2
  (implies
   (contains-unique-prefixed-tail-dominators z x y)
   (contains-unique-prefixed-tail-dominators (append z a) x y)))

(defignore syntax-contains-unique-prefixed-tail-dominators bag::a (list x y type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp list)
    (let ((rest (syn::cdr list)))
      (met ((hit prex) (show-syntax-tail-dominates (syn::car list) x type-alist))
           (or (and hit (syntax-contains-prefixed-tail-dominator rest prex (len prex) y type-alist))
               (met ((hit prey) (show-syntax-tail-dominates (syn::car list) y type-alist))
                    (or (and hit (syntax-contains-prefixed-tail-dominator rest prey (len prey) x type-alist))
                        (syntax-contains-unique-prefixed-tail-dominators rest x y type-alist)))))))
   ((syn::appendp list)
    (syntax-contains-unique-prefixed-tail-dominators (syn::arg 2 list) x y type-alist))
   ((syn::quotep list)
    (and (syn::quotep x) ;; DAG - fix .. we can do better than this.
         (syn::quotep y)
         (contains-unique-prefixed-tail-dominators (syn::dequote list) (syn::dequote x) (syn::dequote y))))
   (t nil)))


(defirrelevant syntax-contains-unique-prefixed-tail-dominators 1 bag::a (list x y type-alist)
  :hints (("goal" :in-theory (e/d (show-syntax-tail-dominates-irrelevant
                              syntax-contains-prefixed-tail-dominator-irrelevant
                              hyp-for-show-syntax-tail-dominates-irrelevant
                              hyp-for-syntax-contains-prefixed-tail-dominator-irrelevant
                              ) (;for efficiency:
                                 SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                                 SYN::OPEN-LEN
                                 HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                                 HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                                 SHOW-SYNTAX-TAIL-DOMINATES-FN
                                 TAIL-DOMINATES
                                 PREFIXED-TAIL-DOMINATOR-P
                                 TAIL-DOMINATES-P
                                 )))))

(defignore hyp-for-syntax-contains-unique-prefixed-tail-dominators bag::a (list x y type-alist)
  (declare (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp list)
    (let ((rest (syn::cdr list)))
      (met ((hit prex) (show-syntax-tail-dominates (syn::car list) x type-alist))
           (or (and hit (syn::and (hyp-for-show-syntax-tail-dominates (syn::car list) x type-alist)
                                  (hyp-for-syntax-contains-prefixed-tail-dominator rest prex (len prex) y type-alist)))
               (met ((hit prey) (show-syntax-tail-dominates (syn::car list) y type-alist))
                    (or (and hit (syn::and (hyp-for-show-syntax-tail-dominates (syn::car list) y type-alist)
                                           (hyp-for-syntax-contains-prefixed-tail-dominator rest prey (len prey) x type-alist)))
                        (hyp-for-syntax-contains-unique-prefixed-tail-dominators rest x y type-alist)))))))
   ((syn::appendp list)
    (hyp-for-syntax-contains-unique-prefixed-tail-dominators (syn::arg 2 list) x y type-alist))
   ((syn::quotep list)
    (and (syn::quotep x) ;; DAG - fix .. we can do better than this.
         (syn::quotep y)
         (contains-unique-prefixed-tail-dominators (syn::dequote list) (syn::dequote x) (syn::dequote y))
         (syn::true)))
   (t nil)))


(defirrelevant hyp-for-syntax-contains-unique-prefixed-tail-dominators 1 bag::a (list x y type-alist)
  :hints (("goal" :in-theory (e/d (show-syntax-tail-dominates-irrelevant
                                   hyp-for-show-syntax-tail-dominates-irrelevant
                                   hyp-for-syntax-contains-prefixed-tail-dominator-irrelevant
                                   ) (HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                                      SHOW-SYNTAX-TAIL-DOMINATES-FN
                                      SYN::OPEN-LEN
                                      HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN
                                      )))))

(defthm syntax-contains-unique-prefixed-tail-dominators-to-hyp-for
  (iff (syntax-contains-unique-prefixed-tail-dominators list x y type-alist)
       (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist))
  :hints (("Goal" :in-theory (disable ;efficiency:
                              HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                              HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                              SYN::OPEN-LEN
                              SHOW-SYNTAX-TAIL-DOMINATES-FN
                              TAIL-DOMINATES-P
                              HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN
                              TAIL-DOMINATES
                              HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN
                              ))))

(defthm pseudo-termp-hyp-for-syntax-contains-unique-prefixed-tail-dominators
  (implies
   (acl2::type-alistp type-alist)
   (pseudo-termp (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist)))
  :hints (("Goal" :in-theory (disable ;efficiency:
                              HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                              HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                              SYN::OPEN-LEN
                              SHOW-SYNTAX-TAIL-DOMINATES-FN
                              TAIL-DOMINATES-P
                              HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN
                              TAIL-DOMINATES
                              HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN
                              ))))


(defthm syntax-contains-unique-prefixed-tail-dominators-implies-contains-unique-prefixed-tail-dominators
  (implies
   (and
    (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist)
    (syn::eval (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist) bag::a))
   (contains-unique-prefixed-tail-dominators (syn::eval list bag::a) (syn::eval x bag::a) (syn::eval y bag::a)))
  :hints (("goal" :in-theory (e/d
                              (syn::conjoin syn::open-nth TAIL-DOMINATOR-BODY)
                              (;TAIL-DOMINATOR-BODY
                               SYNTAX-QUOTE-DOMINATES-P-FN ;these for efficiency
                               TAIL-DOMINATES
                               TAIL-DOMINATES-P
                               CONTAINS-LIST-PREFIXED-TAIL-DOMINATOR-P
                               LIST-PREFIXED-TAIL-DOMINATOR-P
                               HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                               SYNTAX-QUOTE-TAIL-DOMINATES-FN
                               HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                               HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN
                               SHOW-SYNTAX-TAIL-DOMINATES-FN
                               HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN
                               SHOW-SYNTAX-DOMINATES-P-FN

                               TAIL-DOMINATOR-BOODY-TO-TAIL-DOMINATOR-BODY-REC
                               (:REWRITE SYN::CONSP-REC-IMPLIES-CONSP)
                               (:DEFINITION SYN::CONSP-REC)
                               (:REWRITE BAG::SUBBAGP-CDR-LEMMA)
                               ;(:REWRITE list::EQUAL-OF-BOOLEANS-REWRITE)
                               (:rewrite acl2::equal-booleans-reducton)
                               (:REWRITE list::EQUAL-CAR-DIFFERENTIAL)
                               (:REWRITE BAG::SUBBAGP-WHEN-CDR-IS-NON-CONSP))
                              ))))

(defthm diverge-tail-dominator-body-body-rec-implies-diverge
  (implies
   (and
    (tail-dominator-body-body-rec a b x y)
    (diverge a b))
   (diverge x y))
  :hints (("goal" :induct (tail-dominator-body-body-rec a b x y))))

(defthm all-diverge-from-all-tail-dominator-body-implies-diverge
  (implies
   (and
    (tail-dominator-body-rec val rest x y)
    (diverges-from-all val rest))
   (diverge x y))
  :hints (("goal" :in-theory (enable diverges-from-all))))

(defthm all-diverge-from-all-contains-unique-prefixed-tail-dominators-implies-diverge
  (implies
   (and
    (all-diverge list)
    (contains-unique-prefixed-tail-dominators list x y))
   (diverge x y))
  :hints (("goal" :in-theory (enable all-diverge))))

(defignored show-prefix-diverge-from-type-alist bag::a (a b type-alist whole-alist)
  (declare (type t a b type-alist)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-alist)
                              (pseudo-termp a)
                              (pseudo-termp b)
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact  (car entry)))
      (or (and (syn::funcall 'all-diverge 1 fact)
               (bag::ts-non-nil (cadr entry))
               (syntax-contains-unique-prefixed-tail-dominators (syn::arg 1 fact) a b whole-alist))
          (show-prefix-diverge-from-type-alist a b (cdr type-alist) whole-alist)))))


(defirrelevant show-prefix-diverge-from-type-alist 1 bag::a (a b type-alist whole-alist)
  :hints (("goal" :in-theory (e/d (show-prefix-diverge-from-type-alist
                                   syntax-contains-unique-prefixed-tail-dominators-irrelevant
                                   hyp-for-syntax-contains-unique-prefixed-tail-dominators-irrelevant
                                   ) ( ;efficiency (bzo consider making some of these disables global?)
                                   HYP-FOR-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-FN
                                   SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-FN
                                   SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                                   SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                                   HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                                   HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                                   SYN::OPEN-LEN
                                   HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN
                                   )))))

(defignored hyp-for-show-prefix-diverge-from-type-alist bag::a (a b type-alist whole-alist)
  (declare (type t a b type-alist)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-alist)
                              (pseudo-termp a)
                              (pseudo-termp b)
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact  (car entry)))
      (or (and (syn::funcall 'all-diverge 1 fact)
               (bag::ts-non-nil (cadr entry))
               (syn::and (hyp-for-syntax-contains-unique-prefixed-tail-dominators (syn::arg 1 fact) a b whole-alist)
                         fact))
          (hyp-for-show-prefix-diverge-from-type-alist a b (cdr type-alist) whole-alist)))))


(defirrelevant hyp-for-show-prefix-diverge-from-type-alist 1 bag::a (a b type-alist whole-alist)
  :hints (("goal" :in-theory (e/d (hyp-for-syntax-contains-unique-prefixed-tail-dominators-irrelevant
                                   hyp-for-show-prefix-diverge-from-type-alist
                                   )
                                  (;efficiency:
                                   HYP-FOR-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-FN
                                   HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN
                                   HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN
                                   SYN::OPEN-LEN
                                   HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN

                                   )))))

(local (in-theory (disable HYP-FOR-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-FN)))

(defthm to-hyp-for-show-prefix-diverge-from-type-alist
  (iff (show-prefix-diverge-from-type-alist a b alist wlist)
       (hyp-for-show-prefix-diverge-from-type-alist a b alist wlist))
  :hints (("goal" :in-theory (enable show-prefix-diverge-from-type-alist
                                     hyp-for-show-prefix-diverge-from-type-alist))))

(defthm psedu-termp-hyp-for-show-prefix-diverge-from-type-alist
  (implies
   (and
    (acl2::type-alistp type-alist)
    (acl2::type-alistp whole-alist))
   (pseudo-termp (hyp-for-show-prefix-diverge-from-type-alist a b type-alist whole-alist)))
  :hints (("goal" :in-theory (enable hyp-for-show-prefix-diverge-from-type-alist))))

(syn::extend-eval pd-eval
 (
  (diverge x y)
  (dominates x y)
  (diverges-from-all x list)
  (all-diverge-from-all x y)
  (all-diverge x)
  (acl2::list-equiv x y)

  ;; We do this to expediate functional instantiation.
  ;; This should not be necessary as bag:: should use
  ;; the syn:: evaluator as much as possible.

  (bag::hide x)
  (bag::hide-unique list)
  (bag::hide-subbagp x y)
  (bag::hide-disjoint x y)
  (bag::hide-memberp a x)
  (bag::perm x y)
  (bag::unique list)
  (bag::if a b c)
  (bag::consp x)
  (bag::true-listp x)
  (bag::binary-append x y)
  (bag::cons a b)
  (bag::meta-subbagp list1 list2)
  (bag::remove-bag x list)
  (bag::meta-remove-bag x list)
  (bag::remove-1 x list)
  (bag::unique-memberps x y list)
  (bag::unique-subbagps x y list)
  (bag::subbagp-pair x1 x2 list1 list2)
  (bag::meta-memberp x list)
  (bag::any-subbagp x list) ;remove this?
  (list::finalcdr x)
  (acl2::true-list-fix x)
  (bag::subbagp x y)
  (list::memberp a x)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
  (acl2::member-equal a x)
  (bag::disjoint x y)
  ))

(DEFTHM
  PD-EVAL-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-IMPLIES-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS
  (IMPLIES
   (and
    (hyp-for-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS LIST X Y type-alist)
    (pd-eval (hyp-for-syntax-contains-unique-prefixed-tail-dominators list x y type-alist) bag::a))
   (CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS (PD-EVAL LIST BAG::A)
                                             (PD-EVAL X BAG::A)
                                             (PD-EVAL Y BAG::A)))
  :rule-classes (:rewrite :forward-chaining)
  :HINTS
  (("Goal"
    :in-theory (enable pd-eval-constraint-0)
    :USE
    (:FUNCTIONAL-INSTANCE
     (:INSTANCE
      SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-IMPLIES-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS
      (bag::A bag::A)
      (Y Y)
      (X X)
      (type-alist type-alist)
      (LIST LIST))
     (SYN::EVAL PD-EVAL)
     (SYN::EVAL-LIST PD-EVAL-LIST)))))

(defthm pd-eval-show-not-equal-from-type-alist-works-right
  (implies
   (and
    (bag::hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist)
    (pd-eval (bag::hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist) bag::a)
    )
   (not (equal (pd-eval x bag::a)
               (pd-eval y bag::a))))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("Goal"
    :in-theory (enable pd-eval-constraint-0)
    :USE
    (:FUNCTIONAL-INSTANCE
     (:INSTANCE
      bag::show-not-equal-from-type-alist-works-right
      (bag::A bag::A)
      (bag::Y Y)
      (bag::X X)
      (bag::N n)
      (bag::type-alist type-alist)
      (bag::whole-type-alist whole-type-alist)
      )
     (BAG::syntax-EV PD-EVAL)
     (bag::syntax-ev-list PD-EVAL-LIST)))))

(defthm show-prefix-diverge-from-type-alist-works
  (implies
   (and
    (hyp-for-show-prefix-diverge-from-type-alist a b alist wlist)
    (pd-eval (hyp-for-show-prefix-diverge-from-type-alist a b alist wlist) bag::a))
   (diverge (pd-eval a bag::a) (pd-eval b bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (e/d (syn::conjoin
                                   syn::open-nth
                                   hyp-for-show-prefix-diverge-from-type-alist)
                                  (
(:DEFINITION HYP-FOR-SYNTAX-CONTAINS-UNIQUE-PREFIXED-TAIL-DOMINATORS-FN)
(:DEFINITION HYP-FOR-SYNTAX-CONTAINS-PREFIXED-TAIL-DOMINATOR-FN)
(:DEFINITION HYP-FOR-SHOW-SYNTAX-PREFIXED-TAIL-DOMINATOR-P-FN)
(:REWRITE PREFIXED-TAIL-DOMINATOR-MEMBERSHIP-IMPLIES-PREFIXED-TAIL-DOMINATOR)
(:DEFINITION TAIL-DOMINATES-P)
(:DEFINITION TAIL-DOMINATES)
;jcd (:REWRITE CONSP-NON-NULL-TRUE-LIST)
(:DEFINITION HYP-FOR-SHOW-SYNTAX-DOMINATES-P-FN)
(:DEFINITION PREFIXED-TAIL-DOMINATOR-P)
(:REWRITE acl2::MV-NTH-TO-VAL)
(:REWRITE NOT-TAIL-DOMINATES-P-IMPLIES-NIL-PREFIX)
(:REWRITE NOT-DOMINATES-FROM-DIVERGE-ONE)
(:DEFINITION CONTAINS-PREFIXED-TAIL-DOMINATOR-P)
(:DEFINITION HYP-FOR-SHOW-SYNTAX-TAIL-DOMINATES-FN)
(:REWRITE V0-TAIL-DOMINATES-TO-TAIL-DOMINATES-P)
(:DEFINITION SHOW-SYNTAX-TAIL-DOMINATES-FN)
)))))

(defthm pd-eval-syntax-diverge-implies-eval-commute
  (implies
   (syntax-diverge t1 t2)
   (diverge (pd-eval t1 a) (pd-eval t2 a)))
  :hints (("Goal"
           :USE
           (:FUNCTIONAL-INSTANCE
            (:INSTANCE
             syntax-diverge-implies-diverge
             (a a)
             (t1 t1)
             (t2 t2))
            (SYN::EVAL PD-EVAL)
            (SYN::EVAL-LIST PD-EVAL-LIST)))))

(defun syn::singleton (term)
  (declare (type t term))
  (cond
   ((syn::consp term)
    (syn::null (syn::cdr term)))
   ((syn::quotep term)
    (let ((term (syn::dequote term)))
      (and (consp term)
           (not (consp (cdr term))))))
   (t nil)))

(defund syn::single-car (term)
  (declare (type (satisfies syn::singleton) term))
  (if (syn::consp term)
      (syn::car term)
    (syn::enquote (car (syn::dequote term)))))

(defthm pseudo-termp-single-car
  (implies
   (pseudo-termp term)
   (pseudo-termp (syn::single-car term)))
  :hints (("goal" :in-theory (enable
                              pseudo-termp
                              syn::single-car
                              ))))

(in-theory
 (disable
  syn::singleton
  ))

(defignored show-prefix-diverge-from-alist-body bag::a (x y type-alist)
  (declare (type (satisfies pseudo-termp) x y)
           (type (satisfies acl2::type-alistp) type-alist))
  (let ((hit (syntax-diverge x y)))
    (or hit
        (or (and (syn::singleton x)
                 (syn::singleton y)
                 (bag::show-not-equal-from-type-alist
                  (syn::single-car x) (syn::single-car y)
                  (bag::usb16-fix (len type-alist)) type-alist type-alist))
            (show-prefix-diverge-from-type-alist x y type-alist type-alist)))))

(defirrelevant show-prefix-diverge-from-alist-body 1 bag::a (x y type-alist)
  :hints (("goal" :in-theory (enable
                              show-prefix-diverge-from-alist-body
                              bag::hyp-for-show-not-equal-from-type-alist-irrelevant
                              hyp-for-show-prefix-diverge-from-type-alist-irrelevant
                              show-prefix-diverge-from-type-alist-irrelevant
                              ))))

(defignored hyp-for-show-prefix-diverge-from-alist-body bag::a (x y type-alist)
  (declare (type (satisfies pseudo-termp) x y)
           (type (satisfies acl2::type-alistp) type-alist))
  (let ((hit (syntax-diverge x y)))
    (or hit
        (or (and (syn::singleton x)
                 (syn::singleton y)
                 (bag::hyp-for-show-not-equal-from-type-alist
                  (syn::single-car x) (syn::single-car y) (bag::usb16-fix (len type-alist))
                  type-alist type-alist))
            (hyp-for-show-prefix-diverge-from-type-alist x y type-alist type-alist)))))

(defirrelevant hyp-for-show-prefix-diverge-from-alist-body 1 bag::a (x y type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-prefix-diverge-from-alist-body
                              bag::hyp-for-show-not-equal-from-type-alist-irrelevant
                              hyp-for-show-prefix-diverge-from-type-alist-irrelevant
                              ))))

(defthm pseudo-termp-hyp-for-show-prefix-diverge-from-alist-body
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp y)
    (acl2::type-alistp type-alist))
   (pseudo-termp (hyp-for-show-prefix-diverge-from-alist-body x y type-alist)))
  :hints (("goal" :in-theory (enable
                              hyp-for-show-prefix-diverge-from-alist-body
                              ))))

(defthm show-prefix-diverge-from-alist-body-to-hyp-for
  (iff (show-prefix-diverge-from-alist-body x y type-alist)
       (hyp-for-show-prefix-diverge-from-alist-body x y type-alist))
  :hints (("goal" :in-theory (enable
                              show-prefix-diverge-from-alist-body
                              hyp-for-show-prefix-diverge-from-alist-body
                              ))))

(defthm pd-eval-diverge-from-hyp-for-show-prefix-diverge-from-alist-body
  (implies
   (and
    (hyp-for-show-prefix-diverge-from-alist-body x y type-alist)
    (pd-eval (hyp-for-show-prefix-diverge-from-alist-body x y type-alist) bag::a))
   (diverge (pd-eval x bag::a) (pd-eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (e/d
                              (hyp-for-show-prefix-diverge-from-alist-body
                               bag::make-conjunction
                               )
                              (
                               pd-eval-show-not-equal-from-type-alist-works-right
                               ))
           :use (:instance
                 pd-eval-show-not-equal-from-type-alist-works-right
                 (x (syn::single-car x))
                 (y (syn::single-car y))
                 (n (BAG::USB16-FIX (LEN TYPE-ALIST)))
                 (whole-type-alist type-alist)
                 ))
          (and acl2::stable-under-simplificationp
               `(:in-theory (e/d
                             (
                              syn::single-car
                              syn::singleton
                              diverge
                              )
                             (pd-eval-show-not-equal-from-type-alist-works-right
                              ))))))

(defthmd syntax-quote-remove-common-prefix-pd-eval-diverge
  (implies
   (diverge (v0 (syntax-quote-remove-common-prefix x y))
            (pd-eval (v1 (syntax-quote-remove-common-prefix x y)) bag::a))
   (diverge x (pd-eval y bag::a))))

(defthmd syntax-remove-common-prefix-pd-eval-diverge
  (implies
   (diverge (pd-eval (v0 (syntax-remove-common-prefix x y)) bag::a)
            (pd-eval (v1 (syntax-remove-common-prefix x y)) bag::a))
   (diverge (pd-eval x bag::a)
            (pd-eval y bag::a)))
  :hints (("goal"
           :in-theory (e/d
                       (syn::open-nth
                        syntax-quote-remove-common-prefix-pd-eval-diverge)
                       (;jcd (:REWRITE CONSP-NON-NULL-TRUE-LIST)
                        (:REWRITE WF-SYNTAX-PREFIX-IMPLIES-TRUE-LISTP)
                        (:DEFINITION WF-SYNTAX-PREFIX)
                        (:DEFINITION TRUE-LISTP)
                        (:REWRITE PD-EVAL-SYNTAX-DIVERGE-IMPLIES-EVAL-COMMUTE)
                        (:DEFINITION SYNTAX-DIVERGE))))))

(defignored show-prefix-diverge-from-alist bag::a (x y type-alist)
  (declare (type (satisfies pseudo-termp) x y)
           (type (satisfies acl2::type-alistp) type-alist))
  (met ((x y) (syntax-remove-common-prefix x y))
       (show-prefix-diverge-from-alist-body x y type-alist)))

(defirrelevant show-prefix-diverge-from-alist 1 bag::a (x y type-alist)
  :hints (("goal" :in-theory (enable
                              show-prefix-diverge-from-alist
                              show-prefix-diverge-from-alist-body-irrelevant
                              ))))

(defignored hyp-for-show-prefix-diverge-from-alist bag::a (x y type-alist)
  (declare (type (satisfies pseudo-termp) x y)
           (type (satisfies acl2::type-alistp) type-alist))
  (met ((x y) (syntax-remove-common-prefix x y))
       (hyp-for-show-prefix-diverge-from-alist-body x y type-alist)))

(defthm show-prefix-diverge-from-alist-to-hyp-for
  (iff (show-prefix-diverge-from-alist x y type-alist)
       (hyp-for-show-prefix-diverge-from-alist x y type-alist))
  :hints (("goal" :in-theory (enable
                              show-prefix-diverge-from-alist
                              hyp-for-show-prefix-diverge-from-alist
                              ))))

(defthm pseudo-termp-hyp-for-show-prefix-diverge-from-alist
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp y)
    (acl2::type-alistp type-alist))
   (pseudo-termp (hyp-for-show-prefix-diverge-from-alist x y type-alist)))
  :hints (("goal" :in-theory (enable
                              hyp-for-show-prefix-diverge-from-alist
                              ))))

(defirrelevant hyp-for-show-prefix-diverge-from-alist 1 bag::a (x y type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-prefix-diverge-from-alist
                              hyp-for-show-prefix-diverge-from-alist-body-irrelevant
                              ))))

(defthm pd-eval-diverge-from-hyp-for-show-prefix-diverge-from-alist
  (implies
   (and
    (hyp-for-show-prefix-diverge-from-alist x y type-alist)
    (pd-eval (hyp-for-show-prefix-diverge-from-alist x y type-alist) bag::a))
   (diverge (pd-eval x bag::a) (pd-eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable
                              syntax-remove-common-prefix-pd-eval-diverge
                              hyp-for-show-prefix-diverge-from-alist
                              ))))

(set-state-ok t)

(defun show-prefix-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc))
  (if (syn::funcall 'diverge 2 term)
      (let ((x (syn::arg 1 term))
            (y (syn::arg 2 term)))
        (let ((zed #+joe(and (@ show-prefix-diverge-from-mfc)
                             (cw "** show-prefix-diverge-from-mfc(~x0,~x1)?~%" x y))
                   nil))
          (declare (ignore zed))
          (let ((type-alist (acl2::mfc-type-alist mfc)))
            (if (show-prefix-diverge-from-alist-fn nil x y type-alist)
                (acl2::prog2$
                 #+joe
                 (and (@ show-prefix-diverge-from-mfc)
                      (cw "** show-prefix-diverge-from-mfc!~%"))
                 nil
                 (syn::true))
              term))))
    term))

(defun hyp-for-show-prefix-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'diverge 2 term)
      (let ((x (syn::arg 1 term))
            (y (syn::arg 2 term)))
        (let ((type-alist (acl2::mfc-type-alist mfc)))
          (let ((hyp (hyp-for-show-prefix-diverge-from-alist-fn nil x y type-alist)))
            (if hyp (bag::bind-extra-vars-in-hyp hyp term)
              (syn::nil)))))
    (syn::nil)))

(defthm meta-rule-to-show-prefix-diverge
  (implies (pd-eval (hyp-for-show-prefix-diverge-from-mfc term mfc state) bag::a)
           (equal (pd-eval term bag::a)
                  (pd-eval (show-prefix-diverge-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (diverge)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable
                       syn::open-nth
                       syn::conjoin
                       hyp-for-show-prefix-diverge-from-alist-irrelevant
                       bag::make-conjunction
                       )
           :do-not '(generalize eliminate-destructors))))

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (in-theory
    (disable
     all-diverge
     ))

   (defthm test1
     (implies
      (all-diverge
       `((a b ,c d ,e)
         (a b ,c x ,y z)))
      (diverge `(d ,e) `(x ,y z))))

   (defthm test2
     (implies
      (all-diverge
       `((a b ,c d ,e)
         ,z
         (a b ,c x ,y z)))
      (diverge `(d ,e) `(x ,y z))))

   )))

(defun show-domination-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term)))
  (if (syn::funcall 'dominates 2 term)
      (let ((x (syn::arg 1 term))
            (y (syn::arg 2 term)))
        (let ((type-alist (acl2::mfc-type-alist mfc)))
          (if (show-syntax-dominates-p-fn nil t x y type-alist)
              (syn::true)
            (if (show-syntax-dominates-p-fn nil t y x type-alist)
                `(if (acl2::list-equiv ,y ,x) ,(syn::true) ,(syn::nil))
              term))))
    term))

(defun hyp-for-show-domination-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term)))
  (if (syn::funcall 'dominates 2 term)
      (let ((x (syn::arg 1 term))
            (y (syn::arg 2 term)))
        (let ((type-alist (acl2::mfc-type-alist mfc)))
          (let ((hyp (hyp-for-show-syntax-dominates-p-fn nil t x y type-alist)))
            (if hyp
                (bag::bind-extra-vars-in-hyp hyp term)
              (let ((hyp (hyp-for-show-syntax-dominates-p-fn nil t y x type-alist)))
                (if hyp
                    (bag::bind-extra-vars-in-hyp hyp term)
                  (syn::nil)))))))
    (syn::nil)))

(defthm pd-eval-syntax-domination-implies-domination
  (implies
   (hyp-for-show-syntax-dominates-p flg x y type-alist)
   (dominates (pd-eval x bag::a) (pd-eval y bag::a)))
  :hints (("goal" :use (:functional-instance syntax-domination-implies-domination-helper
                                             (syn::eval pd-eval)
                                             (syn::eval-list pd-eval-list)))))

(defthmd non-domination-from-not-equal-dominates
  (implies
   (and
    (dominates x y)
    (not (list::equiv x y)))
   (not (dominates y x)))
  :hints (("goal" :in-theory
           (enable
            dominates
            ))))

(defthm meta-rule-to-show-prefix-domination
  (implies (pd-eval (hyp-for-show-domination-from-mfc term mfc state) bag::a)
           (equal (pd-eval term bag::a)
                  (pd-eval (show-domination-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (dominates)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable
                       syn::open-nth
                       syn::conjoin
                       non-domination-from-not-equal-dominates
                       hyp-for-show-syntax-dominates-p-irrelevant
                       bag::make-conjunction
                       )
           :do-not '(generalize eliminate-destructors))))

(defun all-diverge-remove-prefix (paths)
  (if (not (syn::consp paths)) paths
      (syn::cons (syn::cdr (syn::car paths)) (all-diverge-remove-prefix (syn::cdr paths)))))

(defthm all-diverge-remove-prefix-open
  (implies
   (syn::consp paths)
   (equal (all-diverge-remove-prefix paths)
          (syn::cons (syn::cdr (syn::car paths)) (all-diverge-remove-prefix (syn::cdr paths))))))

(defun all-diverge-prefix-meta-fn (term)
  (if (and (syn::consp term)
           (syn::consp (syn::cdr term))
           (equal 'all-diverge (car term)))
      (if (syn-prefix-p (syn::cdr term))
          (let ((pruned (all-diverge-remove-prefix (syn::cdr term))))
                 (list 'all-diverge pruned))
        term)
    term))

(defthm not-syn-consp-all-diverge-prefix-meta-fn
  (implies (not (syn::consp term))
           (equal (all-diverge-prefix-meta-fn term)
                  term)))

(defun syntax-dominates (p1 p2)
  (if (syn::consp p1)
      (and (syn::consp p2)
           (equal (syn::car p1) (syn::car p2))
           (syntax-dominates (syn::cdr p1) (syn::cdr p2)))
    t))

#+joe ;; better definition later
(defun syntax-dominated-by-some (p paths)
  (if (syn::consp paths)
      (if (syntax-dominates (syn::car paths) p)
          t
        (syntax-dominated-by-some p (syn::cdr paths)))
    nil))

(defun remove-dominator (p paths)
  (if (syn::consp paths)
      (if (syntax-dominates (syn::car paths) p)
          (syn::cdr paths)
        (syn::cons (syn::car paths) (remove-dominator p (syn::cdr paths))))
      paths))

(syn::defevaluator meta-all-diverge-prefix-ev meta-all-diverge-prefix-ev-list
  (
   (len x)
   (syn-prefix-p x)
   (cdr x)
   (if a b c)
   (all-diverge-remove-prefix x)
   (all-diverge-prefix-meta-fn x)
   (consp x)
   (cons x y)
   (equal x y)
   (cpath::diverge a b)
   (cpath::all-diverge x)
   (cpath::all-diverge-from-all x y)
   (car x)
   ;(cadr x)
   (syn::car x)
   (syn::cons x y)
   (syn::cdr x)
   (syn::consp x)
   (syntax-dominates p1 p2)
   ;(syntax-dominated-by-some p paths)
   (remove-dominator p paths)
   ;(show-mapping-from-type-alist a b)
   ;(all-diverge-mapping-from-type-alist a l)
   ;(all-diverge-mapping-from-mfc t m state)
))

(defthm meta-all-diverge-prefix
  (equal (meta-all-diverge-prefix-ev term alist)
         (meta-all-diverge-prefix-ev (all-diverge-prefix-meta-fn term) alist))
  :rule-classes ((:meta :trigger-fns (all-diverge)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :induct (all-diverge-remove-prefix term))
          ("Subgoal *1/1" :in-theory (disable all-diverge-prefix-meta-fn)))
:otf-flg t)

(in-theory (disable (:rewrite wf-syntax-prefix-implies-true-listp)
                    (:definition wf-syntax-prefix)))
