; Supporting materials for:
;    New Rewriter Features in FGL
;    Sol Swords
;    Centaur Technology, Inc.
;    sswords@centtech.com

; Copyright (C) 2020 Centaur Technology
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


(in-package "FGL")

; Matt K. mod: Avoid ACL2(p) error from a clause-processor that returns one or
; more stobjs.
(set-waterfall-parallelism nil)

(include-book "centaur/fgl/top" :dir :system)

;; ------------------------------------------------------
;; Binder function/rule examples.


;; True only if x is true
(defun syntactically-true (var x)
  (and x var))

(defcong iff equal (syntactically-true var x) 2)
(add-fgl-congruence iff-implies-equal-syntactically-true-2)

(def-fgl-brewrite syntactically-true-binder-rewrite-false
  (implies (equal var nil)
           (equal (syntactically-true var x) var)))

(def-fgl-brewrite syntactically-true-binder-rewrite-true
  (implies (and x
                (equal var t))
           (equal (syntactically-true var x) var)))

;; (def-fgl-brewrite syntactically-true-binder-rewrite
;;   (implies (equal var (let ((xtrue (if x t nil)))
;;                         (and (bind-var xtrue (syntax-interp (eq xtrue t)))
;;                              xtrue)))
;;            (equal (syntactically-true var x) var)))


(def-formula-checks syntrue-form-check
  (syntactically-true))

;; Binder metafunction for syntactically-true
(def-fgl-binder-meta syntactically-true-binder-meta
  (b* ((ans
        (fgl-object-case arg
          :g-concrete arg.val
          :g-integer t
          :g-boolean (eq arg.bool t)
          :g-cons t
          :g-map arg.alist
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check syntrue-form-check
  :prepwork ((local (in-theory (enable syntactically-true)))
             (local (defthm fgl-object-alist-eval-under-iff
                      (iff (fgl-object-alist-eval x env)
                           (fgl-object-alist-fix x))
                      :hints (("goal" :expand ((fgl-object-alist-eval x env)
                                               (fgl-object-alist-fix x))
                               :in-theory (enable (:i len))
                               :induct (len x)))))
             (local (defthm fgl-ev-context-equv-forall-extensions-trivial
                      (implies (acl2::rewriting-negative-literal
                                `(fgl-ev-context-equiv-forall-extensions ,contexts ,obj ,term ,eval-alist))
                               (iff (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)
                                    (and
                                     (equal (fgl-ev-context-fix contexts (fgl-ev term eval-alist))
                                            (fgl-ev-context-fix contexts obj))
                                     (hide (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)))))
                      :hints (("goal" :expand ((:free (x) (hide x)))
                               :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                                      (ext eval-alist)))
                               :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc)))))
             (local (include-book "centaur/fgl/primitive-lemmas" :dir :system)))
  :origfn syntactically-true :formals (arg))

(local (in-theory (disable set::empty-set-unique
                           equal-of-booleans-rewrite
                           lrat::nth-n59-listp
                           lrat::nth-i60-listp)))

(install-fgl-metafns fsodfad)


;; Don't actually use the above metafunction, for now
(remove-fgl-binder-meta syntactically-true syntactically-true-binder-meta)

;; ;; Upper bound for (integer-length x) if nonnil
;; (defun integer-length-bound (var x)
;;   (and (integerp var)
;;        (<= (integer-length x) var)
;;        var))

;; All elements of x are in either the first or second return value,
;; and all elements of the first return value are in y
(defun-nx split-list-by-membership (var x y)
   (mv-let (part1 part2) var
       (if (and (set-equiv (append part1 part2) x)
                (subsetp-equal part1 y))
           (mv part1 part2)
         (mv nil x))))

;; ;; No restrictions
;; (defun bind-var (var x)
;;   var)

;; note: integer-length-bound is defined in centaur/fgl/checks.lisp

(def-fgl-brewrite integer-length-bound-binder-rw
  (implies (equal var (cond ((bind-var symbolic (syntax-interp (fgl-object-case x :g-integer)))
                             (if (syntactically-true known-int-endp (int-endp x))
                                 0
                               (let ((rest-bound (integer-length-bound rest-bound (logcdr x))))
                                 (and rest-bound (+ 1 rest-bound)))))
                            ((bind-var concrete (syntax-interp (fgl-object-case x :g-concrete)))
                             (integer-length x))
                            (t nil)))
           (equal (integer-length-bound var x)
                  var))
  :hints(("Goal" :in-theory (enable int-endp integer-length-bound))))

(include-book "centaur/misc/equal-sets" :dir :system)

(def-fgl-brewrite split-list-by-membership-binder-rule
  (implies (equal var (if (syntactically-true known-consp (consp x))
                          (mv-let (rest1 rest2)
                            (split-list-by-membership rest-call (cdr x) y)
                            (if (syntactically-true known-member (member-equal (car x) y))
                                (mv (cons (car x) rest1) rest2)
                              (mv rest1 (cons (car x) rest2))))
                        (mv nil x)))
           (equal (split-list-by-membership var x y)
                  var))
  :hints ((acl2::set-reasoning)))


(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable signed-byte-p)))

(local (defthm signed-byte-p-by-integer-length
         (implies (and (integerp n)
                       (< (integer-length x) n)
                       (integerp x))
                  (signed-byte-p n x))
         :hints (("goal" :induct (logext n x)
                  :in-theory (enable* bitops::ihsext-inductions
                                      bitops::ihsext-recursive-redefs)))))


(def-fgl-rewrite signed-byte-p-by-integer-length-bound
  (implies (and (integerp n)
                (integerp x)
                (equal bound (integer-length-bound bound1 x))
                bound
                (< bound n))
           (signed-byte-p n x))
  :hints(("Goal" :in-theory (enable integer-length-bound))))

(fgl-thm
 (signed-byte-p 30 (logext 20 x)))

(thm (signed-byte-p 30 (logext 20 x)))



;; ----------------------------------------------------------------------------
;; Show that power2-syntaxp and bind-k-to-common-expt-factors have the claimed
;; properties from the paper --- except:
;; "The syntax check POWER2-SYNTAXP provably is only true of terms whose
;; evaluation satisfies POWER2P, and the binding function
;; BIND-K-TO-COMMON-EXPT-FACTORS provably will only bind the variable K to a
;; term satisfying POWER2-SYNTAXP."

(include-book "rtl/rel9/arithmetic/expo" :dir :system)
(include-book "rtl/rel9/arithmetic/power2p" :dir :system)

#!acl2
(progn
(defevaluator p2ev p2ev-list ((expt x y) (binary-* x y) (unary-/ x) (power2p x)) :namedp t)

;; First claim -- power2-syntaxp is only true of terms whose evaluation satisfies power2p.
(defthm power2p-when-power2-syntaxp
  (implies (power2-syntaxp x)
           (power2p (p2ev x a)))
  :hints (("goal" :induct (power2-syntaxp x)
           :in-theory (enable power2-syntaxp))))


(defun power2-syntax-listp (x)
  (if (atom x)
      t
    (and (power2-syntaxp (car x))
         (power2-syntax-listp (cdr x)))))

(defthm power2-syntax-listp-of-get-expt-factors
  (power2-syntax-listp (get-expt-factors x))
  :hints(("Goal" :in-theory (enable get-expt-factors power2-syntaxp))))

(defthm power2-syntaxp-of-make-product-from-list-of-factors
  (implies (and (power2-syntax-listp x)
                (consp x))
           (power2-syntaxp (make-product-from-list-of-factors x)))
  :hints(("Goal" :in-theory (enable make-product-from-list-of-factors
                                    power2-syntaxp))))

;; Second claim -- bind-k-to-common-expt-factors will only bind k to a term
;; satisfying power2-syntaxp.
(defthm power2-syntaxp-of-bind-k-to-common-expt-factors
  (let ((alist (bind-k-to-common-expt-factors expr)))
    (implies alist
             (power2-syntaxp (cdr (assoc 'k alist)))))
  :hints(("Goal" :in-theory (enable bind-k-to-common-expt-factors))))


;; ----------------------------------------------------------------------------
;; Demonstrate quadratic blowup due to power2p-shift-2.
;; Note in order to profile power2-syntaxp I introduced a new version that is
;; identical but guard-verified, and a new version of power2p-shift-2 based on it.

(defun make-expts (n)
  (if (zp n)
      nil
    (cons `(expt 2 ,(intern-in-package-of-symbol (concatenate 'string "X" (coerce (explode-nonnegative-integer n 10 nil) 'string)) 'asd))
          (make-expts (1- n)))))

(defund power2-syntaxp-guarded (term)
  (declare (Xargs :guard (pseudo-termp term)))
  (if (not (consp term))
      nil
    (case (car term)
      (quote (and (rationalp (cadr term))
                  (power2p (cadr term))))
      (expt (equal (cadr term) '(quote 2))) ;allow the base to be any power of 2?  (constants only? or (expt 2 n)??
      (binary-* (and (power2-syntaxp-guarded (cadr term))
                     (power2-syntaxp-guarded (caddr term))
                     t))
      (unary-/ (power2-syntaxp-guarded (cadr term)))
      (otherwise nil))))

(defthm power2p-shift-2-mine
  (implies (and (syntaxp (power2-syntaxp-guarded y))
                (force (power2p y)) ;this should be true if the syntaxp hyp is satisfied
                )
           (equal (power2p (* x y))
                  (power2p x)))
  :hints (("goal" :in-theory (disable power2p)
           :use ( power2p-prod-not power2p-prod))))

(memoize 'power2-syntaxp-guarded :condition nil :recursive t)

(set-rewrite-stack-limit 10000)

;; Note: this originally contained (make-expts 4000), but this caused a stack
;; overflow in translate11-lst on some Lisp implementations.  Using 1000
;; instead seems to avoid the problem.
(make-event
 `(defthm power2p-of-bad-nesting
    (power2p (* . ,(make-expts 1000)))
    :hints(("Goal" :in-theory '(power2p-expt2-i power2p-shift-2-mine)))))



;; ----------------------------------------------------------------------------
;; Mock up of binder hypothesis rules for
;; bind-split-list-by-membership



(defun-nx bind-split-list-by-membership (free-var x y)
  (mv-let (part1 part2) free-var
    (and (set-equiv (append part1 part2) x)
         (subsetp-equal part1 y))))

(defthm bind-split-list-by-membership-default
   (implies (equal free-var (mv nil x))
            (bind-split-list-by-membership free-var x y)))

(defthm bind-split-list-by-membership-nonmember
  (implies (and (consp x)
                (bind-split-list-by-membership rest-split (cdr x) y)
                (equal free-var (mv-let (rest1 rest2) rest-split
                                   (mv rest1 (cons (car x) rest2)))))
           (bind-split-list-by-membership free-var x y))
  :hints ((acl2::set-reasoning)))

(defthm bind-split-list-by-membership-member
  (implies (and (consp x)
                (member (car x) y)
                (bind-split-list-by-membership rest-split (cdr x) y)
                (equal free-var (mv-let (rest1 rest2) rest-split
                                   (mv (cons (car x) rest1) rest2))))
           (bind-split-list-by-membership free-var x y))
  :hints ((acl2::set-reasoning)))
)
