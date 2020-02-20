; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(include-book "add-primitives")
(include-book "primitives-stub")
(include-book "bfr-arithmetic")
(include-book "def-fgl-rewrite")
(include-book "checks")
(include-book "congruence-rules")
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))


(def-formula-checks checks-formula-checks
  (check-true
   check-integerp
   check-natp
   check-int-endp
   check-bitp
   check-signed-byte-p
   check-unsigned-byte-p
   check-non-integerp
   check-consp
   check-non-consp
   check-booleanp
   check-non-booleanp
   check-equal
   integer-length-bound
   ifix))

;; (local (defthm equal-of-len
;;          (implies (syntaxp (quotep n))
;;                   (equal (equal (len x) n)
;;                          (cond ((equal n 0) (atom x))
;;                                ((zp n) nil)
;;                                ((consp x) (equal (len (cdr x)) (1- n)))
;;                                (t nil))))))

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

(local (in-theory (disable fgl-ev-context-equiv-forall-extensions)))

;; (local (defthm fgl-object-bindings-eval-nil
;;          (equal (fgl-object-bindings-eval-

(local (defthm fgl-object-eval-when-booleanp
         (implies (booleanp x)
                  (equal (fgl-object-eval x env) x))
         :hints(("Goal" :in-theory (enable fgl-object-eval fgl-object-kind g-concrete->val)))))

(local (in-theory (disable member-equal
                           equal-of-booleans-rewrite)))

(add-fgl-congruence iff-implies-equal-check-true-2)

(def-fgl-binder-meta check-true-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete arg.val
          :g-integer t
          :g-boolean (eq arg.bool t)
          :g-cons t
          :g-map arg.alist
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :prepwork ((local (in-theory (enable check-true)))
             (local (defthm fgl-object-alist-eval-under-iff
                      (iff (fgl-object-alist-eval x env)
                           (fgl-object-alist-fix x))
                      :hints (("goal" :expand ((fgl-object-alist-eval x env)
                                               (fgl-object-alist-fix x))
                               :in-theory (enable (:i len))
                               :induct (len x))))))
  :origfn check-true :formals (arg))

(def-fgl-binder-meta check-integerp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (integerp arg.val)
          :g-integer t
          :g-apply (or (and (eq arg.fn 'ifix) (eql (len arg.args) 1))
                       (eq arg.fn 'intcdr)
                       (eq arg.fn 'intcons))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :prepwork ((local (in-theory (enable check-integerp))))
  :origfn check-integerp :formals (arg))


(def-fgl-binder-meta check-natp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (natp arg.val)
          :g-integer (eq (car (last arg.bits)) nil)
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-natp :formals (arg)
  :prepwork ((local (in-theory (enable check-natp)))
             (local (defthm bools->int-less-than-0
                      (iff (< (bools->int x) 0)
                           (car (last x)))
                      :hints(("Goal" :in-theory (enable bools->int)))))
             (local (defthm car-last-of-gobj-bfr-list-eval
                      (implies (not (car (last x)))
                               (not (car (last (gobj-bfr-list-eval x env)))))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))))


(def-fgl-binder-meta check-int-endp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (or (not (integerp arg.val))
                          (int-endp arg.val))
          :g-integer (or (atom arg.bits)
                         (atom (cdr arg.bits)))
          :g-boolean t
          :g-cons t
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-int-endp :formals (arg)
  :prepwork ((local (in-theory (enable check-int-endp)))
             (local (defthm int-endp-of-bools->int
                      (implies (atom (cdr x))
                               (int-endp (bools->int x)))
                      :hints(("Goal" :in-theory (enable bools->int int-endp)))))
             (local (defthm consp-cdr-of-gobj-bfr-list-eval
                      (iff (consp (cdr (gobj-bfr-list-eval x env)))
                           (consp (cdr x)))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
             (local (defthm int-endp-when-not-integerp
                      (implies (not (integerp x))
                               (int-endp x))
                      :hints(("Goal" :in-theory (enable int-endp)))))))


(def-fgl-binder-meta check-bitp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (bitp arg.val)
          :g-integer (or (endp arg.bits)
                         (and (endp (cdr arg.bits))
                              (not (car arg.bits)))
                         (and (consp (cdr arg.bits))
                              (endp (cddr arg.bits))
                              (not (cadr arg.bits))))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-bitp :formals (arg)
  :prepwork ((local (in-theory (enable check-bitp)))
             (local (defthm bitp-of-bools->int
                      (implies (or (atom x)
                                   (and (atom (cdr x))
                                        (not (car x)))
                                   (and (consp (cdr x))
                                        (atom (cddr x))
                                        (not (cadr x))))
                               (bitp (bools->int x)))
                      :hints(("Goal" :in-theory (enable bools->int bitp)))))
             (local (defthm consp-cdr-of-gobj-bfr-list-eval
                      (iff (consp (cdr (gobj-bfr-list-eval x env)))
                           (consp (cdr x)))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
             (local (defthm consp-cddr-of-gobj-bfr-list-eval
                      (iff (consp (cddr (gobj-bfr-list-eval x env)))
                           (consp (cddr x)))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
             (local (defthm not-cadr-of-gobj-bfr-list-eval
                      (implies (not (cadr x))
                               (not (cadr (gobj-bfr-list-eval x env))))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))))



(def-fgl-binder-meta check-signed-byte-p-binder
  (b* (((unless (fgl-object-case len :g-concrete))
        (mv nil nil nil nil interp-st state))
       (len (g-concrete->val len))
       ((unless (posp len))
        (mv t 'ans '((ans . nil)) nil interp-st state))
       (ans
        (fgl-object-case arg
          :g-concrete (signed-byte-p len arg.val)
          :g-integer (<= (len arg.bits) len)
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-signed-byte-p :formals (len arg)
  :prepwork ((local (in-theory (enable check-signed-byte-p)))
             (local (defun signed-byte-p-of-bools->int-ind (n x)
                      (if (or (zp n) (eql n 1))
                          x
                        (signed-byte-p-of-bools->int-ind (1- n) (cdr x)))))

             (local (defthm signed-byte-p-of-bools->int
                      (implies (and (posp n)
                                    (<= (len x) n))
                               (signed-byte-p n (bools->int x)))
                      :hints(("Goal" :in-theory (e/d (bools->int len bool->bit)
                                                     (signed-byte-p
                                                      bitops::signed-byte-p-of-logcdr))
                              :induct (signed-byte-p-of-bools->int-ind n x)
                              :expand ((:with bitops::signed-byte-p** (:free (x) (signed-byte-p n x))))))))
             (local (defthm len-of-gobj-bfr-list-eval
                      (equal (len (gobj-bfr-list-eval x env))
                             (len x))))))


(def-fgl-binder-meta check-unsigned-byte-p-binder
  (b* (((unless (fgl-object-case len :g-concrete))
        (mv nil nil nil nil interp-st state))
       (len (g-concrete->val len))
       ((unless (natp len))
        (mv t 'ans '((ans . nil)) nil interp-st state))
       (ans
        (fgl-object-case arg
          :g-concrete (unsigned-byte-p len arg.val)
          :g-integer (and (<= (len arg.bits) (+ 1 len))
                          (not (car (last arg.bits))))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-unsigned-byte-p :formals (len arg)
  :prepwork ((local (in-theory (e/d (check-unsigned-byte-p)
                                    (unsigned-byte-p))))
             (local (defun unsigned-byte-p-of-bools->int-ind (n x)
                      (if (zp n)
                          x
                        (unsigned-byte-p-of-bools->int-ind (1- n) (cdr x)))))

             (local (defthm unsigned-byte-p-of-bools->int
                      (implies (and (natp n)
                                    (<= (len x) (+ 1 n))
                                    (not (car (last x))))
                               (unsigned-byte-p n (bools->int x)))
                      :hints(("Goal" :in-theory (e/d (bools->int len last bool->bit)
                                                     (unsigned-byte-p))
                              :induct (unsigned-byte-p-of-bools->int-ind n x)
                              :expand ((:with bitops::unsigned-byte-p** (:free (x) (unsigned-byte-p n x))))))))
             (local (defthm car-last-of-gobj-bfr-list-eval
                      (implies (not (car (last x)))
                               (not (car (last (gobj-bfr-list-eval x env)))))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))))


(def-fgl-binder-meta check-non-integerp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (not (integerp arg.val))
          :g-integer nil
          :g-boolean t
          :g-cons t
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-non-integerp :formals (arg)
  :prepwork ((local (in-theory (enable check-non-integerp)))))


(def-fgl-binder-meta check-consp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (consp arg.val)
          :g-integer nil
          :g-boolean nil
          :g-cons t
          :g-apply (eq arg.fn 'cons)
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-consp :formals (arg)
  :prepwork ((local (in-theory (enable check-consp)))))

(def-fgl-binder-meta check-non-consp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (not (consp arg.val))
          :g-integer t
          :g-boolean t
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-non-consp :formals (arg)
  :prepwork ((local (in-theory (enable check-non-consp)))))


(def-fgl-binder-meta check-booleanp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (booleanp arg.val)
          :g-boolean t
          :g-apply (or (eq arg.fn 'equal)
                       (eq arg.fn 'intcar)
                       (eq arg.fn 'integerp))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-booleanp :formals (arg)
  :prepwork ((local (in-theory (enable check-booleanp)))))

(def-fgl-binder-meta check-non-booleanp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (not (booleanp arg.val))
          :g-integer t
          :g-cons t
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-non-booleanp :formals (arg)
  :prepwork ((local (in-theory (enable check-non-booleanp)))))

(local (in-theory (enable fgl-object-p-when-integerp)))

(def-fgl-binder-meta integer-length-bound-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (integer-length (ifix arg.val))
          :g-boolean 0
          :g-cons 0
          :g-integer (max 0 (1- (len arg.bits)))
          :otherwise nil)))
    (mv t (kwote ans) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn integer-length-bound :formals (arg)
  :prepwork ((local (in-theory (enable integer-length-bound
                                       fgl-object-p-when-integerp
                                       fgl-object-kind-when-integerp
                                       g-concrete->val-when-integerp)))
             (local (defthm integer-length-when-zip
                      (implies (zip x)
                               (equal (integer-length x) 0))))
             (local (defthm integer-length-of-bools->int
                      (<= (integer-length (bools->int x)) (max 0 (+ -1 (len x))))
                      :hints(("Goal" :in-theory (enable bools->int
                                                        bool->bit
                                                        bitops::integer-length**)))
                      :rule-classes ((:linear :trigger-terms ((integer-length (bools->int x)))))))))



(local (defthm cdr-of-fgl-objectlist-fix
         (equal (cdr (fgl-objectlist-fix x))
                (fgl-objectlist-fix (cdr x)))))

(def-fgl-binder-meta check-equal-binder
  (mv t  (if (equal (fgl-object-fix x)
                    (fgl-object-fix y))
             ''t ''nil)
      nil nil interp-st state)
  :formula-check checks-formula-checks
  :origfn check-equal :formals (x y)
  :prepwork ((local (in-theory (enable check-equal)))))
