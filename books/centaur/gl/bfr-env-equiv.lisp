; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "bfr")
(include-book "bvecs")
(local (include-book "centaur/aig/aig-vars" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))




(acl2::def-universal-equiv bfr-env-equiv
  :qvars (v)
  :equiv-terms ((iff (bfr-lookup v x))))

(in-theory (disable bfr-env-equiv))

(defcong bfr-env-equiv equal (bfr-lookup v x) 2
  :hints (("goal" :use ((:instance bfr-env-equiv-necc
                         (y x-equiv))))))

(local (defthm bfr-env-equiv-of-cdr-in-bdd-mode
         (implies (and (not (bfr-mode))
                       (bfr-env-equiv x y))
                  (equal (bfr-env-equiv (cdr x) (cdr y)) t))
         :hints (("goal" :expand ((bfr-env-equiv (cdr x) (cdr y))))
                 (and stable-under-simplificationp
                      '(:in-theory (enable bfr-lookup bfr-varname-fix)
                        :use ((:instance bfr-env-equiv-necc
                               (v (+ 1 (nfix (bfr-env-equiv-witness (cdr x) (cdr y))))))))))))

(local (defthm bfr-env-equiv-of-cdr-in-bdd-mode-implies-car
         (implies (and (not (bfr-mode))
                       (bfr-env-equiv x y))
                  (and (implies (car x) (car y))
                       (implies (car y) (car x))
                       (implies (not (car y)) (not (car x)))
                       (implies (not (car x)) (not (car y)))))
         :hints (("goal"
                  :in-theory (e/d (bfr-lookup bfr-varname-fix) ((bfr-varname-fix)))
                  :use ((:instance bfr-env-equiv-necc
                         (v 0)))))))

(defsection eval-bdd-when-bfr-env-equiv
  

  (local (defun eval-bdd-when-bfr-env-equiv-ind (x a b)
           (if (atom x)
               (list a b)
             (if (car a)
                 (eval-bdd-when-bfr-env-equiv-ind (car x) (cdr a) (cdr b))
               (eval-bdd-when-bfr-env-equiv-ind (cdr x) (cdr a) (cdr b))))))

  (defthmd eval-bdd-when-bfr-env-equiv
    (implies (And (bfr-env-equiv a b)
                  (not (bfr-mode)))
             (equal (acl2::eval-bdd x a)
                    (acl2::eval-bdd x b)))
    :hints (("goal" :induct (eval-bdd-when-bfr-env-equiv-ind x a b)
             :expand ((acl2::eval-bdd x a)
                      (acl2::eval-bdd x b))
             :in-theory (enable acl2::eval-bdd)))))

(defsection aig-eval-when-bfr-env-equiv


  (defthmd aig-eval-when-bfr-env-equiv
    (implies (And (bfr-env-equiv a b)
                  (bfr-mode))
             (equal (acl2::aig-eval x a)
                    (acl2::aig-eval x b)))
    :hints (("goal" :induct (acl2::aig-eval x a)
             :expand ((acl2::aig-eval x a)
                      (acl2::aig-eval x b))
             :in-theory (e/d (acl2::aig-eval) ()))
            (and stable-under-simplificationp
                 '(:use ((:instance bfr-env-equiv-necc
                          (v x) (x a) (y b)))
                   :in-theory (e/d (bfr-lookup bfr-varname-fix)
                                   (bfr-env-equiv-necc (bfr-varname-fix))))))
    :rule-classes ((:rewrite :loop-stopper ((a b))))))

(defcong bfr-env-equiv equal (bfr-eval x env) 2
  :hints(("Goal" :in-theory (enable bfr-eval)
          :use ((:instance aig-eval-when-bfr-env-equiv
                 (a env) (b env-equiv))
                (:instance eval-bdd-when-bfr-env-equiv
                 (a env) (b env-equiv))))))


(defcong bfr-env-equiv equal (bfr-list->s x env) 2)
(defcong bfr-env-equiv equal (bfr-list->u x env) 2)

(defsection iff*
  (defund iff* (x y)
    (iff x y))
  (defequiv iff* :hints(("Goal" :in-theory (enable iff*))))
  (defrefinement iff iff* :hints(("Goal" :in-theory (enable iff*))))
  (defrefinement iff* iff :hints(("Goal" :in-theory (enable iff*))))

  (defthm iff*-of-nonnils
    (implies (and x y)
             (equal (iff* x y) t))
    :hints(("Goal" :in-theory (enable iff*)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection param-env-under-bfr-env-equiv

  (local (defthm nth-when-bfr-env-equiv-in-bdd-mode
           (implies (and (bfr-env-equiv x y)
                         (not (bfr-mode)))
                    (equal (iff* (nth n x) (nth n y)) t))
           :hints (("goal" :use ((:instance bfr-env-equiv-necc
                                  (v n)))
                    :in-theory (e/d (bfr-lookup bfr-varname-fix) (bfr-env-equiv-necc))))))

  (local (defun param-env-under-bfr-env-equiv-ind (n p x y)
           (cond ((atom p) (list n x y))
                 ((eq (car p) nil)
                  (param-env-under-bfr-env-equiv-ind n (cdr p) (cdr x) (cdr y)))
                 ((eq (cdr p) nil)
                  (param-env-under-bfr-env-equiv-ind n (car p) (cdr x) (cdr y)))
                 ((car x)
                  (param-env-under-bfr-env-equiv-ind (1- n) (car p) (cdr x) (cdr y)))
                 (t
                  (param-env-under-bfr-env-equiv-ind (1- n) (cdr p) (cdr x) (cdr y))))))
  
  (local (defthm nth-of-nil
           (equal (nth n nil) nil)))

  (local (defthm param-env-under-bfr-env-equiv
           (implies (and (bfr-env-equiv x y)
                         (not (bfr-mode)))
                    (equal (iff* (nth n (acl2::param-env p x))
                                 (nth n (acl2::param-env p y)))
                           t))
           :hints (("goal" :induct (param-env-under-bfr-env-equiv-ind n p x y)
                    :in-theory (disable nth)
                    :expand ((:free (x) (acl2::param-env p x))
                             (:free (a b) (nth n (cons a b))))))))

  (defcong bfr-env-equiv bfr-env-equiv (bfr-param-env p env) 2
    :hints(("Goal" :in-theory (e/d (bfr-param-env bfr-lookup bfr-varname-fix)
                                   (param-env-under-bfr-env-equiv))
            :do-not-induct t
            :expand ((bfr-env-equiv (acl2::param-env p env)
                                    (acl2::param-env p env-equiv)))
            :use ((:instance param-env-under-bfr-env-equiv
                   (x env) (y env-equiv)
                   (n (bfr-env-equiv-witness (acl2::param-env p env)
                                             (acl2::param-env p env-equiv)))))))))

(defsection unparam-env-under-bfr-env-equiv

  (local (defthm nth-when-bfr-env-equiv-in-bdd-mode
           (implies (and (bfr-env-equiv x y)
                         (not (bfr-mode)))
                    (equal (iff* (nth n x) (nth n y)) t))
           :hints (("goal" :use ((:instance bfr-env-equiv-necc
                                  (v n)))
                    :in-theory (e/d (bfr-lookup bfr-varname-fix) (bfr-env-equiv-necc))))))

  (local (defun unparam-env-under-bfr-env-equiv-ind (n p x y)
           (cond ((atom p) (list n x y))
                 ((eq (car p) nil)
                  (unparam-env-under-bfr-env-equiv-ind (1- n) (cdr p) x y))
                 ((eq (cdr p) nil)
                  (unparam-env-under-bfr-env-equiv-ind (1- n) (car p) x y))
                 ((car x)
                  (unparam-env-under-bfr-env-equiv-ind (1- n) (car p) (cdr x) (cdr y)))
                 (t
                  (unparam-env-under-bfr-env-equiv-ind (1- n) (cdr p) (cdr x) (cdr y))))))
  
  (local (defthm nth-of-nil
           (equal (nth n nil) nil)))

  (local (defthm unparam-env-under-bfr-env-equiv
           (implies (and (bfr-env-equiv x y)
                         (not (bfr-mode)))
                    (equal (iff* (nth n (acl2::unparam-env p x))
                                 (nth n (acl2::unparam-env p y)))
                           t))
           :hints (("goal" :induct (unparam-env-under-bfr-env-equiv-ind n p x y)
                    :in-theory (disable nth)
                    :expand ((:free (x) (acl2::unparam-env p x))
                             (:free (a b) (nth n (cons a b))))))))

  (defcong bfr-env-equiv bfr-env-equiv (bfr-unparam-env p env) 2
    :hints(("Goal"
            :in-theory (disable unparam-env-under-bfr-env-equiv
                                bfr-env-equiv-necc
                                BFR-ENV-EQUIV-IMPLIES-EQUAL-BFR-LOOKUP-2)
            :do-not-induct t
            :expand ((bfr-env-equiv (bfr-unparam-env p env)
                                    (bfr-unparam-env p env-equiv)))
            :use ((:instance unparam-env-under-bfr-env-equiv
                   (x env) (y env-equiv)
                   (n (bfr-env-equiv-witness (bfr-unparam-env p env)
                                             (bfr-unparam-env p env-equiv))))
                  (:instance bfr-env-equiv-necc
                   (x env) (y env-equiv)
                   (v (bfr-env-equiv-witness (bfr-unparam-env p env)
                                             (bfr-unparam-env p env-equiv))))))
           (and stable-under-simplificationp
                '(:in-theory (e/d (bfr-unparam-env bfr-lookup bfr-varname-fix)
                                  (unparam-env-under-bfr-env-equiv
                                   bfr-env-equiv-necc
                                   BFR-ENV-EQUIV-IMPLIES-EQUAL-BFR-LOOKUP-2)))))))

(defthm bfr-env-equiv-of-unparam-param-env
  (implies (bfr-eval p env)
           (bfr-env-equiv (bfr-unparam-env p (bfr-param-env p env))
                          env))
  :hints(("Goal" :use ((:instance bfr-unparam-env-of-param-env
                        (x (bfr-var (bfr-env-equiv-witness
                                     (bfr-param-env p (bfr-unparam-env p (bfr-param-env p env)))
                                     (bfr-param-env p env))))))
          :in-theory (e/d (bfr-env-equiv)
                          (bfr-param-env-of-unparam-env-of-param-env)))))

;; (defthm bfr-env-equiv-of-param-unparam-param-env
;;   (implies (bfr-eval p env)
;;            (bfr-env-equiv (bfr-param-env p (bfr-unparam-env p (bfr-param-env p env)))
;;                           (bfr-param-env p env)))
;;   :hints(("Goal" :use ((:instance bfr-param-env-of-unparam-env-of-param-env
;;                         (x (bfr-var (bfr-env-equiv-witness
;;                                      (bfr-param-env p (bfr-unparam-env p (bfr-param-env p env)))
;;                                      (bfr-param-env p env))))))
;;           :in-theory (e/d (bfr-env-equiv)
;;                           (bfr-param-env-of-unparam-env-of-param-env)))))
