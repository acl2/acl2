; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "lattice")
(include-book "alist-equiv")
(include-book "rewrite-base")
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defsection svex-[=
  (defun-sk svex-[= (x y)
    (forall env
            (4vec-[= (svex-eval x env)
                     (svex-eval y env)))
    :rewrite :direct)

  (in-theory (disable svex-[=))

  (defcong svex-eval-equiv equal (svex-[= x y) 1
    :hints (("goal" :in-theory (e/d (svex-[=)
                                    (svex-[=-necc))
             :use ((:instance svex-[=-necc
                    (x x-equiv)
                    (env (svex-[=-witness x y)))
                   (:instance svex-[=-necc
                    (env (svex-[=-witness x-equiv y)))))))
  (defcong svex-eval-equiv equal (svex-[= x y) 2
    :hints (("goal" :in-theory (e/d (svex-[=)
                                    (svex-[=-necc))
             :use ((:instance svex-[=-necc
                    (y y-equiv)
                    (env (svex-[=-witness x y)))
                   (:instance svex-[=-necc
                    (env (svex-[=-witness x y-equiv)))))))

  (defthm svex-[=-x
    (svex-[= (4vec-x) x)
    :hints(("Goal" :in-theory (enable svex-[=))))

  (defthm svex-[=-refl
    (svex-[= x x)
    :hints(("Goal" :in-theory (enable svex-[=)))))

(local (defthm nth-redef
         (equal (nth n x)
                (if (zp n)
                    (car x)
                  (nth (1- n) (cdr x))))
         :rule-classes :definition))

(local (defun nth-ind (n x)
         (if (zp n)
             (car x)
           (nth-ind (1- n) (cdr x)))))

(defsection svexlist-[=
  (defun-sk svexlist-[= (x y)
    (forall env
            (4veclist-[= (svexlist-eval x env)
                         (svexlist-eval y env)))
    :rewrite :direct)

  (in-theory (disable svexlist-[=))

  (defcong svexlist-eval-equiv equal (svexlist-[= x y) 1
    :hints (("goal" :in-theory (e/d (svexlist-[=)
                                    (svexlist-[=-necc))
             :use ((:instance svexlist-[=-necc
                    (x x-equiv)
                    (env (svexlist-[=-witness x y)))
                   (:instance svexlist-[=-necc
                    (env (svexlist-[=-witness x-equiv y)))))))
  (defcong svexlist-eval-equiv equal (svexlist-[= x y) 2
    :hints (("goal" :in-theory (e/d (svexlist-[=)
                                    (svexlist-[=-necc))
             :use ((:instance svexlist-[=-necc
                    (y y-equiv)
                    (env (svexlist-[=-witness x y)))
                   (:instance svexlist-[=-necc
                    (env (svexlist-[=-witness x y-equiv)))))))


  (defthm svex-[=-car-when-svexlist-[=
    (implies (svexlist-[= x y)
             (svex-[= (car x) (car y)))
    :hints (("goal" :expand ((svex-[= (car x) (car y)))
             :in-theory (disable svexlist-[=-necc)
             :use ((:instance svexlist-[=-necc
                    (env (svex-[=-witness (car x) (car y))))))))

  (defthm svexlist-[=-cdr-when-svexlist-[=
    (implies (svexlist-[= x y)
             (svexlist-[= (cdr x) (cdr y)))
    :hints (("goal" :expand ((svexlist-[= (cdr x) (cdr y)))
             :in-theory (disable svexlist-[=-necc)
             :use ((:instance svexlist-[=-necc
                    (env (svexlist-[=-witness (cdr x) (cdr y))))))))

  (local (defun nth-x-y-ind (n x y)
           (if (zp n)
               (list x y)
             (nth-x-y-ind (1- n) (cdr x) (cdr y)))))

  (local (defthm nth-redef
           (equal (nth n x)
                  (if (zp n)
                      (car x)
                    (nth (1- n) (cdr x))))
           :rule-classes :definition))


  (defthm svex-[=-nth-when-svexlist-[=
    (implies (svexlist-[= x y)
             (svex-[= (nth n x) (nth n y)))
    :hints (("goal" :induct (nth-x-y-ind n x y)
             :in-theory (e/d (nth-redef) (nth default-car default-cdr)))))

  (defthm svexlist-[=-of-cons
    (implies (and (svex-[= x1 x2)
                  (svexlist-[= y1 y2))
             (svexlist-[= (cons x1 y1) (cons x2 y2)))
    :hints (("goal" :expand ((svexlist-[= (cons x1 y1) (cons x2 y2)))
             :in-theory (disable svexlist-[=-necc svex-[=-necc)
             :use ((:instance svex-[=-necc
                    (x x1) (y x2) (env (svexlist-[=-witness (cons x1 y1) (cons x2 y2))))
                   (:instance svexlist-[=-necc
                    (x y1) (y y2) (env (svexlist-[=-witness (cons x1 y1) (cons x2 y2))))))))

  (defthm svexlist-[=-refl
    (svexlist-[= x x)
    :hints(("Goal" :in-theory (enable svexlist-[=)))))


(defsection svex-env-[=
  (defcong svex-envs-similar equal (svex-env-[= x y) 1
    :hints(("Goal" :in-theory (e/d (svex-env-[=)
                                   (svex-env-[=-necc))
            :use ((:instance svex-env-[=-necc
                   (x x-equiv)
                   (var (svex-env-[=-witness x y)))
                  (:instance svex-env-[=-necc
                   (var (svex-env-[=-witness x-equiv y)))))))

  (defcong svex-envs-similar equal (svex-env-[= x y) 2
    :hints(("Goal" :in-theory (e/d (svex-env-[=)
                                   (svex-env-[=-necc))
            :use ((:instance svex-env-[=-necc
                   (y y-equiv)
                   (var (svex-env-[=-witness x y)))
                  (:instance svex-env-[=-necc
                   (var (svex-env-[=-witness x y-equiv)))))))


  (defthm svex-env-[=-of-cons
    (implies (and (4vec-[= val1 val2)
                  (svex-env-[= rest1 rest2))
             (svex-env-[= (cons (cons var val1) rest1)
                          (cons (cons var val2) rest2)))
    :hints (("goal" :expand ((svex-env-[= (cons (cons var val1) rest1)
                                          (cons (cons var val2) rest2)))
             :in-theory (e/d (svex-env-lookup) (svex-env-[=-necc svex-[=-necc))
             :use ((:instance svex-env-[=-necc
                    (x rest1) (y rest2)
                    (var (svex-env-[=-witness (cons (cons var val1) rest1)
                                              (cons (cons var val2) rest2))))))))

  (local (defthm consp-hons-assoc-equal
           (iff (consp (hons-assoc-equal k x))
                (hons-assoc-equal k x))))

  (local (defthm svex-env-boundp-redef
           (equal (svex-env-boundp var env)
                  (consp (hons-assoc-equal (svar-fix var) (svex-env-fix env))))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))

  (local (defthm hons-assoc-equal-iff-member-alist-keys
           (iff (hons-assoc-equal k x)
                (member-equal k (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svex-env-[=-of-append
    (implies (and (svex-env-[= a1 b1)
                  (svex-env-[= a2 b2)
                  (set-equiv (alist-keys (svex-env-fix a1))
                             (alist-keys (svex-env-fix b1))))
             (svex-env-[= (append a1 a2)
                          (append b1 b2)))
    :hints (("goal" :expand ((svex-env-[= (append a1 a2)
                                          (append b1 b2)))
             :in-theory (e/d (svex-env-lookup svex-env-boundp-redef)
                             (svex-env-[=-necc
                              svex-[=-necc
                              hons-assoc-equal-of-svex-env-fix))
             :use ((:instance svex-env-[=-necc
                    (x a1) (y b1)
                    (var (svex-env-[=-witness (append a1 a2)
                                              (append b1 b2))))
                   (:instance svex-env-[=-necc
                    (x a2) (y b2)
                    (var (svex-env-[=-witness (append a1 a2)
                                              (append b1 b2)))))
             :do-not-induct t)))

  (defthm svex-env-[=-refl
    (svex-env-[= x x)
    :hints(("Goal" :in-theory (enable svex-env-[=)))))

(local (defthmd svex-eval-of-svex-lookup
         (equal (svex-eval (svex-lookup k x) env)
                (svex-env-lookup k (svex-alist-eval x env)))))

(defsection svex-alist-[=
  (defun-sk svex-alist-[= (x y)
    (forall env
            (svex-env-[= (svex-alist-eval x env)
                         (svex-alist-eval y env)))
    :rewrite :direct)

  (in-theory (disable svex-alist-[=))

  (defcong svex-alist-eval-equiv equal (svex-alist-[= x y) 1
    :hints (("goal" :in-theory (e/d (svex-alist-[=)
                                    (svex-alist-[=-necc))
             :use ((:instance svex-alist-[=-necc
                    (x x-equiv)
                    (env (svex-alist-[=-witness x y)))
                   (:instance svex-alist-[=-necc
                    (env (svex-alist-[=-witness x-equiv y)))))))
  (defcong svex-alist-eval-equiv equal (svex-alist-[= x y) 2
    :hints (("goal" :in-theory (e/d (svex-alist-[=)
                                    (svex-alist-[=-necc))
             :use ((:instance svex-alist-[=-necc
                    (y y-equiv)
                    (env (svex-alist-[=-witness x y)))
                   (:instance svex-alist-[=-necc
                    (env (svex-alist-[=-witness x y-equiv)))))))

  (defthm svex-[=-of-svex-lookup-when-svex-alist-[=
    (implies (svex-alist-[= x y)
             (svex-[= (svex-lookup k x) (svex-lookup k y)))
    :hints (("goal" :expand ((svex-[= (svex-lookup k x) (svex-lookup k y)))
             :in-theory (e/d (svex-eval-of-svex-lookup)
                             (svex-alist-[=-necc
                              svex-env-lookup-of-svex-alist-eval))
             :use ((:instance svex-alist-[=-necc
                    (env (svex-[=-witness (svex-lookup k x) (svex-lookup k y))))))))

  (local (defthmd svex-lookup-iff-member-svex-alist-keys
           (iff (svex-lookup var x)
                (member-equal (svar-fix var) (svex-alist-keys x)))))

  (defthm svex-[=-of-svex-compose-lookup-when-svex-alist-[=
    (implies (and (svex-alist-[= x y)
                  (set-equiv (svex-alist-keys x) (svex-alist-keys y)))
             (svex-[= (svex-compose-lookup k x) (svex-compose-lookup k y)))
    :hints(("Goal" :in-theory (e/d (svex-compose-lookup
                                    svex-lookup-iff-member-svex-alist-keys)
                                   (member-svex-alist-keys)))))

  (defund svex-alist-[=-lookup-witness (x y)
    (svex-env-[=-witness (svex-alist-eval x (svex-alist-[=-witness x y))
                         (svex-alist-eval y (svex-alist-[=-witness x y))))

  (defthmd svex-alist-[=-in-terms-of-lookup
    (equal (svex-alist-[= x y)
           (let ((var (svex-alist-[=-lookup-witness x y)))
             (svex-[= (svex-lookup var x) (svex-lookup var y))))
    :hints(("goal" :cases ((svex-alist-[= x y)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (svex-alist-[= svex-env-[= svex-alist-[=-lookup-witness)
                                  (svex-[=-necc))
                  :use ((:instance svex-[=-necc
                         (x (svex-lookup (svex-alist-[=-lookup-witness x y) x))
                         (y (svex-lookup (svex-alist-[=-lookup-witness x y) y))
                         (env (svex-alist-[=-witness x y)))))))
    :rule-classes ((:definition :install-body nil)))

  (defthm svex-alist-[=-refl
    (svex-alist-[= x x)
    :hints(("Goal" :in-theory (enable svex-alist-[=)))))

(defsection svex-monotonic-p
  (defcong svex-eval-equiv equal (svex-monotonic-p x) 1
    :hints(("Goal" :in-theory (e/d (svex-monotonic-p)
                                   (svex-monotonic-p-necc))
            :use ((:instance svex-monotonic-p-necc
                   (env1 (mv-nth 0 (svex-monotonic-p-witness x-equiv)))
                   (env2 (mv-nth 1 (svex-monotonic-p-witness x-equiv))))
                  (:instance svex-monotonic-p-necc
                   (x x-equiv)
                   (env1 (mv-nth 0 (svex-monotonic-p-witness x)))
                   (env2 (mv-nth 1 (svex-monotonic-p-witness x)))))))))

(defsection svexlist-monotonic-p
  (defcong svexlist-eval-equiv equal (svexlist-monotonic-p x) 1
    :hints(("Goal" :in-theory (e/d (svexlist-monotonic-p)
                                   (svexlist-monotonic-p-necc))
            :use ((:instance svexlist-monotonic-p-necc
                   (env1 (mv-nth 0 (svexlist-monotonic-p-witness x-equiv)))
                   (env2 (mv-nth 1 (svexlist-monotonic-p-witness x-equiv))))
                  (:instance svexlist-monotonic-p-necc
                   (x x-equiv)
                   (env1 (mv-nth 0 (svexlist-monotonic-p-witness x)))
                   (env2 (mv-nth 1 (svexlist-monotonic-p-witness x))))))))

  (defthm svex-monotonic-p-of-car-when-svexlist-monotonic-p
    (implies (svexlist-monotonic-p x)
             (svex-monotonic-p (car x)))
    :hints(("Goal" :in-theory (e/d (svex-monotonic-p)
                                   (svexlist-monotonic-p-necc))
            :use ((:instance svexlist-monotonic-p-necc
                   (env1 (mv-nth 0 (svex-monotonic-p-witness (car x))))
                   (env2 (mv-nth 1 (svex-monotonic-p-witness (car x)))))))))

  (defthm svexlist-monotonic-p-of-cdr-when-svexlist-monotonic-p
    (implies (svexlist-monotonic-p x)
             (svexlist-monotonic-p (cdr x)))
    :hints(("Goal" :in-theory (e/d (svexlist-monotonic-p)
                                   (svexlist-monotonic-p-necc))
            :use ((:instance svexlist-monotonic-p-necc
                   (env1 (mv-nth 0 (svexlist-monotonic-p-witness (cdr x))))
                   (env2 (mv-nth 1 (svexlist-monotonic-p-witness (cdr x)))))))))

  (defthm svex-monotonic-p-of-nth-when-svexlist-monotonic-p
    (implies (svexlist-monotonic-p x)
             (svex-monotonic-p (nth n x)))
    :hints (("goal" :induct (nth-ind n x)
             :in-theory (e/d (nth-redef) (nth))))))

(defsection svex-alist-monotonic-p
  (defun-sk svex-alist-monotonic-p (x)
    (forall (env1 env2)
            (implies (svex-env-[= env1 env2)
                     (svex-env-[= (svex-alist-eval x env1)
                                  (svex-alist-eval x env2))))
    :rewrite :direct)
            
  (in-theory (disable svex-alist-monotonic-p))

  (defcong svex-alist-eval-equiv equal (svex-alist-monotonic-p x) 1
    :hints(("Goal" :in-theory (e/d (svex-alist-monotonic-p)
                                   (svex-alist-monotonic-p-necc))
            :use ((:instance svex-alist-monotonic-p-necc
                   (env1 (mv-nth 0 (svex-alist-monotonic-p-witness x-equiv)))
                   (env2 (mv-nth 1 (svex-alist-monotonic-p-witness x-equiv))))
                  (:instance svex-alist-monotonic-p-necc
                   (x x-equiv)
                   (env1 (mv-nth 0 (svex-alist-monotonic-p-witness x)))
                   (env2 (mv-nth 1 (svex-alist-monotonic-p-witness x))))))))

  (defthm svex-monotonic-p-of-svex-lookup-when-svex-alist-monotonic-p
    (implies (svex-alist-monotonic-p x)
             (svex-monotonic-p (svex-lookup k x)))
    :hints(("Goal" :in-theory (e/d (svex-monotonic-p
                                    svex-eval-of-svex-lookup)
                                   (svex-alist-monotonic-p-necc
                                    svex-env-lookup-of-svex-alist-eval))
            :use ((:instance svex-alist-monotonic-p-necc
                   (env1 (mv-nth 0 (svex-monotonic-p-witness (svex-lookup k x))))
                   (env2 (mv-nth 1 (svex-monotonic-p-witness (svex-lookup k x)))))))))

  (defthm svex-monotonic-p-of-svex-compose-lookup-when-svex-alist-monotonic-p
    (implies (svex-alist-monotonic-p x)
             (svex-monotonic-p (svex-compose-lookup k x)))
    :hints(("Goal" :in-theory (e/d (svex-monotonic-p
                                    svex-compose-lookup
                                    svex-eval-of-svex-lookup
                                    svex-eval)
                                   (svex-alist-monotonic-p-necc
                                    svex-env-lookup-of-svex-alist-eval))
            :use ((:instance svex-alist-monotonic-p-necc
                   (env1 (mv-nth 0 (svex-monotonic-p-witness (svex-compose-lookup k x))))
                   (env2 (mv-nth 1 (svex-monotonic-p-witness (svex-compose-lookup k x)))))))))

  (defund svex-alist-monotonic-lookup-witness (x)
    (mv-let (env1 env2)
      (svex-alist-monotonic-p-witness x)
      (svex-env-[=-witness (svex-alist-eval x env1)
                           (svex-alist-eval x env2))))

  (defthmd svex-alist-monotonic-in-terms-of-lookup
    (equal (svex-alist-monotonic-p x)
           (let ((var (svex-alist-monotonic-lookup-witness x)))
             (svex-monotonic-p (svex-lookup var x))))
    :hints(("goal" :cases ((svex-alist-monotonic-p x)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (svex-alist-monotonic-p svex-env-[= svex-alist-monotonic-lookup-witness)
                                  (svex-monotonic-p-necc))
                  :use ((:instance svex-monotonic-p-necc
                         (x (svex-lookup (svex-alist-monotonic-lookup-witness x) x))
                         (env1 (mv-nth 0 (svex-alist-monotonic-p-witness x)))
                         (env2 (mv-nth 1 (svex-alist-monotonic-p-witness x))))))))
    :rule-classes ((:definition :install-body nil))))


(defsection compose-monotonic
  (local (in-theory (enable svex-monotonic-p-necc
                            svexlist-monotonic-p-necc)))

  (defthm svex-compose-monotonic
    (implies (and (svex-monotonic-p x)
                  (svex-alist-monotonic-p a))
             (svex-monotonic-p (svex-compose x a)))
    :hints (("goal" :expand ((svex-monotonic-p (svex-compose x a))))))

  (defthm svexlist-compose-monotonic
    (implies (and (svexlist-monotonic-p x)
                  (svex-alist-monotonic-p a))
             (svexlist-monotonic-p (svexlist-compose x a)))
    :hints (("goal" :expand ((svexlist-monotonic-p (svexlist-compose x a))))))

  (defthm svex-alist-compose-monotonic
    (implies (and (svex-alist-monotonic-p x)
                  (svex-alist-monotonic-p a))
             (svex-alist-monotonic-p (svex-alist-compose x a)))
    :hints (("goal" :expand ((svex-alist-monotonic-p (svex-alist-compose x a))))))


  (defthm svex-compose-preserves-alist-[=
    (implies (and (svex-monotonic-p x)
                  (svex-alist-[= a b)
                  (set-equiv (svex-alist-keys a) (svex-alist-keys b)))
             (svex-[= (svex-compose x a) (svex-compose x b)))
    :hints (("goal" :in-theory (enable svex-[=))))

  (defthm svexlist-compose-preserves-alist-[=
    (implies (and (svexlist-monotonic-p x)
                  (svex-alist-[= a b)
                  (set-equiv (svex-alist-keys a) (svex-alist-keys b)))
             (svexlist-[= (svexlist-compose x a) (svexlist-compose x b)))
    :hints (("goal" :in-theory (enable svexlist-[=))))

  (defthm svex-alist-compose-preserves-alist-[=
    (implies (and (svex-alist-monotonic-p x)
                  (svex-alist-[= a b)
                  (set-equiv (svex-alist-keys a) (svex-alist-keys b)))
             (svex-alist-[= (svex-alist-compose x a) (svex-alist-compose x b)))
    :hints (("goal" :expand ((svex-alist-[= (svex-alist-compose x a) (svex-alist-compose x b))))))

  (defthm svex-compose-preserves-[=
    (implies (svex-[= x y)
             (svex-[= (svex-compose x a) (svex-compose y a)))
    :hints (("goal" :in-theory (enable svex-[=))))

  (defthm svexlist-compose-preserves-[=
    (implies (svexlist-[= x y)
             (svexlist-[= (svexlist-compose x a) (svexlist-compose y a)))
    :hints (("goal" :in-theory (enable svexlist-[=))))

  (defthm svex-alist-compose-preserves-[=
    (implies (svex-alist-[= x y)
             (svex-alist-[= (svex-alist-compose x a) (svex-alist-compose y a)))
    :hints (("goal" :expand ((svex-alist-[= (svex-alist-compose x a) (svex-alist-compose y a)))))))
