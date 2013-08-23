; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "bvecs")
(include-book "tools/bstar" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable floor)))

(defthm consp-bfr-eval-list
  (equal (consp (bfr-eval-list x env))
         (consp x))
  :hints(("Goal" :in-theory (enable bfr-eval-list))))

(defthm bfr-eval-list-consts
  (implies (and (syntaxp (and (quotep x)
                              (boolean-listp (cadr x))))
                (boolean-listp x))
           (equal (bfr-eval-list x env) x)))

(local (bfr-reasoning-mode t))


;; If/then/else where the branches are (unsigned) bit vectors
(defn bfr-ite-bvv-fn (c v1 v0)
  (declare (xargs :measure (+ (acl2-count v1) (acl2-count v0))
                  :guard t))
  (if (and (atom v1) (atom v0))
      nil
    (b* (((mv v11 v1r) (car/cdr v1))
         ((mv v01 v0r) (car/cdr v0))
         (tail (bfr-ite-bvv-fn c v1r v0r))
         (head (bfr-ite-fn c v11 v01)))
      (bfr-ucons head tail))))

(defthm pbfr-list-depends-on-of-bfr-ite-bvv-fn
  (implies (and (not (pbfr-depends-on n p c))
                (not (pbfr-list-depends-on n p v1))
                (not (pbfr-list-depends-on n p v0)))
           (not (pbfr-list-depends-on n p (bfr-ite-bvv-fn c v1 v0))))
  :hints(("Goal" :in-theory (e/d (pbfr-list-depends-on)
                                 (pbfr-depends-on (pbfr-depends-on)
                                                  (pbfr-list-depends-on))))))

(defthm eval-of-bfr-ite-bvv-fn
  (equal (bfr-list->u (bfr-ite-bvv-fn c v1 v0) env)
         (if (bfr-eval c env)
             (bfr-list->u v1 env)
           (bfr-list->u v0 env)))
  :hints (("goal" :induct (bfr-ite-bvv-fn c v1 v0))))

(defmacro bfr-ite-bvv (c v1 v0)
  `(let ((bfr-ite-bvv-test ,c))
     (if bfr-ite-bvv-test
         (if (eq bfr-ite-bvv-test t)
             ,v1
           (bfr-ite-bvv-fn bfr-ite-bvv-test ,v1 ,v0))
       ,v0)))

;; (defcong bfr-equiv bfr-list-equiv (cons a b) 1
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))))))

;; (defcong bfr-list-equiv bfr-list-equiv (cons a b) 2
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))))))

;; (defcong bfr-list-equiv bfr-list-equiv (cdr x) 1
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))
;;                  :in-theory (disable bfr-list-equiv-necc
;;                                      bfr-list-equiv-implies-equal-bfr-eval-list-1)
;;                  :use ((:instance bfr-list-equiv-necc
;;                         (x x) (y x-equiv)
;;                         (env (bfr-list-equiv-witness
;;                               (cdr x) (cdr x-equiv)))))))))

;; (defcong bfr-list-equiv bfr-equiv (car x) 1
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))
;;                  :in-theory (disable bfr-list-equiv-necc
;;                                      bfr-list-equiv-implies-equal-bfr-eval-list-1)
;;                  :use ((:instance bfr-list-equiv-necc
;;                         (x x) (y x-equiv)
;;                         (env (bfr-equiv-witness
;;                               (car x) (car x-equiv)))))))))

;; (defcong bfr-equiv bfr-list-equiv (bfr-ite-bvv-fn c v1 v0) 1
;;   :hints (("goal" :induct (bfr-ite-bvv-fn1 c v1 v0))))
;;           (and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))))))

;; (defcong bfr-list-equiv equal (bfr-ite-bvv-fn c v1 v0) 2)
;; (defcong bfr-list-equiv equal (bfr-ite-bvv-fn c v1 v0) 3)



(defn bfr-ite-bss-fn (c v1 v0)
  (declare (xargs :measure (+ (acl2-count v1) (acl2-count v0))
                  :guard t))
  (b* (((mv head1 tail1 end1) (first/rest/end v1))
       ((mv head0 tail0 end0) (first/rest/end v0)))
    (if (and end1 end0)
        (bfr-sterm (bfr-ite-fn c head1 head0))
      (let ((rst (bfr-ite-bss-fn c tail1 tail0))
            (head (bfr-ite c head1 head0)))
        (bfr-scons head rst)))))


(defthm pbfr-list-depends-on-of-bfr-ite-bss-fn
  (implies (and (not (pbfr-depends-on n p c))
                (not (pbfr-list-depends-on n p v1))
                (not (pbfr-list-depends-on n p v0)))
           (not (pbfr-list-depends-on n p (bfr-ite-bss-fn c v1 v0))))
  :hints(("Goal" :in-theory (e/d (pbfr-list-depends-on)
                                 (pbfr-depends-on (pbfr-depends-on)
                                                  (pbfr-list-depends-on))))))



(defthm eval-of-bfr-ite-bss-fn
  (equal (bfr-list->s (bfr-ite-bss-fn c v1 v0) env)
            (if (bfr-eval c env)
                (bfr-list->s v1 env)
              (bfr-list->s v0 env)))
  :hints (("goal" :induct (bfr-ite-bss-fn c v1 v0))))

;; (defcong bfr-equiv equal (bfr-ite-bss-fn c v1 v0) 1)
;; (defcong bfr-list-equiv equal (bfr-ite-bss-fn c v1 v0) 2)
;; (defcong bfr-list-equiv equal (bfr-ite-bss-fn c v1 v0) 3)

(defmacro bfr-ite-bss (c v1 v0)
  `(let ((bfr-ite-bss-test ,c))
     (if bfr-ite-bss-test
         (if (eq bfr-ite-bss-test t)
             ,v1
           (bfr-ite-bss-fn bfr-ite-bss-test ,v1 ,v0))
       ,v0)))


(add-macro-alias bfr-ite-bss bfr-ite-bss-fn)

(defthm bfr-eval-list-of-atom
  (implies (not (consp x))
           (equal (bfr-eval-list x env) nil))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;; (defthmd v2n-bfr-eval-list-atom
;;   (implies (atom x)
;;            (equal (v2n (bfr-eval-list x env)) 0))
;;   :hints (("goal" :in-theory (enable v2n bfr-eval-list))))


;; (defthmd bfr-ite-bvv-fn-nil
;;   (implies (not (bfr-ite-bvv-fn c v1 v0))
;;            (and (implies (bfr-eval c env)
;;                          (equal (v2n (bfr-eval-list v1 env)) 0))
;;                 (implies (not (bfr-eval c env))
;;                          (equal (v2n (bfr-eval-list v0 env)) 0))))
;;   :hints (("Goal" :in-theory (enable v2n bfr-eval-list)))
;;   :otf-flg t)

;; (defthmd v2n-bfr-ite-bvv-fn
;;   (equal (v2n (bfr-eval-list (bfr-ite-bvv-fn c v1 v0) env))
;;          (if (bfr-eval c env)
;;              (v2n (bfr-eval-list v1 env))
;;            (v2n (bfr-eval-list v0 env))))
;;   :hints (("Goal" :in-theory (enable v2n bfr-eval-list))))

;; (defthm v2i-bfr-ite-bss-fn
;;   (equal (v2i (bfr-eval-list (bfr-ite-bss-fn c v1 v0) env))
;;          (if (bfr-eval c env)
;;              (v2i (bfr-eval-list v1 env))
;;            (v2i (bfr-eval-list v0 env))))
;;   :hints(("Goal" :in-theory (enable v2i bfr-eval-list))))


;; (defthmd boolean-listp-bfr-ite-bvv-fn-v2n-bind-env-car-env
;;   (implies (and (bind-free '((env . (car env))) (env))
;;                 (boolean-listp (bfr-ite-bvv-fn c v1 v0)))
;;            (equal (v2n (bfr-ite-bvv-fn c v1 v0))
;;                   (if (bfr-eval c env)
;;                       (v2n (bfr-eval-list v1 env))
;;                     (v2n (bfr-eval-list v0 env)))))
;;   :hints (("goal" :use ((:instance bfr-eval-list-consts
;;                                    (x (bfr-ite-bvv-fn c v1 v0)))
;;                         v2n-bfr-ite-bvv-fn)
;;            :in-theory (e/d ()
;;                            (bfr-ite-bvv-fn v2n-bfr-ite-bvv-fn
;;                                bfr-eval-list-consts)))))

;; (defthmd boolean-listp-bfr-ite-bss-fn-v2i-bind-env-car-env
;;   (implies (and (bind-free '((env . (car env))) (env))
;;                 (boolean-listp (bfr-ite-bss-fn c v1 v0)))
;;            (equal (v2i (bfr-ite-bss-fn c v1 v0))
;;                   (if (bfr-eval c env)
;;                       (v2i (bfr-eval-list v1 env))
;;                     (v2i (bfr-eval-list v0 env)))))
;;   :hints (("goal" :use ((:instance bfr-eval-list-consts
;;                                    (x (bfr-ite-bss-fn c v1 v0)))
;;                         v2i-bfr-ite-bss-fn)
;;            :in-theory (e/d ()
;;                            (bfr-ite-bss-fn v2i-bfr-ite-bss-fn
;;                                bfr-eval-list-consts)))))






(in-theory (disable bfr-ite-bss-fn bfr-ite-bvv-fn))


