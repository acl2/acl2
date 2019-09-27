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
(include-book "bvecs")
(include-book "centaur/ubdds/param" :dir :system)
(include-book "centaur/aig/misc" :dir :system)
(local (include-book "centaur/aig/eval-restrict" :dir :system))

(local (in-theory (disable acl2::append-of-nil)))


(defun bfr-list-to-param-space (p x)
  (declare (xargs :guard t
                  :guard-hints ('(:in-theory (enable bfr-to-param-space
                                                     bfr-list-to-param-space))))
           (ignorable p))
  (mbe :logic (if (atom x)
                  nil
                (cons (bfr-to-param-space p (car x))
                      (bfr-list-to-param-space p (cdr x))))
       :exec (if (atom x)
                 nil
               (bfr-case :bdd (acl2::to-param-space-list p x)
                         :aig (acl2::aig-restrict-list
                               x (acl2::aig-extract-iterated-assigns-alist p 10))))))

(defthm bfr-eval-list-to-param-space-list
  (implies (bfr-eval p env)
           (equal (bfr-eval-list (bfr-list-to-param-space p x)
                                 (bfr-param-env p env))
                  (bfr-eval-list x env)))
  :hints(("Goal" :in-theory (e/d (bfr-eval-list
                                  bfr-list-to-param-space)
                                 (bfr-param-env)))))

(defthm bfr-eval-list-to-param-space-list-with-unparam-env
  (implies (and (syntaxp (not (and (consp env)
                                   (eq (car env) 'bfr-param-env))))
                (bdd-mode-or-p-true p env))
           (equal (bfr-eval-list (bfr-list-to-param-space p x)
                                 env)
                  (bfr-eval-list x (bfr-unparam-env p env))))
  :hints(("Goal" :in-theory (e/d (bfr-eval-list
                                  bfr-list-to-param-space)
                                 (bfr-param-env)))))

(defthm bfr-list->s-to-param-space-list
  (implies (bfr-eval p env)
           (equal (bfr-list->s (bfr-list-to-param-space p x)
                               (bfr-param-env p env))
                  (bfr-list->s x env)))
  :hints(("Goal" :in-theory (e/d (bfr-list->s
                                  scdr s-endp
                                  default-car
                                  bfr-list-to-param-space)
                                 (bfr-to-param-space
                                  bfr-param-env))
          :induct (bfr-list-to-param-space p x)
          :expand ((bfr-list->s x env)
                   (:free (x y env) (bfr-list->s (cons x y) env))))))

(defthm bfr-list->s-to-param-space-list-with-unparam-env
  (implies (and (syntaxp (not (and (consp env)
                                   (eq (car env) 'bfr-param-env))))
                (bdd-mode-or-p-true p env))
           (equal (bfr-list->s (bfr-list-to-param-space p x)
                               env)
                  (bfr-list->s x (bfr-unparam-env p env))))
  :hints(("Goal" :in-theory (e/d (bfr-list->s
                                  scdr s-endp
                                  default-car
                                  bfr-list-to-param-space)
                                 (bfr-to-param-space
                                  bfr-param-env))
          :induct (bfr-list-to-param-space p x)
          :expand ((:free (env) (bfr-list->s x env))
                   (:free (x y env) (bfr-list->s (cons x y) env))))))

(defthm bfr-list->u-to-param-space-list
  (implies (bfr-eval p env)
           (equal (bfr-list->u (bfr-list-to-param-space p x)
                               (bfr-param-env p env))
                  (bfr-list->u x env)))
  :hints(("Goal" :in-theory (e/d (bfr-list->u scdr s-endp
                                              ;; bfr-eval
                                              bfr-list-to-param-space)
                                 (bfr-to-param-space
                                  bfr-param-env)))))

(defthm bfr-list->u-to-param-space-list-with-unparam-env
  (implies (and (syntaxp (not (and (consp env)
                                   (eq (car env) 'bfr-param-env))))
                (bdd-mode-or-p-true p env))
           (equal (bfr-list->u (bfr-list-to-param-space p x)
                               env)
                  (bfr-list->u x (bfr-unparam-env p env))))
  :hints(("Goal" :in-theory (e/d (bfr-list->u scdr s-endp
                                              ;; bfr-eval
                                              bfr-list-to-param-space)
                                 (bfr-to-param-space
                                  bfr-param-env)))))

(defund genv-param (p env)
  (declare (xargs :guard (consp env))
           (ignorable p))
  (cons (bfr-param-env p (car env))
        (cdr env)))

(defund genv-unparam (p env)
  (declare (xargs :guard (consp env))
           (ignorable p))
  (cons (bfr-unparam-env p (car env))
        (cdr env)))





;; (defun bfr-list-from-param-space (p x)
;;   (declare (xargs :guard t))
;;   (if (atom x)
;;       nil
;;     (cons (bfr-from-param-space p (car x))
;;           (bfr-list-from-param-space p (cdr x)))))

;; (defthm bfr-list-from-param-space-of-list-fix
;;   (equal (bfr-list-from-param-space p (list-fix x))
;;          (bfr-list-from-param-space p x)))


;; (defthm bfr-eval-list-from-param-space
;;   (implies (bfr-eval p env)
;;            (equal (bfr-eval-list (bfr-list-from-param-space p x) env)
;;                   (bfr-eval-list x (bfr-param-env p env)))))

;; (defthm bfr-list->s-from-param-space
;;   (implies (bfr-eval p env)
;;            (equal (bfr-list->s (bfr-list-from-param-space p x) env)
;;                   (bfr-list->s x (bfr-param-env p env))))
;;   :hints(("Goal" :in-theory (enable bfr-list->s s-endp scdr))))

;; (defthm bfr-list->u-from-param-space
;;   (implies (bfr-eval p env)
;;            (equal (bfr-list->u (bfr-list-from-param-space p x) env)
;;                   (bfr-list->u x (bfr-param-env p env))))
;;   :hints(("Goal" :in-theory (enable bfr-list->u))))
