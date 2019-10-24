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

(include-book "logicman")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defthm fgl-objectlist-eval-when-consp
  (implies (consp x)
           (equal (fgl-objectlist-eval x env)
                  (cons (fgl-object-eval (car x) env)
                        (fgl-objectlist-eval (cdr x) env))))
  :hints(("Goal" :in-theory (enable fgl-objectlist-eval))))


(in-theory (enable fgl-objectlist-bfrlist-when-consp))



(in-theory (enable fgl-objectlist-bfrlist-when-consp))

(defthm len-equal-0
  (equal (equal (len x) 0)
         (not (consp x))))

(defthm len-of-cons
  (equal (len (cons a b))
         (+ 1 (len b))))

;; (defun len-is (x n)
;;   (if (zp n)
;;       (and (eql n 0) (atom x))
;;     (and (consp x)
;;          (len-is (cdr x) (1- n)))))

;; (defthm open-len-is
;;   (implies (syntaxp (quotep n))
;;            (equal (len-is x n)
;;                   (if (zp n)
;;                       (and (eql n 0) (atom x))
;;                     (and (consp x)
;;                          (len-is (cdr x) (1- n)))))))
                         

;; (defthm equal-len-hyp
;;   (implies (syntaxp (and (or (acl2::rewriting-negative-literal-fn `(equal (len ,x) ,n) mfc state)
;;                              (acl2::rewriting-negative-literal-fn `(equal ,n (len ,x)) mfc state))
;;                          (quotep n)))
;;            (equal (equal (len x) n)
;;                   (len-is x n))))

(defthm equal-of-len
  (implies (syntaxp (quotep n))
           (equal (equal (len x) n)
                  (if (zp n)
                      (and (equal n 0) (atom x))
                    (and (consp x)
                         (equal (len (cdr x)) (1- n)))))))

(in-theory (enable* fgl-object-bfrlist-when-thms))

(defthm gobj-bfr-list-eval-of-nil
  (equal (gobj-bfr-list-eval nil x) nil)
  :hints(("Goal" :in-theory (enable gobj-bfr-list-eval))))

(defthm bools->int-of-single
  (equal (bools->int (list x))
         (- (bool->bit x)))
  :hints(("Goal" :in-theory (enable bools->int))))

(in-theory (disable len))

(defthm bools->int-of-cons
  (equal (bools->int (cons x y))
         (if (consp y)
             (logcons (bool->bit x) (bools->int y))
           (- (bool->bit x))))
  :hints(("Goal" :in-theory (enable bools->int))))

(defthm logcar-of-bools->int
  (equal (logcar (bools->int x))
         (bool->bit (car x)))
  :hints(("Goal" :in-theory (enable bools->int))))

(defthm car-of-gobj-bfr-list-eval
  (equal (car (gobj-bfr-list-eval x env))
         (gobj-bfr-eval (car x) env)))

(defthm scdr-of-gobj-bfr-list-eval
  (equal (scdr (gobj-bfr-list-eval x env))
         (gobj-bfr-list-eval (scdr x) env))
  :hints(("Goal" :in-theory (enable scdr gobj-bfr-list-eval))))


(defthm fgl-object-bfrlist-implies-bfr-p-gobj-syntactic-boolean->bool
  (implies (and (bfr-listp (fgl-object-bfrlist x))
                (gobj-syntactic-booleanp x))
           (bfr-p (gobj-syntactic-boolean->bool x)))
  :hints(("Goal" :in-theory (enable gobj-syntactic-booleanp
                                    gobj-syntactic-boolean->bool
                                    fgl-object-bfrlist
                                    booleanp))))

(defthm bfr-listp-of-int->bools
  (bfr-listp (int->bools x))
  :hints(("Goal" :in-theory (enable int->bools))))

(defthm fgl-object-bfrlist-implies-bfr-listp-gobj-syntactic-integer->bits
  (implies (and (bfr-listp (fgl-object-bfrlist x))
                (gobj-syntactic-integerp x))
           (bfr-listp (gobj-syntactic-integer->bits x)))
  :hints(("Goal" :in-theory (enable gobj-syntactic-integerp
                                    gobj-syntactic-integer->bits
                                    fgl-object-bfrlist))))


(defthm bools->int-when-consp
  (implies (consp b)
           (equal (bools->int (cons a b))
                  (intcons a (bools->int b))))
  :hints(("Goal" :in-theory (enable bools->int))))

(defthm fgl-object-eval-when-gobj-syntactic-booleanp
  (implies (gobj-syntactic-booleanp x)
           (equal (fgl-object-eval x env)
                  (gobj-bfr-eval (gobj-syntactic-boolean->bool x) env)))
  :hints(("Goal" :in-theory (enable gobj-syntactic-booleanp
                                    gobj-syntactic-boolean->bool))))

(defret fgl-object-eval-of-gobj-syntactic-boolean-fix
  (implies okp
           (equal (gobj-bfr-eval (gobj-syntactic-boolean->bool new-x) env)
                  (bool-fix (fgl-object-eval x env))))
  :hints(("Goal" :in-theory (enable gobj-syntactic-boolean->bool
                                    gobj-syntactic-boolean-fix
                                    gobj-syntactic-booleanp)))
  :fn gobj-syntactic-boolean-fix)

(defthm gobj-bfr-list-eval-of-int->bools
  (equal (gobj-bfr-list-eval (int->bools x) env)
         (int->bools x))
  :hints(("Goal" :in-theory (enable int->bools gobj-bfr-list-eval))))

(defthm bools->int-of-int->bools
  (equal (bools->int (int->bools x))
         (ifix x))
  :hints(("Goal" :in-theory (enable int->bools bools->int))))

(defthm fgl-object-eval-when-gobj-syntactic-integerp
  (implies (gobj-syntactic-integerp x)
           (equal (fgl-object-eval x env)
                  (bools->int (gobj-bfr-list-eval (gobj-syntactic-integer->bits x) env))))
  :hints(("Goal" :in-theory (enable gobj-syntactic-integerp
                                    gobj-syntactic-integer->bits))))

(defret fgl-object-eval-of-gobj-syntactic-integer-fix
  (implies okp
           (equal (bools->int (gobj-bfr-list-eval (gobj-syntactic-integer->bits new-x) env))
                  (ifix (fgl-object-eval x env))))
  :hints(("Goal" :in-theory (e/d (gobj-syntactic-integer-fix
                                  gobj-syntactic-integer->bits
                                  fgl-object-p-when-integerp
                                  fgl-object-kind-when-integerp
                                  g-concrete->val-when-integerp))))
  :fn gobj-syntactic-integer-fix)

(defthm fgl-object-bfrlist-when-integerp
  (implies (integerp x)
           (equal (fgl-object-bfrlist x) nil))
  :hints(("Goal" :in-theory (enable fgl-object-kind-when-integerp))))

(defret fgl-object-bfrlist-of-gobj-syntactic-integer-fix
  (implies (not (member v (fgl-object-bfrlist x)))
           (not (member v (fgl-object-bfrlist new-x))))
  :hints(("Goal" :in-theory (enable gobj-syntactic-integer-fix)))
  :fn gobj-syntactic-integer-fix)

(Defthm car-of-fgl-objectlist-fix
  (equal (car (fgl-objectlist-fix x))
         (fgl-object-fix (car x))))

(in-theory (enable bfr-listp-when-not-member-witness))


(local (defthm bit-identity
         (implies (bitp b)
                  (equal (logcons b (- b)) (- b)))
         :hints(("Goal" :in-theory (enable bitp)))))

(defthm gobj-bfr-list-eval-of-scons
  (equal (bools->int (gobj-bfr-list-eval (scons bit0 rest-bits) env))
         (intcons (gobj-bfr-eval bit0 env)
                  (bools->int (gobj-bfr-list-eval rest-bits env))))
  :hints(("Goal" :in-theory (enable gobj-bfr-list-eval scons)
          :do-not-induct t)))


(defthm equal-of-bfr-listp-witness
  (implies (bfr-p x bfrstate)
           (not (equal (bfr-listp-witness lst bfrstate) x))))




(defthm fgl-object-bfrlist-when-booleanp
  (implies (booleanp x)
           (equal (fgl-object-bfrlist x) nil))
  :hints(("Goal" :in-theory (enable fgl-object-bfrlist
                                    fgl-object-kind))))



(defthm gobj-syntactic-listp-when-gobj-syntactic-consp
  (implies (gobj-syntactic-consp x)
           (gobj-syntactic-listp x))
  :hints(("Goal" :in-theory (enable gobj-syntactic-listp
                                    gobj-syntactic-consp))))

(defthm fgl-object-bfrlist-of-gobj-syntactic-list->car
  (implies (not (member v (fgl-object-bfrlist x)))
           (not (member v (fgl-object-bfrlist (gobj-syntactic-list->car x)))))
  :hints(("Goal" :in-theory (enable gobj-syntactic-list->car))))

(defthm fgl-object-bfrlist-of-gobj-syntactic-list->cdr
  (implies (not (member v (fgl-object-bfrlist x)))
           (not (member v (fgl-object-bfrlist (gobj-syntactic-list->cdr x)))))
  :hints(("Goal" :in-theory (enable gobj-syntactic-list->cdr))))

(defthm fgl-object-eval-of-mk-g-cons
  (equal (fgl-object-eval (mk-g-cons a b) env)
         (cons (fgl-object-eval a env)
               (fgl-object-eval b env)))
  :hints(("Goal" :in-theory (enable mk-g-cons))))

(defthmd fgl-object-eval-when-gobj-syntactic-consp
  (implies (gobj-syntactic-consp x)
           (equal (fgl-object-eval x env)
                  (cons (fgl-object-eval (gobj-syntactic-list->car x) env)
                        (fgl-object-eval (gobj-syntactic-list->cdr x) env))))
  :hints(("Goal" :in-theory (enable gobj-syntactic-consp
                                    gobj-syntactic-list->cdr
                                    gobj-syntactic-list->car))))

(defthm fgl-objectlist-eval-when-atom
  (implies (not (consp x))
           (equal (fgl-objectlist-eval x env) nil))
  :hints(("Goal" :in-theory (enable fgl-objectlist-eval))))

(defthm fgl-object-bindings-eval-of-cons
  (implies (pseudo-var-p key)
           (equal (fgl-object-bindings-eval (cons (cons key val) rest) env logicman)
                  (cons (cons key (fgl-object-eval val env logicman))
                        (fgl-object-bindings-eval rest env logicman))))
  :hints(("Goal" :in-theory (enable fgl-object-bindings-eval))))

(defthm sub-alistp-hons-assoc-equal2
    (implies (and (acl2::sub-alistp a b)
                  (hons-assoc-equal x a))
             (equal (hons-assoc-equal x b)
                    (hons-assoc-equal x a)))
    :hints(("Goal" :in-theory (enable acl2::sub-alistp-hons-assoc-equal))))

(defthm assoc-equal-when-key
  (implies key
           (equal (assoc-equal key x)
                  (hons-assoc-equal key x))))

(in-theory (enable fgl-apply))

(in-theory (e/d (acl2::kwote-lst-redef)
                (kwote-lst)))
