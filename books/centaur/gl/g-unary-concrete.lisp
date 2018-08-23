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

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(in-theory (disable (mk-g-concrete)))

(defthm mk-g-concrete-of-atomic-constant
  (implies (and (syntaxp (quotep x))
                (atom x)
                (not (g-keyword-symbolp x)))
           (equal (mk-g-concrete x) x))
  :hints(("Goal" :in-theory (enable mk-g-concrete
                                    concrete-gobjectp
                                    gobject-hierarchy-lite))))

(program)
(defun def-g-unary-concrete-fn (fn integer-case boolean-case cons-case
                                   hints world)
  (let ((x (car (wgetprop fn 'formals))))
    `(progn
       (def-g-fn ,fn
         (let ((x ',x)
               (fn ',fn))
           `(if (atom ,x)
                (gret (mk-g-concrete (ec-call (,fn ,x))))
              (pattern-match ,x
                ((g-concrete obj)
                 (gret (mk-g-concrete (ec-call (,fn obj)))))
                ((g-ite test then else)
                 (if (zp clk)
                     (gret (g-apply ',fn (gl-list ,x)))
                   (g-if (gret test)
                         (,gfn then . ,params)
                         (,gfn else . ,params))))
                ((g-apply & &) (gret (g-apply ',fn (gl-list ,x))))
                ((g-var &) (gret (g-apply ',fn (gl-list ,x))))
                ((g-integer &) ,',integer-case)
                ((g-boolean &) ,',boolean-case)
                (& ,',cons-case)))))
       ;; (def-gobjectp-thm ,fn
       ;;   :hints `(("goal" :in-theory
       ;;             (e/d ()
       ;;                  ((force)
       ;;                   (:definition ,gfn)))
       ;;             :induct (,gfn ,',x . ,params)
       ;;             :expand ((,gfn ,',x . ,params)))))
       (verify-g-guards
        ,fn
        :hints `(("Goal" :in-theory (Disable ,gfn))))

       (def-gobj-dependency-thm ,fn
         :hints `(("goal" :induct ,gcall
                   :expand (,gcall)
                   :in-theory (disable (:d ,gfn)))))

       (def-g-correct-thm ,fn eval-g-base
         :hints `(("Goal" :in-theory (e/d ((:induction ,gfn)
                                           general-concrete-obj)
                                          ((:definition ,gfn)))
                   :induct (,gfn ,',x . ,params)
                   :expand ((,gfn ,',x . ,params)
                            (:with eval-g-base (eval-g-base ,',x env))))
                  . ,',hints)))))

(defmacro def-g-unary-concrete (fn &key integer-case boolean-case
                                   cons-case hints)
  `(make-event (def-g-unary-concrete-fn ',fn ',integer-case ',boolean-case
                 ',cons-case ',hints(w state))))

(logic)

(local (defthm pbfr-list-depends-on-of-cons
         (implies (and (not (pbfr-depends-on k p x1))
                       (not (pbfr-list-depends-on k p x2)))
                  (not (pbfr-list-depends-on k p (cons x1 x2))))
         :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

(local (defthm pbfr-list-depends-on-of-nil
         (not (pbfr-list-depends-on k p nil))
         :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

(local (defthm bfr-list->s-of-cons
         (implies (consp x2)
                  (equal (bfr-list->s (cons x1 x2) env)
                         (logcons (bool->bit (bfr-eval x1 env))
                                  (bfr-list->s x2 env))))
         :hints(("Goal" :expand ((bfr-list->s (cons x1 x2) env))
                 :in-theory (enable scdr s-endp)))))

(local (defthm bfr-list->s-of-singleton
         (equal (bfr-list->s (list x1) env)
                (bool->sign (bfr-eval x1 env)))
         :hints(("Goal" :expand ((bfr-list->s (cons x1 x2) env))
                 :in-theory (enable scdr s-endp)))))

(def-g-unary-concrete acl2::bool->bit$inline
  :integer-case (gret 1)
  :boolean-case (gret (mk-g-integer (list (g-boolean->bool x) nil)))
  :cons-case (gret 1)
  :hints((and stable-under-simplificationp
              '(:in-theory (enable bool->bit)))))

(def-g-unary-concrete bool->sign
  :integer-case (gret -1)
  :boolean-case (gret (mk-g-integer (list (g-boolean->bool x))))
  :cons-case (gret -1)
  :hints ((and stable-under-simplificationp
               '(:cases ((eval-g-base (g-ite->test x) env))))))

(def-g-unary-concrete symbol-name
  :integer-case (gret "")
  :boolean-case (g-if (gret x) (gret "T") (gret "NIL"))
  :cons-case (gret ""))

(def-g-unary-concrete symbol-package-name
  :integer-case (gret "")
  :boolean-case (gret "COMMON-LISP")
  :cons-case (gret "")
  :hints ((and stable-under-simplificationp
               '(:use
                 ((:instance (:type-prescription bfr-eval)
                             (x (g-boolean->bool x))
                             (env (car env))))
                 :in-theory (disable (:type-prescription bfr-eval))))))



(def-g-unary-concrete char-code
  :integer-case (gret 0)
  :boolean-case (gret 0)
  :cons-case (gret 0))

(def-g-unary-concrete code-char
  :integer-case (gret (g-apply 'code-char (list x)))
  :boolean-case (gret (code-char 0))
  :cons-case (gret (code-char 0))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable eval-g-base-list)))))

(local
 (defthm pkg-witness-of-non-stringp
   (implies (not (stringp x))
            (equal (pkg-witness x)
                   (pkg-witness "ACL2")))
   :hints (("goal" :use ((:instance
                          symbol-equality
                          (acl2::s1 'acl2::acl2-pkg-witness)
                          (acl2::s2 (pkg-witness x))))))))

(def-g-unary-concrete pkg-witness
  :integer-case (gret (mk-g-concrete (pkg-witness "ACL2")))
  :boolean-case (gret (mk-g-concrete (pkg-witness "ACL2")))
  :cons-case (gret (mk-g-concrete (pkg-witness "ACL2"))))



(def-g-unary-concrete realpart
  :integer-case (gret x)
  :boolean-case (gret 0)
  :cons-case (gret 0))

(def-g-unary-concrete imagpart
  :integer-case (gret 0)
  :boolean-case (gret 0)
  :cons-case (gret 0))


