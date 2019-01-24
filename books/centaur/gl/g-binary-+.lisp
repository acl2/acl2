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
(include-book "centaur/misc/starlogic" :dir :system)
;(include-book "tools/with-arith5-help" :dir :system)
(include-book "tools/templates" :dir :system)

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(local (include-book "clause-processors/just-expand" :dir :system))
;(local (allow-arith5-help))

;; (include-book "univ-gl-eval")

;; (local (defthm equal-complexes-rw
;;          (implies (and (acl2-numberp x)
;;                        (rationalp a)
;;                        (rationalp b))
;;                   (equal (equal (complex a b) x)
;;                          (and (equal a (realpart x))
;;                               (equal b (imagpart x)))))
;;          :hints (("goal" :use ((:instance realpart-imagpart-elim))))))




;; (local (defthmd bfr-eval-list-when-boolean-listp
;;          (implies (boolean-listp x)
;;                   (equal (bfr-eval-list x env)
;;                          x))))

(local (defcong number-equiv equal (+ a b) 1))
(local (defcong number-equiv equal (+ a b) 2))
(local (defcong number-equiv equal (- x) 1))
;; (local (defcong number-equiv equal (fix x) 1))
;; (local (defthm fix-when-acl2-numberp
;;          (implies (acl2-numberp x)
;;                   (equal (fix x) x))))

;; (local (defthm fix-under-number-equiv
;;          (number-equiv (fix x) x)))

;; (local (in-theory (disable fix)))

(defconst *plusminus-template*
  '(progn

     (defun g-<fn>-of-integers (x y)
       (declare (xargs :guard (and (general-integerp x)
                                   (general-integerp y))))
       (b* ((xbits (general-integer-bits x))
            (ybits (general-integer-bits y)))
         (mk-g-integer <sum-expr>)))

     (in-theory (disable (g-<fn>-of-integers)))

     (local
      (defthm g-<fn>-of-integers-correct
        (implies (and (general-integerp x)
                      (general-integerp y))
                 (equal (eval-g-base (g-<fn>-of-integers x y) env)
                        (<fn> (eval-g-base x env)
                              (eval-g-base y env))))
        :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                         (general-integerp
                                          general-integer-bits))
                 :do-not-induct t))))

     (local
      (defthm dependencies-of-g-<fn>-of-integers
        (implies (and (general-integerp x)
                      (general-integerp y)
                      (not (gobj-depends-on n p x))
                      (not (gobj-depends-on n p y)))
                 (not (gobj-depends-on n p (g-<fn>-of-integers x y))))
        :hints (("goal" :do-not-induct t))
        :otf-flg t))

     (in-theory (disable g-<fn>-of-integers))

     (def-g-binary-op <fn>
       (b* ((x (general-number-fix x))
            (y (general-number-fix y))
            ((when (and** (general-integerp x) (general-integerp y)))
             (gret (g-<fn>-of-integers x y)))
            ((when (and** (general-concretep x)
                          (eql (general-concrete-obj x) 0)))
             (gret <returnval-for-x-0>))
            ((when (and** (general-concretep y)
                          (eql (general-concrete-obj y) 0)))
             (gret x)))
         (gret (g-apply '<fn> (list x y)))))


     (verify-g-guards
      <fn>
      :hints `(("goal" :in-theory (disable* ,gfn
                                            (:rules-of-class :type-prescription
                                             :here)))))


     (def-gobj-dependency-thm <fn>
       :hints `(("goal" :in-theory (disable (:d ,gfn)
                                            gobj-depends-on)
                 :induct ,gcall
                 :expand (,gcall))))

     (def-g-correct-thm <fn> eval-g-base
       :hints
       `(("goal"
          :in-theory (enable* eval-g-base-list)
          :induct ,gcall
          :do-not-induct t
          :expand (,gcall))
         ;; (and stable-under-simplificationp
         ;;      (flag::expand-calls-computed-hint
         ;;       clause '(eval-g-base)))
         ))))

(defmacro def-g-plusminus (fn &key return-when-x-is-0
                              sum-expr)
  (acl2::template-subst *plusminus-template*
                        :atom-alist `((<fn> . ,fn)
                                      (<returnval-for-x-0> . ,return-when-x-is-0)
                                      (<sum-expr> . ,sum-expr))
                        :str-alist `(("<FN>" . ,(symbol-name fn)))
                        :pkg-sym 'gl::foo))

(def-g-plusminus binary-+ :return-when-x-is-0 y
  :sum-expr (bfr-+-ss nil xbits ybits))

(def-g-plusminus binary-minus-for-gl
  :return-when-x-is-0
  (if (general-concretep y)
      (mk-g-concrete (- (general-concrete-obj y)))
    (mk-g-integer (bfr-unary-minus-s (general-integer-bits y))))
  :sum-expr
  (bfr-+-ss t xbits (bfr-lognot-s ybits)))



