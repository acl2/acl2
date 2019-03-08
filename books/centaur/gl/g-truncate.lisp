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
(include-book "tools/templates" :dir :system)
(local (include-book "bfr-reasoning"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defconst *quotient-template*
  '(progn
     (defun g-<quotient>-of-integers (x y)
       (declare (xargs :guard (and (general-integerp x)
                                   (general-integerp y))))
       (b* ((xbits (general-integer-bits x))
            (ybits (general-integer-bits y)))
         (mk-g-integer (bfr-<quotient>-ss xbits ybits))))

     (in-theory (disable (g-<quotient>-of-integers)))

     (defthm deps-of-g-<quotient>-of-integers
       (implies (and (not (gobj-depends-on k p x))
                     (not (gobj-depends-on k p y))
                     (general-integerp x)
                     (general-integerp y))
                (not (gobj-depends-on k p (g-<quotient>-of-integers x y)))))

     (local (add-bfr-fn-pat bfr-=-uu))
     (local (add-bfr-fn-pat bfr-=-ss))

     (local
      (defthm g-<quotient>-of-integers-correct
        (implies (and (general-integerp x)
                      (general-integerp y))
                 (equal (eval-g-base (g-<quotient>-of-integers x y) env)
                        (<quotient> (eval-g-base x env)
                                    (eval-g-base y env))))
        :hints (("goal" :in-theory
                 (e/d* ((:ruleset general-object-possibilities))
                       (general-integerp
                        general-integer-bits
                        <quotient>))
                 :do-not-induct t)
                (bfr-reasoning))))

     (in-theory (disable g-<quotient>-of-integers))



     (defthm <quotient>-when-dividend-0
       (equal (<quotient> 0 x) 0))

     (defthm <quotient>-when-divisor-0
       (equal (<quotient> x 0) 0))

     (def-g-binary-op <quotient>
       (b* ((x (general-number-fix i))
            (y (general-number-fix j)))
         (cond ((and** (general-integerp x) (general-integerp y))
                (gret (g-<quotient>-of-integers x y)))
               ((or (and** (general-concretep x)
                         (eql (general-concrete-obj x) 0))
                    (and** (general-concretep y)
                         (eql (general-concrete-obj y) 0)))
                (gret 0))
               (t (gret (g-apply '<quotient> (list x y)))))))

     (verify-g-guards
      <quotient>
      :hints `(("goal" :in-theory
                (disable* ,gfn
                          (:rules-of-class :type-prescription :here)))))

     (local (in-theory (disable general-concrete-obj-when-atom)))

     (def-gobj-dependency-thm <quotient>
       :hints `(("goal" :induct ,gcall
                 :expand (,gcall)
                 :in-theory (disable (:d ,gfn)))))

     (local (defthm <quotient>-when-not-acl2-numberp
              (and (implies (not (acl2-numberp i))
                            (equal (<quotient> i j) (<quotient> 0 j)))
                   (implies (not (acl2-numberp j))
                            (equal (<quotient> i j) (<quotient> i 0))))
              :hints(("Goal" :in-theory (disable <quotient>-when-dividend-0
                                                 <quotient>-when-divisor-0)))))


     (local (defcong number-equiv equal (<quotient> x y) 1))
     (local (defcong number-equiv equal (<quotient> x y) 2))

     (def-g-correct-thm <quotient> eval-g-base
       :hints
       `(("goal" :in-theory (e/d (eval-g-base-list
                                  (general-concrete-obj))
                                 (<quotient> equal-of-booleans-rewrite
                                             eval-g-base-alt-def))
          :induct ,gcall
          :do-not-induct t
          :expand (,gcall))))))

(defmacro def-g-quotient (op)
  (acl2::template-subst *quotient-template*
                        :atom-alist `((<quotient> . ,op))
                        :str-alist `(("<QUOTIENT>" . ,(symbol-name op)))
                        :pkg-sym 'gl::foo))

(def-g-quotient truncate)
(def-g-quotient floor)
                                      


(defconst *remainder-template*
  '(progn
     (defun g-<remainder>-of-integers (x y)
       (declare (xargs :guard (and (general-integerp x)
                                   (general-integerp y))))
       (b* ((xbits (general-integer-bits x))
            (ybits (general-integer-bits y)))
         (mk-g-integer (bfr-<remainder>-ss xbits ybits))))

     (in-theory (disable (g-<remainder>-of-integers)))

     (defthm deps-of-g-<remainder>-of-integers
       (implies (and (not (gobj-depends-on k p x))
                     (not (gobj-depends-on k p y))
                     (general-integerp x)
                     (general-integerp y))
                (not (gobj-depends-on k p (g-<remainder>-of-integers x y)))))

     (local (add-bfr-fn-pat bfr-=-uu))
     (local (add-bfr-fn-pat bfr-=-ss))

     (local
      (defthm g-<remainder>-of-integers-correct
        (implies (and (general-integerp x)
                      (general-integerp y))
                 (equal (eval-g-base (g-<remainder>-of-integers x y) env)
                        (<remainder> (eval-g-base x env)
                                     (eval-g-base y env))))
        :hints (("goal" :in-theory
                 (e/d* ((:ruleset general-object-possibilities))
                       (general-integerp
                        general-integer-bits
                        <remainder>))
                 :do-not-induct t)
                (bfr-reasoning))))

     (in-theory (disable g-<remainder>-of-integers))



     (defthm <remainder>-when-dividend-0
       (equal (<remainder> 0 x) 0))

     (defthm <remainder>-when-divisor-0
       (equal (<remainder> x 0) (fix x)))

     (def-g-binary-op <remainder>
       (b* ((x (general-number-fix x))
            (y (general-number-fix y)))
         (cond ((and** (general-integerp x) (general-integerp y))
                (gret (g-<remainder>-of-integers x y)))
               ((and** (general-concretep x)
                       (eql (general-concrete-obj x) 0))
                (gret 0))
               ((and** (general-concretep y)
                       (eql (general-concrete-obj y) 0))
                (gret x))
               (t (gret (g-apply '<remainder> (list x y)))))))

     (verify-g-guards
      <remainder>
      :hints `(("goal" :in-theory
                (disable* ,gfn
                          (:rules-of-class :type-prescription :here)))))

     (local (in-theory (disable general-concrete-obj-when-atom)))

     (def-gobj-dependency-thm <remainder>
       :hints `(("goal" :induct ,gcall
                 :expand (,gcall)
                 :in-theory (disable (:d ,gfn)))))

     (local (defthm <remainder>-when-not-acl2-numberp
              (and (implies (not (acl2-numberp i))
                            (equal (<remainder> i j) (<remainder> 0 j)))
                   (implies (not (acl2-numberp j))
                            (equal (<remainder> i j) (<remainder> i 0))))
              :hints(("Goal" :in-theory (disable <remainder>-when-dividend-0
                                                 <remainder>-when-divisor-0)))))

     (local (defcong number-equiv equal (<remainder> x y) 1))
     (local (defcong number-equiv equal (<remainder> x y) 2))

     (def-g-correct-thm <remainder> eval-g-base
       :hints
       `(("goal" :in-theory (e/d (eval-g-base-list
                                  (general-concrete-obj))
                                 (<remainder> equal-of-booleans-rewrite
                                              eval-g-base-alt-def))
          :induct ,gcall
          :do-not-induct t
          :expand (,gcall))))))

(defmacro def-g-remainder (op)
  (acl2::template-subst *remainder-template*
                        :atom-alist `((<remainder> . ,op))
                        :str-alist `(("<REMAINDER>" . ,(symbol-name op)))
                        :pkg-sym 'gl::foo))

(def-g-remainder mod)
(def-g-remainder rem)

