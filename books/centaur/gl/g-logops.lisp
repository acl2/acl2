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
(include-book "tools/templates" :dir :system)
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))



(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (include-book "clause-processors/just-expand" :dir :system))

(defconst *binary-logop-template*
  '(encapsulate nil
     (defund g-binary-<logop>-of-integers (x y)
       (declare (xargs :guard (and (general-integerp x)
                                   (general-integerp y))))
       (b* ((xbits (general-integer-bits x))
            (ybits (general-integer-bits y)))
         (mk-g-integer (bfr-<logop>-ss xbits ybits))))
     (local (in-theory (enable g-binary-<logop>-of-integers)))

     (defthm deps-of-g-binary-<logop>-of-integers
       (implies (and (not (gobj-depends-on k p x))
                     (not (gobj-depends-on k p y))
                     (general-integerp x)
                     (general-integerp y))
                (not (gobj-depends-on k p (g-binary-<logop>-of-integers x y)))))


     (local
      (defthm g-binary-<logop>-of-integers-correct
        (implies (and (general-integerp x)
                      (general-integerp y))
                 (equal (eval-g-base (g-binary-<logop>-of-integers x y) env)
                        (<logop> (eval-g-base x env)
                                (eval-g-base y env))))
        :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                         (general-integerp))
                 :do-not-induct t))))

     (local (in-theory (disable g-binary-<logop>-of-integers)))

     (def-g-binary-op <binary-logop>
       (b* ((i-num (if (general-integerp i) i 0))
            (j-num (if (general-integerp j) j 0)))
         (gret (g-binary-<logop>-of-integers i-num j-num))))

     (verify-g-guards
      <binary-logop>
      :hints `(("Goal" :in-theory (e/d* (g-if-fn g-or-fn)
                                        (,gfn
                                         general-concretep-def)))))



     (def-gobj-dependency-thm <binary-logop>
       :hints `(("goal" :induct ,gcall
                 :expand (,gcall)
                 :in-theory (disable (:d ,gfn)))))

     (local (defthm <logop>-non-integers
         (and (implies (not (integerp i))
                       (equal (<logop> i j) (<logop> 0 j)))
              (implies (not (integerp j))
                       (equal (<logop> i j) (<logop> i 0))))))

     (with-output :off (prove)
       (def-g-correct-thm <binary-logop> eval-g-base
         :hints `(("Goal" :in-theory (e/d* (general-concretep-atom
                                            (:ruleset general-object-possibilities)
                                            not-general-integerp-not-integerp)
                                           ((:definition ,gfn)
                                            general-concretep-def
                                            <binary-logop>
                                            bfr-list->s
                                            bfr-list->u
                                            equal-of-booleans-rewrite
                                            set::double-containment
                                            hons-assoc-equal
                                            default-car default-cdr
                                            (:rules-of-class :type-prescription :here)))
                   :induct (,gfn i j . ,params)
                   :do-not-induct t
                   :expand ((,gfn i j . ,params))))))))

(defmacro def-g-binary-logop (logop)
  (acl2::template-subst *binary-logop-template*
                        :atom-alist `((<logop> . ,logop)
                                      (<binary-logop> . ,(intern$ (str::cat "BINARY-" (symbol-name logop)) "ACL2")))
                        :str-alist `(("<LOGOP>" . ,(symbol-name logop)))
                        :pkg-sym 'gl::foo))

(def-g-binary-logop logand)
(def-g-binary-logop logior)
(def-g-binary-logop logeqv)
(def-g-binary-logop logxor)




(def-g-fn lognot
  `(let ((x i))
     (if (atom x)
         (gret (lognot (ifix x)))
       (pattern-match x
         ((g-ite test then else)
          (if (zp clk)
              (gret (g-apply 'lognot (gl-list x)))
            (g-if (gret test)
                  (,gfn then . ,params)
                  (,gfn else . ,params))))
         ((g-apply & &)
          (gret (g-apply 'lognot (gl-list x))))
         ((g-concrete obj)
          (gret (lognot (ifix obj))))
         ((g-var &)
          (gret (g-apply 'lognot (gl-list x))))
         ((g-boolean &) (gret -1))
         ((g-integer bits)
          (gret (mk-g-integer (bfr-lognot-s (list-fix bits)))))
         (& (gret -1))))))



;; (local (defthm gobjectp-lognot
;;          (gobjectp (lognot x))
;;          :hints(("Goal" :in-theory (enable gobjectp-def)))))

;; (def-gobjectp-thm lognot
;;   :hints `(("Goal" :in-theory (e/d ()
;;                                    ((:definition ,gfn) lognot))
;;             :induct (,gfn i . ,params)
;;             :expand ((,gfn i . ,params)
;;                      (:free (x) (gobjectp (- x)))))))

(verify-g-guards
 lognot
 :hints `(("Goal" :in-theory (disable ,gfn))))

(def-gobj-dependency-thm lognot
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local
 (progn
   (defthm lognot-non-acl2-numberp
     (implies (not (acl2-numberp n))
              (equal (lognot n) (lognot 0))))

   (defthm lognot-non-integer
     (implies (not (integerp n))
              (equal (lognot n) (lognot 0))))

   (local (include-book "arithmetic/top-with-meta" :dir :system))))

(def-g-correct-thm lognot eval-g-base
   :hints `(("Goal" :in-theory (e/d* (general-concrete-obj)
                                    ((:definition ,gfn) (force)
                                     lognot))
             :induct (,gfn i . ,params)
             :expand ((,gfn i . ,params)
                      (:with eval-g-base (eval-g-base i env))))))



