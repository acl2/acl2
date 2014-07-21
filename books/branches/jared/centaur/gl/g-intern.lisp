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
(include-book "g-primitives-help")
(include-book "eval-g-base")
(include-book "g-if")
(local (include-book "eval-g-base-help"))
(local (in-theory (enable general-concretep-atom)))

(def-g-binary-op intern-in-package-of-symbol
  (cond ((and (consp acl2::sym)
              (g-boolean-p acl2::sym)
              (general-concretep acl2::str))
         (gret
          (mk-g-ite
           acl2::sym
           (mk-g-concrete
            (ec-call (intern-in-package-of-symbol
                      (general-concrete-obj acl2::str)
                      t)))
           (mk-g-concrete
            (ec-call (intern-in-package-of-symbol
                      (general-concrete-obj acl2::str)
                      nil))))))
        (t (gret nil))))

;; (def-gobjectp-thm intern-in-package-of-symbol)

(verify-g-guards intern-in-package-of-symbol
                 :hints `(("Goal" :in-theory (disable ,gfn))))

(def-gobj-dependency-thm intern-in-package-of-symbol
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local
 (progn
   ;; (defthm gobjectp-not-g-keyword-symbolp
   ;;   (implies (gobjectp x)
   ;;            (not (g-keyword-symbolp x)))
   ;;   :hints(("Goal" :in-theory (enable g-keyword-symbolp))))

   (defthm not-stringp-eval-g-base-when-not-ite-var-apply-or-concrete
     (implies (and (not (general-concretep x))
                   (not (g-ite-p x))
                   (not (g-var-p x))
                   (not (g-apply-p x)))
              (not (stringp (eval-g-base x env))))
     :hints (("goal" :expand ((:with eval-g-base (eval-g-base x env)))))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm not-symbolp-eval-g-base-when-not-ite-var-apply-or-concrete
     (implies (and (not (general-concretep x))
                   (not (g-ite-p x))
                   (not (g-var-p x))
                   (not (g-apply-p x))
                   (not (g-boolean-p x)))
              (not (symbolp (eval-g-base x env))))
     :hints (("goal" :expand ((:with eval-g-base (eval-g-base x env)))))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm intern-in-package-of-symbol-bad
     (implies (or (not (stringp str)) (not (symbolp sym)))
              (equal (intern-in-package-of-symbol str sym) nil))
     :hints (("goal" :use ((:instance completion-of-intern-in-package-of-symbol
                                      (x str) (y sym))))))


   (local (in-theory (disable eval-g-base-alt-def)))

   (acl2::def-functional-instance
    mk-g-ite-correct-for-eval-g-base
    mk-g-ite-correct
    ((generic-geval-ev eval-g-base-ev)
     (generic-geval-ev-lst eval-g-base-ev-lst)
     (generic-geval eval-g-base)
     (generic-geval-list eval-g-base-list))
 :hints ('(:in-theory (e/d* (eval-g-base-ev-of-fncall-args
                             eval-g-base-apply-agrees-with-eval-g-base-ev)
                            (eval-g-base-apply))
           :expand ((:with eval-g-base (eval-g-base x env))
                    (eval-g-base-list x env)))))))


(def-g-correct-thm intern-in-package-of-symbol eval-g-base
  :hints `(("goal" :induct (,gfn acl2::str acl2::sym . ,params)
            :in-theory (e/d (general-concrete-obj)
                            ((:definition ,gfn)
                             bfr-eval-list
                             eval-g-base-alt-def))
            :expand ((,gfn acl2::str acl2::sym . ,params)
                     (:with eval-g-base (eval-g-base nil env))))
           (and stable-under-simplificationp
                '(:expand ((:with eval-g-base
                                  (eval-g-base acl2::sym env))
                           (:with eval-g-base
                                  (eval-g-base acl2::str env)))))))
