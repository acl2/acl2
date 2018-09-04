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
(set-inhibit-warnings "theory")

;; (defthm true-listp-of-bfr-integer-length-s1
;;   (true-listp (mv-nth 1 (bfr-integer-length-s1 offset x)))
;;   :hints(("Goal" :in-theory (enable bfr-integer-length-s1)))
;;   :rule-classes :type-prescription)

;; (defthm true-listp-of-bfr-integer-length-s
;;   (true-listp (bfr-integer-length-s x))
;;   :hints(("Goal" :in-theory (enable bfr-integer-length-s)))
;;   :rule-classes :type-prescription)


(def-g-fn integer-length
  `(b* ((x i))
     (if (atom x)
         (gret (ec-call (integer-length x)))
       (pattern-match x
         ((g-ite test then else)
          (if (zp clk)
              (gret (g-apply 'integer-length (gl-list x)))
            (g-if (gret test)
                  (,gfn then . ,params)
                  (,gfn else . ,params))))
         ((g-apply & &)
          (gret (g-apply 'integer-length (gl-list x))))
         ((g-var &)
          (gret (g-apply 'integer-length (gl-list x))))
         ((g-boolean &) (gret 0))
         ((g-concrete obj) (gret (ec-call (integer-length obj))))
         ((g-integer bits)
          (gret (mk-g-integer (bfr-integer-length-s (list-fix bits)))))
         (& (gret 0))))))

;; (local (defthm gobjectp-integer-length
;;          (gobjectp (integer-length a))
;;          :hints(("Goal" :in-theory (enable gobjectp-def)))))

;; (local (defthm gobjectp-equal
;;          (gobjectp (equal a b))
;;          :hints(("Goal" :in-theory (enable gobjectp-def
;;                                            g-keyword-symbolp-def)))))

;; (def-gobjectp-thm integer-length
;;   :hints `(("Goal" :in-theory (e/d ()
;;                                  ((:definition ,gfn)))
;;           :induct (,gfn i . ,params)
;;           :expand ((,gfn i . ,params)))))

(verify-g-guards
 integer-length
 :hints `(("Goal" :in-theory (disable ,gfn))))


(def-gobj-dependency-thm integer-length
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))


(local (defthm non-integerp-integer-length
         (implies (not (integerp x))
                  (equal (integer-length x) 0))
         :rule-classes ((:rewrite :backchain-limit-lst 1))))

(local (defthm eval-g-base-booleanp
         (implies (booleanp x)
                  (equal (eval-g-base x env) x))
         :hints(("Goal" :in-theory (enable eval-g-base booleanp)))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm general-concrete-obj-integer
         (implies (integerp x)
                  (equal (general-concrete-obj x) x))
         :hints(("Goal" :in-theory (enable general-concrete-obj)))))

(local (defthm eval-g-base-integer
         (implies (integerp x)
                  (equal (eval-g-base x env) x))
         :hints(("Goal" :in-theory (enable eval-g-base)))))


(def-g-correct-thm integer-length eval-g-base
  :hints `(("Goal" :in-theory (e/d ()
                                   ((:definition ,gfn)
                                    general-concretep-def
                                    eval-g-base-alt-def
                                    integer-length))
            :induct (,gfn i . ,params)
            :expand ((,gfn i . ,params)))
           (and stable-under-simplificationp
                '(:expand ((:with eval-g-base (eval-g-base i env)))))))
