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
;(include-book "tools/with-arith5-help" :dir :system)

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(local (include-book "clause-processors/just-expand" :dir :system))
(set-inhibit-warnings "theory")

(defun g-ash-of-integers (i c)
  (declare (xargs :guard (and (general-integerp i)
                              (general-integerp c))))
  (mk-g-integer (bfr-ash-ss 1 (general-integer-bits i)
                            (general-integer-bits c))))

(in-theory (disable (g-ash-of-integers)))

(defthm deps-of-g-ash-of-integers
  (implies (and (not (gobj-depends-on k p i))
                (not (gobj-depends-on k p c))
                (general-integerp i)
                (general-integerp c))
           (not (gobj-depends-on k p (g-ash-of-integers i c)))))



(defthm g-ash-of-integers-correct
  (implies (and (general-integerp x)
                (general-integerp y))
           (equal (eval-g-base (g-ash-of-integers x y) env)
                  (ash (eval-g-base x env)
                       (eval-g-base y env))))
  :hints (("goal" :in-theory (e/d* ((:ruleset general-object-possibilities))
                                   (general-integerp))
           :do-not-induct t)))


(def-g-binary-op ash
  (b* ((i-num (if (general-integerp i) i 0))
       (c-num (if (general-integerp c) c 0)))
    (gret (g-ash-of-integers i-num c-num))))


;; (def-gobjectp-thm ash
;;   :hints `(("goal" :in-theory (e/d* (general-concretep-atom)
;;                                     ((:definition ,gfn)
;;                                      (force)
;;                                      general-concretep-def
;;                                      hyp-fix
;;                                      gobj-fix-when-not-gobjectp
;;                                      gobj-fix-when-gobjectp
;;                                      (:rules-of-class :type-prescription :here)
;;                                      (:ruleset gl-wrong-tag-rewrites)))
;;             :induct (,gfn i c hyp clk)
;;             :do-not-induct t
;;             :expand ((,gfn i c hyp clk)))))

(verify-g-guards
 ash
 :hints `(("Goal" :in-theory (disable ,gfn))))


(local (defthm pbfr-list-depends-on-of-empty
         (not (pbfr-list-depends-on k p '(nil)))
         :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))
         

(def-gobj-dependency-thm ash
  :hints `(("goal" :in-theory (e/d ((:i ,gfn))
                                   ((:d ,gfn)
                                    gobj-depends-on)))
           (acl2::just-induct-and-expand ,gcall)))


(local (defthm ash-of-non-integers
         (and (implies (not (integerp i))
                       (equal (ash i c) (ash 0 c)))
              (implies (not (integerp c))
                       (equal (ash i c) (ash i 0))))))

(local (in-theory (disable ash)))


(def-g-correct-thm ash eval-g-base
  :hints
  `(("goal" 
     :in-theory (enable eval-g-base-list)
     :induct ,gcall
     :expand (,gcall)
     :do-not-induct t)))
