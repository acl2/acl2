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
(local (include-book "arithmetic/top-with-meta" :dir :system))
(set-inhibit-warnings "theory")

(def-g-fn unary--
  `(if (atom x)
       (gret (- (fix x)))
     (pattern-match x
       ((g-ite test then else)
        (if (zp clk)
            (gret (g-apply 'unary-- (gl-list x)))
          (g-if (gret test)
                (,gfn then . ,params)
                (,gfn else . ,params))))
       ((g-apply & &)
        (gret (g-apply 'unary-- (gl-list x))))
       ((g-concrete obj)
        (gret (- (fix obj))))
       ((g-var &)
        (gret (g-apply 'unary-- (gl-list x))))
       ((g-boolean &) (gret 0))
       ((g-integer bits)
        (gret (mk-g-integer (bfr-unary-minus-s (list-fix bits)))))
       (& (gret 0)))))

;; (def-gobjectp-thm unary--
;;   :hints `(("Goal" :in-theory (e/d () ((:definition ,gfn)))
;;             :induct (,gfn x . ,params)
;;             :expand ((,gfn x . ,params)
;;                      (:free (x) (gobjectp (- x)))))))

(verify-g-guards
 unary--
 :hints `(("Goal" :in-theory (disable ,gfn))))

(def-gobj-dependency-thm unary--
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))


;; (local (defthm eval-g-base-atom
;;          (implies (and (not (consp x)) (gobjectp x))
;;                   (equal (eval-g-base x env) x))
;;          :hints(("Goal" :in-theory (enable eval-g-base)))))

;; (local (defthm gobjectp-number
;;          (implies (acl2-numberp x)
;;                   (gobjectp x))
;;          :hints(("Goal" :in-theory (enable gobjectp-def)))))

;; (local
;;  (defthm not-integerp-break-g-number
;;    (implies (wf-g-numberp x)
;;             (and (not (integerp (mv-nth 0 (break-g-number x))))
;;                  (not (integerp (mv-nth 1 (break-g-number x))))
;;                  (not (integerp (mv-nth 2 (break-g-number x))))
;;                  (not (integerp (mv-nth 3 (break-g-number x))))))
;;    :hints(("Goal" :in-theory (enable wf-g-numberp-simpler-def
;;                                      break-g-number bfr-listp)))))

(def-g-correct-thm unary-- eval-g-base
  :hints `(("Goal" :in-theory (e/d* (general-concrete-obj natp)
                                    ((:definition ,gfn)
                                     general-integer-bits-correct))
            :induct (,gfn x . ,params)
            :do-not-induct t
            :expand ((,gfn x . ,params)
                     (:with eval-g-base (eval-g-base x env))))))
