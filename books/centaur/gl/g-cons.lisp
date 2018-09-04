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
(include-book "eval-g-base")
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))

(def-g-fn cdr
  `(if (atom x)
       (gret nil)
     (pattern-match x
       ((g-ite test then else)
        (if (zp clk)
            (gret (g-apply 'cdr (gl-list x)))
          (g-if (gret test)
                (,gfn then . ,params)
                (,gfn else . ,params))))
       ((g-boolean &) (gret nil))
       ((g-integer &) (gret nil))
       ((g-apply & &) (gret (g-apply 'cdr (gl-list x))))
       ((g-var &) (gret (g-apply 'cdr (gl-list x))))
       ((g-concrete obj) (gret (mk-g-concrete (ec-call (cdr obj)))))
       ((cons & b) (gret b))
       (& ;; unreachable
        (gret nil)))))

;; (def-gobjectp-thm cdr
;;   :hints `(("goal" :in-theory (disable (:definition ,gfn))
;;            :induct (,gfn x hyp clk)
;;            :expand ((,gfn x hyp clk)))))

(verify-g-guards
 cdr
 :hints `(("goal" :in-theory (disable ,gfn))))

(def-gobj-dependency-thm cdr
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))


(def-g-correct-thm cdr eval-g-base
  :hints `(("goal" :in-theory (e/d (eval-g-base general-concrete-obj)
                                   ((:definition ,gfn)
                                    logcons bfr-list->s
                                    bfr-list->u
                                    eval-g-base-alt-def
                                    equal-of-booleans-rewrite
                                    default-car set::double-containment))
            :induct (,gfn x . ,params)
            :expand ((,gfn x . ,params)))))


(def-g-fn car
  `(if (atom x)
       (gret nil)
     (pattern-match x
       ((g-ite test then else)
        (if (zp clk)
            (gret (g-apply 'car (gl-list x)))
          (g-if (gret  test)
                (,gfn then . ,params)
                (,gfn else . ,params))))
       ((g-boolean &) (gret nil))
       ((g-integer &) (gret nil))
       ((g-apply & &) (gret (g-apply 'car (gl-list x))))
       ((g-var &) (gret (g-apply 'car (gl-list x))))
       ((g-concrete obj) (gret (mk-g-concrete (ec-call (car obj)))))
       ((cons a &) (gret a))
       (& (gret nil)))))

;; (def-gobjectp-thm car
;;   :hints `(("goal" :in-theory (disable (:definition ,gfn))
;;             :induct (,gfn x . ,params)
;;             :expand ((,gfn x . ,params)))))

(verify-g-guards
 car
 :hints `(("goal" :in-theory (disable ,gfn))))

(def-gobj-dependency-thm car
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(def-g-correct-thm car eval-g-base
  :hints `(("goal" :in-theory (e/d (eval-g-base general-concrete-obj)
                                   ((:definition ,gfn)
                                    eval-g-base-alt-def
                                    logcons))
            :induct (,gfn x . ,params)
            :expand ((,gfn x . ,params)))))



(def-g-fn cons
  `(gret (gl-cons x y)))

;; (def-gobjectp-thm cons)

(verify-g-guards cons)

(def-gobj-dependency-thm cons
  :hints `(("Goal" :in-theory (enable ,gfn))))

(def-g-correct-thm cons eval-g-base
  :hints `(("Goal" :in-theory (enable ,gfn))))
