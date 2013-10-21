; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "g-if")
(include-book "g-primitives-help")
(include-book "eval-g-base")
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))

(def-g-fn cdr
  `(if (atom x)
       nil
     (pattern-match x
       ((g-ite test then else)
        (if (zp clk)
            (g-apply 'cdr (gl-list x))
          (g-if test (,gfn then . ,params)
                (,gfn else . ,params))))
       ((g-boolean &) nil)
       ((g-number &) nil)
       ((g-apply & &) (g-apply 'cdr (gl-list x)))
       ((g-var &) (g-apply 'cdr (gl-list x)))
       ((g-concrete obj) (mk-g-concrete (ec-call (cdr obj))))
       ((cons & b) b))))

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
                                   ((:definition ,gfn)))
            :induct (,gfn x . ,params)
            :expand ((,gfn x . ,params)))))


(def-g-fn car
  `(if (atom x)
       nil
     (pattern-match x
       ((g-ite test then else)
        (if (zp clk)
            (g-apply 'car (gl-list x))
          (g-if test (,gfn then . ,params) (,gfn else . ,params))))
       ((g-boolean &) nil)
       ((g-number &) nil)
       ((g-apply & &) (g-apply 'car (gl-list x)))
       ((g-var &) (g-apply 'car (gl-list x)))
       ((g-concrete obj) (mk-g-concrete (ec-call (car obj))))
       ((cons a &) a))))

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
                                   ((:definition ,gfn)))
            :induct (,gfn x . ,params)
            :expand ((,gfn x . ,params)))))



(def-g-fn cons
  `(gl-cons x y))

;; (def-gobjectp-thm cons)

(verify-g-guards cons)

(def-gobj-dependency-thm cons)

(def-g-correct-thm cons eval-g-base)
