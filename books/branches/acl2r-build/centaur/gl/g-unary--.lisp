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
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
(local (include-book "symbolic-arithmetic"))
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
       ((g-number num)
        (mv-let (rn rd in id)
          (break-g-number num)
          (gret
           (mk-g-number (bfr-unary-minus-s rn)
                        (rlist-fix rd)
                        (bfr-unary-minus-s in)
                        (rlist-fix id)))))
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




(local
 (defthm minus-of-non-acl2-number
   (implies (not (acl2-numberp x))
            (equal (- x) (- 0)))))

(local
 (defthm minus-of-complex
   (implies (and (rationalp a) (rationalp b))
            (equal (- (complex a b))
                   (complex (- a) (- b))))
   :hints (("goal" :use ((:instance complex-definition
                                    (x a) (y b))
                         (:instance complex-definition
                                    (x (- a)) (y (- b))))
            :in-theory (disable equal-complexes-rw)))))

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
  :hints `(("Goal" :in-theory (e/d* (components-to-number-alt-def
                                     general-concrete-obj natp)
                                    ((:definition ,gfn)
                                     general-number-components-ev
                                     general-numberp-eval-to-numberp))
            :induct (,gfn x . ,params)
            :do-not-induct t
            :expand ((,gfn x . ,params)
                     (:with eval-g-base (eval-g-base x env))))))
