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
(include-book "g-primitives-help")
(include-book "g-if")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
(include-book "always-equal-prep")
(include-book "g-equal")
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))

(def-g-fn acl2::always-equal
  ;; Once we've ruled out the case where they're both atoms, start by recurring
  ;; down to non-ITEs on both a and b:
  `(bfr-case :bdd (g-always-equal-core x y hyp clk config bvar-db state)
             :aig (glr equal x y hyp clk config bvar-db state)))



;; (def-gobjectp-thm acl2::always-equal
;;   :hints `(("Goal" :in-theory (e/d (booleanp-gobjectp)
;;                                    ((:definition ,gfn)
;;                                     g-always-equal-core
;;                                     general-boolean-value
;;                                     general-boolean-value-cases
;;                                     gobj-fix-when-not-gobjectp
;;                                     gobj-fix-when-gobjectp
;;                                     (:type-prescription booleanp)
;;                                     (:type-prescription gobj-fix)
;;                                     equal-of-booleans-rewrite))
;;             :expand ((,gfn x y hyp clk config bvar-db state)))))

(verify-g-guards
   acl2::always-equal
   :hints `(("Goal" :in-theory (disable ,gfn))))



(def-gobj-dependency-thm acl2::always-equal
  :hints `(("Goal" :in-theory (e/d (,gfn)
                                   (g-always-equal-core
                                    gobj-depends-on)))))


(def-g-correct-thm acl2::always-equal eval-g-base
  :hints `(("Goal" :in-theory (e/d (,gfn)
                                   (g-always-equal-core)))))

