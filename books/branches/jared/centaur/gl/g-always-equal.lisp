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
(include-book "g-if")
(include-book "symbolic-arithmetic")
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

