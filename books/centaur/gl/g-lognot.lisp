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
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(set-inhibit-warnings "theory")

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
         ((g-number num)
          (b* (((mv rn rd in id)
                (break-g-number num))
               ((mv intp intp-known)
                (if (equal rd '(t))
                    (mv (bfr-or (bfr-=-ss in nil) (bfr-=-uu id nil)) t)
                  (mv nil nil))))
            (gret
             (if intp-known
                 (mk-g-number (rlist-fix (bfr-lognot-s (bfr-ite-bss-fn intp rn nil))))
               (g-apply 'lognot (gl-list x))))))
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
   :hints `(("Goal" :in-theory (e/d* (components-to-number-alt-def
                                      general-concrete-obj)
                                    ((:definition ,gfn) (force)
                                     general-number-components-ev
                                     general-numberp-eval-to-numberp
                                     lognot))
             :induct (,gfn i . ,params)
             :expand ((,gfn i . ,params)
                      (:with eval-g-base (eval-g-base i env))))))

