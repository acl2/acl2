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
         ((g-number num)
          (mv-let (arn ard ain aid)
            (break-g-number num)
            (g-if (gret (mk-g-boolean (hyp-fix (bfr-or (bfr-=-uu aid nil)
                                                       (bfr-=-ss ain nil)) hyp)))
                  (g-if (gret (equal ard '(t)))
                        (let ((res (rlist-fix (bfr-integer-length-s arn))))
                          (gret (mk-g-number res 1 0 1)))
                        (gret (g-apply 'integer-length (gl-list x))))
                  (gret 0))))
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
  :hints `(("Goal" :in-theory (e/d (components-to-number-alt-def)
                                   ((:definition ,gfn)
                                    general-concretep-def
                                    eval-g-base-alt-def
                                    integer-length))
            :induct (,gfn i . ,params)
            :expand ((,gfn i . ,params)))
           (and stable-under-simplificationp
                '(:expand ((:with eval-g-base (eval-g-base i env)))))))
