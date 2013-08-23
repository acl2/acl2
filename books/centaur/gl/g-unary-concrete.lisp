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
(local (include-book "hyp-fix-logic"))
(in-theory (disable (mk-g-concrete)))

(defthm mk-g-concrete-of-atomic-constant
  (implies (and (syntaxp (quotep x))
                (atom x)
                (not (g-keyword-symbolp x)))
           (equal (mk-g-concrete x) x))
  :hints(("Goal" :in-theory (enable mk-g-concrete
                                    concrete-gobjectp
                                    gobject-hierarchy-lite))))

(program)
(defun def-g-unary-concrete-fn (fn number-case boolean-case cons-case
                                   hints world)
  (let ((x (car (wgetprop fn 'formals))))
    `(progn
       (def-g-fn ,fn
         (let ((x ',x)
               (fn ',fn))
           `(if (atom ,x)
                (mk-g-concrete (ec-call (,fn ,x)))
              (pattern-match ,x
                ((g-concrete obj)
                 (mk-g-concrete (ec-call (,fn obj))))
                ((g-ite test then else)
                 (if (zp clk)
                     (g-apply ',fn (gl-list ,x))
                   (g-if test
                         (,gfn then . ,params)
                         (,gfn else . ,params))))
                ((g-apply & &) (g-apply ',fn (gl-list ,x)))
                ((g-var &) (g-apply ',fn (gl-list ,x)))
                ((g-number &) ,',number-case)
                ((g-boolean &) ,',boolean-case)
                (& ,',cons-case)))))
       ;; (def-gobjectp-thm ,fn
       ;;   :hints `(("goal" :in-theory
       ;;             (e/d ()
       ;;                  ((force)
       ;;                   (:definition ,gfn)))
       ;;             :induct (,gfn ,',x . ,params)
       ;;             :expand ((,gfn ,',x . ,params)))))
       (verify-g-guards
        ,fn
        :hints `(("Goal" :in-theory (Disable ,gfn))))

       (def-gobj-dependency-thm ,fn
         :hints `(("goal" :induct ,gcall
                   :expand (,gcall)
                   :in-theory (disable (:d ,gfn)))))

       (def-g-correct-thm ,fn eval-g-base
         :hints `(("Goal" :in-theory (e/d ((:induction ,gfn)
                                           general-concrete-obj)
                                          ((:definition ,gfn)))
                   :induct (,gfn ,',x . ,params)
                   :expand ((,gfn ,',x . ,params)
                            (:with eval-g-base (eval-g-base ,',x env))))
                  . ,',hints)))))

(defmacro def-g-unary-concrete (fn &key number-case boolean-case
                                   cons-case hints)
  `(make-event (def-g-unary-concrete-fn ',fn ',number-case ',boolean-case
                 ',cons-case ',hints(w state))))

(logic)

(def-g-unary-concrete symbol-name
  :number-case ""
  :boolean-case (g-if x "T" "NIL")
  :cons-case "")

(def-g-unary-concrete symbol-package-name
  :number-case ""
  :boolean-case "COMMON-LISP"
  :cons-case ""
  :hints ((and stable-under-simplificationp
               '(:use
                 ((:instance (:type-prescription bfr-eval)
                             (x (g-boolean->bool x))
                             (env (car env))))
                 :in-theory (disable (:type-prescription bfr-eval))))))



(def-g-unary-concrete char-code
  :number-case 0
  :boolean-case 0
  :cons-case 0)

(local
 (defthm pkg-witness-of-non-stringp
   (implies (not (stringp x))
            (equal (pkg-witness x)
                   (pkg-witness "ACL2")))
   :hints (("goal" :use ((:instance
                          symbol-equality
                          (acl2::s1 'acl2::acl2-pkg-witness)
                          (acl2::s2 (pkg-witness x))))))))

(def-g-unary-concrete pkg-witness
  :number-case (mk-g-concrete (pkg-witness "ACL2"))
  :boolean-case (mk-g-concrete (pkg-witness "ACL2"))
  :cons-case (mk-g-concrete (pkg-witness "ACL2")))



(def-g-unary-concrete realpart
  :number-case
  (mv-let (rn rd in id)
    (break-g-number (g-number->num x))
    (declare (ignore in id))
    (mk-g-number (rlist-fix rn) (rlist-fix rd)))
  :boolean-case 0
  :cons-case 0)

(def-g-unary-concrete imagpart
  :number-case
  (mv-let (rn rd in id)
    (break-g-number (g-number->num x))
    (declare (ignore rn rd))
    (mk-g-number (rlist-fix in) (rlist-fix id)))
  :boolean-case 0
  :cons-case 0)


