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
(include-book "bfr-sat")
(include-book "gl-mbe")
(include-book "g-primitives-help")
(include-book "g-if")
(include-book "eval-g-base")
(include-book "ctrex-utils")
(local (include-book "hyp-fix"))
(local (include-book "eval-g-base-help"))



(def-g-fn gl-assert-fn$inline
  `(b* (((mv x-nonnil x-unknown & hyp) (gtests x hyp))
        (false (bfr-and (bfr-hyp->bfr hyp)
                        (bfr-not x-unknown)
                        (bfr-not x-nonnil)))
        ((mv false-sat false-succ ?false-ctrex)
         (bfr-sat false))
        (gmsg (if (general-concretep gmsg)
                  (general-concrete-obj gmsg)
                "GL-ASSERT failed!"))
        ((when (and false-sat false-succ))
         (make-fast-alist false-ctrex)
         
         (ec-call
          (glcp-print-single-ctrex false-ctrex
                                   "Error:"
                                   gmsg config bvar-db state))
         (er hard? 'gl-assert "~@0" gmsg)
         (g-if (gret x) (gret t) (gret nil)))
        ((when (not false-succ))
         (er hard? 'gl-assert "Assertion failed to prove.~%~@0" gmsg)
         (g-if (gret x) (gret t) (gret nil)))
        (unk (bfr-and (bfr-hyp->bfr hyp) x-unknown))
        ((mv unk-sat unk-succ ?unk-ctrex)
         (bfr-sat unk))
        ((when (and unk-sat unk-succ))

         (er hard? 'gl-assert "Assertion failed with unknown.~%~@0" gmsg)
         (g-if (gret x) (gret t) (gret nil)))
        ((when (not unk-succ))
         (er hard? 'gl-assert "Assertion failed to prove absence of unknowns.~%~@0" gmsg)
         (g-if (gret x) (gret t) (gret nil))))
     (gret t)))

;; (def-gobjectp-thm gl-mbe)

(verify-g-guards gl-assert-fn$inline)

(local
 (defun instantiate-bfr-sat-hint (clause env)
   (if (atom clause)
       nil
     (let ((lit (car clause)))
       (case-match lit
         (('mv-nth ''0 ('bfr-sat term))
          (cons `(:instance bfr-sat-unsat
                            (prop ,term)
                            (env ,env))
                (instantiate-bfr-sat-hint (cdr clause) env)))
         (& (instantiate-bfr-sat-hint (cdr clause) env)))))))

(def-gobj-dependency-thm gl-assert-fn$inline
  :hints `(("goal"
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(def-g-correct-thm gl-assert-fn$inline eval-g-base
  :hints `(("goal" :do-not-induct t
            :expand (,gcall)
            :in-theory (disable bfr-sat-unsat))
           (and stable-under-simplificationp
                (let ((insts (instantiate-bfr-sat-hint clause '(car env))))
                  (if insts
                      `(:computed-hint-replacement
                        t
                        :use ,insts)
                    (cw "clause: ~x0~%" clause))))))
