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
