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
(include-book "g-always-equal")
(include-book "gl-mbe")
(local (include-book "eval-g-base-help"))


;; [Jared] uses of sneaky-save for the time being.  I don't think we often care
;; about this.  This scheme lets us include gl-mbe in the top-level gl.lisp,
;; without needing a ttag.  We can always redefine the function if we need to
;; debug something.

;; (include-book "../misc/sneaky-load")


(def-g-fn gl-mbe
  `(b* ((equal? (glr acl2::always-equal spec impl . ,params))
        (tests (gtests equal? hyp))
        (false (bfr-and hyp
                        (bfr-not (gtests-unknown tests))
                        (bfr-not (gtests-nonnil tests))))
        ((mv false-sat false-succ ?false-ctrex)
         (bfr-sat false))
        ((when (and false-sat false-succ))
         (make-fast-alist false-ctrex)
         ;; (acl2::sneaky-save 'gl-mbe-ctrex false-ctrex)
         (ec-call
          (glcp-print-single-ctrex false-ctrex
                                   "Error:"
                                   "GL-MBE violation"
                                   config bvar-db state))
         (er hard? 'gl-mbe "GL-MBE assertion failed.  Args: (~x0 ~x1).
                            Diagnostic info: ~x2~%"
             ;; BOZO this is all assuming aig/alist-ctrex mode
             (gobj->term spec (list false-ctrex))
             (gobj->term impl (list false-ctrex))
             (gobj->term other-info (list false-ctrex)))
         spec)
        ((when (not false-succ))
         (er hard? 'gl-mbe "GL-MBE assertion failed to prove.")
         spec)
        (unk (bfr-and hyp (gtests-unknown tests)))
        ((mv unk-sat unk-succ ?unk-ctrex)
         (bfr-sat unk))
        ((when (and unk-sat unk-succ))
         ;; (acl2::sneaky-save 'gl-mbe-ctrex unk-ctrex)
         (er hard? 'gl-mbe "GL-MBE assertion failed with unknown.")
         spec)
        ((when (not unk-succ))
         (er hard? 'gl-mbe "GL-MBE assertion failed to prove absence of unknowns.")
         spec))
     impl))

;; (def-gobjectp-thm gl-mbe)

(verify-g-guards gl-mbe)

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

(def-gobj-dependency-thm gl-mbe
  :hints `(("goal"
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(def-g-correct-thm gl-mbe eval-g-base
  :hints '(("goal" :do-not-induct t
            :in-theory (disable bfr-sat-unsat))
           (and stable-under-simplificationp
                (let ((insts (instantiate-bfr-sat-hint clause '(car env))))
                  (if insts
                      `(:computed-hint-replacement
                        t
                        :use ,insts)
                    (cw "clause: ~x0~%" clause))))))
