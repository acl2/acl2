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
; bfr-satlink.lisp
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "GL")

(include-book "bfr-sat")
(include-book "../aig/aig-sat")

(encapsulate
  (((gl-satlink-config) => *))
  (local (defun gl-satlink-config ()
           satlink::*default-config*))
  (defthm gl-satlink-config-constraint
    (satlink::config-p (gl-satlink-config))))

(defun gl-default-satlink-config ()
  (declare (xargs :guard t))
  (satlink::change-config satlink::*default-config*
                          :verbose nil))

(defattach gl-satlink-config gl-default-satlink-config)

(encapsulate
  (((gl-satlink-gatesimp) => *))
  (local (defun gl-satlink-gatesimp () (aignet::default-gatesimp)))
  (defthm gl-satlink-gatesimp-constraint
    (aignet::gatesimp-p (gl-satlink-gatesimp))))


(defattach gl-satlink-gatesimp aignet::default-gatesimp)

(defun bfr-satlink (prop)
  (declare (xargs :guard t))
  (bfr-case
   :bdd (mv nil nil nil) ;; fail
   :aig
   (b* (((mv status env)
         (acl2::aig-sat prop :config (gl-satlink-config)
                        :transform-config t ;; why not?
                        :gatesimp (gl-satlink-gatesimp))))
     (case status
       (:sat (mv t t env))
       (:unsat (mv nil t nil))
       (t ;; failed
        (mv nil nil nil))))))

(defun bfr-satlink-nosimp (prop)
  (declare (xargs :guard t))
  (bfr-case
   :bdd (mv nil nil nil) ;; fail
   :aig
   (b* (((mv status env)
         (acl2::aig-sat prop :config (gl-satlink-config) :transform-config nil))) ;; why not?
     (case status
       (:sat (mv t t env))
       (:unsat (mv nil t nil))
       (t ;; failed
        (mv nil nil nil))))))

(defsection gl-satlink-mode
  :parents (modes reference)
  :short "GL: Use AIGs as the Boolean function representation and @(see
satlink) to solve queries."

  (defmacro gl-satlink-mode ()
    '(progn
       (defattach bfr-mode bfr-aig)
       (defattach bfr-counterex-mode bfr-counterex-alist)
       (defattach (bfr-sat bfr-satlink)
         :hints(("Goal" :in-theory (enable bfr-eval))))
       (defattach (bfr-vacuity-check
                   bfr-sat)
         :hints (("goal" :use bfr-sat-unsat)))
       (defattach #!aignet (aig->cnf-aignet-transform aig->cnf-default-aignet-transform)))))

