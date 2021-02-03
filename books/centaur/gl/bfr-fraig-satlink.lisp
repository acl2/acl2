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

(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "../aignet/transforms")


;; so we can use with-local-state
(defttag aig-fraig->cnf)
(remove-untouchable acl2::create-state t)


(encapsulate
  (((gl-fraig-config) => *))
  (local (defun gl-fraig-config ()
           aignet::*fraig-default-config*))
  (defthm gl-fraig-config-constraint
    (aignet::fraig-config-p (gl-fraig-config))))

(defun gl-default-fraig-config ()
  (declare (xargs :guard t))
  aignet::*fraig-default-config*)

(defattach gl-fraig-config gl-default-fraig-config)

(define fraig-satlink-transform (aignet::aignet transform-config)
  (declare (ignore transform-config))
  :enabled t
  (with-local-state
    (mv-let (aignet::aignet state)
      (aignet::fraig! aignet::aignet (gl-default-fraig-config) state)
      aignet::aignet)))
  

(defsection gl-fraig-satlink-mode
  :parents (modes reference)
  :short "GL: Use AIGs as the Boolean function representation and @(see
satlink) after aignet fraiging to solve queries."

  (defmacro gl-fraig-satlink-mode ()
    '(progn
       (defattach bfr-mode bfr-aig)
       (defattach bfr-counterex-mode bfr-counterex-alist)
       (defattach (bfr-sat bfr-satlink)
         :hints(("Goal" :in-theory (enable bfr-eval))))
       (defattach aignet::aig->cnf-aignet-transform fraig-satlink-transform))))

(local (gl-fraig-satlink-mode))



(encapsulate
  (((gl-transforms-config) => *))
  (local (defun gl-transforms-config () nil))
  (defthm gl-transforms-config-constraint
    (aignet::comb-transformlist-p (gl-transforms-config))))

(defun gl-default-transforms-config ()
  (declare (xargs :guard t))
  #!aignet (list (make-balance-config)
                 (make-fraig-config)))

(defattach gl-transforms-config gl-default-transforms-config)

(define simplify-satlink-transform (aignet::aignet transform-config)
  (declare (ignore transform-config))
  :enabled t
  (with-local-state
    (mv-let (aignet::aignet state)
      (time$ (aignet::apply-comb-transforms! aignet::aignet (gl-transforms-config) state)
             :msg "All transforms: ~st seconds, ~sa bytes.~%")
      aignet::aignet)))


(defsection gl-simplify-satlink-mode
  :parents (modes reference)
  :short "GL: Use AIGs as the Boolean function representation and @(see
satlink) after a configurable list of aignet transforms to solve queries."
  :long "<p>The Satlink configuration to be used can be set by attaching a
suitable function to @('gl-satlink-config') and the transforms used can be
chosen by attaching to @('gl-transforms-config').</p>"
  (defmacro gl-simplify-satlink-mode ()
    '(progn
       (defattach bfr-mode bfr-aig)
       (defattach bfr-counterex-mode bfr-counterex-alist)
       (defattach (bfr-sat bfr-satlink)
         :hints(("Goal" :in-theory (enable bfr-eval))))
       (defattach (bfr-vacuity-check bfr-satlink-nosimp)
         :hints(("Goal" :in-theory (enable bfr-eval))))
       (defattach aignet::aig->cnf-aignet-transform simplify-satlink-transform))))

(local (gl-simplify-satlink-mode))
