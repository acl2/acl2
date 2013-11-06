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

(defun bfr-satlink (prop)
  (declare (xargs :guard t))
  (bfr-case
   :bdd (mv nil nil nil) ;; fail
   :aig
   (b* (((mv status env)
         (acl2::aig-sat prop :config (gl-satlink-config))))
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
         :hints(("Goal" :in-theory (enable bfr-eval)))))))

