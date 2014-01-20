; Centaur AIG Library
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; cert_param: (uses-glucose)
; cert_param: (ccl-only)

(in-package "ACL2")

(local (progn

(include-book "aig-sat")

(defun my-glucose-config ()
  (declare (xargs :guard t))
  (satlink::make-config :cmdline "glucose"
                        :verbose t
                        :mintime 1/2
                        :remove-temps t))

(value-triple (tshell-ensure))

; These are some extremely basic tests.  The point isn't to thoroughly test the
; SAT solver.  It's just to make sure that everything seems to be basically
; holding together.

(defun test-aig-sat (input expect)
  (b* (((mv status ?alist)
        (aig-sat input :config (my-glucose-config))))
    (cw "Alist: ~x0" alist)
    (equal status expect)))

(assert! (test-aig-sat nil :unsat))
(assert! (test-aig-sat t :sat))

(assert! (test-aig-sat 'x :sat))
(assert! (test-aig-sat (aig-and 'x 'y) :sat))
(assert! (test-aig-sat (aig-ite 'x 'y 'z) :sat))

(assert! (test-aig-sat (aig-and
                        (aig-ite 'x 'y 'z)
                        (aig-ite 'x (aig-not 'y) (aig-not 'z)))
                       :unsat))


(assert! (test-aig-sat (aig-and-list
                        (list (aig-or 'x 'y)
                              'a
                              (aig-or (aig-not 'x) 'y)
                              (aig-and 'a 'b)
                              (aig-or 'x (aig-not 'y))
                              'c
                              (aig-not 'x)
                              (aig-not 'y)))
                       :unsat))


))