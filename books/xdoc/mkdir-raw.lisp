; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>


; mkdir-raw.lisp
;
; This book requires a TTAG.  You should not need to directly include it unless
; you actually need to run mkdir, as in xdoc::save.  Ordinarily this is handled
; by the macros in top.lisp.

(in-package "XDOC")
(include-book "mkdir")
(include-book "tools/bstar" :dir :system)
(set-state-ok t)

(defttag :xdoc)

(progn!
 (set-raw-mode t)

; Added by Matt K.:
; For Lisps that do not compile automatically on the fly, we add the following
; so that a subsequent (comp t) form will not re-installing a logic definition
; for the function, mkdir, that is about to be redefined in raw Lisp.
 #!acl2(f-put-global 'logic-fns-with-raw-code
                     (cons 'xdoc::mkdir (@ program-fns-with-raw-code))
                     state)

 (defun mkdir (dir state)
   (b* (((unless (stringp dir))
         (er hard? 'mkdir "Dir must be a string, but is: ~x0.~%" dir)
         state)
        (- (sys-call "mkdir" (list "-p" dir)))
        ((mv status state)
         (sys-call-status state))
        ((unless (= status 0))
         (er hard? 'mkdir "error making directory ~s0.~%" dir)
         state))
     state)))

(defttag nil)

