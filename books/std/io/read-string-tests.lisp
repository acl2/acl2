; Standard IO Library
; read-string-tests.lisp
; Copyright (C) 2013 Centaur Technology
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

(in-package "ACL2")
(include-book "read-string")

(defmacro test-ok (str expect)
  `(make-event
    (b* (((mv errmsg objects state) (read-string ',str))
         ((when (and (not errmsg)
                     (equal objects ',expect)))
          (value '(value-triple :success))))
      (er soft 'test-ok "Test failed for ~s0: expect ~x1 but got ~x2; msg is ~@3"
          ',str ',expect objects errmsg))))

(defmacro test-fail (str)
  `(make-event
    (b* (((mv errmsg objects state) (read-string ',str))
         ((when errmsg)
          (value '(value-triple :success))))
      (er soft 'test-fail "Test failed for ~s0: expect FAIL but got ~x1."
          ',str objects))))

(test-ok "" nil)
(test-ok "1 2 3" (1 2 3))
(test-ok "#x10 \"foo\"" (16 "foo"))
(test-ok "#ux_1_0_0" (256))
(test-ok "(append x y z)" ((append x y z)))
(test-ok "*foo*" (*FOO*))
(test-ok "#\\a " (#\a))
(test-ok "#\\Page " (#\Page))
(test-ok "#\\a" (#\a)) ; Matt K.: Fixed in acl2-devel svn revision 1154
(test-ok "#\\Page" (#\Page)) ; Matt K.: Fixed in acl2-devel svn revision 1154

;; Some things that had better fail:

(test-fail "3.5")
(test-fail "'#.(list 1 2 3)")
(test-fail "#\wtf ")
(test-fail "#\Return ")
; Matt K.: Commenting out the following, which apparently loops forever when
; using ACL2 rather than ACL2(h).
; (test-fail "#1=(a . #1#)")

#||

The following is odd, perhaps a bug in the EOF handling of ACL2's character
reading routines?

? (let* ((stream (make-string-input-stream "#\\a"))
         (x1 (read stream nil :EOF))
         (x2 (read stream nil :EOF)))
    (list x1 x2))
(#\a :EOF)

? (let* ((*readtable* *acl2-readtable*)
         (stream (make-string-input-stream "#\\a"))
         (x1 (read stream nil :EOF))
         (x2 (read stream nil :EOF)))
    (list x1 x2))
> Error: Unexpected end of file on #<STRING-INPUT-STREAM  #x30200672BEDD>,
> near position 3, within "#\\a"
> While executing: CCL::READ-CHAR-INTERNAL, in process listener(1).
> Type :POP to abort, :R for a list of available restarts.
> Type :? for other options.

||#
