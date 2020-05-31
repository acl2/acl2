; Standard IO Library
; read-string-tests.lisp
; Copyright (C) 2013 Centaur Technology
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
          ',str ',expect objects
          (or errmsg "NIL")))))

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

;; Note: some older versions of SBCL can't handle the following tests due to a
;; bug, e.g., see https://bugs.launchpad.net/sbcl/+bug/1333327.  This seems to
;; be fixed as of SBCL 1.2.0, so we re-enable the tests.
;; Note: These fail in the CMUCL 2014-06 snapshot and also (at least for the
;; first)  CMUCL 20, so we comment them out for CMUCL.
;; Update from Matt K., 5/31/2020: SBCL 2.0.5 has the problem discussed above,
;; so I am disabling these tests once again for SBCL.  I think we are actually
;; hitting a bug in function read-string-fn in read-string-raw.lsp (stream has
;; dynamic extent); probably I'll fix it tomorrow and then restore SBCL here
;; (and delete this comment).
#-(or cmucl sbcl)
(test-fail "#\wtf ")
#-(or cmucl sbcl)
(test-fail "#\Return ")


;; #+hons
; Matt K.: Commenting out the following, which apparently loops forever when
; using ACL2 rather than ACL2(h).
; Jared -- changing it to only be tested on #+hons.
; Jared -- Commenting it out again, see Issue 193.
;; (test-fail "#1=(a . #1#)")

(test-ok "a" (acl2::a))
(test-ok "acl2::a" (acl2::a))
(test-ok "std::foo" (std::foo))

(defttag :more-tests)

(progn! (in-package "STD"))

(acl2::test-ok "a" (std::a))
(acl2::test-ok "acl2::a" (acl2::a))
(acl2::test-ok "std::foo" (std::foo))

