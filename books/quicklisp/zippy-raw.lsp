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

(in-package "ACL2")

; If this raw lisp file has already been loaded into the current environment,
; and if it is being reloaded (see acl2/acl2 issue 1507)
; and if the asdf aready-loaded-systems info has been clobbered
; (see acl2/acl2 issue 1508),
; then require-system will cause a reload.
; A reload will not work with the renamed package, so to handle this case
; we undo the rename-package first.
(let ((package (find-package :zippy)))
  (when (and package
             (string= (package-name package) "ZIPPY")
             (equal (package-nicknames package) '("ORG.SHIRAKUMO.ZIPPY")))
    (rename-package package :org.shirakumo.zippy)))

(asdf:require-system "zippy")

;; The Zippy doc suggests using ZIPPY as a package-local nickname (PLN) for ORG.SHIRAKUMO.ZIPPY.
;; However, the ACL2 package interface doesn't let you define nicknames let alone PLNs.
;; (Although they are supported by both CCL and SBCL.)
;; Also, ACL2 packages can't be renamed.
;; Therefore, in order to refer to the package ORG.SHIRAKUMO.ZIPPY in ACL2 code with a shorter name,
;; we rename the package here.
;; We could just add ZIPPY as a nickname, but printing would be a problem, then.
;; Instead we rename the primary name but keep the original name as a nickname.

(rename-package (find-package :org.shirakumo.zippy) :zippy '("ORG.SHIRAKUMO.ZIPPY"))
