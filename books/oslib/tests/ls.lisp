; OSLIB -- Operating System Utilities
; Copyright (C) 2013-2014 Centaur Technology
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
(include-book "../ls")
(include-book "std/util/defconsts" :dir :system)
(include-book "misc/assert" :dir :system)

(defconsts (*files* state)
  (oslib::ls! "."))

(assert! (member-equal ".fileforls" *files*))
(assert! (member-equal "ls.lisp" *files*))
(assert! (member-equal "top.lisp" *files*))
(assert! (not (member-equal "." *files*)))
(assert! (not (member-equal ".." *files*)))

(defconsts (*acl2-all* state)
  (b* ((acl2-src-dir (f-get-global 'acl2::acl2-sources-dir state)))
    (oslib::ls! acl2-src-dir)))

(assert! (member-equal "axioms.lisp" *acl2-all*))  ;; Regular file with extension
(assert! (member-equal "Makefile" *acl2-all*))     ;; Regular file without extension
(assert! (member-equal "emacs" *acl2-all*))        ;; Directory

(defconsts (*acl2reg* state)
  (b* ((acl2-src-dir (f-get-global 'acl2::acl2-sources-dir state)))
    (oslib::ls-files! acl2-src-dir)))

(assert! (member-equal "axioms.lisp" *acl2reg*))
(assert! (subsetp-equal *acl2reg* *acl2-all*))

(defconsts (*acl2dirs* state)
  (b* ((acl2-src-dir (f-get-global 'acl2::acl2-sources-dir state)))
    (oslib::ls-subdirs! acl2-src-dir)))

(assert! (member-equal "emacs" *acl2dirs*))
(assert! (subsetp-equal *acl2dirs* *acl2-all*))
(assert! (or (subsetp-equal *acl2-all* (append *acl2dirs* *acl2reg*))
             (cw "Oops, somehow acl2-all has files that aren't dirs or regular? ~x0~%"
                 (set-difference-equal *acl2-all*
                                       (append *acl2dirs* *acl2reg*)))))

(assert! (or (not (intersection-equal *acl2dirs* *acl2reg*))
             (cw "Oops, intersecting files and dirs?  ~x0~%"
                 (intersection-equal *acl2dirs* *acl2reg*))))

(defconsts (*err* *val* state)
  ;; There was once a bug with ls-fn's raw lisp definition where it was
  ;; returning (mv (msg ...)) instead of (mv (msg ...) nil state) in an error
  ;; case.  This led to a horrible error message about latch-stobjs1.  At any
  ;; rate, it's a good idea to test that trying to list non-existent dirs
  ;; really do cause errors.
  (oslib::ls "/this-directory-should-not-exist/or-else/this-test/will-fail"))

(assert! *err*)
(assert! (not *val*))
