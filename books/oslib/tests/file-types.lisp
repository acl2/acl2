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
(include-book "../file-types")
(include-book "../catpath")
(include-book "std/util/defconsts" :dir :system)

(defttag :sys-call)

(defmacro check-file-kind (path expected-type &key follow-symlinks)
  `(make-event
    (b* ((path ',path)
         (expected-type ',expected-type)
         (follow-symlinks ',follow-symlinks)
         ((mv err ans state) (oslib::file-kind path
                                               :follow-symlinks follow-symlinks))
         (- (cw "; path ~s0 -> ~x1~%"
                path
                (list :err err :ans ans :expect expected-type)))
         (okp (if (eq expected-type :error)
                  (and (or err
                           (cw "Oops, expected error but no error."))
                       (or (not ans)
                           (cw "Oops, expected no answer.")))
                (and (or (not err)
                         (cw "Oops, expected no error."))
                     (or (eq ans expected-type)
                         (cw "Oops, wrong type.")))))
         ((when okp)
          (value '(value-triple :success))))
      (er soft 'check-file-kind "Assertion failed"))))

(check-file-kind "/" :directory)
(check-file-kind "file-types.lisp" :regular-file)
(check-file-kind "does-not-exist.txt" nil)

(make-event
 ;; Sys-call on my copy of CMUCL doesn't seem able to invoke ./makelink.sh so
 ;; as a workaround use the full path explicitly.
 (b* ((- (sys-call (oslib::catpath (cbd) "makelink.sh")
                   nil)))
   (value '(value-triple :makelink))))

(check-file-kind "test-link"
                 :symbolic-link
                 :follow-symlinks nil)

(check-file-kind "test-link"
                 :regular-file
                 :follow-symlinks t)

(check-file-kind "test-broken-link"
                 :broken-symbolic-link
                 :follow-symlinks t)

(check-file-kind "test-broken-link"
                 :symbolic-link
                 :follow-symlinks nil)

#+Unix ;; <-- maybe need to tweak this
(progn
  (check-file-kind "/dev/null" :character-device)
  ; #-(or darwin freebsd) ;; has failed on Mac OS 10.6.8 and 10.10.5, and FreeBSD
  #+skip ; see comment just above; also fails with CCL on Linux 4.4.0-134-generic #160-Ubuntu
  (check-file-kind "/dev/sda1" :block-device))


