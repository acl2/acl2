; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "top")

(defun sidekick-startup-fn ()
  (declare (xargs :mode :program))
  (er hard? 'sidekick-startup-fn "Under the hood definition not installed?"))

(reset-prehistory nil)
(set-debugger-enable t)

(sidekick::stop)
(acl2::tshell-stop)

;; BOZO this is horrible, but these warnings are really irritating.
(assign acl2::slow-array-action nil)

:q

(setq *print-startup-banner* nil)

(defun sidekick-startup-fn ()
  ;; Blah, recreate some output that print-startup-banner suppresses.  I really
  ;; just want to suppress the ugly modification notice.
  #+ccl
  (format t "~&Welcome to ~A ~A!~%"
          (lisp-implementation-type)
          (lisp-implementation-version))
  (when *print-startup-banner*
    (format t
            *saved-string*
            (acl2-version+)
            (saved-build-dates :terminal)))
  (format t "~%")
  (sidekick::start))

(save-exec "sidekick" nil
           :init-forms '((sidekick-startup-fn)))
