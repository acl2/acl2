; Shellpool - Interface from Common Lisp to External Programs
; Copyright (C) 2014-2015 Kookamara LLC
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

; top.lsp -- top level Shellpool test suite

(ql:quickload "shellpool")
(ql:quickload "uiop")

(format t "Features are ~s~%" *features*)

#+lispworks
(bt:start-multiprocessing)

(let ((oops nil))
  (format t "** Checking running a command before starting any shells.~%")
  (handler-case
    (progn (shellpool:run "echo hello")
           (setq oops t))
    (error (condition)
           (declare (ignore condition))
           (format t "OK: Got error as expected.~%")
           nil))
  (when oops
    (error "Running a command without any shells worked?")))

(shellpool:start)

(load "utils.lisp")

(progn
  (format t "~% -------- Doing basic tests -------------- ~%")
  (load "basic.lisp"))

(setq shellpool:*debug* t)

(progn
  (format t "~% -------- Doing kill tests --------------- ~%")
  (load "kill.lisp"))

(progn
  (format t "~% -------- Doing background tests --------- ~%")
  (load "background.lisp"))

(format t "All tests passed.~%")
(with-open-file (stream "test.ok"
                        :direction :output
                        :if-exists :supersede)
  (format stream "All tests passed.~%"))

(uiop:quit)
