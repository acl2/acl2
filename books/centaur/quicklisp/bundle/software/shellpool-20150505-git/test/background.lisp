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

; background.lisp -- tests of run& command

(defun basic-bg-test ()
  (format t "Doing basic BG test.~%")
  (let ((subname #-windows "sleep.pl"
                 #+windows "perl"))
    (when (has-process subname)
      (error "Looks like ~s is running already, won't be able to test background jobs correctly."
             subname))
    (shellpool:run& "./sleep.pl 10")
    (sleep 4)
    (unless (has-process subname)
      (error "Doesn't seem like ~s got started.~%" subname))
    (sleep 10)
    (when (has-process subname)
      (error "Doesn't seem like ~s exited.~%" subname))))

(loop for i from 1 to 3 do
      (basic-bg-test))


(defun basic-bg-test2 ()
  (format t "Doing basic BG2 test.~%")
  (shellpool:run& "rm hello.txt")
  (sleep 3)
  (when (probe-file "hello.txt")
    (error "Somehow hello.txt exists?"))
  (shellpool:run& "echo hello > hello.txt")
  (sleep 3)
  (basic-test "cat hello.txt" :stdout '("hello"))
  (shellpool:run& "rm hello.txt")
  (sleep 3)
  (when (probe-file "hello.txt")
    (error "Somehow hello.txt exists?")))

(loop for i from 1 to 3 do
      (basic-bg-test2))
