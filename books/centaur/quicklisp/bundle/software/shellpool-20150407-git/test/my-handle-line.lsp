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

; my-handle-line.lsp -- Code that is used in the documentation examples

(ql:quickload "shellpool")
(shellpool:start)

(defun my-handle-line (line type)
  ;; LINE is a string -- a single line of output
  ;; TYPE is either :STDOUT or :STDERR
  (format t "On ~s, got ~s~%" type line))

(shellpool:run "echo hello
                echo world 1>&2
                echo foo
                echo bar 1>&2"
               :each-line #'my-handle-line)

(defun fancy-runner (cmd)
  (let ((out-lines nil)
        (err-lines nil)
        (return-code nil))
    (setq return-code
          (shellpool:run cmd
                         :each-line
                         (lambda (line type)
                           (case type
                             (:STDOUT (push line out-lines))
                             (:STDERR (push line err-lines))
                             (otherwise (error "unexpected line type from shellpool: ~s" type))))))
    (list :return-code return-code
          :out-lines (nreverse out-lines)
          :err-lines (nreverse err-lines))))

(fancy-runner "echo hello
               echo world 1>&2
               echo foo
               echo bar 1>&2")
