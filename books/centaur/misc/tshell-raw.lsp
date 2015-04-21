; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Tshell
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

; See the Shellpool API documentation to understand all of this.

(defun tshell-start-fn (n)
  (shellpool:start n)
  nil)

(defun tshell-ensure-fn (n)
  (shellpool:ensure n)
  nil)

(defun tshell-echo (line   ; current line of stderr or stdout output
                    rlines ; previous lines of output, in reverse order, if :save t
                    stream ; stream to print to
                    )

; This is how tshell prints output from the sub-program using :print t.
;
; We originally put this in a separate function so that it can be redefined.
; Now there's no reason to do that because you can give a custom argument to
; :print.  But your function should be signature-compatible with tshell-echo.
;
; Note: Redefined in transistor/equiv-check (Centaur internal), so don't change
; it unless you update that, too.
;
; We could probably make this more general.  At least it's better than it was
; before.

  (declare (ignorable rlines))
  (write-line line stream)
  (force-output stream))

(defun tshell-call-fn (cmd print save)
  (let* ((rlines nil)
         (stream (get-output-stream-from-channel *standard-co*))
         (print  (if (eq print t)
                     'tshell-echo
                   print))
         (status (shellpool:run cmd
                                :each-line (lambda (line type)
                                             (when save
                                               (push line rlines))
                                             (when print
                                               (funcall print line rlines stream))))))
    (mv status (nreverse rlines))))

(defun tshell-run-background (cmd)
  (shellpool:run& cmd))


#|

;; everything works with no status

(include-book "str/strprefixp" :dir :system)
:q
(load "tshell-raw.lsp")
(in-package "AIGPU")

(setq *tshell-debug* t)
(tshell-start)
(tshell "echo hello")
(tshell "./run_aigpu.sh mul35.aigpu")
(tshell "echo hello")

|#
