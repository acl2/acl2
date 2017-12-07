; Copyright (C) 2012, David Rager

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

; Defines a macro that temporarily disables waterfall parallelism and then
; restores it to its previous value.  Perhaps the calls of
; set-waterfall-parallelism need not be local, but be careful about removing
; the LOCALs: perhaps that would cause problems for how
; set-waterfall-parallelism changes the memoization status of functions, in the
; case of locally defined functions.  Another reason to keep the LOCALs is that
; the user of this macro will be unhappy if it messes with
; waterfall-parallelism settings when including a book.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defun with-waterfall-parallelism-fn (events state)
; (declare (xargs :guard (state-p state) :stobjs state))
  (declare (xargs :mode :program :stobjs state))
  (let ((curr-waterfall-parallelism-val
         (f-get-global 'waterfall-parallelism state)))
    `(progn (local (make-event
                    (er-progn (set-waterfall-parallelism t)
                              (value '(value-triple nil)))
                    :check-expansion t))
            ,@events
            (local (make-event
                    (er-progn (set-waterfall-parallelism
                               ',curr-waterfall-parallelism-val)
                              (value '(value-triple t)))
                    :check-expansion t)))))

(defmacro with-waterfall-parallelism (&rest events)
  `(make-event (with-waterfall-parallelism-fn ',events state)))

(defxdoc with-waterfall-parallelism
  :parents (parallelism)
  :short "Enable waterfall parallelism for an enclosed event"
  :long "<p>Example usage:</p>
  @({
  (with-waterfall-parallelism
    (defthm assoc-append
     (equal (append x (append y z))
            (append (append x y) z))))
  })")
