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

(defun without-waterfall-parallelism-fn (events state)
; (declare (xargs :guard (state-p state) :stobjs state))
  (declare (xargs :mode :program :stobjs state))
  (let ((curr-waterfall-parallelism-val
         (f-get-global 'waterfall-parallelism state)))

; Matt K. mode, 10/1/2014: I removed LOCAL from each MAKE-EVENT below so that
; this utility works when including uncertified books, for example when
; certifying a book after (set-write-acl2x '(t) state).  Then I also removed
; :CHECK-EXPANSION from each, because now that the make-event forms are
; non-local, the second one could cause waterfall-parallelism to be
; inadvertently turned on when including a book.

    `(progn (make-event
             (er-progn (set-waterfall-parallelism nil)
                       (value '(value-triple nil))))
            ,@events
            (make-event
             (er-progn (set-waterfall-parallelism
                        ',curr-waterfall-parallelism-val)
                       (value '(value-triple t)))))))

(defmacro without-waterfall-parallelism (&rest events)
  `(make-event (without-waterfall-parallelism-fn ',events state)))

(defxdoc without-waterfall-parallelism
  :parents (parallelism)
  :short "Disable waterfall parallelism for an enclosed event"
  :long "<p>Example usage:</p>
  @({
  (without-waterfall-parallelism
    (defun foo (x) (* x 3)))
  })")
