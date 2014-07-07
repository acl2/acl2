; ACL2 Event Origin
; Copyright (C) 2013 Kookamara LLC
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
;
; Modified by Matt Kaufmann 8/28/2013 to avoid command world errors.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(set-state-ok t)
(program)

(defxdoc origin
  :parents (acl2::pe)
  :short "Returns a summary of where a @(see logical-name) originates from."
  :long "<p>Examples:</p>
@({
  (include-book \"system/origin\" :dir :system)

  ;; built-in names get a return value of :built-in
  (origin 'consp)    --> (value :built-in)
  (origin 'car-cons) --> (value :built-in)

  ;; include-book path is reported for events included from other books
  (origin 'xdoc::save) --> (value (\"/home/jared/acl2/books/system/origin.lisp\"
                                   \"/home/jared/acl2/books/xdoc/top.lisp\"))

  (origin 'lnfix) --> (value (\"/home/jared/acl2/books/system/origin.lisp\"
                              \"/home/jared/acl2/books/xdoc/top.lisp\"
                              \"/home/jared/acl2/books/xdoc/base.lisp\"))

  ;; some definitions are from the current session, e.g.:
  (defun f (x) x)
  (origin 'f)     --> (value :TOP-LEVEL)

  ;; bad names
  (mv-let (er val state)               ;; ((:er (\"Not a logical name: ~x0\"
          (origin 'not-defined-thing)  ;;        (#\0 . NOT-DEFINED-THING))
   (mv (list :er er :val val)          ;;   :val nil)
       state))                         ;;  <state>)

})")

(defun origin-fn (logical-name state)
  (let* ((wrld (w state)))
    (cond
     ((acl2-system-namep logical-name wrld)
      (value :built-in))
     (t
      (let ((ev-wrld (decode-logical-name logical-name wrld)))
        (cond (ev-wrld
               (value (let ((book-path (global-val 'include-book-path ev-wrld)))
                        (cond (book-path
                               (reverse book-path))
                              (t
                               :top-level)))))
              (t (mv (msg "Not logical name: ~x0." logical-name) nil state))))))))

(defmacro origin (logical-name)
  `(origin-fn ,logical-name state))

