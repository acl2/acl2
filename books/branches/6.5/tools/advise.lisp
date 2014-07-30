; Access to CCL::ADVISE
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "include-raw")

; NOT SOUND.  You can do any old underhanded thing you want when you advise a
; function, including, e.g., smashing ACL2's state.


(defun advise$-fn (fn form when name)
  (declare (ignorable fn form when name)
           (xargs :guard t))
  (er hard? 'advise$ "Raw lisp definition not installed?"))

(defun unadvise$-fn (fn when name)
  (declare (ignorable fn when name)
           (xargs :guard t))
  (er hard? 'unadvise$ "Raw lisp definition not installed?"))

(defun advisedp$-fn (fn when name)
  (declare (ignorable fn when name)
           (xargs :guard t))
  (er hard? 'advisedp$ "Raw lisp definition not installed?"))


(defmacro advise$ (fn form &key when name)
  `(advise$-fn ,fn ,form ,when ,name))

(defmacro unadvise$ (fn &key when name)
  `(unadvise$-fn ,fn ,when ,name))

(defmacro advisedp$ (fn &key when name)
  `(advisedp$-fn ,fn ,when ,name))


(defttag :unsound-advise$)
(include-raw "advise-raw.lsp")




#||

(include-book
 "advise")

(defun f (x)
  (declare (xargs :guard (natp x)))
  (mv (+ 1 x) (+ 2 x)))

(advise$ 'f
         '(cw "Values were ~x0~%" values)
         :when :after)

(f 3)
(f 5)

||#