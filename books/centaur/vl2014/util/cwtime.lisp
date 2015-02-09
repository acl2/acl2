; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(defmacro cwtime (form &key name (mintime 'nil) (minalloc 'nil))
  "Concise time reports with optional names."
  (let ((name (or name
                  (and (consp form)
                       (symbolp (car form))
                       (car form))
                  'cwtime)))
    `(time$ ,form
            :msg "; ~s0: ~st seconds, ~sa bytes.~%"
            :args (list ',name)
            :mintime ,mintime
            :minalloc ,minalloc)))

(defmacro xf-cwtime (form &key
                          name
                          (mintime '1/3)
                          ;; 64 MB minalloc to report
                          (minalloc '67108864))
  "Same as cwtime, but defaults to 1/3 second or 64 MB allocation minimum.
This is nice as a sort of passive performance monitor: if everything is running
quickly you won't be bothered with timing info, but if something is taking
awhile or a lot of memory, you'll get a chance to notice it."
  `(cwtime ,form
           :name ,name
           :mintime ,mintime
           :minalloc ,minalloc))

#||

(cwtime (append '(1 2 3) '(4 5 6)))
(cwtime (+ 1 2))
(cwtime 3)

||#

