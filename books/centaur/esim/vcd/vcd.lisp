; ESIM Symbolic Hardware Simulator
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
(include-book "vcd-stub")
(include-book "esim-snapshot")

; This elaborate stub and redefinition nonsense lets the user include the vcd
; book without getting all the VL theory stuff.

#||
(include-book "vcd-impl") ;; for the dependency scanner
||#

(make-event
 (let ((vcd-impl (extend-pathname (cbd) "vcd-impl" state)))
   `(defconst *vcd-impl* ',vcd-impl)))

(defmacro install-vcd-dump ()
  `(include-book ,*vcd-impl*))

(defmacro vcd-dump (filename snapshots
                             &key (viewer '"gtkwave")
                             emap)
  `(encapsulate
     ()
     (local (include-book ,*vcd-impl*))
     (make-event
      (let ((state (vl2014::vcd-dump-fn ,filename ,snapshots ,viewer ,emap state)))
        (value '(value-triple :invisible))))))


