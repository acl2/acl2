; Centaur BED Library
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

(in-package "BED")
(include-book "ops")

(define bed-op-name ((x bed-op-p))
  (cond
   ((eql x (bed-op-true)) 'true)
   ((eql x (bed-op-ior))  'or)
   ((eql x (bed-op-orc2)) 'orc2)
   ((eql x (bed-op-arg1)) 'arg1)
   ((eql x (bed-op-orc1)) 'orc1)
   ((eql x (bed-op-arg2)) 'arg2)
   ((eql x (bed-op-eqv))  'eqv)
   ((eql x (bed-op-and))  'and)
   ((eql x (bed-op-nand)) 'nand)
   ((eql x (bed-op-xor))  'xor)
   ((eql x (bed-op-not2)) 'not2)
   ((eql x (bed-op-andc2)) 'andc2)
   ((eql x (bed-op-not1)) 'not1)
   ((eql x (bed-op-andc1)) 'andc1)
   ((eql x (bed-op-nor)) 'nor)
   ((eql x (bed-op-false)) 'false)
   (t 'unknown)))

(define bed-print (x)
  (b* (((when (atom x))
        x)
       ((cons a b) x)
       ((when (atom a))
        (let ((yes (bed-print (car$ b)))
              (no  (bed-print (cdr$ b))))
          (cond ((and (eq yes t)
                      (eq no nil))
                 (list 'VAR a))
                ((and (eq yes nil)
                      (eq no t))
                 (list 'NVAR a))
                (t
                 (list 'VAR-ITE a yes no))))))
    (list (bed-op-name (bed-op-fix b))
          (bed-print (car$ a))
          (bed-print (cdr$ a)))))

