; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>


(in-package "FGL")

(include-book "std/util/define" :dir :system)

(define fgl-simplify-object (x transforms
                             &key
                             ((tracked-obj
                               "Object that is not preserved but whose bits' formulas
                                are tracked through possibly non-preserving transforms,
                                for heuristic use by the transforms")
                              'nil)
                             ((use-pathcond
                               "Assume the path condition true when simplifying the formulas")
                              't)
                             ((use-constraint
                               "Assume the constraint condition true when simplifying the formulas")
                              't))
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  x)

(define fgl-simplify-ordered (x transforms
                             &key
                             ((tracked-obj
                               "Object that is not preserved but whose bits' formulas
                                are tracked through possibly non-preserving transforms,
                                for heuristic use by the transforms")
                              'nil)
                             ((use-pathcond
                               "Assume the path condition true when simplifying the formulas")
                              't)
                             ((use-constraint
                               "Assume the constraint condition true when simplifying the formulas")
                              't))
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  x)
