; IPASIR - Link from ACL2 to IPASIR incremental sat solvers
; Copyright (C) 2017 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package :ipasir-raw)

(defcfun "ipasir_bump_var_activity" :void
  (solver :pointer)
  (var :int)
  (bumps :int))

(defcfun "ipasir_simplify" :void
  (solver :pointer))

(defcfun "ipasir_get_curr_num_assigns" :int
  (solver :pointer))

(defcfun "ipasir_get_curr_num_clauses" :int
  (solver :pointer))

(defcfun "ipasir_get_curr_num_learnts" :int
  (solver :pointer))

(defcfun "ipasir_get_curr_num_vars" :int
  (solver :pointer))

(defcfun "ipasir_get_curr_num_free_vars" :int
  (solver :pointer))

;;;;;;;

(in-package "IPASIR")

(defun ipasir-bump-each-var-activity (ipasir vars num-bumps)
  (cond ((atom vars) ipasir)
        (t (ipasir-raw::ipasir-bump-var-activity (ipasir-get-raw ipasir)
                                                 (first vars)
                                                 num-bumps)
           (ipasir-bump-each-var-activity ipasir (rest vars) num-bumps))))

(defun ipasir-bump-activity-vars$c (ipasir vars num-bumps)
  (ipasir-bump-each-var-activity ipasir vars num-bumps)
  ;; NOTE -- we need to rebuild the order heap, which is done as part of
  ;; simplify in MiniSat-based solvers:
  (ipasir-raw::ipasir-simplify (ipasir-get-raw ipasir))
  ipasir)

(defun ipasir-get-curr-stats$c (ipasir)
  (mv (nfix (ipasir-raw::ipasir-get-curr-num-assigns   (ipasir-get-raw ipasir)))
      (nfix (ipasir-raw::ipasir-get-curr-num-clauses   (ipasir-get-raw ipasir)))
      (nfix (ipasir-raw::ipasir-get-curr-num-learnts   (ipasir-get-raw ipasir)))
      (nfix (ipasir-raw::ipasir-get-curr-num-vars      (ipasir-get-raw ipasir)))
      (nfix (ipasir-raw::ipasir-get-curr-num-free-vars (ipasir-get-raw ipasir)))))

