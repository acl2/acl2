; Lispfloat - Interface to the Common Lisp Floating Point Operations
; Copyright (C) 2016 Centaur Technology
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

(in-package "LISPFLOAT")
(include-book "std/basic/defs" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/util/defmvtypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)

(defmacro def-float-op (name args short)
  `(progn

     (local (defun ,name ,args
              ;; Keeping this out of the defsection seems to help to avoid
              ;; sucking the whole encapsulate into the docs for each function.
              (declare (ignorable . ,args))
              (mv nil 0)))

     (defsection-progn ,name
       :parents (lispfloat)
       :short ,short
       :long ,(str::cat
               "<p>@(call " (xdoc::full-escape-symbol name) ") is a @(see
                lispfloat) wrapper function.</p>

                <p>In the logic this function does not have a definition, but
                its @(see acl2::constraint)s say it returns @('(mv errmsg ans)'),
                where:</p>

                <ul>

                <li>@('errmsg') is either a string that indicates an error
                has occurred (e.g., a rounding error when converting rationals
                to floats, an overflow, etc.)</li>

                <li>@('ans') is a rational.</li>

                </ul>")

       "<h5>Basic Type Theorems</h5>"

       (defmvtypes ,name (maybe-stringp rationalp))

       "<h5>Rational-Equiv Congruence Rules</h5>"

       (deffixequiv ,name
         :args ,(pairlis$ args (acl2::replicate (len args) '(rationalp)))))))

(encapsulate
  (((er-float+ * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))
   ((er-float- * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))
   ((er-float* * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))
   ((er-float/ * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))
   ((er-float-expt * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))

   ((er-float-sqrt *) => (mv * *) :formals (a) :guard (rationalp a))
   ((er-float-e^x *) => (mv * *) :formals (a) :guard (rationalp a))

   ((er-float-sin *) => (mv * *) :formals (a) :guard (rationalp a))
   ((er-float-cos *) => (mv * *) :formals (a) :guard (rationalp a))
   ((er-float-tan *) => (mv * *) :formals (a) :guard (rationalp a))

   ;; Not yet implemented:
   ;;   log -- may return complex when given negatives

   ;;   asin -- may return complex
   ;;   acos -- may return complex
   ;;   atan -- may return complex

   )

  (def-float-op er-float+ (a b) "(Single-precision) floating point addition.")
  (def-float-op er-float- (a b) "(Single-precision) floating point subtraction.")
  (def-float-op er-float* (a b) "(Single-precision) floating point multiplication.")
  (def-float-op er-float/ (a b) "(Single-precision) floating point division.")
  (def-float-op er-float-expt (a b) "(Single-precision) floating point exponentiation.")

  (def-float-op er-float-sqrt (a) "(Single-precision) floating point square root.")
  (def-float-op er-float-e^x (a) "(Single-precision) floating point e^x.")

  (def-float-op er-float-sin (a) "(Single-precision) floating point sine.")
  (def-float-op er-float-cos (a) "(Single-precision) floating point cosine.")
  (def-float-op er-float-tan (a) "(Single-precision) floating point tangent.")

  )



(encapsulate
  (((er-double+ * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))
   ((er-double- * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))
   ((er-double* * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))
   ((er-double/ * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))
   ((er-double-expt * *) => (mv * *) :formals (a b) :guard (and (rationalp a) (rationalp b)))

   ((er-double-sqrt *) => (mv * *) :formals (a) :guard (rationalp a))
   ((er-double-e^x *) => (mv * *) :formals (a) :guard (rationalp a))

   ((er-double-sin *) => (mv * *) :formals (a) :guard (rationalp a))
   ((er-double-cos *) => (mv * *) :formals (a) :guard (rationalp a))
   ((er-double-tan *) => (mv * *) :formals (a) :guard (rationalp a))
   )

  (def-float-op er-double+ (a b) "(Double-precision) floating point addition.")
  (def-float-op er-double- (a b) "(Double-precision) floating point subtraction.")
  (def-float-op er-double* (a b) "(Double-precision) floating point multiplication.")
  (def-float-op er-double/ (a b) "(Double-precision) floating point division.")
  (def-float-op er-double-expt (a b) "(Double-precision) floating point exponentiation.")

  (def-float-op er-double-sqrt (a) "(Double-precision) floating point square root.")
  (def-float-op er-double-e^x (a) "(Double-precision) floating point e^x.")

  (def-float-op er-double-sin (a) "(Double-precision) floating point sine.")
  (def-float-op er-double-cos (a) "(Double-precision) floating point cosine.")
  (def-float-op er-double-tan (a) "(Double-precision) floating point tangent.")

  )
