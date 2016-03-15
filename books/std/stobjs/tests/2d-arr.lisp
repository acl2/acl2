; ACL2 Standard Library
; Copyright (C) 2008-2016 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "../2d-arr")
(local (include-book "std/lists/resize-list" :dir :system))

(def-2d-arr intmatrix
  :prefix imx
  :pred integerp
  :type-decl integer
  :default-val 0
  :fix ifix)



(defun f-stringp (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (< 0 (length x))
       (eql (char x 0) #\f)))

(defun nonempty-str-fix (x)
  (declare (xargs :guard t))
  (if (and (stringp x) (< 0 (length x)))
      x
    "f"))

(defthm f-stringp-when-stringp
  (implies (and (stringp x)
                (< 0 (length x))
                (equal (char x 0) #\f))
           (f-stringp x)))

(defthm nonempty-str-fix-when-f-stringp
  (implies (f-stringp x)
           (equal (nonempty-str-fix x) x)))

(in-theory (disable f-stringp nonempty-str-fix))

(def-2d-arr fstring2d
  :prefix fs2d
  :pred (lambda (x) (and (stringp x) (f-stringp x)))
  :type-decl (and string (satisfies f-stringp))
  :fix nonempty-str-fix
  :default-val "f")



(def-2d-arr s61v
  :pred (lambda (x) (signed-byte-p 61 x))
  :type-decl (signed-byte 61)
  :default-val 0
  :fix ifix
  :elt-guard (integerp x)
  :elt-okp (and (<= x (1- (expt 2 60)))
                (<= (- (expt 2 60)) x)))

(define test-s61v ((elt integerp) s61v)
  (let* ((s61v (s61v-resize-rows 5 s61v))
         (s61v (s61v-resize-cols 4 s61v))
         (s61v (s61v-set2 0 0 elt s61v)))
    s61v))
