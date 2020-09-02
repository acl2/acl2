; A simple example of how to model nondeterminism in ACL2 using the
; encapsulate feature.

; Copyright David Rager 2012.

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

(in-package "ACL2")

(encapsulate

; Declare the signature of foo, so that foo can be exported.  Think of this as
; a C header file.

 (((foo) => *))

; Define a non-exported definition of foo, which will be thrown away after the
; scope of the encapsulate is exited.  This definition serves as a "witness" to
; ACL2, which allows us to soundly proclaim that a function named foo with the
; properties we will later specify can actually exist.

 (local (defun foo () t))

; Define the properties of foo that we want exported and to be available
; beyond the scope of the encapsulate.

 (defthm foo-result
   (booleanp (foo)))

 ) ; end encapsulate

(local
 (defthm foo-returns-atom-lemma
   (implies (booleanp x)
            (atom x))))

; We now have a non-deterministic function named foo that is only known to
; return a t or nil.  This function is admitted into the logic, and we can
; reason about it, but we can not execute it.

(defthm foo-returns-atom
  (atom (foo))
  :hints (("Goal" :in-theory (disable atom))))

(include-book "std/testing/must-fail" :dir :system)

(must-fail
 (thm (equal (foo) t)))
