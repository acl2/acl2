;; definline.lisp - The definline and definlined macros.
; Copyright (C) 2005-2009 Kookamara LLC
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
; Original author: Jared Davis <jared@cs.utexas.edu>

(in-package "ACL2")

; Modified 2014-08 by Jared Davis to remove documentation, to try to discourage
; folks from using this.

(defmacro definline (name formals &rest args)
  ;; Alias for @(see defun-inline)
  ;; Examples:
  ;; @({
  ;;   (include-book \"misc/definline\")
  ;;   (definline car-alias (x)
  ;;     (car x))
  ;; })
  ;; @('definline') is a wrapper for @(see defun-inline).

  ;; We probably shouldn't have this wrapper.  But until ACL2 5.0 there was no
  ;; @('defun-inline'), and @('definline') was implemented using a @(see trust-tag).
  ;; When @('defun-inline') was introduced, we already had many books with
  ;; @('definline') and liked the shorter name, so we dropped the trust tag and
  ;; turned it into a wrapper for @('defun-inline').
  `(defun-inline ,name ,formals . ,args))

(defmacro definlined (name formals &rest args)
  ;; Alias for @(see defund-inline)
  ;; This is a @(see defund)-like version of @(see definline).
  `(defund-inline ,name ,formals . ,args))


(local
 (progn

(defun test (x)
  (declare (xargs :guard (natp x)))
  (+ 1 x))

(definline test2 (x)
  (declare (xargs :guard (natp x)))
  (+ 1 x))

(defun f (x) (test x))
(defun g (x) (test2 x))

;; (disassemble$ 'f) ;; not inlined, as expected
;; (disassemble$ 'g) ;; inlined, as expected
  ))
