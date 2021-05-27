; Lemmas about explode-atom
; Copyright (C) 2005-2006 Kookamara LLC
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
; Original author: Jared Davis <jared@kookamara.com>
;
; explode-atom.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "decimal")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "explode-nonnegative-integer"))

(defthm true-listp-of-explode-atom
  (true-listp (explode-atom x base))
  :rule-classes :type-prescription)

(defthm consp-of-explode-atom-when-integerp
  (implies (integerp n)
           (consp (explode-atom n base)))
  :rule-classes :type-prescription)

(defthm equal-of-explode-atoms-when-natps
  (implies (and (natp n)
                (natp m)
                (force (print-base-p base)))
           (equal (equal (explode-atom n base)
                         (explode-atom m base))
                  (equal n m))))

(defthm nonzeroness-of-explode-atom-when-not-zp
  (implies (and (not (zp n))
                (force (print-base-p base)))
           (not (equal (explode-atom n base) '(#\0)))))

(defthm dec-digit-char-listp-of-explode-atom
  (implies (natp n)
           (str::dec-digit-char-listp (explode-atom n 10))))

(defthm character-listp-of-explode-atom
  (character-listp (explode-atom x base))
  :hints(("Goal" :in-theory (disable explode-nonnegative-integer))))

; Copied from std/io/base.lisp, wherein it was added by Matt K. for princ$
; change 12/7/2012.
(defthm character-listp-explode-atom+
  (character-listp (explode-atom+ x base radix)))
