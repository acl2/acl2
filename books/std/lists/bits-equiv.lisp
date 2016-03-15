; Standard Typed Lists Library
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
(include-book "list-defuns")
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "centaur/misc/universal-equiv" :dir :system)
(local (include-book "equiv"))
(local (include-book "take"))

(def-universal-equiv bits-equiv
  :qvars (i)
  :equiv-terms ((bit-equiv (nth i x)))
  :parents (bitarr)
  :short "Bit-for-bit list equivalence: @('bits-equiv') recognizes lists whose
  @(see nth) elements are @(see bit-equiv) to one another.  It is often useful
  for reasoning about bit arrays like @(see bitarr).")

(defsection bits-equiv-thms
  :extension (bits-equiv)

  (defcong bits-equiv bit-equiv (nth i x) 2
    :hints(("Goal" :in-theory (e/d (bits-equiv-necc)
                                   (bit-equiv)))))

  (defcong bits-equiv bits-equiv (update-nth i v x) 3
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defcong bit-equiv bits-equiv (update-nth i v x) 2
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defcong bits-equiv bits-equiv (cdr a) 1
    :hints (("goal" :in-theory (disable default-cdr nth))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:use ((:instance bits-equiv-necc
                          (i (+ 1 (nfix (bits-equiv-witness (cdr a) (cdr a-equiv)))))
                          (x a)
                          (y a-equiv)))
                   :in-theory (e/d ()
                                   (bits-equiv-necc
                                    bits-equiv-implies-bit-equiv-nth-2))))))

  (defcong bits-equiv bit-equiv (car x) 1
    :hints (("goal" :use ((:instance bits-equiv-implies-bit-equiv-nth-2
                           (i 0)))
             :in-theory (disable bits-equiv-implies-bit-equiv-nth-2))))

  (defcong bit-equiv bits-equiv (cons a b) 1
    :hints(("Goal" :in-theory (enable bits-equiv)
            :expand ((:free (a b c) (nth a (cons b c)))))))

  (defcong bits-equiv bits-equiv (cons a b) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))
                            (:free (a b c) (nth a (cons b c))))
                   :in-theory (disable bit-equiv))))))


