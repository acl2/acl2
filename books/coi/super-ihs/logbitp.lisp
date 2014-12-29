; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

(in-package "ACL2")

;bzo many of the rules below suggest analogous logbit rules.  Someone should
;try to add those rules to logbit.lisp.  And vice-versa!

(include-book "ihs/ihs-lemmas" :dir :system)
(local (include-book "arithmetic"))
;(include-book "ash")

(in-theory (disable logbitp))

(defthm logbitp-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logbitp i j)
                  nil))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbitp-when-j-is-zero
  (equal (logbitp i 0)
         nil)
  :hints (("goal" :in-theory (enable logbitp ifix))))

(defthm logbitp-when-i-is-zero
  (equal (logbitp 0 j)
         (equal (logcar j) 1))
  :hints (("goal" :in-theory (enable logbit logbitp))))

;further simplify the RHS?
(defthm logbitp-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logbitp i j)
                  (logbitp 0 j)))
  :hints (("Goal" :in-theory (enable logbitp
                                     ;oddp-rewrite-to-logcar-fact
                                     ))))

(defthm logbitp-when-i-is-non-positive
  (implies (<= i 0)
           (equal (logbitp i j)
                  (not (equal 0 (logcar j)))))
  :hints (("Goal" :in-theory (enable logbitp)
           :do-not '(generalize eliminate-destructors)
           )))

(defthm logbitp-0-minus-1-better-1
  (equal (logbitp pos 0)
         nil)
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbitp-0-minus-1-better-2
  (equal (logbitp pos -1)
         t)
  :hints (("Goal" :in-theory (enable logbitp))))

(in-theory (disable LOGBITP-0-MINUS-1))


;rule for logbit?
(defthm logbitp-of-one
  (equal (logbitp pos 1)
         (zp pos))
  :hints (("Goal" :cases ((zp pos))
           :in-theory (enable logbitp))))

;bzo gen
(defthm logbitp-of-expt-hack
  (implies (and (integerp size) (<= 0 size))
           (logbitp size (expt 2 size)))
  :hints (("Goal" :in-theory (enable logbitp))))