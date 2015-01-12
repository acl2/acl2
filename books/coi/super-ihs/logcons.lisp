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

(include-book "ihs/ihs-lemmas" :dir :system)

(local (include-book "arithmetic"))
(include-book "evenp")

(defthmd open-logcons
  (implies (syntaxp (constant-syntaxp b))
           (equal (logcons b i)
                  (+ (bfix b) (* 2 (ifix i)))))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm equal-logcons-0
  (equal (equal (logcons x y) 0)
         (and (equal (bfix x) 0)
              (equal (ifix y) 0)))
  :hints (("goal" :in-theory (enable logcons
                                     even-odd-different-2
                                     ))))

(defthm evenp-of-logcons
  (equal (evenp (logcons b i))
         (evenp (bfix b)))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm oddp-of-logcons
  (equal (oddp (logcons b i))
         (oddp (bfix b)))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm logcons-of-0
  (equal (logcons 0 x)
         (ash x 1))
  :hints (("Goal" :in-theory (enable logcons ash))))

(defthm floor-of-logcons
  (equal (floor (logcons b i) 2)
         (ifix i)
         )
  :hints (("Goal" :expand  (logcons b i))))