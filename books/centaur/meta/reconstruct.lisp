; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
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

(in-package "CMR")

(include-book "clause-processors/pseudo-term-fty" :dir :system)

(define pseudo-term-fncall-with-hint ((fn pseudo-fnsym-p)
                                      (args pseudo-term-listp)
                                      (hint))
  :returns (x (equal x (pseudo-term-fncall fn args))
              :hints(("Goal" :in-theory (enable pseudo-term-fncall))))
  (cons-with-hint (pseudo-fnsym-fix fn)
                  (pseudo-term-list-fix args)
                  hint))

(define pseudo-term-lambda-with-hint ((formals symbol-listp)
                                      (body pseudo-termp)
                                      (args pseudo-term-listp)
                                      (hint pseudo-termp))
  :guard (and (equal (len formals) (len args))
              (pseudo-term-case hint :lambda))
  :returns (x (equal x (pseudo-term-lambda formals body args))
              :hints(("Goal" :in-theory (enable pseudo-term-lambda))))
  :guard-hints (("goal" :use ((:instance (:guard-theorem pseudo-term-lambda)
                               (formals formals) (body body) (args args))))
                (and stable-under-simplificationp
                     '(:in-theory (e/d (pseudo-term-kind)))))
  (mbe :logic (cons (pseudo-lambda formals body)
                    (remove-corresp-non-symbols formals (pseudo-term-list-fix args)))
       :exec
       (cons-with-hint (cons-with-hint 'lambda
                                       (cons-with-hint formals
                                                       (cons-with-hint body nil (cddar hint))
                                                       (cdar hint))
                                       (car hint))
                       args
                       hint)))
