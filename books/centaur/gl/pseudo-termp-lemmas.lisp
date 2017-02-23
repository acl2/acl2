; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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


(in-package "GL")



(defthm pseudo-termp-car
  (implies (pseudo-term-listp x)
           (pseudo-termp (car x))))

(defthm pseudo-term-listp-cdr
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (cdr x))))

(defthm pseudo-term-listp-cdr-pseudo-term
  (implies (and (pseudo-termp x)
                (consp x)
                (not (equal (car x) 'quote)))
           (pseudo-term-listp (cdr x))))

(defthm pseudo-termp-symbolp-car-x
  (implies (and (pseudo-termp x)
                (not (consp (car x))))
           (symbolp (car x))))

(defthm pseudo-termp-lambda-body
  (implies (and (pseudo-termp x)
                (consp (car x)))
           (pseudo-termp (caddar x))))

(defthm pseudo-termp-car-last-of-pseudo-term-listp
  (implies (pseudo-term-listp x)
           (pseudo-termp (car (last x))))
  :hints(("Goal" :in-theory (enable last))))

(defthm pseudo-termp-car-last
  (implies (and (pseudo-termp x)
                (< 1 (len x))
                (not (equal (car x) 'quote)))
           (pseudo-termp (car (last x))))
  :hints(("Goal" :expand ((pseudo-termp x)))))
