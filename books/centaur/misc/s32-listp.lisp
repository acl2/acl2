; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")


(defun s32-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (signed-byte-p 32 (car x))
         (s32-listp (cdr x)))))

(defthmd nth-in-s32-listp-s32p
  (implies (and (s32-listp gates)
                (< (nfix idx) (len gates)))
           (signed-byte-p 32 (nth idx gates)))
  :hints(("Goal" :in-theory (enable nth))))

(defthmd nth-in-s32-listp-integerp
  (implies (and (s32-listp gates)
                (< (nfix idx) (len gates)))
           (integerp (nth idx gates)))
  :hints(("Goal" :in-theory (enable nth))))

(defthmd nth-in-s32-listp-lower-bound
  (implies (and (s32-listp gates)
                (< (nfix idx) (len gates)))
           (<= (- (expt 2 32)) (nth idx gates)))
  :hints(("Goal" :in-theory (enable nth)))
  :rule-classes :linear)

(defthmd nth-in-s32-listp-upper-bound
  (implies (and (s32-listp gates)
                (< (nfix idx) (len gates)))
           (< (nth idx gates) (expt 2 31)))
  :hints(("Goal" :in-theory (enable nth)))
  :rule-classes :linear)
