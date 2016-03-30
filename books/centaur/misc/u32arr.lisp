; Centaur Miscellaneous Books
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
(include-book "std/stobjs/1d-arr" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(defsection u32p
  :parents (u32arr)
  :short "Recognizer for 32-bit unsigned integers."

  (defun u32p (x)
    (declare (xargs :guard t))
    (unsigned-byte-p 32 x)))

(local (defthm u32p-natp
         (implies (u32p x)
                  (natp x))))

(local (defthm u32p-bound
         (implies (u32p x)
                  (< x 4294967296))))

(local (in-theory (disable u32p)))

(def-1d-arr u32arr
  :slotname u32
  :pred u32p
  :fix nfix
  :type-decl (unsigned-byte 32)
  :default-val 0)

;; (defun-inline set-u32n (i v u32arr)
;;   (declare (xargs :stobjs u32arr
;;                   :guard (and (natp i)
;;                               (< i (u32s-length u32arr))
;;                               (natp v))))
;;   (mbe :logic (set-u32 i v u32arr)
;;        :exec (if (< (the (integer 0 *) v) (expt 2 32))
;;                  (set-u32 i v u32arr)
;;                (ec-call (set-u32 i v u32arr)))))

