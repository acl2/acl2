;
; Memories: Array-like Records for ACL2
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


; log2.lisp - implementation of log base 2 function
;
; This is an implementation file and should not be directly included in
; external work.  Use the interface file (memtree.lisp) instead!
;
; Unfortunately, ACL2 doesn't have a built in base-2 log function, so we need
; to write our own.  There are far more efficient implementations than this
; simple definition available, but I think that this is nice as far as
; reasoning goes and one should realize that for our purposes, log2 will rarely
; be called (only when new memories are being created), so the inefficiency
; here is unlikely to pose a problem.

(in-package "MEM")
(set-verify-guards-eagerness 2)

(local (include-book "arithmetic-3/bind-free/top" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(set-default-hints '((ACL2::nonlinearp-default-hint
                      ACL2::stable-under-simplificationp
                      ACL2::hist
                      ACL2::pspv)))

(defun _log2-tr (n acc)
  (declare (xargs :guard (and (natp n)
                              (natp acc))))
  (if (zp n)
      acc
    (_log2-tr (mbe :logic (floor n 2)
                   :exec (ash n -1))
              (1+ acc))))

(defun _log2 (n)
  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (mbe :logic (if (zp n)
                  0
                (1+ (_log2 (floor n 2))))
       :exec (_log2-tr n 0)))

(defthm _log2-equiv
  (implies (and (natp n)
                (natp acc))
           (equal (_log2-tr n acc)
                  (+ (_log2 n) acc))))

(verify-guards _log2)



(defthm _log2-natural
  (and (integerp (_log2 n))
       (<= 0 (_log2 n)))
  :rule-classes :type-prescription)

(defthm _log2-positive
  (implies (and (integerp n)
                (< 0 n))
           (and (integerp (_log2 n))
                (< 0 (_log2 n))))
  :rule-classes :type-prescription)

(defthm _log2-expt-nat
  (implies (natp n)
           (< n (expt 2 (_log2 n))))
  :rule-classes :linear)

(defthm _log2-expt-pos
  (implies (posp n)
           (<= n (expt 2 (_log2 (1- n)))))
  :rule-classes :linear)

(encapsulate
 nil

 (local (defun my-induction (i j)
          (declare (xargs :guard (and (natp i)
                                      (natp j))))
          (if (or (zp i)
                  (zp j))
              nil
            (list (my-induction (floor i 2)
                                (floor j 2))))))

 (defthm _log2-monotonic
   (implies (and (natp i)
                 (natp j)
                 (<= i j))
            (<= (_log2 i) (_log2 j)))
   :rule-classes :linear
   :hints(("Goal" :induct (my-induction i j))))
)
