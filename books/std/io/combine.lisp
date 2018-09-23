; Standard IO Library
; combine.lisp -- originally part of the Unicode library
; Copyright (C) 2005-2013 Kookamara LLC
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

(in-package "ACL2")
(include-book "centaur/bitops/fast-logext" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(set-verify-guards-eagerness 2)

(local (in-theory (e/d (bitops::signed-byte-p-of-ash-split)
                       (unsigned-byte-p signed-byte-p))))

(defsection combine-functions
  :parents (read-bytes$)
  :short "Optimized byte-combining functions.")


(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))

(local
 (defun logior-ash-loghead-logtail-induction-scheme (size i)
   (declare (xargs :verify-guards nil))
   (if (zp size)
       i
     (logior-ash-loghead-logtail-induction-scheme (- size 1) (logcdr i)))))

(local
 (defthm logior-ash-loghead-logtail
   (implies (and (integerp i) (natp size))
            (equal (logior (ash (logtail size i) size)
                           (loghead size i))
                   i))
   :instructions ((:induct (logior-ash-loghead-logtail-induction-scheme size i))
                  (:dive 2 1 2)
                  (:rewrite loghead*)
                  (:= (logcons (logcar i)
                               (loghead (+ -1 size) (logcdr i))))
                  :top (:dive 2 1 1 1)
                  (:rewrite logtail*)
                  (:= (logtail (+ -1 size) (logcdr i)))
                  :up (:rewrite ash*)
                  (:= (logcons 0
                               (ash (logtail (+ -1 size) (logcdr i))
                                    (+ -1 size))))
                  :top (:dive 2 1)
                  (:rewrite logior*)
                  :top (:dive 2 1 1 1)
                  (:rewrite logcar-logcons)
                  :nx (:rewrite logcar-logcons)
                  :top (:dive 2 1 2 1)
                  (:rewrite logcdr-logcons)
                  :nx (:rewrite logcdr-logcons)
                  :up :top :promote (:demote 2)
                  (:dive 1 1)
                  :s :up :s-prop :top :promote (:dive 1 2)
                  := (:drop 4)
                  :top (:dive 1 1)
                  (:rewrite simplify-bit-functions)
                  (:rewrite bfix-bitp)
                  :up (:rewrite logcar-logcdr-elim)
                  :top :bash :promote (:dive 1 2)
                  (:rewrite loghead*)
                  (:= 0)
                  :top (:dive 1 1 1)
                  (:rewrite logtail*)
                  (:= i)
                  :up (:rewrite ash*)
                  (:= i)
                  :up :s
                  :top :bash)))

(local
 (defthm
   logior-of-ash
   (implies (and (integerp i1)
                 (integerp i2)
                 (natp c))
            (equal (logior (ash i1 c) (ash i2 c))
                   (ash (logior i1 i2) c)))
   :instructions ((:in-theory (disable logior ash logcons logcar logcdr))
                  (:induct (dec-induct c))
                  :promote (:demote 2)
                  (:dive 1)
                  :s :top :promote (:dive 1 1)
                  (:rewrite ash*)
                  :s :nx (:rewrite ash*)
                  :s :up (:rewrite logior*)
                  :s :nx (:rewrite ash*)
                  :s :top :bash :promote (:= c 0)
                  (:drop 1 4)
                  (:dive 1 1)
                  (:rewrite ash*)
                  :s :nx (:rewrite ash*)
                  :s :top (:dive 2)
                  (:rewrite ash*)
                  :s
                  :top :bash)))

(defsection combine16u
  :parents (combine-functions)
  :short "@(call combine16u) merges unsigned bytes, producing the 16-bit
unsigned interpretation of @('(a1 << 8) | a0')."

  (defund-inline combine16u (a1 a0)
    (declare (type (unsigned-byte 8) a1 a0))
    (mbe :logic
         (logior (ash (nfix a1) 8)
                 (nfix a0))
         :exec
         (the (unsigned-byte 16)
           (logior (ash a1 8) a0))))

  (local (in-theory (enable combine16u)))

  (defthm combine16u-unsigned-byte
    (implies (and (force (unsigned-byte-p 8 a1))
                  (force (unsigned-byte-p 8 a0)))
             (unsigned-byte-p 16 (combine16u a1 a0))))

  (defthm combine16u-loghead-logtail
    (implies (natp i)
             (equal (combine16u (logtail 8 i) (loghead 8 i))
                    i))
    :hints (("Goal" :in-theory (disable loghead logtail logior ash)))))



(defsection combine16s
  :parents (combine-functions)
  :short "@(call combine16s) merges unsigned bytes, producing the 16-bit signed
interpretation of @('(a1 << 8) | a0')."

  (defund-inline combine16s (a1 a0)
    (declare (type (unsigned-byte 8) a1 a0))
    (mbe :logic
         (logior (ash (fast-logext 8 (nfix a1)) 8)
                 (nfix a0))
         :exec
         (the (signed-byte 16)
           (logior (the (signed-byte 16)
                     (ash (the (signed-byte 8)
                            (fast-logext 8 a1))
                          8))
                   a0))))

  (local (in-theory (enable combine16s)))

  (defthm combine16s-signed-byte
    (implies (and (force (unsigned-byte-p 8 a1))
                  (force (unsigned-byte-p 8 a0)))
             (signed-byte-p 16 (combine16s a1 a0)))))



(defsection combine32u
  :parents (combine-functions)
  :short "@(call combine32u) merges unsigned bytes, producing the 32-bit
unsigned interpretation of @('(a3 << 24) | (a2 << 16) | (a1 << 8) | a0')."

  (defund-inline combine32u (a3 a2 a1 a0)
    (declare (type (unsigned-byte 8) a3 a2 a1 a0))
    (mbe :logic
         (logior (ash (nfix a3) 24)
                 (ash (nfix a2) 16)
                 (ash (nfix a1) 8)
                 (nfix a0))
         :exec
         ;; Ugly series of LOGIORs because CCL won't optimize multi-arg LOGIORs
         ;; into fixnum computations...
         (b* ((a3  (the (unsigned-byte 32) (ash a3 24)))
              (a2  (the (unsigned-byte 24) (ash a2 16)))
              (a1  (the (unsigned-byte 16) (ash a1 8)))
              (ans (the (unsigned-byte 16)
                     (logior (the (unsigned-byte 16) a1)
                             (the (unsigned-byte 8) a0))))
              (ans (the (unsigned-byte 24)
                     (logior (the (unsigned-byte 24) a2)
                             (the (unsigned-byte 16) ans)))))
           (the (unsigned-byte 32)
             (logior (the (unsigned-byte 32) a3)
                     (the (unsigned-byte 24) ans))))))

  (local (in-theory (enable combine32u)))

  (defthm combine32u-unsigned-byte
    (implies (and (force (unsigned-byte-p 8 a3))
                  (force (unsigned-byte-p 8 a2))
                  (force (unsigned-byte-p 8 a1))
                  (force (unsigned-byte-p 8 a0)))
             (unsigned-byte-p 32 (combine32u a3 a2 a1 a0))))

  (defthm combine32u-loghead-logtail
    (implies (natp i)
             (equal (combine32u (logtail 24 i)
                                (loghead 8 (logtail 16 i))
                                (loghead 8 (logtail 8 i))
                                (loghead 8 i))
                    i))
    :instructions
    (:promote (:dive 1)
              :expand (:dive 2 2)
              (:dive 2)
              (:= (loghead 8 (loghead 16 i)))
              :up (:dive 1 1)
              (:= (logtail 8 (loghead 16 i)))
              :up :up
              (:rewrite logior-ash-loghead-logtail)
              :top (:dive 1)
              (:= (logior (logior (ash (nfix (logtail 24 i)) 24)
                                  (ash (nfix (loghead 8 (logtail 16 i)))
                                       16))
                          (loghead 16 i)))
              (:dive 1 1)
              (:= (ash (ash (logtail 24 i) 8) 16))
              :up (:rewrite logior-of-ash)
              (:dive 1 2)
              :s :up (:dive 1 1)
              (:= (logtail 8 (logtail 16 i)))
              :up :up
              (:rewrite logior-ash-loghead-logtail)
              :up
              :up (:rewrite logior-ash-loghead-logtail)
              :top :bash)))



(defsection combine32s
  :parents (combine-functions)
  :short "@(call combine32s) merges unsigned bytes, producing the 32-bit
signed interpretation of @('(a3 << 24) | (a2 << 16) | (a1 << 8) | a0')."

  (defund-inline combine32s (a3 a2 a1 a0)
    (declare (type (unsigned-byte 8) a3 a2 a1 a0))
    (mbe :logic
         (logior (ash (fast-logext 8 (nfix a3)) 24)
                 (ash (nfix a2) 16)
                 (ash (nfix a1) 8)
                 (nfix a0))
         :exec
         ;; Ugly series of LOGIORs because CCL won't optimize multi-arg LOGIORs
         ;; into fixnum computations...
         (b* ((a3  (the (signed-byte 32)
                     (ash (the (signed-byte 8) (fast-logext 8 a3))
                          24)))
              (a2  (the (unsigned-byte 24) (ash a2 16)))
              (a1  (the (unsigned-byte 16) (ash a1 8)))
              (ans (the (unsigned-byte 16)
                     (logior (the (unsigned-byte 16) a1)
                             (the (unsigned-byte 8) a0))))
              (ans (the (unsigned-byte 24)
                     (logior (the (unsigned-byte 24) a2)
                             (the (unsigned-byte 16) ans)))))
           (the (signed-byte 32)
             (logior (the (signed-byte 32) a3)
                     (the (signed-byte 32) ans))))))

  (local (in-theory (enable combine32s)))

  (defthm combine32s-signed-byte
    (implies (and (force (unsigned-byte-p 8 a3))
                  (force (unsigned-byte-p 8 a2))
                  (force (unsigned-byte-p 8 a1))
                  (force (unsigned-byte-p 8 a0)))
             (signed-byte-p 32 (combine32s a3 a2 a1 a0)))))


(defsection combine64u
  :parents (combine-functions)
  :short "@(call combine64u) merges unsigned bytes, producing the 64-bit
unsigned interpretation of @('{a7, a6, a5, a4, a3, a2, a1, a0}')."

  (defund-inline combine64u (a7 a6 a5 a4 a3 a2 a1 a0)
    (declare (type (unsigned-byte 8) a7 a6 a5 a4 a3 a2 a1 a0))
    (mbe :logic
         (logior (ash (nfix a7) 56)
                 (ash (nfix a6) 48)
                 (ash (nfix a5) 40)
                 (ash (nfix a4) 32)
                 (ash (nfix a3) 24)
                 (ash (nfix a2) 16)
                 (ash (nfix a1) 8)
                 (nfix a0))
         :exec
         (b* ((a1 (the (unsigned-byte 16) (ash a1 8)))
              ;; Ugly series of LOGIORs because CCL won't optimize multi-arg
              ;; LOGIORs into fixnum computations...
              (ans (the (unsigned-byte 16)
                     (logior (the (unsigned-byte 16) a1)
                             (the (unsigned-byte 16) a0))))
              (a2 (the (unsigned-byte 24) (ash a2 16)))
              (ans (the (unsigned-byte 24)
                     (logior (the (unsigned-byte 24) a2)
                             (the (unsigned-byte 24) ans))))
              (a3 (the (unsigned-byte 32) (ash a3 24)))
              (ans (the (unsigned-byte 32)
                     (logior (the (unsigned-byte 32) a3)
                             (the (unsigned-byte 32) ans))))
              (a4 (the (unsigned-byte 40) (ash a4 32)))
              (ans (the (unsigned-byte 40)
                     (logior (the (unsigned-byte 40) a4)
                             (the (unsigned-byte 40) ans))))
              (a5 (the (unsigned-byte 48) (ash a5 40)))
              (ans (the (unsigned-byte 48)
                     (logior (the (unsigned-byte 48) a5)
                             (the (unsigned-byte 48) ans))))
              (a6 (the (unsigned-byte 56) (ash a6 48)))
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a6)
                             (the (unsigned-byte 56) ans))))
              ;; Can't really do better here... :(
              (a7 (the (unsigned-byte 64) (ash a7 56))))
           (the (unsigned-byte 64)
             (logior (the (unsigned-byte 64) a7)
                     (the (unsigned-byte 56) ans))))))

  (local (in-theory (enable combine64u)))

  (defthm combine64u-unsigned-byte
    (implies (and (force (unsigned-byte-p 8 a7))
                  (force (unsigned-byte-p 8 a6))
                  (force (unsigned-byte-p 8 a5))
                  (force (unsigned-byte-p 8 a4))
                  (force (unsigned-byte-p 8 a3))
                  (force (unsigned-byte-p 8 a2))
                  (force (unsigned-byte-p 8 a1))
                  (force (unsigned-byte-p 8 a0)))
             (unsigned-byte-p 64 (combine64u a7 a6 a5 a4 a3 a2 a1 a0)))))



(defsection combine64s
  :parents (combine-functions)
  :short "@(call combine64s) merges unsigned bytes, producing the 64-bit
unsigned interpretation of @('{a7, a6, a5, a4, a3, a2, a1, a0}')."

  (defund-inline combine64s (a7 a6 a5 a4 a3 a2 a1 a0)
    (declare (type (unsigned-byte 8) a7 a6 a5 a4 a3 a2 a1 a0))
    (mbe :logic
         (logior (ash (fast-logext 8 (nfix a7)) 56)
                 (ash (nfix a6) 48)
                 (ash (nfix a5) 40)
                 (ash (nfix a4) 32)
                 (ash (nfix a3) 24)
                 (ash (nfix a2) 16)
                 (ash (nfix a1) 8)
                 (nfix a0))
         :exec
         (b* ((a1 (the (unsigned-byte 16) (ash a1 8)))
              ;; Ugly series of LOGIORs because CCL won't optimize multi-arg
              ;; LOGIORs into fixnum computations...
              (ans (the (unsigned-byte 16)
                     (logior (the (unsigned-byte 16) a1)
                             (the (unsigned-byte 16) a0))))
              (a2 (the (unsigned-byte 24) (ash a2 16)))
              (ans (the (unsigned-byte 24)
                     (logior (the (unsigned-byte 24) a2)
                             (the (unsigned-byte 24) ans))))
              (a3 (the (unsigned-byte 32) (ash a3 24)))
              (ans (the (unsigned-byte 32)
                     (logior (the (unsigned-byte 32) a3)
                             (the (unsigned-byte 32) ans))))
              (a4 (the (unsigned-byte 40) (ash a4 32)))
              (ans (the (unsigned-byte 40)
                     (logior (the (unsigned-byte 40) a4)
                             (the (unsigned-byte 40) ans))))
              (a5 (the (unsigned-byte 48) (ash a5 40)))
              (ans (the (unsigned-byte 48)
                     (logior (the (unsigned-byte 48) a5)
                             (the (unsigned-byte 48) ans))))
              (a6 (the (unsigned-byte 56) (ash a6 48)))
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a6)
                             (the (unsigned-byte 56) ans))))
              ;; Can't really do better here... :(
              (a7 (the (signed-byte 64)
                    (ash (the (signed-byte 8) (fast-logext 8 a7))
                         56))))
           (the (signed-byte 64)
             (logior (the (signed-byte 64) a7)
                     (the (unsigned-byte 56) ans))))))

  (local (in-theory (enable combine64s)))

  (defthm combine64s-unsigned-byte
    (implies (and (force (unsigned-byte-p 8 a7))
                  (force (unsigned-byte-p 8 a6))
                  (force (unsigned-byte-p 8 a5))
                  (force (unsigned-byte-p 8 a4))
                  (force (unsigned-byte-p 8 a3))
                  (force (unsigned-byte-p 8 a2))
                  (force (unsigned-byte-p 8 a1))
                  (force (unsigned-byte-p 8 a0)))
             (signed-byte-p 64 (combine64s a7 a6 a5 a4 a3 a2 a1 a0)))))
