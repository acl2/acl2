; Standard IO Library
; read-ints.lisp -- originally part of the Unicode library
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
(include-book "base")
(include-book "combine")
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(set-verify-guards-eagerness 2)
(set-state-ok t)

(local (defthm rationalp-when-integerp
         (implies (integerp x)
                  (rationalp x))))

#+non-standard-analysis
(local
 (defthm integer-to-real
   (implies (integerp x)
	    (realp x))))

(local (defthm unsigned-byte-p-of-read-byte$
         (implies (and (state-p1 state)
                       (open-input-channel-p1 channel :byte state))
                  (b* (((mv x1 ?state) (read-byte$ channel state)))
                    (iff (unsigned-byte-p 8 x1)
                         x1)))))

(local (defthm read-byte$-returns-plenty-of-nils-after-eof
         (implies (and (state-p1 state)
                       (open-input-channel-p1 channel :byte state))
                  (b* (((mv x1 state) (read-byte$ channel state))
                       ((mv x2 ?state) (read-byte$ channel state)))
                    (implies x2 x1)))))

;; There's no read-8u since that's just read-byte$.


(defsection read-8s
  :parents (read-bytes$)
  :short "@(call read-8s) reads a signed byte from the input channel."

  (defund read-8s (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv byte state) (read-byte$ channel state))
         ((unless byte)
          (mv nil state)))
      (mv (fast-logext 8 byte) state)))

  (local (in-theory (enable read-8s)))

  (defthm read-8s-signed-byte
    (implies (and (mv-nth 0 (read-8s channel state))
                  (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (signed-byte-p 8 (mv-nth 0 (read-8s channel state)))))

  (defthm read-8s-integer
    (implies (mv-nth 0 (read-8s channel state))
             (integerp (mv-nth 0 (read-8s channel state)))))

  (defthm read-8s-range
    (implies (and (mv-nth 0 (read-8s channel state))
                  (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (and (<= -128 (mv-nth 0 (read-8s channel state)))
                  (<= (- (expt 2 7)) (mv-nth 0 (read-8s channel state)))
                  (< (mv-nth 0 (read-8s channel state)) 128)
                  (< (mv-nth 0 (read-8s channel state)) (expt 2 7))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable signed-byte-p)
            :use (:instance read-8s-signed-byte))))

  (defthm read-8s-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-8s channel state)))))

  (defthm read-8s-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-8s channel state))))))


(defsection read-16ube
  :parents (read-bytes$)
  :short "@(call read-16ube) reads a 16-bit, unsigned, big-endian value from
the input channel."

  (defund read-16ube (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x2)
          (mv 'fail state)))
      (mv (combine16u x1 x2) state)))

  (local (in-theory (enable read-16ube)))

  (defthm read-16ube-unsigned-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-16ube channel state))
                  (not (equal (mv-nth 0 (read-16ube channel state)) 'fail)))
             (unsigned-byte-p 16 (mv-nth 0 (read-16ube channel state)))))

  (defthm read-16ube-integer
    (implies (and (mv-nth 0 (read-16ube channel state))
                  (not (equal (mv-nth 0 (read-16ube channel state)) 'fail)))
             (integerp (mv-nth 0 (read-16ube channel state)))))

  (defthm read-16ube-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-16ube channel state))
                  (not (equal (mv-nth 0 (read-16ube channel state)) 'fail)))
             (and (<= 0 (mv-nth 0 (read-16ube channel state)))
                  (< (mv-nth 0 (read-16ube channel state)) 65536)
                  (< (mv-nth 0 (read-16ube channel state)) (expt 2 16))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable unsigned-byte-p)
            :use (:instance read-16ube-unsigned-byte))))

  (defthm read-16ube-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-16ube channel state)))))

  (defthm read-16ube-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-16ube channel state))))))


(defsection read-16ule
  :parents (read-bytes$)
  :short "@(call read-16ule) reads a 16-bit, unsigned, little-endian value
from the input channel."

  (defund read-16ule (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x2)
          (mv 'fail state)))
      (mv (combine16u x2 x1) state)))

  (local (in-theory (enable read-16ule)))

  (defthm read-16ule-unsigned-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-16ule channel state))
                  (not (equal (mv-nth 0 (read-16ule channel state)) 'fail)))
             (unsigned-byte-p 16 (mv-nth 0 (read-16ule channel state)))))

  (defthm read-16ule-integer
    (implies (and (mv-nth 0 (read-16ule channel state))
                  (not (equal (mv-nth 0 (read-16ule channel state)) 'fail)))
             (integerp (mv-nth 0 (read-16ule channel state)))))

  (defthm read-16ule-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-16ule channel state))
                  (not (equal (mv-nth 0 (read-16ule channel state)) 'fail)))
             (and (<= 0 (mv-nth 0 (read-16ule channel state)))
                  (< (mv-nth 0 (read-16ule channel state)) 65536)
                  (< (mv-nth 0 (read-16ule channel state)) (expt 2 16))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable unsigned-byte-p)
            :use (:instance read-16ule-unsigned-byte))))

  (defthm read-16ule-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-16ule channel state)))))

  (defthm read-16ule-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-16ule channel state))))))


(defsection read-16sbe
  :parents (read-bytes$)
  :short "@(call read-16sbe) reads a 16-bit, signed, big-endian value from the
input channel."

  (defund read-16sbe (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x2)
          (mv 'fail state)))
      (mv (combine16s x1 x2) state)))

  (local (in-theory (enable read-16sbe)))

  (defthm read-16sbe-signed-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-16sbe channel state))
                  (not (equal (mv-nth 0 (read-16sbe channel state)) 'fail)))
             (signed-byte-p 16 (mv-nth 0 (read-16sbe channel state)))))

  (defthm read-16sbe-integer
    (implies (and (mv-nth 0 (read-16sbe channel state))
                  (not (equal (mv-nth 0 (read-16sbe channel state)) 'fail)))
             (integerp (mv-nth 0 (read-16sbe channel state)))))

  (defthm read-16sbe-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-16sbe channel state))
                  (not (equal (mv-nth 0 (read-16sbe channel state)) 'fail)))
             (and (<= -32768 (mv-nth 0 (read-16sbe channel state)))
                  (<= (- (expt 2 15)) (mv-nth 0 (read-16sbe channel state)))
                  (< (mv-nth 0 (read-16sbe channel state)) 32768)
                  (< (mv-nth 0 (read-16sbe channel state)) (expt 2 15))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable signed-byte-p)
            :use (:instance read-16sbe-signed-byte))))

  (defthm read-16sbe-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-16sbe channel state)))))

  (defthm read-16sbe-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-16sbe channel state))))))


(defsection read-16sle
  :parents (read-bytes$)
  :short "@(call read-16sle) reads a 16-bit, signed, little-endian value from
the input channel."

  (defund read-16sle (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x2)
          (mv 'fail state)))
      (mv (combine16s x2 x1) state)))

  (local (in-theory (enable read-16sle)))

  (defthm read-16sle-signed-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-16sle channel state))
                  (not (equal (mv-nth 0 (read-16sle channel state)) 'fail)))
             (signed-byte-p 16 (mv-nth 0 (read-16sle channel state)))))

  (defthm read-16sle-integer
    (implies (and (mv-nth 0 (read-16sle channel state))
                  (not (equal (mv-nth 0 (read-16sle channel state)) 'fail)))
             (integerp (mv-nth 0 (read-16sle channel state)))))

  (defthm read-16sle-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-16sle channel state))
                  (not (equal (mv-nth 0 (read-16sle channel state)) 'fail)))
             (and (<= -32768 (mv-nth 0 (read-16sle channel state)))
                  (<= (- (expt 2 15)) (mv-nth 0 (read-16sle channel state)))
                  (< (mv-nth 0 (read-16sle channel state)) 32768)
                  (< (mv-nth 0 (read-16sle channel state)) (expt 2 15))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable signed-byte-p)
            :use (:instance read-16sle-signed-byte))))

  (defthm read-16sle-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-16sle channel state)))))

  (defthm read-16sle-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-16sle channel state))))))



(defsection read-32ube
  :parents (read-bytes$)
  :short "@(call read-32ube) reads a 32-bit, unsigned, big-endian value from
the input channel."

  (defund read-32ube (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((mv x3 state) (read-byte$ channel state))
         ((mv x4 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x4)
          (mv 'fail state)))
      (mv (combine32u x1 x2 x3 x4) state)))

  (local (in-theory (enable read-32ube)))

  (defthm read-32ube-unsigned-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32ube channel state))
                  (not (equal (mv-nth 0 (read-32ube channel state)) 'fail)))
             (unsigned-byte-p 32 (mv-nth 0 (read-32ube channel state)))))

  (defthm read-32ube-integer
    (implies (and (mv-nth 0 (read-32ube channel state))
                  (not (equal (mv-nth 0 (read-32ube channel state)) 'fail)))
             (integerp (mv-nth 0 (read-32ube channel state)))))

  (defthm read-32ube-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32ube channel state))
                  (not (equal (mv-nth 0 (read-32ube channel state)) 'fail)))
             (and (<= 0 (mv-nth 0 (read-32ube channel state)))
                  (< (mv-nth 0 (read-32ube channel state)) 4294967296)
                  (< (mv-nth 0 (read-32ube channel state)) (expt 2 32))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable unsigned-byte-p)
            :use (:instance read-32ube-unsigned-byte))))

  (defthm read-32ube-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-32ube channel state)))))

  (defthm read-32ube-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-32ube channel state))))))



(defsection read-32ule
  :parents (read-bytes$)
  :short "@(call read-32ule) reads a 32-bit, unsigned, little-endian value
from the input channel."

  (defund read-32ule (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((mv x3 state) (read-byte$ channel state))
         ((mv x4 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x4)
          (mv 'fail state)))
      (mv (combine32u x4 x3 x2 x1) state)))

  (local (in-theory (enable read-32ule)))

  (defthm read-32ule-unsigned-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32ule channel state))
                  (not (equal (mv-nth 0 (read-32ule channel state)) 'fail)))
             (unsigned-byte-p 32 (mv-nth 0 (read-32ule channel state)))))

  (defthm read-32ule-integer
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32ule channel state))
                  (not (equal (mv-nth 0 (read-32ule channel state)) 'fail)))
             (integerp (mv-nth 0 (read-32ule channel state)))))

  (defthm read-32ule-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32ule channel state))
                  (not (equal (mv-nth 0 (read-32ule channel state)) 'fail)))
             (and (<= 0 (mv-nth 0 (read-32ule channel state)))
                  (< (mv-nth 0 (read-32ule channel state)) 4294967296)
                  (< (mv-nth 0 (read-32ule channel state)) (expt 2 32))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable unsigned-byte-p)
            :use (:instance read-32ule-unsigned-byte))))

  (defthm read-32ule-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-32ule channel state)))))

  (defthm read-32ule-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-32ule channel state))))))


(defsection read-32sbe
  :parents (read-bytes$)
  :short "@(call read-32sbe) reads a 32-bit, signed, big-endian value from the
input channel."

  (defund read-32sbe (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((mv x3 state) (read-byte$ channel state))
         ((mv x4 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x4)
          (mv 'fail state)))
      (mv (combine32s x1 x2 x3 x4) state)))

  (local (in-theory (enable read-32sbe)))

  (defthm read-32sbe-signed-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32sbe channel state))
                  (not (equal (mv-nth 0 (read-32sbe channel state)) 'fail)))
             (signed-byte-p 32 (mv-nth 0 (read-32sbe channel state)))))

  (defthm read-32sbe-integer
    (implies (and (mv-nth 0 (read-32sbe channel state))
                  (not (equal (mv-nth 0 (read-32sbe channel state)) 'fail)))
             (integerp (mv-nth 0 (read-32sbe channel state)))))

  (defthm read-32sbe-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32sbe channel state))
                  (not (equal (mv-nth 0 (read-32sbe channel state)) 'fail)))
             (and (<= -2147483648 (mv-nth 0 (read-32sbe channel state)))
                  (<= (- (expt 2 31)) (mv-nth 0 (read-32sbe channel state)))
                  (< (mv-nth 0 (read-32sbe channel state)) 2147483648)
                  (< (mv-nth 0 (read-32sbe channel state)) (expt 2 31))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable signed-byte-p)
            :use (:instance read-32sbe-signed-byte))))

  (defthm read-32sbe-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-32sbe channel state)))))

  (defthm read-32sbe-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-32sbe channel state))))))


(defsection read-32sle
  :parents (read-bytes$)
  :short "@(call read-32sle) reads a 32-bit, signed, little-endian value from
the input channel."

  (defund read-32sle (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((mv x3 state) (read-byte$ channel state))
         ((mv x4 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x4)
          (mv 'fail state)))
      (mv (combine32s x4 x3 x2 x1) state)))

  (local (in-theory (enable read-32sle)))

  (defthm read-32sle-signed-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32sle channel state))
                  (not (equal (mv-nth 0 (read-32sle channel state)) 'fail)))
             (signed-byte-p 32 (mv-nth 0 (read-32sle channel state)))))

  (defthm read-32sle-integer
    (implies (and (mv-nth 0 (read-32sle channel state))
                  (not (equal (mv-nth 0 (read-32sle channel state)) 'fail)))
             (integerp (mv-nth 0 (read-32sle channel state)))))

  (defthm read-32sle-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-32sle channel state))
                  (not (equal (mv-nth 0 (read-32sle channel state)) 'fail)))
             (and (<= -2147483648 (mv-nth 0 (read-32sle channel state)))
                  (<= (- (expt 2 31)) (mv-nth 0 (read-32sle channel state)))
                  (< (mv-nth 0 (read-32sle channel state)) 2147483648)
                  (< (mv-nth 0 (read-32sle channel state)) (expt 2 31))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable signed-byte-p)
            :use (:instance read-32sle-signed-byte))))

  (defthm read-32sle-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-32sle channel state)))))

  (defthm read-32sle-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-32sle channel state))))))



(defsection read-64ube
  :parents (read-bytes$)
  :short "@(call read-64ube) reads a 64-bit, unsigned, big-endian value from
the input channel."

  (defund read-64ube (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((mv x3 state) (read-byte$ channel state))
         ((mv x4 state) (read-byte$ channel state))
         ((mv x5 state) (read-byte$ channel state))
         ((mv x6 state) (read-byte$ channel state))
         ((mv x7 state) (read-byte$ channel state))
         ((mv x8 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x8)
          (mv 'fail state)))
      (mv (combine64u x1 x2 x3 x4 x5 x6 x7 x8) state)))

  (local (in-theory (enable read-64ube)))

  (defthm read-64ube-unsigned-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-64ube channel state))
                  (not (equal (mv-nth 0 (read-64ube channel state)) 'fail)))
             (unsigned-byte-p 64 (mv-nth 0 (read-64ube channel state)))))

  (defthm read-64ube-integer
    (implies (and (mv-nth 0 (read-64ube channel state))
                  (not (equal (mv-nth 0 (read-64ube channel state)) 'fail)))
             (integerp (mv-nth 0 (read-64ube channel state)))))

  (defthm read-64ube-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-64ube channel state))
                  (not (equal (mv-nth 0 (read-64ube channel state)) 'fail)))
             (and (<= 0 (mv-nth 0 (read-64ube channel state)))
                  (< (mv-nth 0 (read-64ube channel state)) 18446744073709551616)
                  (< (mv-nth 0 (read-64ube channel state)) (expt 2 64))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable unsigned-byte-p)
            :use (:instance read-64ube-unsigned-byte))))

  (defthm read-64ube-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-64ube channel state)))))

  (defthm read-64ube-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-64ube channel state))))))



(defsection read-64ule
  :parents (read-bytes$)
  :short "@(call read-64ule) reads a 64-bit, unsigned, little-endian value from
the input channel."

  (defund read-64ule (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((mv x3 state) (read-byte$ channel state))
         ((mv x4 state) (read-byte$ channel state))
         ((mv x5 state) (read-byte$ channel state))
         ((mv x6 state) (read-byte$ channel state))
         ((mv x7 state) (read-byte$ channel state))
         ((mv x8 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x8)
          (mv 'fail state)))
      (mv (combine64u x8 x7 x6 x5 x4 x3 x2 x1) state)))

  (local (in-theory (enable read-64ule)))

  (defthm read-64ule-unsigned-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-64ule channel state))
                  (not (equal (mv-nth 0 (read-64ule channel state)) 'fail)))
             (unsigned-byte-p 64 (mv-nth 0 (read-64ule channel state)))))

  (defthm read-64ule-integer
    (implies (and (mv-nth 0 (read-64ule channel state))
                  (not (equal (mv-nth 0 (read-64ule channel state)) 'fail)))
             (integerp (mv-nth 0 (read-64ule channel state)))))

  (defthm read-64ule-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-64ule channel state))
                  (not (equal (mv-nth 0 (read-64ule channel state)) 'fail)))
             (and (<= 0 (mv-nth 0 (read-64ule channel state)))
                  (< (mv-nth 0 (read-64ule channel state)) 18446744073709551616)
                  (< (mv-nth 0 (read-64ule channel state)) (expt 2 64))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable unsigned-byte-p)
            :use (:instance read-64ule-unsigned-byte))))

  (defthm read-64ule-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-64ule channel state)))))

  (defthm read-64ule-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-64ule channel state))))))


(defsection read-64sbe
  :parents (read-bytes$)
  :short "@(call read-64sbe) reads a 64-bit, signed, big-endian value from the
input channel."

  (defund read-64sbe (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((mv x3 state) (read-byte$ channel state))
         ((mv x4 state) (read-byte$ channel state))
         ((mv x5 state) (read-byte$ channel state))
         ((mv x6 state) (read-byte$ channel state))
         ((mv x7 state) (read-byte$ channel state))
         ((mv x8 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x8)
          (mv 'fail state)))
      (mv (combine64s x1 x2 x3 x4 x5 x6 x7 x8) state)))

  (local (in-theory (enable read-64sbe)))

  (defthm read-64sbe-signed-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-64sbe channel state))
                  (not (equal (mv-nth 0 (read-64sbe channel state)) 'fail)))
             (signed-byte-p 64 (mv-nth 0 (read-64sbe channel state)))))

  (defthm read-64sbe-integer
    (implies (and (mv-nth 0 (read-64sbe channel state))
                  (not (equal (mv-nth 0 (read-64sbe channel state)) 'fail)))
             (integerp (mv-nth 0 (read-64sbe channel state)))))

  (defthm read-64sbe-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-64sbe channel state))
                  (not (equal (mv-nth 0 (read-64sbe channel state)) 'fail)))
             (and (<= -9223372036854775808 (mv-nth 0 (read-64sbe channel state)))
                  (<= (- (expt 2 63)) (mv-nth 0 (read-64sbe channel state)))
                  (< (mv-nth 0 (read-64sbe channel state)) 9223372036854775808)
                  (< (mv-nth 0 (read-64sbe channel state)) (expt 2 63))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable signed-byte-p)
            :use (:instance read-64sbe-signed-byte))))

  (defthm read-64sbe-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-64sbe channel state)))))

  (defthm read-64sbe-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-64sbe channel state))))))


(defsection read-64sle
  :parents (read-bytes$)
  :short "@(call read-64sle) reads a 64-bit, signed, big-endian value from the
input channel."

  (defund read-64sle (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((mv x1 state) (read-byte$ channel state))
         ((mv x2 state) (read-byte$ channel state))
         ((mv x3 state) (read-byte$ channel state))
         ((mv x4 state) (read-byte$ channel state))
         ((mv x5 state) (read-byte$ channel state))
         ((mv x6 state) (read-byte$ channel state))
         ((mv x7 state) (read-byte$ channel state))
         ((mv x8 state) (read-byte$ channel state))
         ((unless x1)
          (mv nil state))
         ((unless x8)
          (mv 'fail state)))
      (mv (combine64s x8 x7 x6 x5 x4 x3 x2 x1) state)))

  (local (in-theory (enable read-64sle)))

  (defthm read-64sle-signed-byte
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-64sle channel state))
                  (not (equal (mv-nth 0 (read-64sle channel state)) 'fail)))
             (signed-byte-p 64 (mv-nth 0 (read-64sle channel state)))))

  (defthm read-64sle-integer
    (implies (and (mv-nth 0 (read-64sle channel state))
                  (not (equal (mv-nth 0 (read-64sle channel state)) 'fail)))
             (integerp (mv-nth 0 (read-64sle channel state)))))

  (defthm read-64sle-range
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel))
                  (mv-nth 0 (read-64sle channel state))
                  (not (equal (mv-nth 0 (read-64sle channel state)) 'fail)))
             (and (<= -9223372036854775808 (mv-nth 0 (read-64sle channel state)))
                  (<= (- (expt 2 63)) (mv-nth 0 (read-64sle channel state)))
                  (< (mv-nth 0 (read-64sle channel state)) 9223372036854775808)
                  (< (mv-nth 0 (read-64sle channel state)) (expt 2 63))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable signed-byte-p)
            :use (:instance read-64sle-signed-byte))))

  (defthm read-64sle-state
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (state-p1 (mv-nth 1 (read-64sle channel state)))))

  (defthm read-64sle-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (open-input-channel-p1 channel
                                    :byte
                                    (mv-nth 1 (read-64sle channel state))))))


(defsection read-bytes$
  :parents (std/io)
  :short "Flexible macro for reading and combining 1, 2, 4, or 8 bytes from an
open @(':byte') input stream into a single value."

  :long "<p>General form:</p>
@({
     (read-bytes$ channel
                  [:bytes bytes]    ;; default: 1
                  [:signed signed]  ;; default: nil
                  [:end end]        ;; default: :big
                  )
       -->
     (mv value state)
})

<ul>

<li>If you provide @('bytes'), it must be explicitly 1, 2, 4, or 8.</li>

<li>If you provide @('signed'), it must be either t or nil.</li>

<li>If you provide @('end'), it must be either @(':big') or @(':little'). (For
the 1-byte readers, @('end') does not matter.)</li>

</ul>

<p>@('Read-byte$') is a macro that expands into the appropriate function from
the table below.</p>

@({
     Name         Bytes Read    Value Range        Endian-ness
   ---------------------------------------------------------------
     read-byte$   1             [0, 2^8-1]         N/A
     read-8s      1             [-2^7, 2^7-1]      N/A

     read-16ube   2             [0, 2^16-1]        Big Endian
     read-16ule   2             [0, 2^16-1]        Little Endian
     read-16sbe   2             [-2^15, 2^15-1]    Big Endian
     read-16sle   2             [-2^15, 2^15-1]    Little Endian

     read-32ube   4             [0, 2^32-1]        Big Endian
     read-32ule   4             [0, 2^32-1]        Little Endian
     read-32sbe   4             [-2^31, 2^31-1]    Big Endian
     read-32sle   4             [-2^31, 2^31-1]    Little Endian

     read-64ube   8             [0, 2^64-1]        Big Endian
     read-64ule   8             [0, 2^64-1]        Little Endian
     read-64sbe   8             [-2^63, 2^63-1]    Big Endian
     read-64sle   8             [-2^63, 2^63-1]    Little Endian
   ---------------------------------------------------------------
})"

  (defmacro read-bytes$ (channel &key
                                 (bytes '1)
                                 (signed 'nil)
                                 (end ':big))
    (declare (xargs :guard (and (symbolp channel)
                                (booleanp signed)
                                (or (equal bytes 1)
                                    (equal bytes 2)
                                    (equal bytes 4))
                                (or (equal end :little)
                                    (equal end :big)))))
    (case end
      (:big (if signed
                (case bytes
                  (1 `(read-8s ,channel state))
                  (2 `(read-16sbe ,channel state))
                  (4 `(read-32sbe ,channel state))
                  (8 `(read-64sbe ,channel state))
                  (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))
              (case bytes
                (1 `(read-byte$ ,channel state))
                (2 `(read-16ube ,channel state))
                (4 `(read-32ube ,channel state))
                (8 `(read-64ube ,channel state))
                (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))))
      (:little (if signed
                   (case bytes
                     (1 `(read-8s ,channel state))
                     (2 `(read-16sle ,channel state))
                     (4 `(read-32sle ,channel state))
                     (8 `(read-64sle ,channel state))
                     (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))
                 (case bytes
                   (1 `(read-byte$ ,channel state))
                   (2 `(read-16ule ,channel state))
                   (4 `(read-32ule ,channel state))
                   (8 `(read-64ule ,channel state))
                   (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))))
      (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))))




;; reading sequences of data

(defmacro create-n-reader (read-1 fails? &key (short '""))
  (declare (xargs :guard (and (symbolp read-1)
                              (booleanp fails?)
                              (stringp short))))
  (let ((tr-read-n (intern-in-package-of-symbol
                    (concatenate 'string "TR-" (symbol-name read-1) "-N")
                    read-1))
        (read-n (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name read-1) "-N")
                 read-1))
        (read-n-state (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name read-1) "-N-STATE")
                       read-1))
        (read-n-open-input-channel (intern-in-package-of-symbol
                                    (concatenate 'string (symbol-name read-1)
                                                 "-N-OPEN-INPUT-CHANNEL")
                                    read-1))
        (read-n-data (intern-in-package-of-symbol
                      (concatenate 'string (symbol-name read-1) "-N-DATA")
                      read-1)))
    `(defsection ,read-n
       :parents (read-bytes$-n)
       :short ,short

       (defun ,tr-read-n (n channel state acc)
         (declare (xargs :guard (and (natp n)
                                     (state-p state)
                                     (symbolp channel)
                                     (open-input-channel-p channel :byte state)
                                     (true-listp acc))))
         (if (mbe :logic (zp n) :exec (= 0 n))
             (mv (reverse acc) state)
           (mv-let (byte state)
             (,read-1 channel state)
             (cond ((eq byte nil)
                    (mv 'fail state))
                   ,@(if fails?
                         `(((eq byte 'fail)
                            (mv 'fail state)))
                       nil)
                   (t (,tr-read-n (1- n) channel state
                                  (cons byte acc)))))))

       (defun ,read-n (n channel state)
         (declare (xargs :guard (and (natp n)
                                     (state-p state)
                                     (symbolp channel)
                                     (open-input-channel-p channel :byte state))
                         :verify-guards nil))
         (mbe :logic (if (zp n)
                         (mv nil state)
                       (mv-let (byte state)
                         (,read-1 channel state)
                         (cond ((eq byte nil)
                                (mv 'fail state))
                               ,@(if fails?
                                     `(((eq byte 'fail)
                                        (mv 'fail state)))
                                   nil)
                               (t (mv-let (rest state)
                                    (,read-n (1- n) channel state)
                                    (mv (if (eq rest 'fail)
                                            'fail
                                          (cons byte rest))
                                        state))))))
              :exec (,tr-read-n n channel state nil)))

      (local (defthm lemma-decompose-impl
               (equal (,tr-read-n n channel state acc)
                      (list (mv-nth 0 (,tr-read-n n channel state acc))
                            (mv-nth 1 (,tr-read-n n channel state acc))))
               :rule-classes nil))

      (local (defthm lemma-decompose-spec
               (equal (,read-n n channel state)
                      (list (mv-nth 0 (,read-n n channel state))
                            (mv-nth 1 (,read-n n channel state))))
               :rule-classes nil))

      (local (defthm lemma-data-equiv-1
               (implies (equal (mv-nth 0 (,read-n n channel state)) 'fail)
                        (equal (mv-nth 0 (,tr-read-n n channel state acc)) 'fail))))

      (local (defthm lemma-data-equiv-2
               (implies (and (true-listp acc)
                             (not (equal (mv-nth 0 (,read-n n channel state)) 'fail)))
                        (equal (mv-nth 0 (,tr-read-n n channel state acc))
                               (revappend acc (mv-nth 0 (,read-n n channel state)))))))

      (local (defthm lemma-state-equiv
               (equal (mv-nth 1 (,tr-read-n n channel state acc))
                      (mv-nth 1 (,read-n n channel state)))))

      (local (defthm lemma-equiv
               (equal (,tr-read-n n channel state nil)
                      (,read-n n channel state))
               :hints(("Goal" :in-theory (disable ,tr-read-n ,read-n)
                       :use ((:instance lemma-decompose-impl (acc nil))
                             (:instance lemma-decompose-spec)
                             (:instance lemma-data-equiv-2 (acc nil)))))))

      (verify-guards ,read-n)

      (defthm ,read-n-state
        (implies (and (force (state-p1 state))
                      (force (symbolp channel))
                      (force (open-input-channel-p1 channel :byte state)))
                 (state-p1 (mv-nth 1 (,read-n n channel state)))))

      (defthm ,read-n-open-input-channel
        (implies (and (force (state-p1 state))
                      (force (symbolp channel))
                      (force (open-input-channel-p1 channel :byte state)))
                 (open-input-channel-p1 channel
                                        :byte
                                        (mv-nth 1 (,read-n n channel state)))))

      (defthm ,read-n-data
        (implies (not (equal (mv-nth 0 (,read-n n channel state)) 'fail))
                 (and (true-listp (mv-nth 0 (,read-n n channel state)))
                      (equal (len (mv-nth 0 (,read-n n channel state)))
                             (nfix n))))))))


(create-n-reader read-byte$ nil
                 :short "@(call read-byte$-n) reads @('n') unsigned bytes from
                         the input channel and returns them as a list.")

(create-n-reader read-8s nil
                 :short "@(call read-8s-n) reads @('n') signed bytes from the
                         input channel and returns them as a list.")



(create-n-reader read-16ube t
                 :short "@(call read-16ube-n) reads @('n') 16-bit, unsigned,
                         big-endian values from the input channel and returns
                         them as a list.")

(create-n-reader read-16ule t
                 :short "@(call read-16ule-n) reads @('n') 16-bit, unsigned,
                         little-endian values from the input channel and
                         returns them as a list.")

(create-n-reader read-16sbe t
                 :short "@(call read-16sbe-n) reads @('n') 16-bit, signed,
                         big-endian values from the input channel and returns
                         them as a list.")

(create-n-reader read-16sle t
                 :short "@(call read-16sle-n) reads @('n') 16-bit, signed,
                         little-endian values from the input channel and
                         returns them as a list.")




(create-n-reader read-32ube t
                 :short "@(call read-32ube-n) reads @('n') 32-bit, unsigned,
                         big-endian values from the input channel and returns
                         them as a list.")

(create-n-reader read-32ule t
                 :short "@(call read-32ule-n) reads @('n') 32-bit, unsigned,
                         little-endian values from the input channel and
                         returns them as a list.")

(create-n-reader read-32sbe t
                 :short "@(call read-32sbe-n) reads @('n') 32-bit, signed,
                         big-endian values from the input channel and returns
                         them as a list.")

(create-n-reader read-32sle t
                 :short "@(call read-32sle-n) reads @('n') 32-bit, signed,
                         little-endian values from the input channel and
                         returns them as a list.")



(create-n-reader read-64ube t
                 :short "@(call read-64ube-n) reads @('n') 64-bit, unsigned,
                         big-endian values from the input channel and returns
                         them as a list.")

(create-n-reader read-64ule t
                 :short "@(call read-64ule-n) reads @('n') 64-bit, unsigned,
                         little-endian values from the input channel and
                         returns them as a list.")

(create-n-reader read-64sbe t
                 :short "@(call read-64sbe-n) reads @('n') 64-bit, signed,
                         big-endian values from the input channel and returns
                         them as a list.")

(create-n-reader read-64sle t
                 :short "@(call read-64sle-n) reads @('n') 64-bit, signed,
                         little-endian values from the input channel and
                         returns them as a list.")



(defsection read-bytes$-n
  :parents (std/io)
  :short "Flexible macro for reading whole lists of @('n') 1-, 2-, 4-, or
8-byte values from an open @(':byte') input stream."

  :long "<p>General form:</p>

@({
     (read-bytes$-n n channel
                    [:bytes bytes]     ;; default: 1
                    [:signed signed]   ;; default: nil
                    [:end end]         ;; default: :big
                    )
})

<p>The @('bytes'), @('signed'), and @('end') arguments are as in @(see
read-bytes$).</p>

<p>The number @('n') says how many values to read.  The actual number of bytes
that will be read is therefore @('n * bytes').  E.g., reading three 8-byte
values will consume a total of 24 bytes from the input stream.</p>

<p>If EOF is reached before @('n * bytes') bytes are read from the stream, then
we return @('fail').  Otherwise, we return an @('n')-element list, where every
member is an appropriate integer for this combination of signedness and
size.</p>"

  (defmacro read-bytes$-n (n channel &key (bytes '1) (signed 'nil) (end ':big))
    (declare (xargs :guard (and (symbolp channel)
                                (booleanp signed)
                                (or (equal bytes 1)
                                    (equal bytes 2)
                                    (equal bytes 4))
                                (or (equal end :little)
                                    (equal end :big)))))
    (case end
      (:big (if signed
                (case bytes
                  (1 `(read-8s-n ,n ,channel state))
                  (2 `(read-16sbe-n ,n ,channel state))
                  (4 `(read-32sbe-n ,n ,channel state))
                  (8 `(read-64sbe-n ,n ,channel state))
                  (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))
              (case bytes
                (1 `(read-byte$-n ,n ,channel state))
                (2 `(read-16ube-n ,n ,channel state))
                (4 `(read-32ube-n ,n ,channel state))
                (8 `(read-64ube-n ,n ,channel state))
                (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))))
      (:little (if signed
                   (case bytes
                     (1 `(read-8s-n ,n ,channel state))
                     (2 `(read-16sle-n ,n ,channel state))
                     (4 `(read-32sle-n ,n ,channel state))
                     (8 `(read-64sle-n ,n ,channel state))
                     (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))
                 (case bytes
                   (1 `(read-byte$-n ,n ,channel state))
                   (2 `(read-16ule-n ,n ,channel state))
                   (4 `(read-32ule-n ,n ,channel state))
                   (8 `(read-64ule-n ,n ,channel state))
                   (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))))
      (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))))
