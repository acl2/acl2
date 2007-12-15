;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")

(set-verify-guards-eagerness 2)
(set-state-ok t)

(include-book "read-byte")
(local (include-book "unsigned-byte-listp"))
(local (include-book "signed-byte-listp"))
(include-book "sign-byte")
(include-book "combine")
(local (include-book "arithmetic-3/bind-free/top" :dir :system))

;; Below are many similar functions, which we have aggregated into the
;; following macro:
;;
;;     (read-bytes$ channel [:bytes bytes] 
;;                          [:signed signed] 
;;                          [:end end])
;;
;; If you provide :bytes, it must be either 1, 2, or 4.  (default is 1)
;; If you provide :signed, it must be either t or nil.   (default is nil)
;; If you provide :end, it must be either big or little. (default is big)
;;
;; The macro simply expands into the appropriate function from the table 
;; below.  (For the 1-byte readers, :end does not matter.)
;;
;;     Name         Bytes Read    Value Range        Endian-ness
;;     read-byte$   1             [0, 2^8-1]         N/A
;;     read-8s      1             [-2^7, 2^7-1]      N/A
;;     read-16ube   2             [0, 2^16-1]        Big Endian
;;     read-16ule   2             [0, 2^16-1]        Little Endian
;;     read-16sbe   2             [-2^15, 2^15-1]    Big Endian
;;     read-16sle   2             [-2^15, 2^15-1]    Little Endian
;;     read-32ube   4             [0, 2^32-1]        Big Endian
;;     read-32ule   4             [0, 2^32-1]        Little Endian
;;     read-32sbe   4             [-2^32, 2^32-1]    Big Endian
;;     read-32sle   4             [-2^32, 2^32-1]    Little Endian
;;
;; We also provide another macro which allows you to read a fixed sequence of
;; same-length quantifies.  The interface is very similar to the above:
;;
;;     (read-bytes$-n n channel [:bytes bytes]
;;                              [:signed signed]
;;                              [:end end])
;;
;; Here n must be a natural number, while :bytes, :signed, and :end must
;; conform to the same restrictions as before.  The macro expands to a list
;; version of the appropriate function, which is logically a simple recursion
;; until n reaches zero, but under the hood is implemented in a tail recursive
;; manner for greater efficiency.
;;
;; These functions return fail if EOF is reached before (n * bytes) are read
;; from the stream.  Otherwise, they return an n-element list where every
;; member is constructed in accordance with the table above.



(local (defthm rationalp-when-integerp
         (implies (integerp x)
                  (rationalp x))))


;; read-8s

(defun read-8s (channel state)
  "Read a signed byte from an input channel."
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :verify-guards nil))
  (mv-let (byte state)
          (read-byte$ channel state)
          (if byte 
              (mv (mbe :logic (sign-byte byte)
                       :exec  (if (< (the-fixnum byte) 128)
                                  byte
                                (the-fixnum 
                                 (- (the-fixnum byte) 256))))
                  state)
            (mv nil state))))

(verify-guards read-8s
  :hints(("Goal" :in-theory (enable sign-byte signed-byte-p))))

(defthm read-8s-signed-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-8s channel state)))
           (signed-byte-p 8 (car (read-8s channel state)))))
                
(defthm read-8s-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-8s channel state)))
           (integerp (car (read-8s channel state)))))

(defthm read-8s-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-8s channel state)))
           (and (<= -128 (car (read-8s channel state)))
                (<= (- (expt 2 7)) (car (read-8s channel state)))
                (< (car (read-8s channel state)) 128)
                (< (car (read-8s channel state)) (expt 2 7))))
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
                                  (mv-nth 1 (read-8s channel state)))))

(in-theory (disable read-8s))



;; read-16ube

(defun read-16ube (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine16u)))))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (null x2)
        (mv 'fail state)
      (mv (mbe :logic (combine16u x1 x2)
               :exec (logior 
                      (the (unsigned-byte 16) 
                        (ash (the (unsigned-byte 8) x1) 8))
                      (the (unsigned-byte 8) 
                        x2)))
          state))))))

(defthm read-16ube-unsigned-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16ube channel state))
                (not (equal (car (read-16ube channel state)) 'fail)))
           (unsigned-byte-p 16 (car (read-16ube channel state)))))
                
(defthm read-16ube-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16ube channel state))
                (not (equal (car (read-16ube channel state)) 'fail)))
           (integerp (car (read-16ube channel state)))))

(defthm read-16ube-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16ube channel state))
                (not (equal (car (read-16ube channel state)) 'fail)))
           (and (<= 0 (car (read-16ube channel state)))
                (< (car (read-16ube channel state)) 65536)
                (< (car (read-16ube channel state)) (expt 2 16))))
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
                                  (mv-nth 1 (read-16ube channel state)))))

(in-theory (disable read-16ube))



;; read-16ule

(defun read-16ule (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine16u)))))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (null x2)
        (mv 'fail state)
      (mv (mbe :logic (combine16u x2 x1)
               :exec (logior 
                      (the (unsigned-byte 16) 
                        (ash (the (unsigned-byte 8) x2) 8))
                      (the (unsigned-byte 8) 
                        x1)))
          state))))))

(defthm read-16ule-unsigned-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16ule channel state))
                (not (equal (car (read-16ule channel state)) 'fail)))
           (unsigned-byte-p 16 (car (read-16ule channel state)))))
                
(defthm read-16ule-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16ule channel state))
                (not (equal (car (read-16ule channel state)) 'fail)))
           (integerp (car (read-16ule channel state)))))

(defthm read-16ule-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16ule channel state))
                (not (equal (car (read-16ule channel state)) 'fail)))
           (and (<= 0 (car (read-16ule channel state)))
                (< (car (read-16ube channel state)) 65536)
                (< (car (read-16ube channel state)) (expt 2 16))))
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
                                  (mv-nth 1 (read-16ule channel state)))))

(in-theory (disable read-16ule))

;; read-16sbe

(defun read-16sbe (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine16s sign-byte)))))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (null x2)
        (mv 'fail state)
      (mv (mbe :logic (combine16s x1 x2)
               :exec (logior (the (signed-byte 16) 
                                  (ash (the (signed-byte 8) 
                                            (if (< (the-fixnum x1) 128)
                                                (the-fixnum x1)
                                              (the-fixnum 
                                               (- (the-fixnum x1) 256))))
                                       8))
                             (the (unsigned-byte 8)
                                  x2)))
          state))))))

(defthm read-16sbe-signed-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16sbe channel state))
                (not (equal (car (read-16sbe channel state)) 'fail)))
           (signed-byte-p 16 (car (read-16sbe channel state)))))
                
(defthm read-16sbe-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16sbe channel state))
                (not (equal (car (read-16sbe channel state)) 'fail)))
           (integerp (car (read-16sbe channel state)))))

(defthm read-16sbe-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16sbe channel state))
                (not (equal (car (read-16sbe channel state)) 'fail)))
           (and (<= -32768 (car (read-16sbe channel state)))
                (<= (- (expt 2 15)) (car (read-16sbe channel state)))
                (< (car (read-16sbe channel state)) 32768)
                (< (car (read-16sbe channel state)) (expt 2 15))))
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
                                  (mv-nth 1 (read-16sbe channel state)))))

(in-theory (disable read-16sbe))



;; read-16sle

(defun read-16sle (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine16s sign-byte)))))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (null x2)
        (mv 'fail state)
      (mv (mbe :logic (combine16s x2 x1)
               :exec (logior (the (signed-byte 16) 
                                  (ash (the (signed-byte 8) 
                                            (if (< (the-fixnum x2) 128)
                                                (the-fixnum x2)
                                              (the-fixnum 
                                               (- (the-fixnum x2) 256))))
                                       8))
                             (the (unsigned-byte 8)
                                  x1)))
          state))))))

(defthm read-16sle-signed-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16sle channel state))
                (not (equal (car (read-16sle channel state)) 'fail)))
           (signed-byte-p 16 (car (read-16sle channel state)))))
                
(defthm read-16sle-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16sle channel state))
                (not (equal (car (read-16sle channel state)) 'fail)))
           (integerp (car (read-16sle channel state)))))

(defthm read-16sle-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-16sle channel state))
                (not (equal (car (read-16sle channel state)) 'fail)))
           (and (<= -32768 (car (read-16sle channel state)))
                (<= (- (expt 2 15)) (car (read-16sle channel state)))
                (< (car (read-16sle channel state)) 32768)
                (< (car (read-16sle channel state)) (expt 2 15))))
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
                                  (mv-nth 1 (read-16sle channel state)))))

(in-theory (disable read-16sle))



;; read-32ube

(defun read-32ube (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine32u)))))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (mv-let (x3 state) (read-byte$ channel state)
  (mv-let (x4 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (or (null x2) (null x3) (null x4))
        (mv 'fail state)
      (mv (mbe :logic (combine32u x1 x2 x3 x4)
               :exec (logior (the (unsigned-byte 32) 
                               (ash (the (unsigned-byte 8) x1) 24))
                      (the (unsigned-byte 24)
                           (logior
                             (the (unsigned-byte 24)
                               (ash (the (unsigned-byte 8) x2) 16))
                             (the (unsigned-byte 16)
                                  (logior
                                   (the (unsigned-byte 16)
                                        (ash (the (unsigned-byte 8) x3) 8))
                                   (the (unsigned-byte 8)
                                        x4)))))))
          state))))))))

(defthm read-32ube-unsigned-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32ube channel state))
                (not (equal (car (read-32ube channel state)) 'fail)))
           (unsigned-byte-p 32 (car (read-32ube channel state)))))
                
(defthm read-32ube-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32ube channel state))
                (not (equal (car (read-32ube channel state)) 'fail)))
           (integerp (car (read-32ube channel state)))))

(defthm read-32ube-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32ube channel state))
                (not (equal (car (read-32ube channel state)) 'fail)))
           (and (<= 0 (car (read-32ube channel state)))
                (< (car (read-32ube channel state)) 4294967296)
                (< (car (read-32ube channel state)) (expt 2 32))))
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
                                  (mv-nth 1 (read-32ube channel state)))))

(in-theory (disable read-32ube))



;; read-32ule

(defun read-32ule (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine32u)))))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (mv-let (x3 state) (read-byte$ channel state)
  (mv-let (x4 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (or (null x2) (null x3) (null x4))
        (mv 'fail state)
      (mv (mbe :logic (combine32u x4 x3 x2 x1)
               :exec (logior (the (unsigned-byte 32) 
                               (ash (the (unsigned-byte 8) x4) 24))
                             (the (unsigned-byte 24)
                                  (logior
                                   (the (unsigned-byte 24)
                                        (ash (the (unsigned-byte 8) x3) 16))
                                   (the (unsigned-byte 16)
                                        (logior 
                                         (the (unsigned-byte 16)
                                              (ash (the (unsigned-byte 8) x2) 8))
                                         (the (unsigned-byte 8)
                                              x1)))))))
          state))))))))

(defthm read-32ule-unsigned-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32ule channel state))
                (not (equal (car (read-32ule channel state)) 'fail)))
           (unsigned-byte-p 32 (car (read-32ule channel state)))))
                
(defthm read-32ule-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32ule channel state))
                (not (equal (car (read-32ule channel state)) 'fail)))
           (integerp (car (read-32ule channel state)))))

(defthm read-32ule-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32ule channel state))
                (not (equal (car (read-32ule channel state)) 'fail)))
           (and (<= 0 (car (read-32ule channel state)))
                (< (car (read-32ule channel state)) 4294967296)
                (< (car (read-32ule channel state)) (expt 2 32))))
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
                                  (mv-nth 1 (read-32ule channel state)))))

(in-theory (disable read-32ule))



;; read-32sbe

(defun read-32sbe (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine32s sign-byte)))))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (mv-let (x3 state) (read-byte$ channel state)
  (mv-let (x4 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (or (null x2) (null x3) (null x4))
        (mv 'fail state)
      (mv (mbe :logic (combine32s x1 x2 x3 x4)
               :exec (logior (the (signed-byte 32) 
                               (ash (the (signed-byte 8) 
                                         (if (< (the-fixnum x1) 128)
                                             x1
                                           (the-fixnum 
                                            (- (the-fixnum x1) 256))))
                                    24))
                             (the (unsigned-byte 24)
                                  (logior
                                   (the (unsigned-byte 24)
                                        (ash (the (unsigned-byte 8) x2) 16))
                                   (the (unsigned-byte 16)
                                        (logior 
                                         (the (unsigned-byte 16)
                                              (ash (the (unsigned-byte 8) x3) 8))
                                         (the (unsigned-byte 8)
                                              x4)))))))
          state))))))))

(defthm read-32sbe-signed-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32sbe channel state))
                (not (equal (car (read-32sbe channel state)) 'fail)))
           (signed-byte-p 32 (car (read-32sbe channel state)))))
                
(defthm read-32sbe-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32sbe channel state))
                (not (equal (car (read-32sbe channel state)) 'fail)))
           (integerp (car (read-32sbe channel state)))))

(defthm read-32sbe-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32sbe channel state))
                (not (equal (car (read-32sbe channel state)) 'fail)))
           (and (<= -2147483648 (car (read-32sbe channel state)))
                (<= (- (expt 2 31)) (car (read-32sbe channel state)))
                (< (car (read-32sbe channel state)) 2147483648)
                (< (car (read-32sbe channel state)) (expt 2 31))))
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
                                  (mv-nth 1 (read-32sbe channel state)))))

(in-theory (disable read-32sbe))



;; read-32sle

(defun read-32sle (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine32s sign-byte)))))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (mv-let (x3 state) (read-byte$ channel state)
  (mv-let (x4 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (or (null x2) (null x3) (null x4))
        (mv 'fail state)
      (mv (mbe :logic (combine32s x4 x3 x2 x1)
               :exec (logior (the (signed-byte 32) 
                               (ash (the (signed-byte 8) 
                                         (if (< (the-fixnum x4) 128)
                                             x4
                                           (the-fixnum 
                                            (- (the-fixnum x4) 256))))
                                    24))
                             (the (unsigned-byte 24)
                                  (logior 
                                   (the (unsigned-byte 24)
                                        (ash (the (unsigned-byte 8) x3) 16))
                                   (the (unsigned-byte 16)
                                        (logior
                                         (the (unsigned-byte 16)
                                              (ash (the (unsigned-byte 8) x2) 8))
                                         (the (unsigned-byte 8)
                                              x1)))))))
          state))))))))

(defthm read-32sle-signed-byte
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32sle channel state))
                (not (equal (car (read-32sle channel state)) 'fail)))
           (signed-byte-p 32 (car (read-32sle channel state)))))
                
(defthm read-32sle-integer
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32sle channel state))
                (not (equal (car (read-32sle channel state)) 'fail)))
           (integerp (car (read-32sle channel state)))))

(defthm read-32sle-range
  (implies (and (force (state-p1 state))
                (force (open-input-channel-p1 channel :byte state))
                (force (symbolp channel))
                (car (read-32sle channel state))
                (not (equal (car (read-32sle channel state)) 'fail)))
           (and (<= -2147483648 (car (read-32sle channel state)))
                (<= (- (expt 2 31)) (car (read-32sle channel state)))
                (< (car (read-32sle channel state)) 2147483648)
                (< (car (read-32sle channel state)) (expt 2 31))))
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
                                  (mv-nth 1 (read-32sle channel state)))))

(in-theory (disable read-32sle))



;; read-bytes$ macro

(defmacro read-bytes$ (channel &key (bytes '1) 
                                    (signed 'nil) 
                                    (end 'big))
  (declare (xargs :guard (and (symbolp channel)
                              (booleanp signed)
                              (or (equal bytes 1)
                                  (equal bytes 2)
                                  (equal bytes 4))
                              (or (equal end 'little)
                                  (equal end 'big)))))
  (case end 
    ('big (if signed
              (case bytes
                (1 `(read-8s ,channel state))
                (2 `(read-16sbe ,channel state))
                (4 `(read-32sbe ,channel state))
                (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))
            (case bytes 
              (1 `(read-byte$ ,channel state))
              (2 `(read-16ube ,channel state))
              (4 `(read-32ube ,channel state))
              (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))))
    ('little (if signed
                 (case bytes
                   (1 `(read-8s ,channel state))
                   (2 `(read-16sle ,channel state))
                   (4 `(read-32sle ,channel state))
                   (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))
               (case bytes
                 (1 `(read-byte$ ,channel state))
                 (2 `(read-16ule ,channel state))
                 (4 `(read-32ule ,channel state))
                 (t (er hard 'read-bytes$ "Bad case in read-bytes$.")))))
    (t (er hard 'read-bytes$ "Bad case in read-bytes$."))))

                   



;; reading sequences of data

(defmacro create-n-reader (read-1 fails?)
  (declare (xargs :guard (and (symbolp read-1)
                              (booleanp fails?))))
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
    `(encapsulate 
      nil
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
                      (list (car (,tr-read-n n channel state acc))
                            (mv-nth 1 (,tr-read-n n channel state acc))))
               :rule-classes nil))
      
      (local (defthm lemma-decompose-spec
               (equal (,read-n n channel state)
                      (list (car (,read-n n channel state))
                            (mv-nth 1 (,read-n n channel state))))
               :rule-classes nil))

      (local (defthm lemma-data-equiv-1 
               (implies (equal (car (,read-n n channel state)) 'fail)
                        (equal (car (,tr-read-n n channel state acc)) 'fail))))

      (local (defthm lemma-data-equiv-2
               (implies (and (true-listp acc)
                             (not (equal (car (,read-n n channel state)) 'fail)))
                        (equal (car (,tr-read-n n channel state acc))
                               (revappend acc (car (,read-n n channel state)))))))

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
        (implies (not (equal (car (,read-n n channel state)) 'fail))
                 (and (true-listp (car (,read-n n channel state)))
                      (equal (len (car (,read-n n channel state)))
                             (nfix n)))))
                            
)))



(create-n-reader read-byte$ nil)
(create-n-reader read-8s nil)

(create-n-reader read-16ube t)
(create-n-reader read-16ule t)
(create-n-reader read-16sbe t)
(create-n-reader read-16sle t)

(create-n-reader read-32ube t)
(create-n-reader read-32ule t)
(create-n-reader read-32sbe t)
(create-n-reader read-32sle t)



(defmacro read-bytes$-n (n channel &key (bytes '1) (signed 'nil) (end 'big))
  (declare (xargs :guard (and (symbolp channel)
                              (booleanp signed)
                              (or (equal bytes 1)
                                  (equal bytes 2)
                                  (equal bytes 4))
                              (or (equal end 'little)
                                  (equal end 'big)))))
  (case end 
    ('big (if signed
              (case bytes
                (1 `(read-8s-n ,n ,channel state))
                (2 `(read-16sbe-n ,n ,channel state))
                (4 `(read-32sbe-n ,n ,channel state))
                (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))
            (case bytes 
              (1 `(read-byte$-n ,n ,channel state))
              (2 `(read-16ube-n ,n ,channel state))
              (4 `(read-32ube-n ,n ,channel state))
              (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))))
    ('little (if signed
                 (case bytes
                   (1 `(read-8s-n ,n ,channel state))
                   (2 `(read-16sle-n ,n ,channel state))
                   (4 `(read-32sle-n ,n ,channel state))
                   (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))
               (case bytes
                 (1 `(read-byte$-n ,n ,channel state))
                 (2 `(read-16ule-n ,n ,channel state))
                 (4 `(read-32ule-n ,n ,channel state))
                 (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n.")))))
    (t (er hard 'read-bytes$-n "Bad case in read-bytes$-n."))))
