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

(include-book "sign-byte")
(local (include-book "unsigned-byte-listp"))
(local (include-book "signed-byte-listp"))

(defun combine16u (x1 x2)
  "Given unsigned bytes x1 and x2, compute (x1 << 8) | x2, interpreted
   as a 16-bit unsigned integer."
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2))
  (logior (ash x1 8) x2))

(defthm combine16u-unsigned-byte
  (implies (and (force (unsigned-byte-p 8 x1))
                (force (unsigned-byte-p 8 x2)))
           (unsigned-byte-p 16 (combine16u x1 x2))))

(in-theory (disable combine16u))


(defun combine16s (x1 x2)
  "Given unsigned bytes x1 and x2, compute (x1 << 8) | x2, interpreted
   as a 16-bit signed integer."
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2))
  (logior (ash (sign-byte x1) 8)
          x2))

(defthm combine16s-signed-byte
  (implies (and (force (unsigned-byte-p 8 x1))
                (force (unsigned-byte-p 8 x2)))
           (signed-byte-p 16 (combine16s x1 x2))))

(in-theory (disable combine16s))


(defun combine32u (x1 x2 x3 x4)
  "Given unsigned bytes x1, x2, x3, and x4, compute
     (x1 << 24) | (x2 << 16) | (x3 << 8) | x4
  and interpret the result as a 32-bit unsigned integer."
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2)
           (type (unsigned-byte 8) x3)
           (type (unsigned-byte 8) x4))
  (logior (ash x1 24)
          (ash x2 16)
          (ash x3 8)
          x4))

(defthm combine32u-unsigned-byte
  (implies (and (force (unsigned-byte-p 8 x1))
                (force (unsigned-byte-p 8 x2))
                (force (unsigned-byte-p 8 x3))
                (force (unsigned-byte-p 8 x4)))
           (unsigned-byte-p 32 (combine32u x1 x2 x3 x4))))

(in-theory (disable combine32u))

(defun combine32s (x1 x2 x3 x4)
  "Given unsigned bytes x1, x2, x3, and x4, compute
     (x1 << 24) | (x2 << 16) | (x3 << 8) | x4
   and interpret the result as an 32-bit signed integer."
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2)
           (type (unsigned-byte 8) x3)
           (type (unsigned-byte 8) x4))
  (logior (ash (sign-byte x1) 24)
          (ash x2 16)
          (ash x3 8)
          x4))

(defthm combine32s-signed-byte
  (implies (and (force (unsigned-byte-p 8 x1))
                (force (unsigned-byte-p 8 x2))
                (force (unsigned-byte-p 8 x3))
                (force (unsigned-byte-p 8 x4)))
           (signed-byte-p 32 (combine32s x1 x2 x3 x4)))
  :hints(("Goal" :use ((:instance signed-byte-p-logior
                                  (size 32)
                                  (x (ash (sign-byte x1) 24))
                                  (y (logior (ash x2 16)
                                             (ash x3 8)
                                             x4)))
                       (:instance unsigned-to-signed-promote
                                  (size1 24)
                                  (size2 32)
                                  (x (logior (ash x2 16)
                                             (ash x3 8)
                                             x4)))))))

(in-theory (disable combine32s))

