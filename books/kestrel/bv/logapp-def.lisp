; BV Library: A lightweight book providing logapp.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
; The definitions in this file come from books/ihs. See the copyright there.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;the definitions below are compatible with books/ihs/basic-definitions

(local (include-book "../../ihs/basic-definitions"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/numerator"))

(defun expt2$inline (n)
  (declare (xargs :guard (natp n)))
  (let ((__function__ 'expt2))
       (declare (ignorable __function__))
       (mbe :logic (expt 2 (nfix n))
            :exec (the unsigned-byte
                       (ash 1 (the unsigned-byte n))))))

(defmacro expt2 (n)
  (list 'expt2$inline n))(defun imod$inline (i j)
       (declare (xargs :guard (and (integerp i)
                                   (and (integerp j) (not (= 0 j))))))
       (let ((__function__ 'imod))
            (declare (ignorable __function__))
            (mbe :logic (mod (ifix i) (ifix j))
                 :exec (mod i j))))

(defmacro imod (i j)
  (list 'imod$inline i j))

(defun loghead$inline (size i)
 (declare (type unsigned-byte size))
 (declare (xargs :guard (and (and (integerp size) (<= 0 size))
                             (integerp i))))
 (declare
  (xargs :guard-hints (("Goal" :in-theory (enable ;mod-of-expt-2-is-logand
                                           )))
          :split-types t))
 (let
     ((__function__ 'loghead))
     (declare (ignorable __function__))
     (mbe :logic (imod i (expt2 size))
          :exec (the unsigned-byte
                     (logand i
                             (the unsigned-byte
                                  (1- (the unsigned-byte (ash 1 size)))))))))

(defmacro loghead (size i)
  (list 'loghead$inline size i))

(defun logapp (size i j)
  (declare (type unsigned-byte size))
  (declare (xargs :guard (and (and (integerp size) (<= 0 size))
                              (integerp i)
                              (integerp j))))
  (declare (xargs :split-types t))
  (let ((__function__ 'logapp))
       (declare (ignorable __function__))
       (mbe :logic (let ((j (ifix j)))
                        (+ (loghead size i) (* j (expt2 size))))
            :exec (+ (loghead size i) (ash j size)))))
