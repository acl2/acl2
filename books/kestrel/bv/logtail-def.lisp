; BV Library: A lightweight book providing logtail.
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

;; The definitions below are compatible with books/ihs/basic-definitions.

(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/floor"))

(defun expt2$inline (n)
  (declare (xargs :guard (natp n)))
  (let ((__function__ 'expt2))
       (declare (ignorable __function__))
       (mbe :logic (expt 2 (nfix n))
            :exec (the unsigned-byte
                       (ash 1 (the unsigned-byte n))))))

(defmacro expt2 (n)
  (list 'expt2$inline n))

(defun ifloor$inline (i j)
  (declare (xargs :guard (and (integerp i)
                              (and (integerp j) (not (= 0 j))))))
  (let ((__function__ 'ifloor))
       (declare (ignorable __function__))
       (mbe :logic (floor (ifix i) (ifix j))
            :exec (floor i j))))

(defmacro ifloor (i j)
  (list 'ifloor$inline i j))

(defun logtail$inline (pos i)
  (declare (type unsigned-byte pos))
  (declare (xargs :guard (and (and (integerp pos) (<= 0 pos))
                              (integerp i))))
  (declare (xargs :guard (and (integerp pos)
                              (>= pos 0)
                              (integerp i))))
  (declare (xargs :split-types t))
  (let ((__function__ 'logtail))
       (declare (ignorable __function__))
       (mbe :logic (ifloor i (expt2 pos))
            :exec (ash i (- (the unsigned-byte pos))))))

(defmacro logtail (pos i)
  (list 'logtail$inline pos i))

(add-macro-alias logtail logtail$inline)
