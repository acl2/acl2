; BV Library: unsigned-byte-p-forced
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
; For unsigned-byte-p-forward and unsigned-byte-p-from-bounds,
; see the copyrights on the ihs and coi libraries.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; For rules where we get the size of a term syntactically, we sometimes have
;; to prove that the term does indeed have that size. We use this alternate
;; version of unsigned-byte-p so that no expensive rules fire (as they might on
;; unsigned-byte-p itself).
(defun unsigned-byte-p-forced (bits x)
  (declare (type t bits x))
  (unsigned-byte-p bits x))
