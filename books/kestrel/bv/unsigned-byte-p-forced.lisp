; BV Library: unsigned-byte-p-forced
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; For rules where we get the size of a term syntactically, we sometimes have
;; to prove that the term does indeed have that size.  We use this alternate
;; version of unsigned-byte-p so that no expensive rules fire (as they might if
;; we used unsigned-byte-p itself).
(defund unsigned-byte-p-forced (bits x)
  (declare (xargs :guard t))
  (unsigned-byte-p bits x))

(defthm unsigned-byte-p-forced-forward-to-unsigned-byte-p
  (implies (unsigned-byte-p-forced size x)
           (unsigned-byte-p size x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))
