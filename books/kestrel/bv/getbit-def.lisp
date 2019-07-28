; BV Library: The definition of getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See getbit.lisp for theorems about getbit.

(include-book "slice-def")
(local (include-book "../arithmetic-light/floor")) ; for FLOOR-DIVIDE-BY-SAME
(local (include-book "../arithmetic-light/expt"))

;; Extract bit N from the bit vector X, where the numbering starts at 0 for the
;; least significant bit.
;; Similar to bitn in books/rtl.
(defund getbit (n x)
  (declare (type (integer 0 *) n)
           (type integer x)
           (xargs :guard-hints (("Goal"
                                 :use (:instance floor-divide-by-same
                                                 (i x)
                                                 (j (expt 2 n))
                                                 (k (expt 2 n)))
                                 :in-theory (e/d (ash slice logtail bvchop)
                                                 (floor-unique-equal-version))))))
  (mbe :logic (slice n n x)
       ;;i think this is faster than calling slice:
       :exec (mod (ash x (- n)) 2)))
