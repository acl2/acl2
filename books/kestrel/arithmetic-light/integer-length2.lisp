; More theorems about integer-length
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "integer-length")
(include-book "lg")

(defthm integer-length-of-one-less-when-power-of-2p
  (implies (power-of-2p x) ;expensive?
           (equal (integer-length (+ -1 x))
                  (lg x)))
  :hints (("Goal" :in-theory (enable power-of-2p lg))))
