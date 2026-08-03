; Signed bit-vector division
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the rules in sbvdiv.lisp.

(include-book "bvchop-def")
(include-book "logext-def")
(local (include-book "logext"))
(local (include-book "bvchop"))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;fixme make sure this is right
;this is like java's idiv
;takes and returns USBs
(defund sbvdiv (n x y)
  (declare (type (integer 1 *) n)
           (type integer x y)
           (xargs :guard (not (equal 0 (bvchop n y)))))
  (bvchop n (truncate (logext n x) (logext n y))))
