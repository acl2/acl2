; Mixed theorems about bit-vector operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains more BV rules (TODO: integrate into the rest of the library)

(include-book "sbvlt")
(include-book "bvcat")
(include-book "rules") ;for SBVLT-REWRITE
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;gen the 0?
(defthm sbvlt-of-bvcat-and-0
  (implies (and (equal size (+ lowsize highsize))
                (posp highsize)
                (natp lowsize))
           (equal (sbvlt size (bvcat highsize highval lowsize lowval) 0)
                  (equal 1 (getbit (+ -1 highsize) highval))))
  :hints (("Goal" :in-theory (enable sbvlt-rewrite))))

;asking whether a bvsx is negative is the same as asking whether the top bit of
;the value being sign extended is 1.
(defthm sbvlt-of-bvsx
  (implies (and (natp size)
                (posp n)
                (< n size))
           (equal (sbvlt size (bvsx size n x) 0)
                  (equal 1 (getbit (+ -1 n) x))))
  :hints (("Goal"; :cases ((< (BINARY-+ '1 (BINARY-+ (UNARY-- N) SIZE)) '0))
           :in-theory (enable bvsx))))
