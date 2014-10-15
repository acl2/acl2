; ACL2 books on arithmetic
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:
; Ruben Gamboa
; LIM International, Inc.
; 9390 Research Blvd, Suite II-200
; Austin, TX 78759 U.S.A.

; Plagiarized from rational-listp.lisp.

(in-package "ACL2")

#+:non-standard-analysis
(defthm append-preserves-real-listp
  (implies (true-listp x)
           (equal (real-listp (append x y))
                  (and (real-listp x)
                       (real-listp y)))))

#+:non-standard-analysis
(defthm realp-car-real-listp
  (implies (and (real-listp x)
		x)
	   (realp (car x)))
  :rule-classes :forward-chaining)
