; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled append-of-take-len-minus-1-and-last
  (implies (true-listp x)
           (equal (append (take (1- (len x)) x)
                          (last x))
                  x)))

(defruled append-of-butlast-of-1-and-last
  (implies (true-listp x)
           (equal (append (butlast x 1) (last x))
                  x)))

(defruled len-of-butlast
  (implies (>= (len x) (nfix n))
           (equal (len (butlast x n))
                  (- (len x) (nfix n)))))
