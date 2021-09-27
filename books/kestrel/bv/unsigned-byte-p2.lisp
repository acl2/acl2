; More rules about unsigned-byte-p
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book includes theorems about unsigned-byte-p that mention non-built-in functions.

(include-book "unsigned-byte-p")
(include-book "kestrel/utilities/polarity" :dir :system)
(include-book "kestrel/arithmetic-light/lg" :dir :system)

(defthm unsigned-byte-p-from-bound-constant-version
  (implies (and (syntaxp (want-to-weaken (unsigned-byte-p n x)))
                (< x free)
                (syntaxp (quotep free))
                (syntaxp (quotep n))
                (<= free (expt 2 n)))
           (equal (unsigned-byte-p n x)
                  (and (<= 0 x)
                       (integerp x)
                       (integerp n)
                       (<= 0 n))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-*-of-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                ;; (natp (lg k)) ;drop? or simplify?
                (<= (lg k) n)
                (integerp x)
                (integerp n))
           (equal (unsigned-byte-p n (* k x))
                  (unsigned-byte-p (- n (lg k)) x)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-*-of-expt (m (lg k)))
           :in-theory (e/d (lg ;fixme
                            power-of-2p
                            )
                           (unsigned-byte-p-of-*-of-expt)))))
