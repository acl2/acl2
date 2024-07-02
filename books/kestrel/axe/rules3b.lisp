; Mixed rules 3 (part 2)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/rules" :dir :system)

;; this was very slow when it was in rules3.lisp, but why?
;; mostly linear reasoning
;; was partly due to this:
;;(local (include-book "kestrel/arithmetic-light/times" :dir :system))
;; This rule does not seem needed anyway.
(defthmd bvplus-of-bvcat-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep lowsize)))
                (equal (+ lowsize 25) size)
                (unsigned-byte-p lowsize k2)
                (equal 6 lowsize) ;gen!
                (unsigned-byte-p (+ lowsize 25) k1)
                (unsigned-byte-p 25 x))
           (equal (bvplus size k1 (bvcat 25 x lowsize k2))
                  (bvcat 25 (bvplus 25 (slice (+ lowsize 25) lowsize (+ k1 k2)) x)
                         lowsize (bvchop lowsize (+ k1 k2)))))
  :hints (("Goal"
           :use (:instance split-bv (x k1) (n (+ lowsize 25)) (m lowsize))
           :in-theory (e/d (bvchop-of-sum-cases
                            slice-of-sum-cases
                            logapp
                            bvplus bvcat)
                           (;bvchop-identity
;                            plus-bvcat-with-0 ; looped
 ;                           PLUS-BVCAT-WITH-0-ALT
                            )))))
