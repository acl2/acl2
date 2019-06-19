; A book to fix a problem with arithmetic/equalities.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../../arithmetic/equalities")

;; TODO: Consider changing equal-/ itself.

(in-theory (disable equal-/)) ;since we have equal-/-better

;; Includes a syntaxp hyp to prevent this rule from firing on (equal 1/4 x)
;; due to acl2's overly-aggressive term matching.
(defthm equal-/-better
  (implies (and (acl2-numberp x)
                (syntaxp (not (quotep x)))
                (not (equal 0 x)))
           (equal (equal (/ x) y)
                  (equal 1 (* x y))))
  :hints (("Goal" :use equal-/)))
