; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book takes advantage of Grant Jurgensen's ACL2 formalization and proof
; of the Schroeder-Bernstein theorem, to state and prove a version here in
; purely set-theoretic terms.  See the final theorem, Schroeder-Bernstein,
; below.  The real work takes place in the book
; schroeder-bernstein-support.lisp.  It may have been simpler to redo the proof
; from scratch, using Grant's proof as a guide.  But I wanted to do the
; experiment of deriving the new result from the old one, taking advantage of
; ACL2's functional instantiation.  It's conceivable that future such
; conversion efforts (from an earlier ACL2 proof into proof of a purely
; set-theoretic formulation) could benefit from automating the approach taken
; in schroeder-bernstein-support.lisp.

(in-package "ZF")

(include-book "injective-funp")
(include-book "defthmz-plus")

(defun-sk exists-bijection (s1 s2)
  (exists fn
    (and (injective-funp fn)
         (equal (domain fn) s1)
         (equal (image fn) s2))))

(defthmz+ schroeder-bernstein
  (implies (and (injective-funp f)
                (injective-funp g)
                (equal s1 (domain f))
                (equal s2 (domain g))
                (subset (image f) s2)
                (subset (image g) s1))
           (exists-bijection s1 s2))
  :locals ((include-book "schroeder-bernstein-1"))
  :props (sbt-prop fun-bij$prop))
