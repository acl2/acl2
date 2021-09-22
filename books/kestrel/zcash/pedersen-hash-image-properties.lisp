; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "pedersen-hash")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pedersen-hash-image-properties
  :parents (pedersen-hash)
  :short "Some properties about the image of @(tsee pedersen)."
  :long
  (xdoc::topstring
   (xdoc::p
    "[ZPS] includes theorems showing that
     certain values are not possible values of Pedersen hash."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pedersen-is-not-uncommitted-sapling
  :short "@(tsee *uncommitted-sapling*) is not
          in the image of @(tsee pedersen)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This was Theorem 5.4.2 in certain earlier versions of [ZPS],
     such as version 2020.1.0.
     Later versions of [ZPS] have similar theorems,
     but not quite the same.
     In any case, this property still holds, and it is proved here.")
   (xdoc::p
    "The theorem is of interest when @(tsee pedersen) returns a good hash,
     which requires @(tsee pedersen-point) to return a Jubjub point.
     However, since our definition of @(tsee pedersen)
     returns @('nil') when @(tsee pedersen-point) does not return a point,
     this theorem holds unconditionally.")
   (xdoc::p
    "We first prove the case in which @(tsee pedersen-point) returns a point,
     and we use the definition of @(tsee *uncommitted-sapling*) in this lemma.
     This is critical for
     the injectivity theorem of @(tsee i2lebsp) to apply,
     which reduces the goal to the inequality of
     the abscissa of a Jubjub point with 1,
     which is false by @(tsee jubjub-point-abscissa-is-not-1).
     The latter theorem is disabled,
     but it appears that ACL2's tau system makes use of it."))
  (not (equal (pedersen d m)
              *uncommitted-sapling*))
  :enable pedersen
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (implies (jubjub-pointp (pedersen-point d m))
              (not (equal (pedersen d m)
                          (i2lebsp *l-merkle-sapling* 1))))
     :enable (pedersen
              coordinate-extract
              jubjub-q)
     :disable ((:e i2lebsp)))))
