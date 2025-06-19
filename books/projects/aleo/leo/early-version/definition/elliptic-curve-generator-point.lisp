; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "kestrel/crypto/ecurve/points-fty" :dir :system)

(include-book "std/util/add-io-pairs" :dir :system)
(acl2::merge-io-pairs
 primep
 (include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-generator ()
  :returns (point ecurve::edwards-bls12-pointp)
  :parents (elliptic-curves)
  :short "The point on the edwards-bls12 curve that is used as a generator point."
  :long
  (xdoc::topstring
   (xdoc::p
    "This generator point is used by Leo to define a mapping from integers
     modulo the group order to points on the edwards-bls12 elliptic curve.")
   (xdoc::p
     "In some sense the generator point is arbitrary, but once chosen, it cannot
      be changed without changing the semantics of Leo operations on group values.")
   (xdoc::p
    "The generator point is returned by the literal `1group' in the Leo language.")
   (xdoc::p
    "For more information on the edwards bls12 curve, see @(see ecurve::edwards-bls12)")
   (xdoc::p
    (xdoc::ahref
     "https://github.com/AleoHQ/snarkVM/blob/033c4397df8fa9ae4505548065670a9ab1155202/curves/src/edwards_bls12/parameters.rs#L147"
     "Here is a link")
    "to the source code containing these values."))
  (ecurve::point-finite
   7810607721416582242904415504650443951498042435501746664987470571546413371306
   1867362672570137759132108893390349941423731440336755218616442213142473202417))
