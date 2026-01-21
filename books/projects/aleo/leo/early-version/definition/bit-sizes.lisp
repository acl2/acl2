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

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bit-sizes
  :parents (abstract-syntax)
  :short "Leo integer bit sizes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo has unsigned and signed integers
     of sizes 8, 16, 32, 64, and 128 in bits."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bitsize
  :short "Fixtype of Leo integer bit sizes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We capture the possible sizes as an enumeration,
     since there are just five of them."))
  (:8 ())
  (:16 ())
  (:32 ())
  (:64 ())
  (:128 ())
  :pred bitsizep)
