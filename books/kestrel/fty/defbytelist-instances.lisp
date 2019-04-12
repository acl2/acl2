; FTY -- Byte List Fixtype Instances
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "defubytelist")
(include-book "defsbytelist")
(include-book "defbyte-instances")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbytelist-instances
  :parents (fty-extensions specific-types defbytelist)
  :short "Fixtypes of true lists of unsigned and signed bytes of various sizes,
          with some accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all generated via @(tsee defbytelist).")
   (xdoc::p
    "If fixtypes of true lists of unsigned or signed bytes of a certain size
     are needed but are not among the ones defined here,
     they can be added here.")
   (xdoc::p
    "These fixtypes are based on
     <see topic='@(url defbyte-instances)'>these fixtypes</see>.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defubytelist 1)
(defubytelist 2)
(defubytelist 3)
(defubytelist 4)
(defubytelist 8)
(defubytelist 16)
(defubytelist 32)
(defubytelist 64)
(defubytelist 128)
(defubytelist 256)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsbytelist 1)
(defsbytelist 2)
(defsbytelist 3)
(defsbytelist 4)
(defsbytelist 8)
(defsbytelist 16)
(defsbytelist 32)
(defsbytelist 64)
(defsbytelist 128)
(defsbytelist 256)
