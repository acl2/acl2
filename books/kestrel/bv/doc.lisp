; Documentation for BV library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/topics" :dir :system)

(defxdoc bv
  :short "The BV library for reasoning about bit-vectors"
  :long "See books/kestrel/bv/." ;todo: improve
  :parents (bit-vectors))
