; Ethereum Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "xdoc/defxdoc-plus" :dir :system)

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the BASICS topic below:
(include-book "scalars")
(include-book "nibbles")
(include-book "bytes")
(include-book "words")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ basics
  :parents (ethereum)
  :short "Some basic Ethereum notions and utilities."
  :order-subtopics t)
