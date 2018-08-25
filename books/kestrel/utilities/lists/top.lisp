; List Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)

(include-book "last-theorems")
(include-book "len-const-theorems")
(include-book "primitive-theorems")
(include-book "set-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc list-utilities
  :parents (kestrel-utilities lists)
  :short "Some utilities for @(see lists)."
  :long
  (xdoc::topapp
   (xdoc::p
    "These are for lists with elements of any type,
     similarly to @(see std/lists).")
   (xdoc::p
    "These utilities may be eventually integrated into @(see std/lists).")))
