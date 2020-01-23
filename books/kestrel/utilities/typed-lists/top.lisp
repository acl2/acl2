; Typed List Utilities
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bit-listp")
(include-book "nat-list-fix-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc typed-list-utilities
  :parents (kestrel-utilities lists)
  :short "Some utilities for typed @(see lists)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for lists with elements of homogeneous types,
     similarly to @(see std/typed-lists).
     In contrast,
     the <see topic='@(url list-utilities)'>list utilities</see>
     are for lists with elements of any types.")
   (xdoc::p
    "These utilities may be eventually integrated
     into @(see std/typed-lists).")))
