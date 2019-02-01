; Alist Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)

(include-book "alist-map-keys")
(include-book "alist-map-vals")
(include-book "remove-assoc-theorems")
(include-book "remove-assocs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc alist-utilities
  :parents (kestrel-utilities alists)
  :short "Some utilities for @(see alists)."
  :long
  (xdoc::topapp
   (xdoc::p
    "These utilities may be eventually integrated into @(see std/alists).")))
