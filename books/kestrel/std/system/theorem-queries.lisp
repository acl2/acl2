; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "classes")
(include-book "classes-plus")
(include-book "guard-verified-p")
(include-book "guard-verified-p-plus")
(include-book "thm-formula")
(include-book "thm-formula-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/theorem-queries
  :parents (std/system)
  :short "Utilities to query theorems."
  :long
  (xdoc::topstring-p
   "These utilities retrieve properties of theorems in the @(see world)."))
