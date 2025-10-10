; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "centaur/fty/top" :dir :system)

(include-book "../../portcullis")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ versions
  :parents (implementation-environments)
  :short "Versions of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a data structure to indicate the specific version of C.
     This includes the standards (e.g. C17 [C17] and C23 [C23]),
     but also GCC extensions, and possibly other variants.
     We start with only some choices,
     but we will add more choices in the future as needed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum version
  :short "Fixtype of C versions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model four choices for now:")
   (xdoc::ul
    (xdoc::li
     "C17 standard [C17].")
    (xdoc::li
     "C23 standard [C23].")
    (xdoc::li
     "C17 standard with GCC extensions [C17] [GCCM] [GCCL].")
    (xdoc::li
     "C23 standard with GCC extensions [C23] [GCCM] [GCCL].")))
  (:c17 ())
  (:c23 ())
  (:c17+gcc ())
  (:c23+gcc ())
  :pred versionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define version-std-c17p ((version versionp))
  :returns (yes/no booleanp)
  :short "Check if the C standard for this C version is C17."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether the C version is C17,
     with or without GCC extensions."))
  (or (version-case version :c17)
      (version-case version :c17+gcc))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define version-std-c23p ((version versionp))
  :returns (yes/no booleanp)
  :short "Check if the C standard for this C version is C23."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether the C version is C23,
     with or without GCC extensions."))
  (or (version-case version :c23)
      (version-case version :c23+gcc))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define version-gccp ((version versionp))
  :returns (yes/no booleanp)
  :short "Check if this C version includes GCC extensions or not."
  (or (version-case version :c17+gcc)
      (version-case version :c23+gcc))
  :hooks (:fix))
