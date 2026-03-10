; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../portcullis")

(include-book "std/util/defirrelevant" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

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
    "We model six choices for now:")
   (xdoc::ul
    (xdoc::li
     "C17 standard [C17].")
    (xdoc::li
     "C23 standard [C23].")
    (xdoc::li
     "C17 standard with GCC extensions [C17] [GCCM] [GCCL].")
    (xdoc::li
     "C23 standard with GCC extensions [C23] [GCCM] [GCCL].")
    (xdoc::li
     "C17 standard with Clang extensions [C17] [CLE].")
    (xdoc::li
     "C23 standard with Clang extensions [C17] [CLE].")))
  (:c17 ())
  (:c23 ())
  (:c17+gcc ())
  (:c23+gcc ())
  (:c17+clang ())
  (:c23+clang ())
  :pred versionp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-version
  :short "An irrelevant C version"
  :type versionp
  :body (version-c17))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define version-std-c17p ((version versionp))
  :returns (yes/no booleanp)
  :short "Check if the C standard for this C version is C17."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether the C version is C17,
     with or without GCC/Clang extensions."))
  (or (version-case version :c17)
      (version-case version :c17+gcc)
      (version-case version :c17+clang)))

;;;;;;;;;;;;;;;;;;;;

(define version-std-c23p ((version versionp))
  :returns (yes/no booleanp)
  :short "Check if the C standard for this C version is C23."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether the C version is C23,
     with or without GCC/Clang extensions."))
  (or (version-case version :c23)
      (version-case version :c23+gcc)
      (version-case version :c23+clang)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define version-gccp ((version versionp))
  :returns (yes/no booleanp)
  :short "Check if this C version includes GCC extensions or not."
  (or (version-case version :c17+gcc)
      (version-case version :c23+gcc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define version-clangp ((version versionp))
  :returns (yes/no booleanp)
  :short "Check if this C version includes Clang extensions or not."
  (or (version-case version :c17+clang)
      (version-case version :c23+clang)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define version-gcc/clangp ((version versionp))
  :returns (yes/no booleanp)
  :short "Check if this C version includes either GCC or Clang extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is very large overlap between the of extensions
     supported by GCC and by Clang.
     Therefore, it is most often sufficient to check
     if the version includes either."))
  (or (version-gccp version)
      (version-clangp version)))
