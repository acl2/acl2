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

(fty::deftagsum standard
  :short "Fixtype of C standards."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model two choices for now:")
   (xdoc::ul
    (xdoc::li
     "C17 standard [C17].")
    (xdoc::li
     "C23 standard [C23].")))
  (:c17 ())
  (:c23 ())
  :pred standardp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod version
  :short "Fixtype of C versions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model versions as a product of the @(see standard)
     and several optional extensions.
     The current extensions are:")
   (xdoc::ul
    (xdoc::li
     "GCC extensions [GCCM] [GCCL].")
    (xdoc::li
     "Clang extensions [C17] [CLE].")
    (xdoc::li
     "CHERI extensions [CHERI]."))
   (xdoc::p
    "Not all combinations of extensions are valid.
     We therefore constrain @('version') to disallow such combinations.
     Currently, the only constraint is that
     GCC and Clang extensions cannot both be enabled.")
   (xdoc::p
    "Among those versions which are considered valid,
     some may be unsupported or only partially supported by our tools.
     For instance, it is valid (i.e. non-contradictory)
     to apply the CHERI extensions to a base standard
     without Clang or GCC extensions,
     but this is not to our knowledge a dialect that is ever used in practice,
     and so receives very little support and testing."))
  ((std standard)
   (gcc booleanp
        :reqfix (if (and gcc clang)
                    nil
                  gcc)
        :default nil)
   (clang booleanp
          :reqfix (if (and gcc clang)
                      nil
                    clang)
          :default nil)
   (cheri booleanp
          :default nil))
  :require (or (not gcc) (not clang))
  :pred versionp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-version
  :short "An irrelevant C version"
  :type versionp
  :body (make-version :std (standard-c17)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  (or (version->gcc version)
      (version->clang version)))
