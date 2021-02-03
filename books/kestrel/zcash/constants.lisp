; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "bit-byte-integer-conversions")

(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ constants
  :parents (zcash)
  :short "Constants used in Zcash."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the constants listed in [ZPS:5.3].
     Those are not all the constants, as such, used in Zcash;
     however, those have a dedicated section explicitly titled `Constants'.")
   (xdoc::p
    "For now we only capture some of them.
     More will be added as needed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *l-merkle-sapling*
  :short "The constant @($\\ell_\\mathsf{MerkleSapling}$) in [ZPS:5.3]."
  255)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *uncommitted-sapling*
  :short "The constant @($\\mathsf{Uncommitted}^\\mathsf{Sapling}$) [ZPS:5.3]."
  (i2lebsp *l-merkle-sapling* 1)
  ///
  (assert-event (= (len *uncommitted-sapling*)
                   *l-merkle-sapling*)))
