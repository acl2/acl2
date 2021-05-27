; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "kestrel/fty/byte-list" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ randomness-beacon
  :parents (zcash)
  :short "Randomness beacon in Zcash."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the value described in [ZPS:5.9].
     It is a random, well-defined value used in Zcash."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *urs*
  :short "The constant @($\\mathsf{URS}$) [ZPS:5.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is copied and pasted from [ZPS], and visually compared with it.
     Nonetheless, eventually it would be good to replicate, in ACL2,
     its calculation, which is described in [ZPS:5.9]."))
  (acl2::string=>nats
   "096b36a5804bfacef1691e173c366a47ff5ba84a44f26ddd7e8d9f79d5b42df0")
  ///
  (assert-event (byte-listp *urs*))
  (assert-event (equal (len *urs*) 64)))
