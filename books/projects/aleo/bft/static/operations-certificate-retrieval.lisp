; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "certificates")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-certificate-retrieval
  :parents (operations)
  :short "Operations to retrieve certificates from sets of certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define operations to retrieve certificates, from sets of certificates,
     based on various author and round criteria.
     These operations are primarily used on DAGs in our model,
     which are modeled as sets of certificates
     (satisfying certain invariants
     formalized and proved in @(see correctness)),
     but they are also used on buffers,
     which are also modeled as sets of certificates."))
  :order-subtopics t
  :default-parent t)
