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

(include-book "messages")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-message-creation
  :parents (operations)
  :short "Operations for creating messages."
  :long
  (xdoc::topstring
   (xdoc::p
    "Messages are created from certificates.
     In our model there is only one kind of messages."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define messages-for-certificate ((cert certificatep)
                                  (dests address-setp))
  :returns (msgs message-setp)
  :short "Create messages for a certificate with given destinations."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each address,
     we create a message with the certificate
     and the address as destination.")
   (xdoc::p
    "This is used to model the broadcasting of a certificate
     in @(tsee create-certificate-next)."))
  (cond ((set::emptyp dests) nil)
        (t (set::insert (make-message :certificate cert
                                      :destination (set::head dests))
                        (messages-for-certificate cert (set::tail dests)))))
  :verify-guards :after-returns
  ///

  (defruled message->certificate-when-in-messages-for-certificate
    (implies (and (certificatep cert)
                  (set::in msg (messages-for-certificate cert dests)))
             (equal (message->certificate msg) cert))
    :induct t)

  (defruled in-of-messages-for-certificate
    (implies (address-setp dests)
             (equal (set::in msg
                             (messages-for-certificate cert dests))
                    (and (messagep msg)
                         (equal (message->certificate msg)
                                (certificate-fix cert))
                         (set::in (message->destination msg)
                                  dests))))
    :induct t
    :enable message->certificate-when-in-messages-for-certificate))
