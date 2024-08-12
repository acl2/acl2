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

(include-book "operations-faults-and-quora")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-fault-tolerance
  :parents (operations-additional)
  :short "Operations about fault tolerance."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we capture the classic BFT condition for fault tolerance,
     in the context of our AleoBFT model.
     We define a predicate that says whether
     the system is (Byzantine-)fault-tolerant"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fault-tolerant-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if the system is (Byzatine-)fault-tolerant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when the faulty validators
     are no more than the maximum number of faulty validators,
     i.e. @($f \\leq F$), which is equivalent to @($f < n/3$)."))
  (<= (number-faulty systate)
      (max-faulty systate))
  :hooks (:fix)
  ///

  (defruled fault-tolerant-p-alt-def
    (implies (not (zp (number-validators systate)))
             (equal (fault-tolerant-p systate)
                    (< (number-faulty systate)
                       (/ (number-validators systate) 3))))
    :enable (max-faulty max-faulty-for-total)
    :prep-books ((include-book "arithmetic-5/top" :dir :system))))
