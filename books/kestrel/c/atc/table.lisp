; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/std/system/maybe-pseudo-event-formp" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-table
  :parents (atc-implementation)
  :short "Table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every successful call of @(tsee atc) is recorded in a table.
     This is used to support redundancy checking (see @(tsee atc-fn))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-table*
  :short "Name of the table of @(tsee atc) calls."
  'atc-table)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atc-call-info
  :short "Information associated to an @(tsee atc) call
          in the table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only record the generated encapsulate.
     More information may be recorded in the future."))
  ((encapsulate pseudo-event-formp))
  :pred atc-call-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-maybe-call-infop (x)
  :short "Optional information associated to an @(tsee atc) call
          in the table of @(tsee atc) calls."
  (or (atc-call-infop x)
      (eq x nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-table-definition
  :short "Definition of the table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys of the table are calls of @(tsee atc).
     The values of the table are the associated information."))

  (make-event
   `(table ,*atc-table* nil nil
      :guard (and (pseudo-event-formp acl2::key)
                  (atc-call-infop acl2::val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-table-lookup ((call pseudo-event-formp) (wrld plist-worldp))
  :returns (info? atc-maybe-call-infop)
  :short "Look up an @(tsee atc) call in the table."
  (b* ((table (table-alist+ *atc-table* wrld))
       (info? (cdr (assoc-equal call table))))
    (if (atc-maybe-call-infop info?)
        info?
      (raise "Internal error: value ~x0 of key ~x1 in the ATC table."
             info? call)))
  :prepwork ((local (include-book "std/alists/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-table-record-event ((call pseudo-event-formp) (info atc-call-infop))
  :returns (event pseudo-event-formp)
  :short "Event to update the table of @(tsee atc) calls."
  `(table ,*atc-table* ',call ',info))
