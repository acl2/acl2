; APT Utilities -- Untranslate Specifiers
;
; Copyright (C) 2018 Regents of the University of Texas
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/error-checking" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc untranslate-specifier-utilities
  :parents (utilities)
  :short "Some utilities for
          <see topic='@(url untranslate-specifier)'>untranslate
          specifiers</see>.")

(local (xdoc::set-default-parents untranslate-specifier-utilities))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *untranslate-specifier-keywords*
  :short "List of keywords used for untranslate specifiers."
  '(t nil :nice :nice-expanded)
  ///

  (assert-event (symbol-listp *untranslate-specifier-keywords*))

  (assert-event (no-duplicatesp-eq *untranslate-specifier-keywords*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define untranslate-specifier-p (x)
  :returns (yes/no booleanp)
  :short "Recognize untranslate specifiers."
  (if (member-eq x *untranslate-specifier-keywords*) t nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following is analogous to apt::ensure-is-print-specifier.  It may well be
; nice to have at some point, but it is not yet used.

#||
(def-error-checker ensure-is-untranslate-specifier
  ((x "Value to check."))
  "Cause an error if a value is not a untranslate specifier."
  (((untranslate-specifier-p x)
    "~@0 must be an APT untranslate specifier.  See :DOC APT::UNTRANSLATE-SPECIFIER."
    description))
  :returns (val (and (implies erp (equal val error-val))
                     (implies (and (not erp) error-erp)
                              (untranslate-specifier-p val))))
  :result x)
||#
