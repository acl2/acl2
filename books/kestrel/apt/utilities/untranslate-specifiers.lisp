; APT (Automated Program Transformations) Library
;
; Copyright (C) 2018 Regents of the University of Texas
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "std/util/defval" :dir :system)
(include-book "kestrel/error-checking/def-error-checker" :dir :system)

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

(def-error-checker ensure-is-untranslate-specifier
  ((x "Value to check."))
  :short "Cause an error if a value is not a untranslate specifier."
  :body
  (((untranslate-specifier-p x)
    "~@0 must be an APT untranslate specifier. ~
     See :DOC APT::UNTRANSLATE-SPECIFIER."
    description))
  :returns (val (and (implies erp (equal val error-val))
                     (implies (and (not erp) error-erp)
                              (untranslate-specifier-p val))))
  :result x)
