; APT Utilities -- Print Specifiers
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/error-checking" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc print-specifier-utilities
  :parents (utilities)
  :short "Some utilities for
          <see topic='@(url print-specifier)'>print specifiers</see>.")

(local (xdoc::set-default-parents print-specifier-utilities))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *print-specifier-keywords*
  :short "List of keywords used for print specifiers."
  (list :expand :submit :result)
  ///

  (assert-event (symbol-listp *print-specifier-keywords*))

  (assert-event (no-duplicatesp-eq *print-specifier-keywords*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-print-specifier-p (x)
  :returns (yes/no booleanp)
  :short "Recognize canonical print specifiers,
          i.e. print specifiers that are lists of keywords."
  :long
  "<p>
   These are the print specifiers that are not abbreviations.
   See @(tsee print-specifier-p) and @(tsee canonicalize-print-specifier).
   </p>"
  (and (symbol-listp x)
       (no-duplicatesp-eq x)
       (subsetp-eq x *print-specifier-keywords*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-specifier-p (x)
  :returns (yes/no booleanp)
  :short "Recognize print specifiers."
  :long
  "<p>
   These are the canonical ones (see @(tsee canonical-print-specifier-p))
   as well as the ones that are abbreviations of canonical ones.
   </p>"
  (or (eq x t)
      (if (member-eq x *print-specifier-keywords*) t nil)
      (canonical-print-specifier-p x))
  ///

  (defrule print-specifier-p-when-canonical-print-specifier-p
    (implies (canonical-print-specifier-p ps)
             (print-specifier-p ps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonicalize-print-specifier ((ps print-specifier-p))
  :returns (cps canonical-print-specifier-p)
  :short "Turn a print specifier into an equivalent canonical one."
  :long
  "<p>
   If the print specifier is already canonical, it is left unchanged.
   Otherwise, the abbreviation is &ldquo;expanded&rdquo;.
   </p>"
  (cond ((canonical-print-specifier-p ps) ps)
        ((member-eq ps *print-specifier-keywords*) (list ps))
        (t *print-specifier-keywords*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-is-print-specifier
  ((x "Value to check."))
  "Cause an error if a value is not a print specifier,
   otherwise return an equivalent canonical print specifier."
  (((print-specifier-p x)
    "~@0 must be an APT print specifier.  See :DOC APT::PRINT-SPECIFIER."
    description))
  :returns (val (and (implies erp (equal val error-val))
                     (implies (and (not erp) error-erp)
                              (canonical-print-specifier-p val))))
  :result (canonicalize-print-specifier x))
