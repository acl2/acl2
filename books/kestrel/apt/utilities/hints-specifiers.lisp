; APT (Automated Program Transformations) Library
;
; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)
;
; Note: This file is patterned after a similar file in the same directory,
; print-specifiers.lisp, authored by Alessandro Coglio.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc hints-specifier-utilities
  :parents (utilities)
  :short "Some utilities for
          <see topic='@(url hints-specifier)'>hints specifiers</see>.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-hints-specifier-p (x
                                     (legal-kwds acl2::keyword-listp))
  :returns (yes/no booleanp)
  :parents (hints-specifier)
  :short "Recognize canonical hints specifiers,i.e. hints specifiers that are
          keyword-value-lists that associated applicability conditions with
          hints."
  :long
  "<p>
   These are the hints specifiers that are not abbreviations.
   See @(tsee hints-specifier-p) and @(tsee canonicalize-hints-specifier).
   </p>"
  (and (keyword-value-listp x)
       (no-duplicatesp-eq (evens x))
       (subsetp-eq (evens x) legal-kwds)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hints-specifier-p (x
                           (legal-kwds acl2::keyword-listp))
  :returns (yes/no booleanp)
  :parents (hints-specifier)
  :short "Recognize hints specifiers."
  (or (canonical-hints-specifier-p x legal-kwds)

; A weaker check than translate-hints is below.

      (and (true-listp x)
           (not (acl2::first-keyword x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#!acl2
(local (defthm keyword-listp-forward-to-symbol-listp
         (implies (keyword-listp x)
                  (symbol-listp x))
         :rule-classes :forward-chaining))

(defthm canonicalize-hints-specifier-p-make-keyword-value-list-from-keys-and-value
  (implies (and (acl2::keyword-listp legal-kwds)
                (no-duplicatesp-equal legal-kwds))
           (canonical-hints-specifier-p
            (acl2::make-keyword-value-list-from-keys-and-value legal-kwds x)
            legal-kwds))
  :hints (("Goal"
           :in-theory (enable acl2::make-keyword-value-list-from-keys-and-value
                              canonical-hints-specifier-p))))

(define canonicalize-hints-specifier (x legal-kwds)
  :guard (and (acl2::keyword-listp legal-kwds)
              (no-duplicatesp-eq legal-kwds)
              (hints-specifier-p x legal-kwds))
  :returns (cx (canonical-hints-specifier-p cx legal-kwds)
               :hyp :guard)
  :parents (hints-specifier)
  :short "Turn a hints specifier into an equivalent canonical one."
  :long
  "<p>
   If the hints specifier is already canonical, it is left unchanged.
   Otherwise, the abbreviation is &ldquo;expanded&rdquo;.
   </p>"
  (cond ((canonical-hints-specifier-p x legal-kwds) x)
        (t (acl2::make-keyword-value-list-from-keys-and-value legal-kwds x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-is-hints-specifier
  ((x "Value to check.")
   (legal-kwds (and (acl2::keyword-listp legal-kwds)
                    (no-duplicatesp-eq legal-kwds))))
  "Cause an error if a value is not a hints specifier."
  (((hints-specifier-p x legal-kwds)
    "~@0 must be an APT hints specifier.  See :DOC APT::HINTS-SPECIFIER."
    description))
  :parents (hints-specifier acl2::error-checking)
  :returns (val (and (implies erp (equal val error-val))
                     (implies (and (not erp) error-erp)
                              (canonical-hints-specifier-p val legal-kwds)))
                :hyp :guard)
  :result (canonicalize-hints-specifier x legal-kwds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
