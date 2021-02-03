; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/error-checking/def-error-checker" :dir :system)
(include-book "std/util/defenum" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc print-specifier-utilities
  :parents (utilities)
  :short "Some utilities for
          <see topic='@(url print-specifier)'>print specifiers</see>.")

(local (xdoc::set-default-parents print-specifier-utilities))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defenum print-specifier-p (nil :error :result :info :all)
  :short "Recognize a print specifier.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-is-print-specifier
  ((x "Value to check."))
  :short "Cause an error if a value is not a print specifier."
  :body
  (((print-specifier-p x)
    "~@0 must be a print specifier.  See :DOC APT::PRINT-SPECIFIER."
    description)))
