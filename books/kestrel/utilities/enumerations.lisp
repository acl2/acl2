; Miscellaneous Enumerations
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defenum" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc miscellaneous-enumerations
  :parents (kestrel-utilities)
  :short "Some miscellaneous enumerations.")

(std::defenum logic/program-p (:logic :program)
  :parents (miscellaneous-enumerations)
  :short "Enumeration of @(see defun-mode)s.")

(std::defenum logic/program/auto-p (:logic :program :auto)
  :parents (miscellaneous-enumerations)
  :short "Enumeration of @(see defun-mode)s and @(':auto').")

(std::defenum t/nil/auto-p (t nil :auto)
  :parents (miscellaneous-enumerations)
  :short "Enumeration of booleans and @(':auto').")
