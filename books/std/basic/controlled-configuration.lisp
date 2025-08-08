; Controlled Configuration
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides a macro to go into a "controlled configuration",
; i.e. one where many built-ins are disabled, there is no implicit induction,
; and certain options of DEFINE (if present) are set to certain values.
; A call of this macro must be placed towards the beginning of the file,
; just after all the necessary local and non-local book inclusions,
; and before the actual content of the file.
; This file that contains this macro must be explicitly included
; in every file that calls the macro and that does not already include
; another file that includes this file.

; The purpose of this controlled configuration macro is
; to make proofs more maintainable and efficient,
; and to reduce the verbosity of some aspects of the code.
; The macro call includes some books locally to the file
; and sets certain options locally to the file.
; The macro provides customization options,
; which should be obvious from the definition of the macro below.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun controlled-configuration-fn (induction-depth
                                    no-function
                                    state)
  (declare (xargs :stobjs state))
  `(progn
     (local (include-book "kestrel/built-ins/disable" :dir :system))
     (local (acl2::disable-most-builtin-logic-defuns))
     (local (acl2::disable-builtin-rewrite-rules-for-defaults))
     (set-induction-depth-limit ,induction-depth)
     ,@(and (not (eq (getpropc 'std::make-define-config
                               'macro-args
                               :absent
                               (w state))
                     :absent))
            `((std::make-define-config :no-function ,no-function)))))

(defmacro controlled-configuration (&key (induction-depth '0)
                                         (no-function 't))
  `(make-event (controlled-configuration-fn ,induction-depth
                                            ,no-function
                                            state)))
