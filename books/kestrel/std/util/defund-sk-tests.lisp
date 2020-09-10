; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defund-sk")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y)))
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-necc))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-necc))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t
   :thm-enable nil)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t
   :thm-enable t)
 (assert! (disabledp 'f-definition))
 (assert! (not (disabledp 'f-necc))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule
   :thm-enable nil)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule
   :thm-enable t)
 (assert! (disabledp 'f-def-rule))
 (assert! (not (disabledp 'f-necc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :thm-name nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :thm-name nil
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-necc))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil
   :thm-name nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil
   :thm-name nil
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-necc))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t
   :thm-name nil)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t
   :thm-name nil
   :thm-enable t)
 (assert! (disabledp 'f-definition))
 (assert! (not (disabledp 'f-necc))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-necc)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule
   :thm-name nil
   :thm-enable t)
 (assert! (disabledp 'f-def-rule))
 (assert! (not (disabledp 'f-necc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :thm-name f-rw-rule)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :thm-name f-rw-rule
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :thm-name f-rw-rule
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-rw-rule))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil
   :thm-name f-rw-rule)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil
   :thm-name f-rw-rule
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain nil
   :thm-name f-rw-rule
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-rw-rule))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t
   :thm-name f-rw-rule)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t
   :thm-name f-rw-rule
   :thm-enable nil)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain t
   :thm-name f-rw-rule
   :thm-enable t)
 (assert! (disabledp 'f-definition))
 (assert! (not (disabledp 'f-rw-rule))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule
   :thm-name f-rw-rule)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule
   :thm-name f-rw-rule
   :thm-enable nil)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (forall y (equal x y))
   :constrain f-def-rule
   :thm-name f-rw-rule
   :thm-enable t)
 (assert! (disabledp 'f-def-rule))
 (assert! (not (disabledp 'f-rw-rule))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y)))
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-suff))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-suff))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t
   :thm-enable nil)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t
   :thm-enable t)
 (assert! (disabledp 'f-definition))
 (assert! (not (disabledp 'f-suff))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule
   :thm-enable nil)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule
   :thm-enable t)
 (assert! (disabledp 'f-def-rule))
 (assert! (not (disabledp 'f-suff))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :thm-name nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :thm-name nil
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-suff))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil
   :thm-name nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil
   :thm-name nil
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-suff))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t
   :thm-name nil)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t
   :thm-name nil
   :thm-enable t)
 (assert! (disabledp 'f-definition))
 (assert! (not (disabledp 'f-suff))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule
   :thm-name nil)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule
   :thm-name nil
   :thm-enable nil)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-suff)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule
   :thm-name nil
   :thm-enable t)
 (assert! (disabledp 'f-def-rule))
 (assert! (not (disabledp 'f-suff))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :thm-name f-rw-rule)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :thm-name f-rw-rule
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :thm-name f-rw-rule
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-rw-rule))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil
   :thm-name f-rw-rule)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil
   :thm-name f-rw-rule
   :thm-enable nil)
 (assert! (disabledp 'f))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain nil
   :thm-name f-rw-rule
   :thm-enable t)
 (assert! (disabledp 'f))
 (assert! (not (disabledp 'f-rw-rule))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t
   :thm-name f-rw-rule)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t
   :thm-name f-rw-rule
   :thm-enable nil)
 (assert! (disabledp 'f-definition))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain t
   :thm-name f-rw-rule
   :thm-enable t)
 (assert! (disabledp 'f-definition))
 (assert! (not (disabledp 'f-rw-rule))))

;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule
   :thm-name f-rw-rule)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule
   :thm-name f-rw-rule
   :thm-enable nil)
 (assert! (disabledp 'f-def-rule))
 (assert! (disabledp 'f-rw-rule)))

(must-succeed*
 (defund-sk f (x)
   (exists y (equal x y))
   :constrain f-def-rule
   :thm-name f-rw-rule
   :thm-enable t)
 (assert! (disabledp 'f-def-rule))
 (assert! (not (disabledp 'f-rw-rule))))
