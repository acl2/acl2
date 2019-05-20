; Return Type Theorems for Representation of Natural Numbers as Digits -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defthm-dab-return-types")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test DEFTHM-DAB-RETURN-TYPES:

(defun hexdigitp (x) ; = (DAB-DIGITP 16 X)
  (declare (xargs :guard t))
  (integer-range-p 0 16 x))

(std::deflist hexdigit-listp (x) ; = (DAB-DIGIT-LISTP 16 X) -- see below
  (hexdigitp x)
  :true-listp t
  :elementp-of-nil nil)

(defthmd equality ; equality theorem
  (equal (dab-digit-listp 16 x)
         (hexdigit-listp x))
  :hints (("Goal" :in-theory (enable dab-digit-listp dab-digitp))))

(defmacro check-redundant-theorems () ; check generated theorems
  '(must-be-redundant
    (progn
      (defthm hexdigit-listp-of-nat=>bendian*
        (hexdigit-listp (nat=>bendian* 16 nat)))
      (defthm hexdigit-listp-of-nat=>bendian+
        (hexdigit-listp (nat=>bendian+ 16 nat)))
      (defthm hexdigit-listp-of-nat=>bendian
        (hexdigit-listp (nat=>bendian 16 width nat)))
      (defthm hexdigit-listp-of-nat=>lendian*
        (hexdigit-listp (nat=>lendian* 16 nat)))
      (defthm hexdigit-listp-of-nat=>lendian+
        (hexdigit-listp (nat=>lendian+ 16 nat)))
      (defthm hexdigit-listp-of-nat=>lendian
        (hexdigit-listp (nat=>lendian 16 width nat))))))

(must-succeed*
 (defthm-dab-return-types equality hexdigit-listp-of)
 (check-redundant-theorems))

(must-succeed*
 (defthm-dab-return-types equality hexdigit-listp-of
   :topic nat-hexdigits-return-types)
 (check-redundant-theorems))

(must-succeed*
 (defthm-dab-return-types equality hexdigit-listp-of
   :topic nat-hexdigits-return-types
   :parents (digits-any-base))
 (check-redundant-theorems))

(must-succeed*
 (defthm-dab-return-types equality hexdigit-listp-of
   :topic nat-hexdigits-return-types
   :parents (digits-any-base)
   :short "Additional return type theorems.")
 (check-redundant-theorems))

(must-succeed*
 (defthm-dab-return-types equality hexdigit-listp-of
   :topic nat-hexdigits-return-types
   :short "Additional return type theorems.")
 (check-redundant-theorems))

(must-succeed*
 (defthm-dab-return-types equality hexdigit-listp-of
   :topic nat-hexdigits-return-types
   :parents (digits-any-base)
   :short "Additional return type theorems."
   :long "<p>These are for hexadecimal digits.</p>")
 (check-redundant-theorems))

(must-succeed*
 (defthm-dab-return-types equality hexdigit-listp-of
   :topic nat-hexdigits-return-types
   :short "Additional return type theorems."
   :long "<p>These are for hexadecimal digits.</p>")
 (check-redundant-theorems))
