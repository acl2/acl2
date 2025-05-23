; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "execution")

(local (include-book "ihs/logops-lemmas" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests in the form of theorems
; that include a mix of symbolic and concrete data.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Register x0 always contains 0.

(defruled read-xreg-unsigned-of-x0
  (equal (read-xreg-unsigned 0 stat feat)
         0)
  :enable (read-xreg-unsigned))

(defruled read-xreg-signed-of-x0
  (equal (read-xreg-signed 0 stat feat)
         0)
  :enable (read-xreg-signed
           read-xreg-unsigned-of-x0))

(defruled read-xreg-unsigned32-of-x0
 (equal (read-xreg-unsigned32 0 stat feat)
        0)
 :enable (read-xreg-unsigned32
          read-xreg-unsigned-of-x0))

(defruled read-xreg-signed32-of-x0
  (equal (read-xreg-signed32 0 stat feat)
         0)
  :enable (read-xreg-signed32
           read-xreg-unsigned-of-x0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Writing to register x0 has no effect.

(defruled write-xreg-of-x0
  (equal (write-xreg 0 val stat feat)
         (stat-fix stat))
  :enable write-xreg)

(defruled write-xreg-32-of-x0
  (equal (write-xreg-32 0 val stat feat)
         (stat-fix stat))
  :enable (write-xreg-32
           write-xreg-of-x0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add more
