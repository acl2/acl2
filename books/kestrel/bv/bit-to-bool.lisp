; Theorems about bit-to-bool
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See bit-to-bool-def.lisp for the definition of bit-to-bool.

(include-book "bit-to-bool-def")
(include-book "bitnot")
(include-book "bitand")
(include-book "kestrel/booleans/booland" :dir :system)

;; The BITNOT is turned into a NOT.
(defthm bit-to-bool-of-bitnot
  (implies (unsigned-byte-p 1 x)
           (equal (bit-to-bool (bitnot x))
                  (not (bit-to-bool x))))
  :hints (("Goal" :in-theory (enable bit-to-bool))))

;; The BITNOT is turned into a NOT.
;; This version has no hyps.
(defthm bit-to-bool-of-bitnot-strong
  (equal (bit-to-bool (bitnot x))
         ;; the getbit here should go away if X is a bit:
         (not (bit-to-bool (getbit 0 x))))
  :hints (("Goal" :in-theory (enable bit-to-bool))))

;; The BITAND is turned into a BOOLAND (we use BOOLAND because AND in ACL2 is a
;; macro).
(defthm bit-to-bool-of-bitand
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (bit-to-bool (bitand x y))
                  (booland (bit-to-bool x)
                           (bit-to-bool y))))
  :hints (("Goal" :in-theory (enable bit-to-bool))))

;; The BITAND is turned into a BOOLAND (we use BOOLAND because AND in ACL2 is a
;; macro).
;; This version has no hyps.
(defthm bit-to-bool-of-bitand-strong
  (equal (bit-to-bool (bitand x y))
         ;; the getbits here should go away if X is a bit:
         (booland (bit-to-bool (getbit 0 x))
                  (bit-to-bool (getbit 0 y))))
  :hints (("Goal" :in-theory (enable bit-to-bool))))
