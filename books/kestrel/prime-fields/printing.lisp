; Utilities for readable naming and printing of prime field values
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "prime-fields")
(include-book "kestrel/utilities/pack" :dir :system) ;for nat-to-string, todo reduce
(local (include-book "prime-fields-rules"))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; These tools generate symbols in the supplied package, and the printing is
;; done with no package qualifier, so the package supplied should be the
;; package in which you intend to work after running these tools

;; TODO: Remove calls to symbol-name below

;; For N down through STOP, add constants and evisc tuples for (2^n).  For
;; sufficiently large primes, these really don't have much to do with the
;; prime.
(defun add-evisc-tuples-for-powers-of-2 (n stop prime package)
  (declare (xargs :guard (and (natp n)
                              (natp stop)
                              (natp prime)
                              (< (expt 2 n) prime)
                              (stringp package)
                              (not (equal "" package)))))
  (if (or (zp n)
          (< n stop))
      nil
    (let* ((fep-val (mod (expt 2 n) prime))
           ;; (neg-val (- fep-val prime))
           (base-name (concatenate 'string "2^" (acl2::nat-to-string n)))
           (fep-defconst-print-name (concatenate 'string "*" base-name "*"))
           (fep-defconst-name (intern$ fep-defconst-print-name package))
           ;;(neg-defconst-name (intern$ (concatenate 'string "*" base-name "-NEG*") package))
           )
      (append `((defconst ,fep-defconst-name ',fep-val)
                ;;(defconst ,neg-defconst-name ',neg-val)
                (table acl2::evisc-table ,fep-val ,fep-defconst-print-name ;;(concatenate 'string "#.acl2::" fep-defconst-print-name)
                       )
                ;; also handle equivalent negative numbers:
                ;; (table acl2::evisc-table ,neg-val ,(concatenate 'string "#.acl2::" (symbol-name neg-defconst-name)))
                )
              (add-evisc-tuples-for-powers-of-2 (+ -1 n) stop prime package)))))

;; For n down to 1, add constants and evisc tuples for -(2^n) mod the prime.
;; This covers both equivalent forms of each value that might arise (the
;; positive one that is a field element, and the negative one obtained by
;; subtracting p from that).
(defun add-evisc-tuples-for-negated-powers-of-2 (n prime package)
  (declare (xargs :guard (and (natp n)
                              (natp prime)
                              (< (expt 2 n) prime)
                              (stringp package)
                              (not (equal "" package)))))
  (if (zp n)
      nil
    (let* ((fep-val (neg (expt 2 n) prime))
           (neg-val (- fep-val prime))
           (base-name (concatenate 'string "-2^" (acl2::nat-to-string n)))
           (fep-defconst-print-name (concatenate 'string "*" base-name "*"))
           (fep-defconst-name (intern$ fep-defconst-print-name package))
           (neg-defconst-print-name (concatenate 'string "*" base-name "-NEG*"))
           (neg-defconst-name (intern$ neg-defconst-print-name package)))
      (append `((defconst ,fep-defconst-name ',fep-val)
                (defconst ,neg-defconst-name ',neg-val)
                (table acl2::evisc-table ,fep-val ,fep-defconst-print-name)
                ;; also handle equivalent negative numbers:
                (table acl2::evisc-table ,neg-val ,neg-defconst-print-name))
              (add-evisc-tuples-for-negated-powers-of-2 (+ -1 n) prime package)))))

;; For n down to 1, add constants and evisc tuples for 1/(2^n) mod the prime.
;; This covers both equivalent forms of each value that might arise (the
;; positive one that is a field element, and the negative one obtained by
;; subtracting p from that).
(defun add-evisc-tuples-for-inverse-powers-of-2 (n prime package)
  (declare (xargs :guard (and (natp n)
                              (natp prime)
                              (< (expt 2 n) prime)
                              (stringp package)
                              (not (equal "" package)))))
  (if (zp n)
      nil
    (let* ((fep-val (inv (expt 2 n) prime))
           (neg-val (- fep-val prime))
           (base-name (concatenate 'string "1/2^" (acl2::nat-to-string n)))
           (fep-defconst-print-name (concatenate 'string "*" base-name "*"))
           (fep-defconst-name (intern$ fep-defconst-print-name package))
           (neg-defconst-print-name (concatenate 'string "*" base-name "-NEG*"))
           (neg-defconst-name (intern$ neg-defconst-print-name package)))
      (append `((defconst ,fep-defconst-name ',fep-val)
                (defconst ,neg-defconst-name ',neg-val)
                (table acl2::evisc-table ,fep-val ,fep-defconst-print-name)
                ;; also handle equivalent negative numbers:
                (table acl2::evisc-table ,neg-val ,neg-defconst-print-name))
              (add-evisc-tuples-for-inverse-powers-of-2 (+ -1 n) prime package)))))

;; For n down to 1, add constants and evisc tuples for -1/(2^n) mod the prime.
;; This covers both equivalent forms of each value that might arise (the
;; positive one that is a field element, and the negative one obtained by
;; subtracting p from that).
(defun add-evisc-tuples-for-negated-inverse-powers-of-2 (n prime package)
  (declare (xargs :guard (and (natp n)
                              (natp prime)
                              (< (expt 2 n) prime)
                              (stringp package)
                              (not (equal "" package)))))
  (if (zp n)
      nil
    (let* ((fep-val (neg (inv (expt 2 n) prime) prime))
           (neg-val (- fep-val prime)) ;; equivalent value
           (base-name (concatenate 'string "-1/2^" (acl2::nat-to-string n)))
           (fep-defconst-print-name (concatenate 'string "*" base-name "*"))
           (fep-defconst-name (intern$ fep-defconst-print-name package))
           (neg-defconst-print-name (concatenate 'string "*" base-name "-NEG*"))
           (neg-defconst-name (intern$ neg-defconst-print-name package)))
      (append `((defconst ,fep-defconst-name ',fep-val)
                (defconst ,neg-defconst-name ',neg-val)
                (table acl2::evisc-table ,fep-val ,fep-defconst-print-name)
                ;; also handle equivalent negative numbers:
                (table acl2::evisc-table ,neg-val ,neg-defconst-print-name))
              (add-evisc-tuples-for-negated-inverse-powers-of-2 (+ -1 n) prime package)))))
