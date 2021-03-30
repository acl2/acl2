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

;; For n down to 1, add constants and evisc tuples for -(2^n) mod the prime.
;; This covers both equivalent forms of each value that might arise (the
;; positive one that is a field element, and the negative one obtained by
;; subtracting p from that).
(defun add-evisc-tuples-for-negated-powers-of-2 (n prime)
  (declare (xargs :guard (and (natp n)
                              (natp prime)
                              (< (expt 2 n) prime))))
  (if (zp n)
      nil
    (let* ((fep-val (pfield::neg (expt 2 n) prime))
           (neg-val (- fep-val prime))
           (base-name (concatenate 'string "-2^" (acl2::nat-to-string n)))
           (fep-defconst-name (acl2::pack$ '* base-name '*))
           (neg-defconst-name (acl2::pack$ '* base-name '-neg*)))
      (append `((defconst ,fep-defconst-name ',fep-val)
                (defconst ,neg-defconst-name ',neg-val)
                (table acl2::evisc-table ,fep-val ,(concatenate 'string "#.acl2::" (symbol-name fep-defconst-name)))
                ;; also handle equivalent negative numbers:
                (table acl2::evisc-table ,neg-val ,(concatenate 'string "#.acl2::" (symbol-name neg-defconst-name))))
              (add-evisc-tuples-for-negated-powers-of-2 (+ -1 n) prime)))))

;; For n down to 1, add constants and evisc tuples for 1/(2^n) mod the prime.
;; This covers both equivalent forms of each value that might arise (the
;; positive one that is a field element, and the negative one obtained by
;; subtracting p from that).
(defun add-evisc-tuples-for-inverse-powers-of-2 (n prime)
  (declare (xargs :guard (and (natp n)
                              (natp prime)
                              (< (expt 2 n) prime))))
  (if (zp n)
      nil
    (let* ((fep-val (pfield::inv (expt 2 n) prime))
           (neg-val (- fep-val prime))
           (base-name (concatenate 'string "1/2^" (acl2::nat-to-string n)))
           (fep-defconst-name (acl2::pack$ '* base-name '*))
           (neg-defconst-name (acl2::pack$ '* base-name '-neg*)))
      (append `((defconst ,fep-defconst-name ',fep-val)
                (defconst ,neg-defconst-name ',neg-val)
                (table acl2::evisc-table ,fep-val ,(concatenate 'string "#.acl2::" (symbol-name fep-defconst-name)))
                ;; also handle equivalent negative numbers:
                (table acl2::evisc-table ,neg-val ,(concatenate 'string "#.acl2::" (symbol-name neg-defconst-name))))
              (add-evisc-tuples-for-inverse-powers-of-2 (+ -1 n) prime)))))

;; For n down to 1, add constants and evisc tuples for -1/(2^n) mod the prime.
;; This covers both equivalent forms of each value that might arise (the
;; positive one that is a field element, and the negative one obtained by
;; subtracting p from that).
(defun add-evisc-tuples-for-negated-inverse-powers-of-2 (n prime)
  (declare (xargs :guard (and (natp n)
                              (natp prime)
                              (< (expt 2 n) prime))))
  (if (zp n)
      nil
    (let* ((fep-val (pfield::neg (pfield::inv (expt 2 n) prime) prime))
           (neg-val (- fep-val prime)) ;; equivalent value
           (base-name (concatenate 'string "-1/2^" (acl2::nat-to-string n)))
           (fep-defconst-name (acl2::pack$ '* base-name '*))
           (neg-defconst-name (acl2::pack$ '* base-name '-neg*)))
      (append `((defconst ,fep-defconst-name ',fep-val)
                (defconst ,neg-defconst-name ',neg-val)
                (table acl2::evisc-table ,fep-val ,(concatenate 'string "#.acl2::" (symbol-name fep-defconst-name)))
                ;; also handle equivalent negative numbers:
                (table acl2::evisc-table ,neg-val ,(concatenate 'string "#.acl2::" (symbol-name neg-defconst-name))))
              (add-evisc-tuples-for-negated-inverse-powers-of-2 (+ -1 n) prime)))))
