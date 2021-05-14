; Tools to convert hex chars and strings to bytes
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)

;; Returns (mv erp val)
(defund hex-char-to-val (char)
  (declare (xargs :guard (characterp char)))
  (let ((code (char-code char)))
    (if (and (<= 48 code)
             (<= code 57))
        ;; digit 0-9
        (mv nil (- code 48))
      (if (and (<= 65 code)
               (<= code 70))
          ;; capital A-F
          (mv nil (+ 10 (- code 65)))
        (if (and (<= 97 code)
                 (<= code 102))
            ;; lowercase a-f
            (mv nil (+ 10 (- code 97)))
          (mv :bad-digit 0))))))

(defthm natp-of-mv-nth-1-of-hex-char-to-val
  (natp (mv-nth 1 (hex-char-to-val char)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable hex-char-to-val))))

(defthm <-16-of-mv-nth-1-of-hex-char-to-val
  (< (mv-nth 1 (hex-char-to-val char)) 16)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable hex-char-to-val))))

;; Returns (mv erp val)
(defund hex-chars-to-bytes (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (true-listp acc))))
  (if (endp chars)
      (mv nil (reverse acc))
    (if (endp (rest chars))
        (mv :odd-number-of-chars nil)
      (b* ((first-char (first chars))
           (second-char (second chars))
           ((mv erp first-char-value)
            (hex-char-to-val first-char))
           ((when erp) (mv erp nil))
           ((mv erp second-char-value)
            (hex-char-to-val second-char))
           ((when erp) (mv erp nil))
           (byte (+ (* 16 first-char-value)
                    second-char-value)))
        (hex-chars-to-bytes (rest (rest chars))
                            (cons byte acc))))))

(defthm all-unsigned-byte-p-of-mv-nth-1-of-hex-chars-to-bytes
  (implies (all-unsigned-byte-p 8 acc)
           (all-unsigned-byte-p 8 (mv-nth 1 (hex-chars-to-bytes chars acc))))
  :hints (("Goal" :in-theory (enable hex-chars-to-bytes unsigned-byte-p))))

(defthm true-listp-of-mv-nth-1-of-hex-chars-to-bytes
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (hex-chars-to-bytes chars acc))))
  :hints (("Goal" :in-theory (enable hex-chars-to-bytes))))

;; Returns (mv erp val)
(defund hex-string-to-bytes (s)
  (declare (xargs :guard (stringp s)))
  (let ((chars (coerce s 'list)))
    (hex-chars-to-bytes chars nil)))

(defthm all-unsigned-byte-p-of-mv-nth-1-of-hex-string-to-bytes
  (all-unsigned-byte-p 8 (mv-nth 1 (hex-string-to-bytes s)))
  :hints (("Goal" :in-theory (enable hex-string-to-bytes))))

(defthm true-listp-of-mv-nth-1-of-hex-string-to-bytes
  (true-listp (mv-nth 1 (hex-string-to-bytes s)))
  :hints (("Goal" :in-theory (enable hex-string-to-bytes))))

;; Suppresses any errors.
(defund hex-string-to-bytes! (s)
  (declare (xargs :guard (stringp s)))
  (mv-let (erp val)
    (hex-string-to-bytes s)
    (declare (ignore erp))
    val))
