; Tools to convert hex chars and to values
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

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
