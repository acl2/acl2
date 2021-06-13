; Convert hex chars to a unicode code point
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/hex-char-to-val" :dir :system)
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))

(local
 (defthm <=-of-ash-of-mv-nth-1-of-hex-char-to-val
   (implies (and (natp x)
                 (natp c))
            (<= (ash (mv-nth 1 (hex-char-to-val char1)) c)
                (* 15 (expt 2 c))))
   :rule-classes :linear))

;; Convert 4 chars representing hex digits into a Unicode code point in the
;; range U+0000 through U+FFFF (the basic multilingual plane).
;; Returns (mv erp code-point) where code-point is a natural number.
(defund hex-digit-chars-to-code-point (char1 ;most significant
                                          char2
                                          char3
                                          char4 ;least significant
                                          )
  (declare (xargs :guard (and (characterp char1)
                              (characterp char2)
                              (characterp char3)
                              (characterp char4))))
  (mv-let (erp val1)
    (hex-char-to-val char1)
    (if erp
        (mv erp 0)
      (mv-let (erp val2)
        (hex-char-to-val char2)
        (if erp
            (mv erp 0)
          (mv-let (erp val3)
            (hex-char-to-val char3)
            (if erp
                (mv erp 0)
              (mv-let (erp val4)
                (hex-char-to-val char4)
                (if erp
                    (mv erp 0)
                  (mv nil ; no error
                      ;; each val is 4 bits:
                      (+ (ash val1 12)
                         (ash val2 8)
                         (ash val3 4)
                         val4)))))))))))

(defthm natp-of-mv-nth-1-of-hex-digit-chars-to-code-point
  (natp (mv-nth 1 (hex-digit-chars-to-code-point char1 char2 char3 char4)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable hex-digit-chars-to-code-point))))

(defthm <-of-mv-nth-1-of-hex-digit-chars-to-code-point
  (< (mv-nth 1 (hex-digit-chars-to-code-point char1 char2 char3 char4))
     65536)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable hex-digit-chars-to-code-point))))
