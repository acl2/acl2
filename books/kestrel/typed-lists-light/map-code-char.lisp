; Turning a list of bytes into the corresponding characters
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)
(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))

;; Converts each of the CODES into its corresponding character.
(defund map-code-char (codes)
  (declare (xargs :guard (byte-listp codes)))
  (if (endp codes)
      nil
    (cons (code-char (first codes))
          (map-code-char (rest codes)))))

(defthm character-listp-of-map-code-char
  (character-listp (map-code-char codes))
  :hints (("Goal" :in-theory (enable map-code-char))))

(defthm len-of-map-code-char
  (equal (len (map-code-char codes))
         (len codes))
  :hints (("Goal" :in-theory (enable map-code-char))))

(defthm map-code-char-of-cons
  (equal (map-code-char (cons code codes))
         (cons (code-char code)
               (map-code-char codes)))
  :hints (("Goal" :in-theory (enable map-code-char))))
