; Turning a list of bytes into the corresponding chars
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/byte-listp" :dir :system)

(defund map-code-char (codes)
  (declare (xargs :guard (byte-listp codes)))
  (if (endp codes)
      nil
    (cons (code-char (first codes))
          (map-code-char (rest codes)))))

(defthm character-listp-of-map-code-char
  (character-listp (map-code-char codes))
  :hints (("Goal" :in-theory (enable map-code-char))))
