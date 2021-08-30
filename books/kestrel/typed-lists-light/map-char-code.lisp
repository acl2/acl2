; Turning a list of characters into the corresponding bytes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)

;; todo: move to a book about char-code
(defthm unsigned-byte-p-of-char-code
  (unsigned-byte-p 8 (char-code char))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;; Apply char-code to each element of CHARS, returning a list of bytes
(defund map-char-code (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      nil
    (cons (char-code (first chars))
          (map-char-code (rest chars)))))

(defthm all-unsigned-byte-p-8-of-map-char-code
  (all-unsigned-byte-p 8 (map-char-code chars))
  :hints (("Goal" :in-theory (enable map-char-code))))

(defthm len-of-map-char-code
  (equal (len (map-char-code chars))
         (len chars))
  :hints (("Goal" :in-theory (enable map-char-code))))

(defthm map-char-code-of-cons
  (equal (map-char-code (cons char chars))
         (cons (char-code char)
               (map-char-code chars)))
  :hints (("Goal" :in-theory (enable map-char-code))))
