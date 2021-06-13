; A fast, lightweight function to read a file's contents into a character list
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (in-theory (disable read-file-into-string2)))

;; Returns a character list, or nil if the file does not exist.
(defund read-file-into-character-list-fn (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (let ((string (read-file-into-string filename)))
    (if (not string)
        nil
      (coerce string 'list))))

(defthm character-listp-of-read-file-into-character-list-fn
  (character-listp (read-file-into-character-list-fn filename state))
  :hints (("Goal" :in-theory (enable read-file-into-character-list-fn))))

;; Returns a character list, or nil if the file does not exist.
;; May be faster than read-file-characters from std/io.
;; Note that this does not return state (see :doc read-file-into-string
;; for an explanation).
(defmacro read-file-into-character-list (filename)
  `(read-file-into-character-list-fn ,filename state))
