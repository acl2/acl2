; Some checks on format strings
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "kestrel/utilities/forms" :dir :system)
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(defun skip-chars-through-right-bracket (chars whole-string)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      (cw "Bad format string (missing right bracket): ~x0" whole-string)
    (if (eql #\] (first chars))
        (rest chars)
      (skip-chars-through-right-bracket (rest chars) whole-string))))

;; Returns the list of characters (each between #\0 and #\9) mentioned in
;; format directives like ~x0 or ~Y01.
(defun args-in-format-string-aux (chars whole-string)
  (declare (xargs :guard (and (character-listp chars)
                              (stringp whole-string))))
  (if (endp chars)
      nil
    (if (not (eql #\~ (first chars)))
        (args-in-format-string-aux (rest chars) whole-string)
      (let ((second-char (first (rest chars))))
        (case second-char
          ;; skip over ~%, ~ followed by newline, etc:
          ((#\Space #\Newline #\% #\| #\~ #\-)
           (args-in-format-string-aux (rest (rest chars)) whole-string))
          ;; TODO: Add support for ~#x~...
          ((#\x #\y #\@ #\* #\& #\v #\n #\N #\t #\c #\f #\F #\s #\S #\_
            #\p #\q ;; these two are deprecated
            )
           (if (endp (rest (rest chars)))
               (cw "ERROR: Bad format string: ~x0~%." whole-string) ;todo: print the context with things like this
             (let ((third-char (third chars)))
               (if (not (member third-char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))
                   (cw "ERROR: Bad format string: ~x0~%." whole-string)
                 (cons third-char
                       (args-in-format-string-aux (rest (rest (rest chars)))
                                                  whole-string))))))
          ((#\X #\Y
            #\P #\Q ;; these two are deprecated
            )
           (if (or (endp (rest (rest chars)))
                   (endp (rest (rest (rest chars)))))
               (cw "ERROR: Bad format string: ~x0~%." whole-string)
             (let ((third-char (third chars))
                   (fourth-char (fourth chars)))
               (if (or (not (member third-char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))
                       (not (member fourth-char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))))
                   (cw "ERROR: Bad format string: ~x0~%." whole-string)
                 (cons third-char
                       (cons fourth-char
                             (args-in-format-string-aux (rest (rest (rest (rest chars))))
                                                        whole-string)))))))
          ;; special handling for ~#x~[ ... ]
          (#\# (if (or (endp (rest (rest chars)))
                       (endp (rest (rest (rest chars))))
                       (endp (rest (rest (rest (rest chars))))))
                   (cw "ERROR: Bad format string: ~x0~%." whole-string)
                 (let ((third-char (third chars))
                       (fourth-char (fourth chars))
                       (fifth-char (fifth chars)))
                   (if (not (and (eql #\~ fourth-char)
                                 (eql #\[ fifth-char)))
                       (cw "ERROR: Bad format string: ~x0~%." whole-string)
                     (cons third-char
                           (args-in-format-string-aux (skip-chars-through-right-bracket chars whole-string) whole-string))))))
          (t (er hard? 'args-in-format-string-aux "(Unexpected format directive in ~x0.)" whole-string))
          )))))

;; Returns the list of characters (each between #\0 and #\9) mentioned in
;; format directives like ~x0 or ~Y01.
(defun args-in-format-string (str)
  (declare (xargs :guard (stringp str)))
  (let ((chars (coerce str 'list)))
    (args-in-format-string-aux chars str)))
