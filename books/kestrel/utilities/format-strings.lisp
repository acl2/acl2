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

(include-book "forms")
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/add-to-set-equal" :dir :system))

;; (defund skip-chars-through-right-bracket (chars whole-string)
;;   (declare (xargs :guard (character-listp chars)))
;;   (if (endp chars)
;;       (cw "Bad format string (missing right bracket): ~x0" whole-string)
;;     (if (eql #\] (first chars))
;;         (rest chars)
;;       (skip-chars-through-right-bracket (rest chars) whole-string))))

;; (local
;;  (defthm <=-of-len-of-skip-chars-through-right-bracket
;;    (<= (len (skip-chars-through-right-bracket chars whole-string))
;;        (len chars))
;;    :rule-classes :linear
;;    :hints (("Goal" :in-theory (enable skip-chars-through-right-bracket)))))

;; (local
;;  (defthm character-listp-of-skip-chars-through-right-bracket
;;    (implies (character-listp chars)
;;             (character-listp (skip-chars-through-right-bracket chars whole-string)))
;;    :hints (("Goal" :in-theory (enable skip-chars-through-right-bracket)))))

;; Returns the list of characters (each between #\0 and #\9) mentioned in
;; format directives like ~x0 or ~Y01.
(defun args-in-format-string-aux (chars bracket-depth whole-string)
  (declare (xargs :guard (and (character-listp chars)
                              (stringp whole-string)
                              (natp bracket-depth))
                  :verify-guards nil ; done below
                  ;:hints (("Goal" :in-theory (enable skip-chars-through-right-bracket)))
                  :measure (len chars)))
  (if (endp chars)
      nil
    (if (not (eql #\~ (first chars)))
        (args-in-format-string-aux (rest chars) bracket-depth whole-string)
      (let ((second-char (first (rest chars))))
        (case second-char
          ;; skip over ~%, ~ followed by newline, etc:
          ((#\Space #\Newline #\% #\| #\~ #\-)
           (args-in-format-string-aux (rest (rest chars)) bracket-depth whole-string))
          ((#\x #\y #\@ #\* #\& #\v #\n #\N #\t #\c #\f #\F #\s #\S #\_
            #\p #\q ;; these two are deprecated (see below)
            )
           (prog2$
            (and (member second-char '(#\p #\q))
                 ;; TODO: Add an option to suppress this:
                 (cw "Note: Deprecated command ~x0 used in format-string ~x1.~%" second-char whole-string))
            (if (endp (rest (rest chars)))
                (cw "ERROR: Bad format string: ~x0~%." whole-string) ;todo: print the context with things like this
              (let ((third-char (third chars)))
                (add-to-set-eql third-char
                                (args-in-format-string-aux (rest (rest (rest chars)))
                                                           bracket-depth
                                                           whole-string))))))
          ((#\X #\Y
            #\P #\Q ;; these two are deprecated (see below)
            )
           (prog2$
            (and (member second-char '( #\P #\Q))
                 ;; TODO: Add an option to suppress this:
                 (cw "Note: Deprecated command ~x0 used in format-string ~x1.~%" second-char whole-string))
            (if (or (endp (rest (rest chars)))
                    (endp (rest (rest (rest chars)))))
                (cw "ERROR: Bad format string: ~x0~%." whole-string)
              (let ((third-char (third chars))
                    (fourth-char (fourth chars)))
                (add-to-set-eql third-char
                                (add-to-set-eql fourth-char
                                                (args-in-format-string-aux (rest (rest (rest (rest chars))))
                                                                           bracket-depth
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
                     (add-to-set-eql third-char
                                     (args-in-format-string-aux (rest (rest (rest (rest (rest chars)))))
                                                                (+ 1 bracket-depth)
                                                                whole-string))))))
          (#\/ ; can only appear within a bracket
           (if (posp bracket-depth)
               (args-in-format-string-aux (rest (rest chars)) bracket-depth whole-string)
             (cw "ERROR: Bad format string (\~~\ not within \~~#x\~~[ ... ]): ~x0~%." whole-string)))

          (#\] ; can only appear within a bracket and ends (one-level of) bracketing
           (if (posp bracket-depth)
               (args-in-format-string-aux (rest (rest chars)) (+ -1 bracket-depth) whole-string)
             (cw "ERROR: Bad format string (\~~] not within \~~#x\~~[ ... ]): ~x0~%." whole-string)))

          (t (cw "(Unexpected format directive in ~x0 starting at ~x1.)~%" whole-string chars)))))))

(defthm true-listp-of-args-in-format-string-aux
  (true-listp (args-in-format-string-aux chars bracket-depth whole-string))
  :hints (("Goal" :in-theory (enable args-in-format-string-aux))))

(verify-guards args-in-format-string-aux)

;; Returns the list of characters (each between #\0 and #\9) mentioned in
;; format directives like ~x0 or ~Y01.
(defun args-in-format-string (str)
  (declare (xargs :guard (stringp str)))
  (let ((chars (coerce str 'list)))
    (args-in-format-string-aux chars 0 str)))
