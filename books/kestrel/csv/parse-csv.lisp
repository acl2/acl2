; A parser for CSV (comma-separated value) data
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also parse-csv-file.lisp.

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable mv-nth)))

;; Returns (mv extended-acc chars).  Reads through the closing quote, which
;; must exist and is not included in the result.
(defun parse-quoted-part-of-csv-item (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (character-listp acc))))
  (if (endp chars)
      (prog2$ (er hard? 'parse-quoted-part-of-csv-item "No closing quote found.")
              (mv nil nil))
    (let ((char (first chars))
          (chars (rest chars)))
      (if (eql #\" char)
          (if (and (consp chars)
                   (eql #\" (first chars)))
              ;; two double-quotes represent an escaped double-quote and do not end the quoted part:
              (parse-quoted-part-of-csv-item (rest chars) ; skip the second double-quote
                                             (cons #\" acc))
            ;; a single double-quote indicates the end of the quoted part:
            (mv acc ; not reversed, since there may be more of the item to read (todo: can this happen?)
                chars))
        ;; not a double-quote, so this char is part of the quoted string:
        (parse-quoted-part-of-csv-item chars (cons char acc))))))

(local
 (defthm <=-of-len-of-mv-nth-1-of-parse-quoted-part-of-csv-item
   (<= (len (mv-nth 1 (parse-quoted-part-of-csv-item chars acc)))
       (len chars))
   :rule-classes :linear))

(local
 (defthm <-of-len-of-mv-nth-1-of-parse-quoted-part-of-csv-item
   (implies (consp chars)
            (< (len (mv-nth 1 (parse-quoted-part-of-csv-item chars acc)))
               (len chars)))
   :rule-classes :linear))

(local
 (defthm character-listp-of-mv-nth-0-of-parse-quoted-part-of-csv-item
   (implies (and (character-listp chars)
                 (character-listp acc))
            (character-listp (mv-nth 0 (parse-quoted-part-of-csv-item chars acc))))
   :hints (("Goal" :in-theory (enable parse-quoted-part-of-csv-item)))))

(local
 (defthm character-listp-of-mv-nth-1-of-parse-quoted-part-of-csv-item
   (implies (character-listp chars)
            (character-listp (mv-nth 1 (parse-quoted-part-of-csv-item chars acc))))
   :hints (("Goal" :in-theory (enable parse-quoted-part-of-csv-item)))))

;; Returns (mv item-chars chars eolp).  Reads an item, through a comma or LF/CRLF or end of file.
;; TODO: What about newlines?
(defun parse-csv-item (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (character-listp acc))
                  :measure (len chars)))
  (if (endp chars)
      (mv (reverse acc) nil t)
    (let ((char (first chars)))
      (if (eql #\, char) ; end of the item
          (mv (reverse acc)
              (rest chars) ; skip the comma
              nil)
        (if (eql #\Newline char) ; end of the line (LF), so end of the item too
            (mv (reverse acc)
                (rest chars) ;consume the LF
                t)
          (if (and (eql #\Return char) ; end of the line (CRLF), so end of the item too
                   (consp (rest chars))
                   (eql #\Newline (second chars))
                   )
              (mv (reverse acc)
                  (rest (rest chars)) ; consume the CRLF
                  t)
            (if (eql #\" char)
                (mv-let (acc chars)
                  (parse-quoted-part-of-csv-item (rest chars) acc)
                  ;; TODO: this assumes there may be more chars after the quoted part
                  (parse-csv-item chars acc))
              ;; normal char:
              (parse-csv-item (rest chars) (cons char acc)))))))))

(local
 (defthm <=-of-len-of-mv-nth-1-of-parse-csv-item
   (<= (len (mv-nth 1 (parse-csv-item chars acc)))
       (len chars))
   :rule-classes :linear))

(local
 (defthm <-of-len-of-mv-nth-1-of-parse-csv-item
   (implies (consp chars)
            (< (len (mv-nth 1 (parse-csv-item chars acc)))
               (len chars)))
   :rule-classes :linear))

(local
 (defthm not-mv-nth-2-of-parse-csv-item-forward
   (implies (not (mv-nth 2 (parse-csv-item chars acc)))
            (consp chars))
   :rule-classes :forward-chaining))

;; (local
;;  (defthm <-of-len-of-mv-nth-1-of-parse-csv-item-2
;;    (implies (mv-nth 2 (parse-csv-item chars acc))
;;             (< (len (mv-nth 1 (parse-csv-item chars acc)))
;;                (len chars)))
;;    :rule-classes :linear))

(local
 (defthm character-listp-of-mv-nth-0-of-parse-csv-item
   (implies (and (character-listp chars)
                 (character-listp acc))
            (character-listp (mv-nth 0 (parse-csv-item chars acc))))
   :hints (("Goal" :in-theory (enable parse-csv-item)))))

(local
 (defthm character-listp-of-mv-nth-1-of-parse-csv-item
   (implies (character-listp chars)
            (character-listp (mv-nth 1 (parse-csv-item chars acc))))
   :hints (("Goal" :in-theory (enable parse-csv-item)))))

;; Returns (mv line chars).
(defun parse-csv-line (chars items-acc)
  (declare (xargs :guard (and (character-listp chars)
                              (true-listp items-acc))
                  :measure (len chars)))
  (mv-let (item-chars chars eolp) ; may be empty (e.g., if the line has just a CRLF)
    (parse-csv-item chars nil)
    (let ((items-acc (cons (coerce item-chars 'string) items-acc)))
      (if eolp
          (mv (reverse items-acc)
              chars)
        (parse-csv-line chars items-acc)))))

(local
 (defthm <=-of-len-of-mv-nth-1-of-parse-csv-line
   (<= (len (mv-nth 1 (parse-csv-line chars acc)))
       (len chars))
   :rule-classes :linear))

(local
 (defthm character-listp-of-mv-nth-1-of-parse-csv-line
   (implies (character-listp chars)
            (character-listp (mv-nth 1 (parse-csv-line chars acc))))
   :hints (("Goal" :in-theory (enable parse-csv-line)))))

(local
 (defthm character-listp-of-mv-nth-0-of-parse-csv-line
   (implies (true-listp acc)
            (true-listp (mv-nth 0 (parse-csv-line chars acc))))
   :hints (("Goal" :in-theory (enable parse-csv-line)))))

;; Returns a list of lines
(defun parse-csv-lines (chars lines-acc)
  (declare (xargs :guard (and (character-listp chars)
                              (true-list-listp lines-acc))
                  :measure (len chars)))
  (if (endp chars)
      (reverse lines-acc)
    (mv-let (line chars)
      (parse-csv-line chars nil)
      (parse-csv-lines chars (cons line lines-acc)))))

(defun parse-csv (chars)
  (declare (xargs :guard (character-listp chars)))
  (parse-csv-lines chars nil))
