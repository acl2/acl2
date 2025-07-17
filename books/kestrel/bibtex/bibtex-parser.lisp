; Parses BibTeX files and creates alist representations of the file
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Aakash Koneru (akitaki79 on GitHub)

(in-package "ACL2")

; necessary books
(local
  (include-book "std/strings/top" :dir :system)
  )

(include-book "std/io/read-file-characters" :dir :system)

; Helper functions for string processing

(defun whitespace-char-p (c)
  "Check if character is whitespace and/or comma"
  (declare (xargs :guard (characterp c)))
  (member c '(#\Space #\Tab #\Newline #\Return #\,)))

(defun skip-whitespace (str pos)
  "Skip whitespace characters starting from position pos"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))
                  :measure (nfix (- (length str) pos))))
  (if (or (not (mbt (natp pos)))
          (>= pos (length str))
          (not (whitespace-char-p (char str pos))))
      pos
    (skip-whitespace str (+ 1 pos))))

(defun find-char (str c start-pos)
  "Find the position of character c in string str starting from start-pos"
  (declare (xargs :guard (and (stringp str)
                              (characterp c)
                              (natp start-pos)
                              (<= start-pos (length str)))
                  :measure (nfix (- (length str) start-pos))))
  (if (or (>= start-pos (length str))
          (not (mbt (natp start-pos))))
      nil
    (if (equal (char str start-pos) c)
        start-pos
      (find-char str c (1+ start-pos)))))


(defun find-matching-brace-helper (str pos brace-count)
  "Helper for find-matching-brace"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str))
                              (natp brace-count))
                  :measure (nfix (- (length str) pos))))
  (if (mbt (natp pos))
      (if (or (>= pos (length str)) (= brace-count 0))
          (if (= brace-count 0)
              pos
            nil)
        (let ((c (char str pos)))
          (cond ((equal c #\{)
                 (find-matching-brace-helper str (1+ pos) (1+ brace-count)))
                ((equal c #\})
                 (find-matching-brace-helper str (1+ pos) (1- brace-count)))
                (t
                  (find-matching-brace-helper str (1+ pos) brace-count)))))
    nil))

(defun find-matching-brace (str start-pos)
  "Find the position of the matching closing brace"
  (declare (xargs :guard (and (stringp str)
                              (natp start-pos)
                              (< start-pos (length str))
                              (equal (char str start-pos) #\{))))
  (find-matching-brace-helper str (1+ start-pos) 1))

(defun trim-whitespace-left (chars)
  "Remove leading whitespace characters"
  (declare (xargs :guard (character-listp chars)))
  (if (or (endp chars) (not (whitespace-char-p (car chars))))
      chars
    (trim-whitespace-left (cdr chars))))

(defthm trim-whitespace-left-preserves-character-listp
  (implies (character-listp chars)
           (character-listp (trim-whitespace-left chars))))

(local
  (defthm reverse-preserves-character-listp
    (implies (character-listp chars)
             (character-listp (reverse chars))))
  )

(defun trim-string (str)
  "Remove leading and trailing whitespace"
  (declare (xargs :guard (stringp str)))
  (let* ((chars (coerce str 'list))
         (trimmed-left (trim-whitespace-left chars))
         (trimmed-both (reverse (trim-whitespace-left (reverse trimmed-left)))))
    (coerce trimmed-both 'string)))

;lemmas
(defthm find-char-upper-bound
  (implies (and (stringp str)
                (characterp c)
                (natp start-pos)
                (<= start-pos (length str))
                (find-char str c start-pos))
           (and (natp (find-char str c start-pos))
                (<= (find-char str c start-pos) (length str)))))

(defthm find-char-lower-bound
  (implies (and (stringp str)
                (characterp c)
                (natp start-pos)
                (<= start-pos (length str))
                (find-char str c start-pos))
           (<= start-pos (find-char str c start-pos))))

(local
  (defthm len-of-explode-is-length
    (implies (stringp str)
             (equal (len (explode str)) (length str)))
    :rule-classes (:forward-chaining))
  )

; BibTeX entry parsing functions

(defun parse-bibtex-entry-type (str pos)
  "Parse the entry type (e.g., @article, @inproceedings)"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (< pos (length str))
                              (equal (char str pos) #\@))))
  (let* ((start-pos (1+ pos))
         (brace-pos (find-char str #\{ start-pos)))
    (if brace-pos
        (let ((entry-type (trim-string (subseq str start-pos brace-pos))))
          (mv entry-type (1+ brace-pos)))
      (mv nil nil))))

(defun parse-bibtex-key (str pos)
  "Parse the citation key"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))))
  (let* ((start-pos (skip-whitespace str pos))
         (comma-pos (find-char str #\, start-pos)))
    (if (and comma-pos (> comma-pos start-pos))
        (let ((key (trim-string (subseq str start-pos comma-pos))))
          (mv key (1+ comma-pos)))
      (mv nil nil))))


(defun parse-field-name (str pos)
  "Parse a field name (before the = sign)"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))))
  (let* ((start-pos (skip-whitespace str pos))
         (eq-pos (find-char str #\= start-pos)))
    (if (and eq-pos
             (< eq-pos (length str))
             (> eq-pos start-pos))
        (let ((field-name (trim-string (subseq str start-pos eq-pos))))
          (mv field-name (1+ eq-pos)))
      (mv nil nil))))

(defthm parse-field-name-position-bounds
  (implies (and (stringp str)
                (natp pos)
                (<= pos (length str))
                (mv-nth 1 (parse-field-name str pos)))
           (and (natp (mv-nth 1 (parse-field-name str pos)))
                (<= (mv-nth 1 (parse-field-name str pos)) (length str)))))

(defun find-unquoted-delimiter (str pos)
  "Find comma or closing brace that ends an unquoted value"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))
                  :measure (nfix (- (length str) pos))))
  (if (or (not (natp pos)) (>= pos (length str)))
      pos
    (let ((c (char str pos)))
      (if (or (equal c #\,) (equal c #\}) (equal c #\Newline))
          pos
        (find-unquoted-delimiter str (1+ pos))))))

(defun parse-unquoted-value (str pos)
  "Parse an unquoted field value"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))))
  (let ((end-pos (find-unquoted-delimiter str pos)))
    (if end-pos
        (let ((value (trim-string (subseq str pos end-pos))))
          (mv value end-pos))
      (mv nil nil))))

;more lemmas
(defthm skip-whitespace-returns-natp
  (implies (and (stringp str)
                (natp pos)
                (<= pos (length str)))
           (natp (skip-whitespace str pos))))

(defthm skip-whitespace-upper-bound
  (implies (and (stringp str)
                (natp pos)
                (<= pos (length str)))
           (<= (skip-whitespace str pos) (length str))))

(defthm skip-whitespace-lower-bound
  (implies (and (stringp str)
                (natp pos)
                (<= pos (length str)))
           (<= pos (skip-whitespace str pos))))

(defthm find-matching-brace-helper-upper-bound
  (implies (and (stringp str)
                (natp pos)
                (<= pos (length str))
                (natp brace-count)
                (find-matching-brace-helper str pos brace-count))
           (<= (find-matching-brace-helper str pos brace-count) (length str))))

(defthm find-matching-brace-helper-lower-bound
  (implies (and (stringp str)
                (natp pos)
                (<= pos (length str))
                (natp brace-count)
                (> brace-count 0)
                (find-matching-brace-helper str pos brace-count))
           (<= pos (find-matching-brace-helper str pos brace-count))))

(defthm find-char-plus-one-bound
  (implies (and (stringp str)
                (characterp c)
                (natp start-pos)
                (<= start-pos (length str))
                (find-char str c start-pos))
           (<= (1+ (find-char str c start-pos))
               (length str))))

(defthm find-char-returns-correct-char
  (implies (and (stringp str)
                (characterp c)
                (natp start-pos)
                (<= start-pos (length str))
                (find-char str c start-pos))
           (equal (nth (find-char str c start-pos)
                       (explode str))
                  c)))

(defthm find-char-strict-upper-bound
  (implies (and (stringp str)
                (characterp c)
                (natp start-pos)
                (<= start-pos (length str))
                (find-char str c start-pos))
           (< (find-char str c start-pos)
              (length str))))

(defun parse-field-value (str pos)
  "Parse a field value (after the = sign)"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))))
  (let ((start-pos (skip-whitespace str pos)))
    (if (>= start-pos (length str))
        (mv nil nil)
      (let ((first-char (char str start-pos)))
        (cond ((equal first-char #\{)
               ;; Braced value - find the closing brace position
               (let ((end-pos (find-matching-brace str start-pos)))
                 (if (and end-pos
                          (natp end-pos)
                          (> end-pos start-pos)
                          (<= end-pos (length str)))
                     (let ((inner-start (1+ start-pos))
                           (inner-end (1- end-pos)))
                       (if (and (natp inner-end)
                                (>= inner-end inner-start)
                                (<= inner-end (length str)))
                           (let ((value (subseq str inner-start inner-end)))
                             (mv value end-pos))
                         (mv nil nil)))
                   (mv nil nil))))
              ((equal first-char #\")
               ;; Quoted value
               (let ((end-pos (find-char str #\" (1+ start-pos))))
                 (if end-pos
                     (let ((value (subseq str (1+ start-pos) end-pos)))
                       (mv value (1+ end-pos)))
                   (mv nil nil))))
              (t
                ;; Unquoted value (until comma or closing brace)
                (parse-unquoted-value str start-pos)))))))


(defun end-of-fields? (str pos)
  (declare (xargs :guard (and (stringp str)
                              (natp pos))))
  (or (>= pos (length str))
      (equal (nth pos (explode str)) #\})))

(defun parse-one-field (str pos)
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))))
  (mv-let (field-name name-end-pos)
          (parse-field-name str pos)
    (if (and field-name name-end-pos)
        (mv-let (field-value value-end-pos)
                (parse-field-value str name-end-pos)
          (mv field-name field-value value-end-pos))
      (mv nil nil nil))))

(defun parse-bibtex-fields-helper (str pos)
  (declare (xargs :measure (nfix (- (length str) pos))
                  :hints (("Goal" :in-theory (disable end-of-fields? parse-one-field)))
                  :guard t))
  (if (or (not (natp pos))
          (not (stringp str))
          (>= pos (length str))
          (end-of-fields? str pos))
      (mv nil pos)
    (mv-let (field-name field-value next-pos)
            (parse-one-field str pos)
      (if (and field-name field-value next-pos (natp next-pos) (< pos next-pos))
          ;; Successful parse - continue recursively
          (mv-let (rest-fields final-pos)
                  (parse-bibtex-fields-helper str next-pos)
            (mv (cons (cons field-name field-value) rest-fields)
                final-pos))
        ;; Failed parse - skip one character and try again
        (parse-bibtex-fields-helper str (1+ pos))))))

(defun parse-bibtex-fields (str)
  "Parse all fields in a BibTeX entry"
  (declare (xargs :guard (stringp str)))
  (mv-let (fields x)
          (parse-bibtex-fields-helper str 0)
    (declare (ignore x))
    fields))

(defun parse-single-bibtex-entry (str pos)
  "Parse a single complete BibTeX entry starting at position pos"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))))
  (let ((at-pos (find-char str #\@ pos)))
    (if (or (not (natp pos))
            (not (stringp str))
            (>= pos (length str))
            (not at-pos))
        (mv nil nil nil)  ; No entry found
      (mv-let (entry-type type-end-pos)
              (parse-bibtex-entry-type str at-pos)
        (if (and entry-type type-end-pos)
            (mv-let (key key-end-pos)
                    (parse-bibtex-key str type-end-pos)
              (if (and key key-end-pos)
                  (let ((closing-brace-pos (find-matching-brace str (1- type-end-pos))))
                    (if (and closing-brace-pos
                             (natp closing-brace-pos)
                             (<= key-end-pos closing-brace-pos)  ; Explicit bounds check
                             (<= closing-brace-pos (length str)))
                        (let* ((fields-str (subseq str key-end-pos closing-brace-pos))
                               (fields (parse-bibtex-fields fields-str))
                               (entry (list (cons "type" entry-type)
                                            (cons "key" key)
                                            (cons "fields" fields))))
                          (mv key entry (1+ closing-brace-pos)))
                      (mv nil nil nil)))
                (mv nil nil nil)))
          (mv nil nil nil))))))

(defun find-next-bibtex-entry (str pos)
  "Find the position of the next @ symbol that starts a BibTeX entry"
  (declare (xargs :guard (and (stringp str)
                              (natp pos)
                              (<= pos (length str)))
                  :measure (nfix (- (length str) pos))))
  (let ((at-pos (find-char str #\@ pos)))
    (if (not at-pos)
        nil
      ;; Check if this @ is followed by a valid entry type
      (let ((after-at (1+ at-pos)))
        (if (>= after-at (length str))
            nil
          ;; Look for opening brace to confirm this is a valid entry
          (let ((brace-pos (find-char str #\{ after-at)))
            (if brace-pos
                at-pos
              ;; Keep looking for the next @
              (find-next-bibtex-entry str (1+ at-pos)))))))))

;this guard verification proof is very slow
(defun parse-bibtex-entries-from-positions (str positions)
  "Parse BibTeX entries starting at the given positions"
  (declare (xargs :guard (and (stringp str)
                              (nat-listp positions))))
  (if (endp positions)
      nil
    (if (<= (car positions) (length str))  ; Explicit bounds check
        (mv-let (key entry next-pos)
                (parse-single-bibtex-entry str (car positions))
          (declare (ignore next-pos))
          (if (and key entry)
              (cons (cons key entry)
                    (parse-bibtex-entries-from-positions str (cdr positions)))
            (parse-bibtex-entries-from-positions str (cdr positions))))
        ; Skip out-of-bounds positions
      (parse-bibtex-entries-from-positions str (cdr positions)))))

(defun find-all-at-positions (str pos acc)
  "Find all positions of @ symbols in the string"
  (declare (xargs :measure (nfix (- (length str) pos))
                  :guard (and (stringp str)
                              (natp pos)
                              (nat-listp acc))))
  (if (>= pos (length str))
      (reverse acc)
    (let ((at-pos (find-char str #\@ pos)))
      (if at-pos
          (find-all-at-positions str (1+ at-pos) (cons at-pos acc))
        (reverse acc)))))

(defthm find-all-at-positions-returns-nat-listp
  (implies (and (stringp str)
                (natp pos)
                (nat-listp acc))
           (nat-listp (find-all-at-positions str pos acc)))
  :hints (("Goal" :in-theory (enable rev))))

(defun parse-bibtex-entries-simple (str)
  "Simpler version that finds all @ positions first, then parses each"
  (declare (xargs :guard (stringp str)))
  (parse-bibtex-entries-from-positions str (find-all-at-positions str 0 nil)))

(defun parse-bibtex-file (filename state)
  "Parse a BibTeX file and return an alist from citation keys to entries"
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (mv-let (contents state)
          (read-file-as-string filename state)
    (if (stringp contents)
        (mv (parse-bibtex-entries-simple contents) state)
      (mv nil state))))
