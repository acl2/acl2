; A utility to split a list of characters at a given char
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; Returns (mv foundp chars-before chars-after).
(defund split-chars-aux (chars char acc)
  (declare (xargs :measure (len chars)
                  :guard (and (character-listp chars)
                              (characterp char)
                              (character-listp acc))))
  (if (endp chars)
      (mv nil ; CHAR not found
          (reverse acc)
          nil)
    (if (eql (first chars) char)
        ;; found an occurrence of CHAR:
        (mv t (reverse acc) (rest chars))
      (split-chars-aux (rest chars) char (cons (first chars) acc)))))

(defthmd split-chars-aux-correct-1
  (implies (and (member char chars) ;this case
                (character-listp chars)
                (character-listp acc))
           (and (mv-nth 0 (split-chars-aux chars char acc)) ; foundp
                (equal (append (mv-nth 1 (split-chars-aux chars char acc))
                               (list char)
                               (mv-nth 2 (split-chars-aux chars char acc)))
                       (append (reverse acc) chars))))
  :hints (("Goal" :in-theory (enable split-chars-aux
                                     equal-of-append))))

(defthmd split-chars-aux-correct-2
  (implies (and (not (member char chars)) ;this case
                (character-listp chars)
                (characterp char)
                (character-listp acc))
           (and (not (mv-nth 0 (split-chars-aux chars char acc))) ; not found
                (equal (mv-nth 1 (split-chars-aux chars char acc))
                       (append (reverse acc) chars))
                (equal (mv-nth 2 (split-chars-aux chars char acc))
                       nil)))
  :hints (("Goal" :in-theory (enable split-chars-aux
                                     equal-of-append))))

(defthm booleanp-of-mv-nth-0-of-split-chars-aux
  (booleanp (mv-nth 0 (split-chars-aux chars char acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable split-chars-aux))))

(defthm character-listp-of-mv-nth-1-of-split-chars-aux
  (implies (and (character-listp chars)
                (character-listp acc))
           (character-listp (mv-nth 1 (split-chars-aux chars char acc))))
  :hints (("Goal" :in-theory (enable split-chars-aux))))

(defthm character-listp-of-mv-nth-2-of-split-chars-aux
  (implies (and (character-listp chars)
                (character-listp acc))
           (character-listp (mv-nth 2 (split-chars-aux chars char acc))))
  :hints (("Goal" :in-theory (enable split-chars-aux))))

(defthm <=-of-len-of-mv-nth-2-of-split-chars-aux
  (<= (len (mv-nth 2 (split-chars-aux chars char acc)))
      (len chars))
  :hints (("Goal" :in-theory (enable split-chars-aux))))

(defthm <-of-len-of-mv-nth-2-of-split-chars-aux
  (implies (mv-nth 0 (split-chars-aux chars char acc))
           (< (len (mv-nth 2 (split-chars-aux chars char acc)))
              (len chars)))
  :hints (("Goal" :in-theory (enable split-chars-aux))))

;; Splits the CHARS into two parts, the characters before the first occurence
;; of CHAR and the characters after the first occurrence of CHAR.  Returns (mv
;; foundp chars-before chars-after).  If CHAR does not occur in CHARS, FOUNDP
;; will be nil, CHARS-BEFORE will contain all the chars, and CHARS-AFTER will
;; be nil.
(defund split-chars (chars char)
  (declare (xargs :guard (and (character-listp chars)
                              (characterp char))))
  (split-chars-aux chars char nil))

;; Example: (split-chars '(#\a #\b #\c #\d #\e) #\c)
;; Example: (split-chars '(#\a #\b #\c #\d #\e) #\X)

(defthm booleanp-of-mv-nth-0-of-split-chars
  (booleanp (mv-nth 0 (split-chars chars char)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable split-chars))))

(defthm character-listp-of-mv-nth-1-of-split-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (split-chars chars char))))
  :hints (("Goal" :in-theory (enable split-chars))))

(defthm character-listp-of-mv-nth-2-of-split-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (split-chars chars char))))
  :hints (("Goal" :in-theory (enable split-chars))))

(defthm <=-of-len-of-mv-nth-2-of-split-chars
  (<= (len (mv-nth 2 (split-chars chars char)))
      (len chars))
  :hints (("Goal" :in-theory (enable split-chars))))

(defthm <-of-len-of-mv-nth-2-of-split-chars
  (implies (mv-nth 0 (split-chars chars char))
           (< (len (mv-nth 2 (split-chars chars char)))
              (len chars)))
  :hints (("Goal" :in-theory (enable split-chars))))

(defthmd split-chars-correct-1
  (implies (and (member char chars) ;this case
                (character-listp chars))
           (and (mv-nth 0 (split-chars chars char)) ; foundp
                (equal (append (mv-nth 1 (split-chars chars char))
                               (list char)
                               (mv-nth 2 (split-chars chars char)))
                       chars)))
  :hints (("Goal" :use (:instance split-chars-aux-correct-1
                                  (acc nil))
           :in-theory (e/d (split-chars) (split-chars-aux-correct-1)))))

(defthmd split-chars-correct-2
  (implies (and (not (member char chars)) ;this case
                (character-listp chars)
                (characterp char))
           (and (not (mv-nth 0 (split-chars chars char))) ; not found
                (equal (mv-nth 1 (split-chars chars char)) chars)
                (equal (mv-nth 2 (split-chars chars char)) nil)))
  :hints (("Goal" :use (:instance split-chars-aux-correct-2
                                  (acc nil))
           :in-theory (e/d (split-chars) (split-chars-aux-correct-1)))))
