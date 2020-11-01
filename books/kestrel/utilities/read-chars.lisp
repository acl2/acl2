; Utilities to read from lists of characters
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(local (in-theory (disable mv-nth)))

;;; TODO: Combine this with readthroughterminator-aux, etc.

;read characters up to but not including TERMINATOR
;returns (mv chars-before-item rest-chars)
(defund read-chars-to-terminator-aux (char-lst terminator acc)
  (declare (xargs :measure (len char-lst)
                  :guard (and (character-listp char-lst)
                              (characterp terminator)
                              (character-listp acc))))
  (if (endp char-lst)
      (mv (reverse acc) nil)
    (if (eql (car char-lst) terminator)
        (mv (reverse acc) char-lst)
      (read-chars-to-terminator-aux (cdr char-lst) terminator (cons (car char-lst) acc)))))

(defthm character-listp-of-mv-nth-0-of-read-chars-to-terminator-aux
  (implies (and (character-listp chars)
                (character-listp acc))
           (character-listp (mv-nth 0 (read-chars-to-terminator-aux chars terminator acc))))
  :hints (("Goal" :in-theory (enable read-chars-to-terminator-aux))))

(defthm character-listp-of-mv-nth-1-of-read-chars-to-terminator-aux
  (implies (and (character-listp chars)
                (character-listp acc))
           (character-listp (mv-nth 1 (read-chars-to-terminator-aux chars terminator acc))))
  :hints (("Goal" :in-theory (enable read-chars-to-terminator-aux))))

(defthm true-listp-of-mv-nth-0-of-read-chars-to-terminator-aux
  (implies (true-listp acc)
           (true-listp (mv-nth 0 (read-chars-to-terminator-aux chars terminator acc))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable read-chars-to-terminator-aux))))

(defthm true-listp-of-mv-nth-1-of-read-chars-to-terminator-aux
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (read-chars-to-terminator-aux chars terminator acc))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable read-chars-to-terminator-aux))))

(defthm read-chars-to-terminator-aux-len-bound
  (<= (len (mv-nth 1 (read-chars-to-terminator-aux chars terminator acc)))
      (+ (len chars) (len acc)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable read-chars-to-terminator-aux))))

;returns (mv chars-before-item rest-chars)
(defund read-chars-to-terminator (char-lst terminator)
  (declare (xargs :guard (and (character-listp char-lst)
                              (characterp terminator))))
  (read-chars-to-terminator-aux char-lst terminator nil))

;(READ-CHARS-TO-TERMINATOR '(#\a #\b #\c #\d #\e) #\c)

(defthm character-listp-of-mv-nth-0-of-read-chars-to-terminator
  (implies (character-listp chars)
           (character-listp (mv-nth 0 (read-chars-to-terminator chars terminator))))
  :hints (("Goal" :in-theory (enable read-chars-to-terminator))))

(defthm character-listp-of-mv-nth-1-of-read-chars-to-terminator
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (read-chars-to-terminator chars terminator))))
  :hints (("Goal" :in-theory (enable read-chars-to-terminator))))

(defthm true-listp-of-mv-nth-0-of-read-chars-to-terminator
  (true-listp (mv-nth 0 (read-chars-to-terminator chars terminator)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable read-chars-to-terminator))))

(defthm true-listp-of-mv-nth-1-of-read-chars-to-terminator
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (read-chars-to-terminator chars terminator))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable read-chars-to-terminator))))

(defthm read-chars-to-terminator-len-bound
  (<= (len (mv-nth 1 (read-chars-to-terminator chars terminator)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable read-chars-to-terminator))))
