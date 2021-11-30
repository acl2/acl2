; Misc string utilities
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in string-utilities.lisp

;; TODO: Split this book

(include-book "read-chars")
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable mv-nth)))

(local (in-theory (enable <-of-0-and-len)))

;this used to deal with strings, but it seemed nicer to use lists of chars
;terminator may often be #\;
;takes a list of chars and a terminator and returns (mv <chars-before-terminator> <chars-after-terminator>)
;; Returns (mv chars-before-terminator chars-after-terminator).
(defund readthroughterminator-aux (char-lst terminator)
  (declare (xargs ; :mode :program
            :measure (len char-lst)
            :guard (character-listp char-lst)
            ))
  (if (endp char-lst)
      (mv (er hard? 'readthroughterminator-aux "Found the end of the string but no terminator (looking for: ~x0)" terminator)
          nil)
    (if (eql (car char-lst) terminator)
        (mv nil (cdr char-lst)) ;return the empty char-list and consume the terminator
      (mv-let (val char-lst2)
              (readthroughterminator-aux (cdr char-lst) terminator)
              (mv (cons (car char-lst) val)
                  char-lst2)))))

(defthm character-listp-of-mv-nth-0-of-readthroughterminator-aux
  (implies (character-listp char-list)
           (character-listp (mv-nth 0 (readthroughterminator-aux char-list terminator))))
  :hints (("Goal" :in-theory (enable readthroughterminator-aux))))

(defthm character-listp-of-mv-nth-1-of-readthroughterminator-aux
  (implies (character-listp char-list)
           (character-listp (mv-nth 1 (readthroughterminator-aux char-list terminator))))
  :hints (("Goal" :in-theory (enable readthroughterminator-aux))))

(defthm len-of-mv-nth-1-of-readthroughterminator-aux-bound
  (<= (len (mv-nth 1 (readthroughterminator-aux chars terminator)))
      (len chars))
  :hints (("Goal" :in-theory (enable readthroughterminator-aux))))

;returns (mv stringbeforeterminator stringafterterminator)
(defund readthroughterminator (str terminator)
  (declare (xargs :guard (and (stringp str)
                              (characterp terminator))))
  (mv-let (val rest)
    (readthroughterminator-aux (coerce str 'list) terminator)
    (mv (coerce val 'string) (coerce rest 'string))))

(defthm stringp-of-mv-nth-0-of-readthroughterminator
  (implies (stringp str)
           (stringp (mv-nth 0 (readthroughterminator str char))))
  :hints (("Goal" :in-theory (enable readthroughterminator))))

(defthm stringp-of-mv-nth-1-of-readthroughterminator
  (implies (stringp str)
           (stringp (mv-nth 1 (readthroughterminator str char))))
  :hints (("Goal" :in-theory (enable readthroughterminator))))

(defund substring-before-terminator (str terminator)
  (declare (xargs :guard (and (stringp str)
                              (characterp terminator))))
  (mv-let (chars-before chars-after)
    (readthroughterminator-aux (coerce str 'list) terminator)
    (declare (ignore chars-after))
    (coerce chars-before 'string)))

;(local (assert-equal (substring-before-terminator "abcde" #\c) "ab"))

(defund substring-after-terminator (str terminator)
  (declare (xargs :guard (and (stringp str)
                              (characterp terminator))))
  (mv-let (chars-before chars-after)
    (readthroughterminator-aux (coerce str 'list) terminator)
    (declare (ignore chars-before))
    (coerce chars-after 'string)))

;(local (assert-equal (substring-after-terminator "abcde" #\c) "de"))

(defun empty-stringp (str)
  (declare (xargs :guard t))
  (equal "" str))

(defun non-empty-stringp (str)
  (declare (xargs :guard t))
  (and (stringp str)
       (not (empty-stringp str))))

(defthmd consp-when-true-listp
  (implies (true-listp x)
           (equal (consp x)
                  (not (equal x nil)))))

(defthm coerce-injective
  (implies (and (equal (coerce x 'list) (coerce y 'list))
                (stringp x)
                (stringp y))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable COERCE-INVERSE-2)
           :use ((:instance coerce-inverse-2 (x x))
                 (:instance coerce-inverse-2 (x y))))))

;fixme pull out all this string stuff
(defthm consp-of-coerce
  (implies (stringp str)
           (iff (consp (coerce str 'list))
                (not (equal str ""))))
  :hints (("Goal" :in-theory (enable consp-when-true-listp)
           :use ((:instance coerce-injective (x str) (y ""))
                 (:instance completion-of-coerce (x str) (y 'list))))))

(defthm equal-of-len-of-coerce-and-0
  (equal (equal (len (coerce str 'list)) 0)
         (or (not (stringp str))
             (equal "" str)))
  :hints (("Goal" :use consp-of-coerce
           :in-theory (disable consp-of-coerce))))

(local (in-theory (disable nth))) ;fixme

;use this more
(defund strcdr (str)
  (declare (xargs :guard (non-empty-stringp str)))
  (subseq str 1 (length str)))

(defthm stringp-of-strcdr
  (implies (stringp str)
           (stringp (strcdr str)))
  :hints (("Goal" :in-theory (enable strcdr))))

;fixme use more
(defund strcar (str)
  (declare (xargs :guard (non-empty-stringp str)))
  (char str 0))

(defthm characterp-of-strcar
  (implies (and (stringp str)
                (not (equal "" str)))
           (characterp (strcar str)))
  :hints (("Goal" :in-theory (enable strcar))))

;fixme pull out this string stuff into a library

(defthm acl2-count-when-string
  (implies (stringp x)
           (equal (acl2-count x)
                  (length x))))

(defthm stringp-of-subseq
  (implies (stringp seq)
           (stringp (subseq seq start end)))
  :hints (("Goal" :in-theory (enable subseq))))

;(in-theory (enable subseq))

(in-theory (disable position-equal))

(DEFthm COERCE-INVERSE-1-forced
  (IMPLIES (force (CHARACTER-LISTP X))
           (EQUAL (COERCE (COERCE X 'STRING) 'LIST)
                  X)))

(defthm position-equal-ac-bound
  (implies (and (POSITION-EQUAL-ac item lst acc) ;item is present
                )
           (< (POSITION-EQUAL-ac item lst acc)
              (+ acc (len lst))))
  :hints (("Goal" :in-theory (enable position-equal-ac))))

(defthm position-equal-ac-bound-special
  (implies (and (POSITION-EQUAL-ac item lst 0) ;item is present
                )
           (< (POSITION-EQUAL-ac item lst 0)
              (len lst)))
  :hints (("Goal" :use (:instance position-equal-ac-bound (acc 0)))))

(defthm position-equal-bound
  (implies (and (stringp str) ;fixme gen
                (position-equal item str))
           (< (position-equal item str)
              (length str)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance position-equal-ac-bound-special (lst (coerce str 'list)))
           :in-theory (e/d (position-equal) (position-equal-ac-bound-special)))))

(defthm natp-of-position-equal
  (implies (position-equal item lst)
           (natp (position-equal item lst)))
  :hints (("Goal" :in-theory (enable position-equal))))

(defthm position-equal-type
  (or (not (position-equal item lst))
      (natp (position-equal item lst)))
  :rule-classes (:type-prescription))



;returns (mv string-before-char rest-of-string)
(defund split-string-before-char (str char)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (mv-let (chars-before-item rest-chars)
          (read-chars-to-terminator (coerce str 'list) char)
          (mv (coerce chars-before-item 'string)
              (coerce rest-chars 'string))))

(defthm stringp-of-mv-nth-0-of-split-string-before-char
  (stringp (mv-nth 0 (split-string-before-char str char)))
  :hints (("Goal" :in-theory (enable split-string-before-char))))

(defthm stringp-of-mv-nth-1-of-split-string-before-char
  (stringp (mv-nth 1 (split-string-before-char str char)))
  :hints (("Goal" :in-theory (enable split-string-before-char))))

;(split-string-before-char "abcde" #\c)

;; Drop the part of STR up to, but not including, the first occurrence of CHAR.
;; If CHAR does not occur, return the empty string.
(defund drop-string-before-char (str char)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (mv-let (chars-before-item rest-chars)
    (read-chars-to-terminator (coerce str 'list) char)
    (declare (ignore chars-before-item))
    (coerce rest-chars 'string)))

;(local (assert-equal (drop-string-before-char "abcde" #\c) "cde"))
;(local (assert-equal (drop-string-before-char "abcde" #\X) ""))

(defund substring-before-char (str char)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (mv-let (chars-before-item rest-chars)
    (read-chars-to-terminator (coerce str 'list) char)
    (declare (ignore rest-chars))
    (coerce chars-before-item 'string)))

;(local (assert-equal (substring-before-char "abcde" #\c) "ab"))
;(local (assert-equal (substring-before-char "abcde" #\X) "abcde")) ;is this what we want?


;returns (mv string-up-through-terminator rest-string)
(defund read-string-to-last-terminator (str terminator)
  (declare (xargs :guard (and (stringp str)
                              (characterp terminator))))
  (let ((str-rev (reverse str)))
    (mv-let (string-after-item rest-string)
            (split-string-before-char str-rev terminator)
            (mv (reverse rest-string)
                (reverse string-after-item)))))

(defthm stringp-of-mv-nth-1-of-read-string-to-last-terminator
  (stringp (mv-nth 1 (read-string-to-last-terminator str terminator)))
  :hints (("Goal" :in-theory (enable read-string-to-last-terminator))))

;(read-string-to-last-terminator "abcXdefXghiXjkl" #\X)

;returns the substring of STR before the last occurrence of CHAR
(defund substring-before-last-occurrence (str char)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (let* ((str-rev (reverse str))
         (rev-answer (substring-after-terminator str-rev char)))
    (reverse rev-answer)))

(defthm stringp-of-substring-before-last-occurrence
  (stringp (substring-before-last-occurrence str char))
  :hints (("Goal" :in-theory (enable substring-before-last-occurrence))))

(defund substring-after-last-occurrence (str char)
  (declare (xargs :guard (and (stringp str)
                              (characterp char))))
  (let* ((str-rev (reverse str))
         (rev-answer (substring-before-terminator str-rev char)))
    (reverse rev-answer)))

;(local (assert-equal (substring-before-last-occurrence "ab.cd.ef.gh" #\.) "ab.cd.ef"))

(defund digit-string-range-p (str i j)
  (declare (xargs :guard (and (stringp str)
                              (natp i)
                              (natp j)
                              (<= i (length str))
                              (<= j (length str))
                              (<= i j))
                  :measure (nfix (- (nfix j) (nfix i)))))
  (if (>= (nfix i) (nfix j))
      t
    (and (digit-char-p (char str i))
         (digit-string-range-p str (+ (nfix i) 1) j))))
