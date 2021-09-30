; Utilities for generating new function names with incremented suffixes
;
; Copyright (C) 2016-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "../../utilities/symbol-has-propsp")
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "std/strings/coerce" :dir :system) ;for explode
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defun numeric-charp (char)
  (declare (xargs :guard (characterp char)))
  (if (member char '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
      t
    nil))

(defun all-numeric-charp (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      t
    (and (numeric-charp (first chars))
         (all-numeric-charp (rest chars)))))

(defun leading-numeric-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      nil
    (if (numeric-charp (first chars))
        (cons (first chars) (leading-numeric-chars (rest chars)))
      nil)))

;(LEADING-NUMERIC-CHARS '(#\1 #\2 #\3 #\A))

(defconst *char-to-value-alist*
  `((#\0 . 0)
    (#\1 . 1)
    (#\2 . 2)
    (#\3 . 3)
    (#\4 . 4)
    (#\5 . 5)
    (#\6 . 6)
    (#\7 . 7)
    (#\8 . 8)
    (#\9 . 9)))

;TTODO Verify guards

(defund parse-int-char (char)
  (declare (xargs :guard (and (characterp char)
                              (numeric-charp char))))
  (cdr (assoc char *char-to-value-alist*)))

;TODO: Does something like this exist somewhere else?
(defun parse-int-chars (chars-rev)
  (declare (xargs :guard (and (character-listp chars-rev)
                              (all-numeric-charp chars-rev))))
  (if (endp chars-rev)
      0
    (+ (parse-int-char (first chars-rev))
       (* 10 (parse-int-chars (rest chars-rev))))))

;(parse-int-chars '(#\1 #\2 #\3)) = 321

(defthm natp-of-parse-int-chars
  (natp (parse-int-chars chars))
  :hints (("Goal" :in-theory (enable parse-int-char))))

(defthm integerp-of-parse-int-chars
  (integerp (parse-int-chars chars))
  :hints (("Goal" :in-theory (enable parse-int-char))))

(defthm non-neg-of-parse-int-chars
  (<= 0 (parse-int-chars chars))
  :rule-classes (( :linear)))

(defthm character-listp-of-leading-numeric-chars
  (implies (character-listp chars)
           (character-listp (leading-numeric-chars chars))))

(defthm all-numeric-charp-leading-numeric-chars
  (all-numeric-charp (leading-numeric-chars chars)))

;drop? ;dup
(defthm character-listp-of-reverse-list
  (implies (character-listp l)
           (character-listp (reverse-list l)))
  :hints (("Goal" :in-theory (enable character-listp reverse-list))))

;returns nil or the numeric suffix (converted to an integer) between the $ and the end of the string NAME.
(defun numeric-suffix-of-name-aux (name separator-char)
  (declare (xargs :guard (symbolp name)))
  (let* ((name-str (symbol-name name))
         (name-chars (explode name-str))
         (rev-name-chars (reverse name-chars))
         (numeric-suffix-rev (leading-numeric-chars rev-name-chars)))
    (if (not numeric-suffix-rev)
        nil
      (if (not (equal separator-char (car (nthcdr (len numeric-suffix-rev) rev-name-chars)))) ;the numeric suffix must be preceded by a dollar sign
          nil
        (parse-int-chars numeric-suffix-rev)))))

(defun numeric-suffix-of-name (name)
  (declare (xargs :guard (symbolp name)))
  (numeric-suffix-of-name-aux name #\$))

;(NUMERIC-SUFFIX-OF-NAME 'foo$1) = 1

(defun chop-through-item (item lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      lst
    (if (equal item (first lst))
        (rest lst)
      (chop-through-item item (rest lst)))))

(defthm true-listp-of-chop-through-item
  (implies (true-listp lst)
           (true-listp (chop-through-item item lst))))

(defthm character-listp-of-chop-through-item
  (implies (character-listp lst)
           (character-listp (chop-through-item item lst))))

;assumes chars include a dollar sign
(defun chop-chars-from-last-separator (chars separator-char)
  (declare (xargs :guard (and (character-listp chars)
                              (characterp separator-char))))
  (reverse (chop-through-item separator-char (reverse chars))))

(defun chop-string-from-last-separator (str separator-char)
  (declare (xargs :guard (and (stringp str)
                              (characterp separator-char))))
  (implode (chop-chars-from-last-separator (explode str) separator-char)))

;this returns a string...
(defun chop-symbol-from-last-separator (sym separator-char)
  (declare (xargs :guard (and (symbolp sym)
                              (characterp separator-char))))
  (chop-string-from-last-separator (symbol-name sym) separator-char))

;this returns a string...
(defun chop-symbol-from-last-dollar (sym)
  (declare (xargs :guard (symbolp sym)))
  (chop-symbol-from-last-separator sym #\$))

;; Increment the $-separated numeric suffix at the end of NAME (if any).  If none, add a suffix of $1.
;; Example: foo -> foo$1, foo$14 -> foo$15
(defun increment-name-suffix (sym)
  (declare (xargs :guard (symbolp sym)))
  (let ((suff (numeric-suffix-of-name sym)))
    (if suff
        (pack$ (chop-symbol-from-last-dollar sym) "$" (+ 1 suff))
      (pack$ sym "$1"))))

(defun increment-name-suffixes (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
      nil
    (cons (increment-name-suffix (first syms))
          (increment-name-suffixes (rest syms)))))

;; (thm (equal (increment-name-suffix 'foo) 'foo$1))
;; (thm (equal (increment-name-suffix 'foo$14) 'foo$15))

(defun increment-name-suffix-safe-aux (sym num-to-try state tries-left)
  (declare (xargs :measure (nfix tries-left)
                  :stobjs state
                  :guard (and (natp tries-left)
                              (natp num-to-try))))
  (if (zp tries-left)
      (hard-error 'increment-name-suffix-safe-aux  "Could not find a fresh name." nil)
    (let ((name (pack$ sym "$" num-to-try)))
      (if (symbol-has-propsp name state)
          ;; there is a clash, so keep looking:
          (increment-name-suffix-safe-aux sym (+ 1 num-to-try) state (+ -1 tries-left))
        name))))

;avoids clashes with existing names
(defun increment-name-suffix-safe (sym state)
  (declare (xargs :stobjs state
                  :guard (symbolp sym)))
  (let* ((suff (numeric-suffix-of-name sym))
         (num-to-try (if suff
                         (+ 1 suff)
                       1)) ;no suiffix, so start with $1
         (base-sym (if suff
                       (chop-symbol-from-last-dollar sym)
                     sym)))
    (increment-name-suffix-safe-aux base-sym num-to-try state 10000)))

;(increment-name-suffix-safe 'foo state)

;TODO: Maybe keep the suffixes in sync (if one has a clash, increment them all past the clashing number and keep looking)?
(defun increment-name-suffixes-safe (syms state)
  (declare (xargs :stobjs state
                  :guard (symbol-listp syms)
                  ))
  (if (endp syms)
      nil
    (cons (increment-name-suffix-safe (first syms) state)
          (increment-name-suffixes-safe (rest syms) state))))

(defthm symbol-listp-of-increment-name-suffixes-safe
  (symbol-listp (increment-name-suffixes-safe syms state)))

(defthm len-of-increment-name-suffixes-safe
  (equal (len (increment-name-suffixes-safe syms state))
         (len syms)))

;; Use new-name unless it is :auto, in which case increment the name suffix.
;; This provides a central place to codify this behavior, in case we want to
;; change it in the future.
(defun pick-new-name (old-name
                      new-name ;a new name or :auto
                      state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp old-name)
                              (symbolp new-name))))
  (if (eq new-name :auto)
      (increment-name-suffix-safe old-name state)
    new-name))

;; Returns an alist.  Handles :auto in the vals of the alist (also checks the
;; values).  Preserves the order of the entries in the alist.
(defun pick-new-names (new-name-alist state)
  (declare (xargs :guard (symbol-alistp new-name-alist)
                  :stobjs state))
  (if (endp new-name-alist)
      new-name-alist
    (let* ((entry (first new-name-alist))
           (old-name (car entry))
           (new-name (cdr entry))) ;might be :auto
      (if (not (symbolp new-name)) ;TODO: Check that it is not already bound and that it is a legal function name
          (er hard? 'pick-new-names "Invalid new name, ~x0, for ~x1." new-name old-name)
        (acons old-name
               (pick-new-name old-name new-name state)
               (pick-new-names (rest new-name-alist) state))))))
