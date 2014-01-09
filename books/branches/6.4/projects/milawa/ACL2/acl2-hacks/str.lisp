;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")
(include-book "str/top" :dir :system)

;; We introduce some string manipulation functions.  Note that we do not do
;; much with strings, so we have not tried to make these functions efficient.
;; Beware of trying to use them on larger data sets.
;;
;; We might eventually want to try to submit something like this to the ACL2
;; distribution.

(defun __cat-list (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (stringp (car x))
          (string-append (car x) (__cat-list (cdr x)))
        (__cat-list (cdr x)))
    ""))


(encapsulate
 ()
 (defun __pad-number-triple (x)
   ;; X is a list of characters which are an exploded number between 0 and 999.
   ;; Our job is to pad the number with leading zeroes (if necessary) so that it
   ;; has three digits, e.g., "3" becomes "003", "14" becomes "014", etc.
   (declare (xargs :guard t))
   (let ((len (len x)))
     (cond ((equal len 1) (cons #\0 (cons #\0 x)))
           ((equal len 2) (cons #\0 x))
           (t             x))))

 (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

 (local (defthm lemma
          (implies (character-listp ans)
                   (character-listp (explode-nonnegative-integer n base ans)))))

 (defun __pretty-number-aux (n)
   ;; We produce a list of the triples and commas, in reverse order of how they
   ;; should be printed
   (declare (xargs :guard t))
   (let ((n (nfix n)))
     (if (< n 1000)
         ;; No padding for the leading digits
         (list (coerce (explode-atom n 10) 'string))
       (cons (coerce (__pad-number-triple (explode-atom (mod n 1000) 10)) 'string)
             (cons "," (__pretty-number-aux (floor n 1000)))))))

 (defun pretty-number (n)
   (declare (xargs :guard t))
   (__cat-list (reverse (__pretty-number-aux n)))))



(defun character-list-fix (x)
  (declare (xargs :guard t))
  (if (character-listp x)
      x
    nil))

(defund string-fix (x)
  (declare (xargs :guard t))
  (cond ((stringp x)
         x)
        ((natp x)
         (pretty-number x))
        ((integerp x)
         (string-append "-" (pretty-number (- x))))
        (t
         "")))

(defund string-list-fix (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (string-fix (car x))
            (string-list-fix (cdr x)))
    nil))

(defthm string-listp-of-string-list-fix
  (equal (string-listp (string-list-fix x))
         t)
  :hints(("Goal" :in-theory (enable string-list-fix))))

(defun cat-list (strings)
  ;; Concatenates a list of strings and natural numbers
  (declare (xargs :guard t))
  (string-append-lst (string-list-fix strings)))

(defun cat-list-with-separator (strings sep)
  ;; Concatenates the strings together, inserting the separator between each one
  (declare (xargs :guard t))
  (if (consp strings)
      (if (consp (cdr strings))
          (string-append (string-fix (car strings))
                         (string-append (string-fix sep)
                                        (cat-list-with-separator (cdr strings) sep)))
        (string-fix (car strings)))
    ""))

;; This used to be STR::cat, but I renamed it for compatibility with the ACL2
;; string library.

(defmacro ncat (&rest strings)
  `(cat-list (list ,@strings)))

(defmacro sep (separator &rest strings)
  `(cat-list-with-separator (list ,@strings) ,separator))





(defun prefixp (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (prefixp (cdr x) (cdr y)))
    t))

;; (defun implode (char-list)
;;   ;; Coerces a character list into a string
;;   (declare (xargs :guard t))
;;   (coerce (character-list-fix char-list) 'string))

;; (defun explode (string)
;;   ;; Coerces a string into a character list
;;   (declare (xargs :guard t))
;;   (coerce (string-fix string) 'list))

(defun explode-list (x)
  ;; Coerces a string list into a "character list list"
  (declare (xargs :guard t))
  (if (consp x)
      (cons (explode (string-fix (car x)))
            (explode-list (cdr x)))
    nil))



(defun char-list-replace (old new char-list)
  ;; Replace a single character with a new one throughout a character list
  (declare (xargs :mode :program))
  (if (consp char-list)
      (cons (if (equal (car char-list) old)
                new
              (car char-list))
            (char-list-replace old new (cdr char-list)))
    nil))

(defun char-list-replace-char-list (old new char-list)
  ;; Replaces all occurrences of "old" with "new" throughout char-list
  (declare (xargs :mode :program))
  (if (prefixp old char-list)
      (append new
              (char-list-replace-char-list old new (nthcdr (len old) char-list)))
    (if (consp char-list)
        (cons (car char-list)
              (char-list-replace-char-list old new (cdr char-list)))
      nil)))

(defun char-list-replace-patterns (char-list patterns)
  ;; Patterns is an alist of (old char-list . new char-list) entires.  We
  ;; replace all old char-lists with new ones throughout char-list.  The
  ;; replacements are done "one after another", so beware of inadvertent
  ;; capture
  (declare (xargs :mode :program))
  (if (consp patterns)
      (char-list-replace-patterns
       (char-list-replace-char-list (car (car patterns))
                                    (cdr (car patterns))
                                    char-list)
       (cdr patterns))
    char-list))

(defun string-replace-patterns (string patterns)
  ;; Patterns is an alist of (old . new) entries, where old and new are
  ;; strings.  We replace all substrings matching old with new.  The
  ;; replacements are done "one after another", so beware of inadvertent
  ;; capture
  (declare (xargs :mode :program))
  (implode (char-list-replace-patterns (explode string)
                                       (pairlis$ (explode-list (strip-cars patterns))
                                                 (explode-list (strip-cdrs patterns))))))


