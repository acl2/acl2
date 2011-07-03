; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

; names.lisp
;
; This file defines XDOC functions for displaying symbol names and generating
; file names for symbols.  Normally you should not need to include this file
; directly, but it may be useful if you are writing macros to directly generate
; XDOC topics.

(in-package "XDOC")
(include-book "str/strsubst" :dir :system)
(program)


; ----------------- File Name Generation ------------------------

; Symbol names need to be escaped for many file systems to deal with them.  We
; replace colons with two underscores, and funny characters become _[code],
; somewhat like url encoding.

(defun funny-char-code (x acc)
  (declare (type character x))
  (let* ((code  (char-code x))
         (high  (ash code -4))
         (low   (logand code #xF)))
    (list* (digit-to-char high)
           (digit-to-char low)
           acc)))

(defun file-name-mangle-aux (x n xl acc)
  (declare (type string x))
  (if (= n xl)
      acc
    (let ((char (char x n)))
      (cond ((or (and (char<= #\a char) (char<= char #\z))
                 (and (char<= #\A char) (char<= char #\Z))
                 (and (char<= #\0 char) (char<= char #\9))
                 (eql char #\-)
                 (eql char #\.))
             (file-name-mangle-aux x (+ n 1) xl (cons char acc)))
            ((eql char #\:)
             (file-name-mangle-aux x (+ n 1) xl (revappend '(#\_ #\_) acc)))
            (t
             (file-name-mangle-aux x (+ n 1) xl (funny-char-code char (cons #\_ acc))))))))

(defun file-name-mangle (x acc)

; Our "standard" for generating safe file names from symbols.  The mangled
; characters are accumulated onto acc in reverse order.  We always use the full
; package and the symbol name when creating file names.

  (declare (type symbol x))
  (let ((str (concatenate 'string
                          (symbol-package-name x)
                          "::"
                          (symbol-name x))))
    (file-name-mangle-aux str 0 (length str) acc)))



; ----------------- Displaying Symbols --------------------------

; We imagine the reader of the documentation wants to view the world from some
; BASE-PKG (which we pass around as a symbol).  When he reads about a symbol
; that is in this package, he doesn't want to see the PKG:: prefix.  But when
; he reads about symbols from other packages, he needs to see the prefix.

(defun in-package-p (sym base-pkg)

; We don't just ask if the symbol-package-names of sym and base-pkg are equal,
; because this would fail to account for things like COMMON-LISP::car versus
; ACL2::foo.

  (equal (intern-in-package-of-symbol (symbol-name sym) base-pkg)
         sym))

(defun simple-html-encode-chars (x acc)

; X is a character list that we copy into acc (in reverse order), except that
; we escape any HTML entities like < into the &lt; format.

  (if (atom x)
      acc
    (let ((acc (case (car x)
                 (#\< (list* #\; #\t #\l #\& acc))         ;; "&lt;" (in reverse)
                 (#\> (list* #\; #\t #\g #\& acc))         ;; "&gt;"
                 (#\& (list* #\; #\p #\m #\a #\& acc))     ;; "&amp;"
                 (#\" (list* #\; #\t #\o #\u #\q #\& acc)) ;; "&quot;"
                 (t   (cons (car x) acc)))))
      (simple-html-encode-chars (cdr x) acc))))

;(reverse (coerce (simple-html-encode-chars '(#\a #\< #\b) nil) 'string))
;(reverse (coerce (simple-html-encode-chars '(#\a #\> #\b) nil) 'string))
;(reverse (coerce (simple-html-encode-chars '(#\a #\& #\b) nil) 'string))
;(reverse (coerce (simple-html-encode-chars '(#\a #\" #\b) nil) 'string))


(defun sneaky-downcase (x)
  (let ((down (string-downcase x)))
    (str::strsubst "acl2" "ACL2" down)))

;(sneaky-downcase "SILLY-ACL2-TUTORIAL")


(defun sym-mangle (x base-pkg acc)

; This is our "standard" for displaying symbols in HTML (in lowercase).  We
; write the package part only if it is not the same as the base package.
; Characters to print are accumulated onto acc in reverse order.  BOZO think
; about adding keyword support?

  (let* ((pkg-low  (string-downcase (symbol-package-name x)))
         (name-low (sneaky-downcase (symbol-name x)))
         (acc (if (in-package-p x base-pkg)
                  acc
                (list* #\: #\:
                       (simple-html-encode-chars (coerce pkg-low 'list) acc)))))
    (simple-html-encode-chars (coerce name-low 'list) acc)))

(defun upcase-first-letter (x)
  (declare (type string x))
  (if (equal x "")
      x
    (concatenate 'string
                 (coerce (list (char-upcase (char x 0))) 'string)
                 (subseq x 1 nil))))

(defun sym-mangle-cap (x base-pkg acc)

; Same as sym-mangle, but upper-case the first letter.

    (if (in-package-p x base-pkg)
        (let* ((name-low (sneaky-downcase (symbol-name x)))
               (name-cap (upcase-first-letter name-low)))
          (simple-html-encode-chars (coerce name-cap 'list) acc))
      (let* ((pkg-low (string-downcase (symbol-package-name x)))
             (pkg-cap (upcase-first-letter pkg-low))
             (name-low (sneaky-downcase (symbol-name x)))
             (acc (list* #\: #\: (simple-html-encode-chars (coerce pkg-cap 'list) acc))))
        (simple-html-encode-chars (coerce name-low 'list) acc))))


; (reverse (coerce (sym-mangle 'acl2 'acl2::foo nil) 'string))
; (reverse (coerce (sym-mangle 'acl2-tutorial 'acl2::foo nil) 'string))
