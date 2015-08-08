; ACL2 Parser for Java
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
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
; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "tools/mv-nth" :dir :system)

(define str-trim-left2 ((char-bag character-listp)
                        (str-chars character-listp))

  :returns (mv (done booleanp :hyp :fguard)
               (thechars character-listp :hyp :fguard))
  :parents (earley-parser)

  (cond ((atom char-bag)
         (mv t str-chars)) ; t is for "done"
        ((equal (car char-bag)
                (car str-chars))
         (mv nil (cdr str-chars)))
        (t
         (str-trim-left2 (cdr char-bag) str-chars))))

(local
 (defthm str-trim-left2-makes-progress
   (implies (and (character-listp char-bag)
                 (character-listp str-chars)
                 (null (mv-nth 0 (str-trim-left2 char-bag str-chars))))
            (< (acl2-count (mv-nth 1 (str-trim-left2 char-bag str-chars)))
               (acl2-count str-chars)))
   :hints (("Goal" :in-theory (enable str-trim-left2)))))

(define str-trim-left1 ((char-bag character-listp)
                        (str-chars character-listp))
  :returns (ans character-listp :hyp :fguard)
  :parents (earley-parser)
  (b* (((when (or (not (character-listp char-bag))
                  (not (character-listp str-chars))))
        (prog2$ (er hard 'str-trim-left1
                    ;; By using hard and verified guards, we are guaranteed
                    ;; that we never enter this branch.
                    "Two arguments to str-trim-left1 were not character-listp")
                str-chars))
       ((mv done str-chars)
        (str-trim-left2 char-bag str-chars)))
    (cond (done str-chars)
          (t (str-trim-left1 char-bag str-chars)))))

(define str-trim-left ((char-bag character-listp)
                       (str stringp))
  :returns (ans stringp :hyp :fguard)
  :parents (earley-parser)
  (coerce (str-trim-left1 char-bag (coerce str 'list)) 'string))

(local
 (defthm rev-returns-character-listp
   (implies (character-listp chars)
            (character-listp (reverse chars)))))

(define str-trim-right1 ((char-list character-listp)
                         (str-chars character-listp))
  :returns (ans character-listp :hyp :fguard)
  :parents (earley-parser)
  (reverse (str-trim-left1 char-list (reverse str-chars))))

(define str-trim-right ((char-bag character-listp)
                        (str stringp))
  :returns (ans stringp :hyp :fguard)
  :parents (earley-parser)
  (coerce (str-trim-right1 char-bag (coerce str 'list)) 'string))

(define str-trim ((char-bag character-listp "Bag of characters to trim from str")
                  (str stringp "String to trim"))
  :returns (ans stringp "Result of trimming the given characters from the ~
                         front and back of the given string")
  :parents (earley-parser)
  (str-trim-right char-bag (str-trim-left char-bag str)))

(define string-fix (x)
  :returns (ans stringp "String version of the input")
  (cond ((stringp x)
         x)
        (t "")))

(define string-fix-with-error (x)
  :returns (ans stringp "String version of the input")
  (cond ((stringp x)
         x)
        (t (prog2$ (er hard? 'string-fix-with-error
                       "Input wasn't a string but: ~x0" x)
                       ""))))
