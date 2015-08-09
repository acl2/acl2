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

(include-book "std/strings/top" :dir :system)
(include-book "std/util/define" :dir :system)

(defconst *token-separators*
  '(#\+ #\- #\* #\/ #\{ #\} #\( #\) #\[ #\] #\; #\,


    ;; The inclusion of a period means that we are disabling our ability to
    ;; parse floating point numbers for now.

    #\.


    ))

(defconst *whitespace*
  '(#\Space #\Newline))


(define tokenize-string2 ((input character-listp)
                          (curr-chars character-listp)
                          (acc string-listp))

; At some point I'll need to add the ability to recognize decimal numbers.
; This won't be too bad, as I'll be able to look-ahead by looking at the input
; and look-behind by looking at the curr-chars.

  :returns (tokenized-string string-listp :hyp :fguard)
  (cond ((atom input)
         (if (atom curr-chars)
             acc
           (cons (coerce (rev curr-chars) 'string)
                 acc)))
        ((member (car input)
                 *whitespace*)
         (tokenize-string2 (cdr input)
                           nil
                           (if curr-chars
                               (cons (coerce (rev curr-chars) 'string)
                                     acc)
                             acc)))
        ((member (car input)
                 *token-separators*)
         (tokenize-string2 (cdr input)
                           nil
                           (if curr-chars
                               (cons (coerce (list (car input)) 'string)
                                     (cons (coerce (rev curr-chars) 'string)
                                           acc))
                             (cons (coerce (list (car input)) 'string)
                                   acc))))
        (t (tokenize-string2 (cdr input)
                             (cons (car input) curr-chars)
                             acc))))

(define tokenize-string1 ((input stringp))
  :returns (result string-listp :hyp :fguard)

  (rev (tokenize-string2 (coerce input 'list)
                         nil
                         nil))
  :prepwork
  ((defthm lemma
     (implies (string-listp x)
              (string-listp (rev x))))))

(define tokenize-string ((input stringp))
  :returns (result stringp :hyp :fguard)
  (str::join (tokenize-string1 input) " "))
