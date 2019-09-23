; Standard Strings Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/lists/rev" :dir :system)
(include-book "std/strings/cat-base" :dir :system)
(include-book "std/strings/coerce" :dir :system)
(include-book "std/strings/eqv" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define strtok! ((string stringp) (delimiters character-listp))
  :returns (strings string-listp)
  :parents (std/strings-extensions std/strings)
  :short "Variant of @(tsee strtok)
          that does not treat contiguous delimiters as one."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee strtok) treats contiguous delimiters as one,
     and thus it never returns empty strings, e.g.:")
   (xdoc::codeblock
    "(strtok \"abc.de..f\" (list #\\.)) --> (\"abc\" \"de\" \"f\")")
   (xdoc::p
    "In contrast, @('strtok!') considers each delimiter separately,
     possibly returning empty string between contiguous delimiters:")
   (xdoc::codeblock
    "(strtok! \"abc.de..f\" (list #\\.)) --> (\"abc\" \"de\" \"\" \"f\")")
   (xdoc::p
    "The implementation of @('strtok!') is very similar to @(tsee strtok),
     aside from some parameter name changes.
     The main difference is that @('strtok!') omits some tests
     about the (reversed) current token being non-empty:
     in this way, empty tokens are considered and returned.")
   (xdoc::p
    "Note that @('strtok!') returns the singleton list @('(\"\")')
     when given the empty string @('\"\"') as argument.
     This seems to make sense because the beginning and end of the string
     are considered like delimiters,
     and @('strtok!') considers and returns empty strings between delimiters.
     However, it would be easy to change @('strtok!') to return @('nil')
     when given the empty string as argument, if so desired and agreed upon."))
  (b* ((rev-tokens (strtok!-aux string
                                0
                                (mbe :logic (len (explode string))
                                     :exec (length string))
                                delimiters
                                nil
                                nil)))
    (mbe :logic (rev rev-tokens)
         :exec (reverse rev-tokens)))

  :prepwork
  ((define strtok!-aux ((string stringp :type string)
                        (pos natp :type (integer 0 *))
                        (len natp :type (integer 0 *))
                        (delimiters character-listp)
                        (rev-curr-tok character-listp)
                        (acc string-listp))
     :guard (and (<= pos len) (<= len (length string)))
     :returns (result string-listp :hyp (string-listp acc))
     (if (mbe :logic (zp (- (nfix len) (nfix pos)))
              :exec (int= pos len))
         (cons (rchars-to-string rev-curr-tok) acc)
       (b* ((char (char string pos))
            (matchp (member char delimiters)))
         (strtok!-aux (the string string)
                      (the (integer 0 *) (1+ (mbe :logic (nfix pos) :exec pos)))
                      (the (integer 0 *) len)
                      delimiters
                      (if matchp nil (cons char rev-curr-tok))
                      (if matchp
                          (cons (rchars-to-string rev-curr-tok) acc)
                        acc))))
     :measure (nfix (- (nfix len) (nfix pos)))
     ///
     (defcong streqv equal
       (strtok!-aux string pos len delimiters rev-curr-tok acc) 1)))

  ///

  (defcong streqv equal (strtok! string delimiters) 1))
