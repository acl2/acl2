; String Utilities -- Kinds of Characters
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc character-kinds
  :parents (string-utilities)
  :short "Predicates that characterize various kinds of characters.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define alpha/digit/dash-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-kinds)
  :short "Check if a character is a letter, a (decimal) digit, or a dash."
  (or (and (standard-char-p char)
           (alpha-char-p char))
      (if (digit-char-p char) t nil)
      (eql char #\-)))

(std::deflist alpha/digit/dash-char-listp (x)
  (alpha/digit/dash-char-p x)
  :guard (character-listp x)
  :parents (character-kinds alpha/digit/dash-char-p)
  :short "Check if a true list of characters includes only
          letters, (decimal) digits, and dashes."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define alpha/uscore/dollar-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-kinds)
  :short "Check if a character is a letter, an underscore, or a dollar sign."
  (or (and (standard-char-p char)
           (alpha-char-p char))
      (eql char #\_)
      (eql char #\$)))

(std::deflist alpha/uscore/dollar-char-listp (x)
  (alpha/uscore/dollar-char-p x)
  :guard (character-listp x)
  :parents (character-kinds alpha/uscore/dollar-char-p)
  :short "Check if a list of characters includes only
          letters, underscores, and dollar signs."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define alpha/digit/uscore/dollar-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-kinds)
  :short "Check if a character is
          a letter, a (decimal) digit, an underscore, or a dollar sign."
  (or (and (standard-char-p char)
           (alpha-char-p char))
      (if (digit-char-p char) t nil)
      (eql char #\_)
      (eql char #\$)))

(std::deflist alpha/digit/uscore/dollar-char-listp (x)
  (alpha/digit/uscore/dollar-char-p x)
  :guard (character-listp x)
  :parents (character-kinds alpha/digit/uscore/dollar-char-p)
  :short "Check if a list of characters includes only
          letters, (decimal) digits, underscores, and dollar signs."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nondigit-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-kinds)
  :short "Check if a character is not a (decimal) digit."
  (not (digit-char-p char)))

(std::deflist nondigit-char-listp (x)
  (nondigit-char-p x)
  :guard (character-listp x)
  :parents (character-kinds nondigit-char-p)
  :short "Check if a true list of characters includes no (decimal) digits."
  :true-listp t
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define printable-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-kinds)
  :short "Check if a character is a printable ASCII character,
          i.e. it is a space or a visible character."
  (b* ((code (char-code char)))
    (and (<= #x20 code)
         (<= code #x7e))))

(std::deflist printable-char-listp (x)
  (printable-char-p x)
  :guard (character-listp x)
  :parents (character-kinds printable-char-p)
  :short "Check if a list of characters includes only
          printable ASCII characters, i.e. spaces and visible characters."
  :true-listp t
  :elementp-of-nil nil)
