; String Utilities -- Kinds of Characters
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/strings/charset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc character-kinds
  :parents (string-utilities)
  :short "Predicates that characterize various kinds of characters,
          and true lists thereof.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(str::defcharset alpha/digit
  (or (and (standard-char-p x)
           (alpha-char-p x))
      (and (digit-char-p x) t))
  :parents (character-kinds)
  :short "Recognize letters and (decimal) digits.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(str::defcharset alpha/digit/dash
  (or (and (standard-char-p x)
           (alpha-char-p x))
      (and (digit-char-p x) t)
      (eql x #\-))
  :parents (character-kinds)
  :short "Recognize letters, (decimal) digits, and dashes.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(str::defcharset alpha/uscore/dollar
  (or (and (standard-char-p x)
           (alpha-char-p x))
      (eql x #\_)
      (eql x #\$))
  :parents (character-kinds)
  :short "Recognize letters, underscores, and dollar signs.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(str::defcharset alpha/digit/uscore/dollar
  (or (and (standard-char-p x)
           (alpha-char-p x))
      (and (digit-char-p x) t)
      (eql x #\_)
      (eql x #\$))
  :parents (character-kinds)
  :short "Recognize letters, (decimal) digits, underscores, and dollar signs.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(str::defcharset nondigit
  (not (digit-char-p x))
  :parents (character-kinds)
  :short "Recognize characters that are not (decimal) digits.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(str::defcharset printable
  (b* ((code (char-code x)))
    (and (<= #x20 code)
         (<= code #x7e)))
  :parents (character-kinds)
  :short "Recognize printable ASCII characters,
          i.e. spaces and visible ASCII characters.")
