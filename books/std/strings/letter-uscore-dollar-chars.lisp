; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/charset" :dir :system)
(include-book "xdoc/constructors" :dir :system)
; Matt K. mod, 9/4/2023 (see that book for explanation), to avoid a failure.
(local (include-book "std/basic/code-char-char-code-with-force" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(str::defcharset letter/uscore/dollar
  (b* ((code (char-code x)))
    (or (and (<= (char-code #\A) code)
             (<= code (char-code #\Z)))
        (and (<= (char-code #\a) code)
             (<= code (char-code #\z)))
        (eql x #\_)
        (eql x #\$)))
  :parents (character-kinds)
  :short "Recognize ASCII letters, underscores, and dollar signs.")
