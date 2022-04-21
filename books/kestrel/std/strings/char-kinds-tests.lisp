; Standard Strings Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "char-kinds")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::letter-char-p #\a))

(assert! (str::letter-char-p #\G))

(assert! (not (str::letter-char-p #\5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::letter/digit-char-p #\a))

(assert! (str::letter/digit-char-p #\G))

(assert! (str::letter/digit-char-p #\5))

(assert! (not (str::letter/digit-char-p #\-)))

(assert! (not (str::letter/digit-char-p #\\)))

(assert! (not (str::letter/digit-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::letter/digit/dash-char-p #\a))

(assert! (str::letter/digit/dash-char-p #\G))

(assert! (str::letter/digit/dash-char-p #\5))

(assert! (str::letter/digit/dash-char-p #\-))

(assert! (not (str::letter/digit/dash-char-p #\\)))

(assert! (not (str::letter/digit/dash-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::letter/digit/uscore-char-p #\a))

(assert! (str::letter/digit/uscore-char-p #\G))

(assert! (str::letter/digit/uscore-char-p #\5))

(assert! (str::letter/digit/uscore-char-p #\_))

(assert! (not (str::letter/digit/uscore-char-p #\\)))

(assert! (not (str::letter/digit/uscore-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::letter/digit/uscore/dollar-char-p #\a))

(assert! (str::letter/digit/uscore/dollar-char-p #\G))

(assert! (str::letter/digit/uscore/dollar-char-p #\5))

(assert! (str::letter/digit/uscore/dollar-char-p #\_))

(assert! (str::letter/digit/uscore/dollar-char-p #\$))

(assert! (not (str::letter/digit/uscore/dollar-char-p #\-)))

(assert! (not (str::letter/digit/uscore/dollar-char-p #\^)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::letter/uscore/dollar-char-p #\a))

(assert! (str::letter/uscore/dollar-char-p #\G))

(assert! (str::letter/uscore/dollar-char-p #\_))

(assert! (str::letter/uscore/dollar-char-p #\$))

(assert! (not (str::letter/uscore/dollar-char-p #\5)))

(assert! (not (str::letter/uscore/dollar-char-p #\#)))

(assert! (not (str::letter/uscore/dollar-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::nondigit-char-p #\a))

(assert! (not (str::nondigit-char-p #\0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::printable-char-p #\a))

(assert! (str::printable-char-p #\Y))

(assert! (str::printable-char-p #\Space))

(assert! (str::printable-char-p #\())

(assert! (str::printable-char-p #\@))

(assert! (not (str::printable-char-p #\Return)))

(assert! (not (str::printable-char-p #\Tab)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::ucletter-char-p #\Y))

(assert! (not (str::ucletter-char-p #\y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::lcletter-char-p #\z))

(assert! (not (str::lcletter-char-p #\Z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::ucletter/digit-char-p #\Y))

(assert! (str::ucletter/digit-char-p #\4))

(assert! (not (str::ucletter/digit-char-p #\y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (str::lcletter/digit-char-p #\y))

(assert! (str::lcletter/digit-char-p #\4))

(assert! (not (str::lcletter/digit-char-p #\Y)))
