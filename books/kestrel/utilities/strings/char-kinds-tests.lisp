; String Utilities -- Kinds of Characters -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/testing" :dir :system)

(include-book "char-kinds")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit-char-p #\a))

(assert! (alpha/digit-char-p #\G))

(assert! (alpha/digit-char-p #\5))

(assert! (not (alpha/digit-char-p #\-)))

(assert! (not (alpha/digit-char-p #\\)))

(assert! (not (alpha/digit-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit-charlist-p nil))

(assert! (alpha/digit-charlist-p '(#\O #\5 #\a)))

(assert! (not (alpha/digit-charlist-p '(#\a #\<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit/dash-char-p #\a))

(assert! (alpha/digit/dash-char-p #\G))

(assert! (alpha/digit/dash-char-p #\5))

(assert! (alpha/digit/dash-char-p #\-))

(assert! (not (alpha/digit/dash-char-p #\\)))

(assert! (not (alpha/digit/dash-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit/dash-charlist-p nil))

(assert! (alpha/digit/dash-charlist-p '(#\- #\5 #\a)))

(assert! (not (alpha/digit/dash-charlist-p '(#\a #\<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/uscore/dollar-char-p #\a))

(assert! (alpha/uscore/dollar-char-p #\G))

(assert! (alpha/uscore/dollar-char-p #\_))

(assert! (alpha/uscore/dollar-char-p #\$))

(assert! (not (alpha/uscore/dollar-char-p #\5)))

(assert! (not (alpha/uscore/dollar-char-p #\#)))

(assert! (not (alpha/uscore/dollar-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/uscore/dollar-charlist-p nil))

(assert! (alpha/uscore/dollar-charlist-p '(#\_ #\a)))

(assert! (alpha/uscore/dollar-charlist-p '(#\_ #\G #\$)))

(assert! (not (alpha/uscore/dollar-charlist-p '(#\a #\#))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit/uscore/dollar-char-p #\a))

(assert! (alpha/digit/uscore/dollar-char-p #\G))

(assert! (alpha/digit/uscore/dollar-char-p #\5))

(assert! (alpha/digit/uscore/dollar-char-p #\_))

(assert! (alpha/digit/uscore/dollar-char-p #\$))

(assert! (not (alpha/digit/uscore/dollar-char-p #\-)))

(assert! (not (alpha/digit/uscore/dollar-char-p #\^)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit/uscore/dollar-charlist-p nil))

(assert! (alpha/digit/uscore/dollar-charlist-p '(#\a #\$ #\5)))

(assert! (alpha/digit/uscore/dollar-charlist-p '(#\_ #\$ #\G)))

(assert! (not (alpha/digit/uscore/dollar-charlist-p '(#\Space))))

(assert! (not (alpha/digit/uscore/dollar-charlist-p '(#\1 #\-))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (nondigit-char-p #\a))

(assert! (not (nondigit-char-p #\0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (nondigit-charlist-p nil))

(assert! (nondigit-charlist-p '(#\a #\~)))

(assert! (not (nondigit-charlist-p '(#\: #\9))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (printable-char-p #\a))

(assert! (printable-char-p #\Y))

(assert! (printable-char-p #\Space))

(assert! (printable-char-p #\())

(assert! (printable-char-p #\@))

(assert! (not (printable-char-p #\Return)))

(assert! (not (printable-char-p #\Tab)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (printable-charlist-p nil))

(assert! (printable-charlist-p '(#\u #\7 #\! #\-)))

(assert! (not (printable-charlist-p '(#\r #\Return))))
