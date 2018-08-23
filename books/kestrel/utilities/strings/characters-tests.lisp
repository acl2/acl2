; Character Utilities -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/testing" :dir :system)

(include-book "characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit/dash-char-p #\a))

(assert! (alpha/digit/dash-char-p #\G))

(assert! (alpha/digit/dash-char-p #\5))

(assert! (alpha/digit/dash-char-p #\-))

(assert! (not (alpha/digit/dash-char-p #\\)))

(assert! (not (alpha/digit/dash-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit/dash-char-listp nil))

(assert! (alpha/digit/dash-char-listp '(#\- #\5 #\a)))

(assert! (not (alpha/digit/dash-char-listp '(#\a #\<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/uscore/dollar-char-p #\a))

(assert! (alpha/uscore/dollar-char-p #\G))

(assert! (alpha/uscore/dollar-char-p #\_))

(assert! (alpha/uscore/dollar-char-p #\$))

(assert! (not (alpha/uscore/dollar-char-p #\5)))

(assert! (not (alpha/uscore/dollar-char-p #\#)))

(assert! (not (alpha/uscore/dollar-char-p #\<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/uscore/dollar-char-listp nil))

(assert! (alpha/uscore/dollar-char-listp '(#\_ #\a)))

(assert! (alpha/uscore/dollar-char-listp '(#\_ #\G #\$)))

(assert! (not (alpha/uscore/dollar-char-listp '(#\a #\#))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit/uscore/dollar-char-p #\a))

(assert! (alpha/digit/uscore/dollar-char-p #\G))

(assert! (alpha/digit/uscore/dollar-char-p #\5))

(assert! (alpha/digit/uscore/dollar-char-p #\_))

(assert! (alpha/digit/uscore/dollar-char-p #\$))

(assert! (not (alpha/digit/uscore/dollar-char-p #\-)))

(assert! (not (alpha/digit/uscore/dollar-char-p #\^)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (alpha/digit/uscore/dollar-char-listp nil))

(assert! (alpha/digit/uscore/dollar-char-listp '(#\a #\$ #\5)))

(assert! (alpha/digit/uscore/dollar-char-listp '(#\_ #\$ #\G)))

(assert! (not (alpha/digit/uscore/dollar-char-listp '(#\Space))))

(assert! (not (alpha/digit/uscore/dollar-char-listp '(#\1 #\-))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (nondigit-char-p #\a))

(assert! (not (nondigit-char-p #\0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (nondigit-char-listp nil))

(assert! (nondigit-char-listp '(#\a #\~)))

(assert! (not (nondigit-char-listp '(#\: #\9))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (printable-char-p #\a))

(assert! (printable-char-p #\Y))

(assert! (printable-char-p #\Space))

(assert! (printable-char-p #\())

(assert! (printable-char-p #\@))

(assert! (not (printable-char-p #\Return)))

(assert! (not (printable-char-p #\Tab)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (printable-char-listp nil))

(assert! (printable-char-listp '(#\u #\7 #\! #\-)))

(assert! (not (printable-char-listp '(#\r #\Return))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nats=>chars nil) nil)

(assert-equal (nats=>chars '(65 99 46)) '(#\A #\c #\.))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (chars=>nats nil) nil)

(assert-equal (chars=>nats '(#\a #\5 #\~)) '(97 53 126))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubyte8s=>hexchars nil)
              nil)

(assert-equal (ubyte8s=>hexchars '(0 1 2 3))
              '(#\0 #\0 #\0 #\1 #\0 #\2 #\0 #\3))

(assert-equal (ubyte8s=>hexchars '(240 15 169))
              '(#\F #\0 #\0 #\F #\A #\9))
