; Character Utilities -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "characters")
(include-book "testing")

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

(assert! (nondigit-char-p #\a))

(assert! (not (nondigit-char-p #\0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (nondigit-char-listp nil))

(assert! (nondigit-char-listp '(#\a #\~)))

(assert! (not (nondigit-char-listp '(#\: #\9))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nats=>chars nil) nil)

(assert-equal (nats=>chars '(65 99 46)) '(#\A #\c #\.))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (chars=>nats nil) nil)

(assert-equal (chars=>nats '(#\a #\5 #\~)) '(97 53 126))
