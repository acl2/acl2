; Standard Strings Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "strtok-bang")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (str::strtok! "abc.de..f" (list #\.))
              '("abc" "de" "" "f"))

(assert-equal (str::strtok! "abc.de.:f" (list #\. #\:))
              '("abc" "de" "" "f"))

(assert-equal (str::strtok! "" (list #\. #\:))
              '(""))

(assert-equal (str::strtok! "a sequence of  words" (list #\Space))
              '("a" "sequence" "of" "" "words"))
