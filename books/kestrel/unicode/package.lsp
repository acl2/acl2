; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The "UNICODE" package is for the model of the Unicode Standard
; in this directory: code points, character properties, and normalization.
; (The verified UTF-8 codec of [books]/unicode and
; the lightweight encoding utilities of [books]/kestrel/unicode-light
; are in the "ACL2" package.)

(defpkg "UNICODE" (append *std-pkg-symbols*
                          '(bool
                            defmacro+
                            defxdoc+
                            high-surrogatep
                            impossible
                            lnfix
                            low-surrogatep
                            nat
                            nat-list
                            nat-list-fix
                            pos)))
