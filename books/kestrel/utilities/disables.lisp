; A books that disables some built-in functions.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; In my opinion, these things should be disabled when ACL2 starts up:
(in-theory (disable floor
                    mod
                    digit-to-char
                    explode-nonnegative-integer
                    character-listp
                    add-to-set-equal
                    binary-logior
                    binary-logand
                    logorc1
                    lognot
                    binary-logeqv
                    binary-logxor))
