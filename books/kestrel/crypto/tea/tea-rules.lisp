; Rules for reasoning about TEA
;
; Copyright (C) 2016-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tea")
(include-book "kestrel/utilities/defopeners" :dir :system)

(defopeners tea-encrypt-loop)
(defopeners tea-decrypt-loop)
(in-theory (disable tea-encrypt-loop-unroll))

(defun tea-spec-rules ()
  '(tea-encrypt-loop-unroll
    tea-encrypt-loop-base
    tea-encrypt
    tea-encrypt-loop-body
    tea-step
    tea-decrypt-loop-unroll
    tea-decrypt-loop-base
    tea-decrypt
    tea-decrypt-loop-body
    pack-tea-key
    pack-tea-input
    unpack-tea-output
    packbv-base
    packbv-opener
    unpackbv-opener
    unpackbv-when-zp
    subrange-rewrite))
