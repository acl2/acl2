; A package for Web Assembly (WASM)
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "std/portcullis" :dir :system)

(defpkg "WASM"
  (append '(byte-listp
            bytep
            b*
            when
            len-at-least
            lookup
            repeat
            append-all
            std::defaggregate
            fargs
            farg1
            ffn-symb
            bvplus)
          (set-difference-eq *acl2-exports*
                             '(state state-p))))
