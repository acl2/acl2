; Support for verifying WASM code
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "WASM")

(include-book "execution")
(include-book "kestrel/utilities/defopeners" :dir :system)

(acl2::defopeners run)
(acl2::defopeners nth-local)

(acl2::defopeners top-n-operands)
(acl2::defopeners push-vals)
