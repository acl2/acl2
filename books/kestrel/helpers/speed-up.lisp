; Use with-supporters to just get the code of speed-up
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/with-supporters" :dir :system)

;; The point of this book is to provide the speed-up utility without
;; causing its supporting libraries to be included.  This helps minimize the
;; effect of the speed-up tool itself on the books being improved.

;; (defttag speed-up) ; because books-in-subtree and books-in-dir call sys-call+

(with-supporters
  (local (include-book "speed-up-implementation"))
  ;; Export only these functions/macros and their supporting definitions:
  :names (speed-up-event-fn
          speed-up-event
          speed-up-book-fn
          speed-up-book))
