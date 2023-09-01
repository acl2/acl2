; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This should be loaded two directories down from the gather/ directory
; (where patch-book.lisp is located).

(set-raw-mode-on!)
(push :acl2data *features*)
; Keep the following in sync with the same form in patch.lsp.
(let ((adv (getenv$-raw "ACL2_ADVICE")))
  (when (and adv (not (equal adv "")))
    (pushnew :skip-hyp *features*)
    (pushnew :skip-book-runes *features*)
    (pushnew :skip-rune *features*)
    (pushnew :acl2-advice *features*)))
(set-raw-mode nil)

(f-put-global
 'skip-retry-alist
 `((,(make-sysfile :system "kestrel/acl2data/gather/tests/runs/test2b.lisp") :rune))
 state)

(include-book #-acl2-advice "../../patch-book"
              #+acl2-advice "../../patch-book-advice"
              :ttags :all
              :load-compiled-file nil)
