; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; Help dependency scanner.
#|
(depends-on "patch.lsp")
|#

; Warning: Keep this in sync with the include-book forms in patch.lsp.
(include-book "remove-hyp-checkpoints")
(include-book "remove-hint-setting-checkpoints")
(include-book "remove-rune-checkpoints")
(include-book "remove-book-runes-checkpoints")
(include-book "count-acl2data")
(include-book "event-symbol-table")
; See patch-book-advice.lisp:
; (include-book "my-advice")

(defttag :acl2data)

(progn!
 (set-raw-mode t)
 (cond
  ((f-boundp-global 'acl2data-patch-loaded state)
   nil)
  (t
   (assign ld-okp t)
   (load (concatenate 'string (cbd) "patch.lsp"))
   (f-put-global 'acl2data-patch-loaded t state)))
 (assign ld-okp nil))

