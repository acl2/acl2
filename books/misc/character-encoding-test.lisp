(in-package "ACL2")

; This file has been saved using the utf-8 character encoding.  As a result,
; the constant below has length 2 when using ACL2, which fixes the character
; encoding at iso-8859-1 (see :DOC character-encoding).  If the length of this
; constant is 1, then this file was probably saved with a different encoding,
; quite possibly iso-8859-1.

; WARNING: Before saving this file in emacs, evaluate the following form,
; especially if you have loaded distributed file emacs/emacs-acl2.el into your
; emacs session, since that file sets the character encoding to iso-8859-1.

; (setq save-buffer-coding-system 'utf-8)

; If you have not done this, then in a linux shell, executing
;   cat character-encoding-test.lisp
; may show clearly that the string below has a single character.

(defthm len-test-1
  (equal (length (test-1)) 2)
  :rule-classes nil)

(defun test-2 () "ó")

(defthm len-test-2
  (equal (length (test-2)) 2)
  :rule-classes nil)
