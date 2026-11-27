((lisp-mode . (
               ;; Do not insert tabs when indenting.
               (indent-tabs-mode . nil)
               ;; Auto-wrap lines longer than 80 characters.
               (fill-column . 80)
               ;; Enforce ACL2 single-semicolon block comment convention.
               (comment-column . 0)
               (comment-fill-column . 80)
               ;; Ensure `BEGINNING-OF-DEFUN' (called in `ACL2-BEGINNING-OF-DEF' in
               ;; emacs-acl2.el) finds the top-level of a form rather than the most
               ;; recent line-initiating open-parenthesis.
               (open-paren-in-column-0-is-defun-start . nil)
               (defun-prompt-regexp . nil)
               ;; Maintain Emacs defaults.
               (lisp-indent-offset . nil)
               (comment-padding . " ")

;;; Common Lisp
               ;; Use Common Lisp instead of Emacs Lisp indentation for `IF'.
               (eval . (put 'if 'common-lisp-indent-function 3))
               ;; NOTE: `COMMON-LISP-INDENT-FUNCTION' has hard-coded indentation
               ;; for any form beginning with "loop", and the match is
               ;; case-insensitive.  This causes Emacs to misindent the body of
               ;; the `LOOP$' macro.  Moreover, this bug cannot be resolved by
               ;; setting the `COMMON-LISP-INDENT-FUNCTION' property of `LOOP$'.

;;; ACL2 built-ins
               (eval . (put 'defpkg 'common-lisp-indent-function 1))
               (eval . (put 'defsection 'common-lisp-indent-function 1))
               (eval . (put 'deftheory 'common-lisp-indent-function 1))
               (eval . (put 'defthm 'common-lisp-indent-function 1))
               (eval . (put 'defxdoc 'common-lisp-indent-function 1))
               (eval . (put 'encapsulate 'common-lisp-indent-function 1))
               (eval . (put 'in-theory 'common-lisp-indent-function 0))
               (eval . (put 'include-book 'common-lisp-indent-function 0))
               (eval . (put 'local 'common-lisp-indent-function 0))
               (eval . (put 'make-event 'common-lisp-indent-function 0))

               ))
 (shell-mode . (
                ;; Fix `BEGINNING-OF-DEFUN' (see above comment).
                (open-paren-in-column-0-is-defun-start . nil)
                (defun-prompt-regexp . nil)
                ))
 ;; Ensure Emacs opens files in the appropriate major mode.
 (auto-mode-alist . (
                     ("\\.acl2\\'" . lisp-mode)
                     ("\\.lisp\\'" . lisp-mode)
                     ("\\.lsp\\'" . lisp-mode)
                     )))
