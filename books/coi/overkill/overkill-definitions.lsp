; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility

(error "is anyone using this?  If so please remove this message.")
#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|                                                                           |#
#|===========================================================================|#
;; overkill-definitions.lisp
;; John D. Powell
;(in-package "OVERKILL")

;;
;; This file isolates overkill definitions and types. The file currently 
;; contains the following ACL2 constructs as the occur in the overkill book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

;; jcd - bzo - this is a temporary file that can be appended onto the 
;; Makefile.acl2s that we generate in order to prove :dir support for 
;; my-load, a standin for ld, until v2.9.3 is released.

(defun bozo-include-book-dir (dir acl2-defaults-table)
  (cdr (assoc-eq dir
                 (cdr (assoc-eq :include-book-dir-alist
                                acl2-defaults-table)))))

