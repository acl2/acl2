#|
; Instructions for rebuilding Paco:

cd /u/moore/paco
make tags   - make the tags file
make clean  - delete .cert, etc., files
make        - recertify as necessary

; ---------------------------------------------------------------------------
; To load

V27
:paco       ; load load paco (if unloaded) and switch to PACO pkg

; "paco.boot" goes a little further and loads "ptrace.lisp" and cheats
; to make paco::prove look Common Lisp compliant.

v27
(value :q)
(load "paco.boot")
(lp)
(in-package "PACO")

; ---------------------------------------------------------------------------
; To test

(ld  ;; newline to fool dependency scanner
 "books/proveall-input.lsp" :ld-pre-eval-print t)

; ---------------------------------------------------------------------------
; To change the "PACO" package definition

; Edit the defpkg in utilities.acl2.

; ---------------------------------------------------------------------------
; To play

; Load all but the last form in utilities.acl2 and then these files

(include-book "utilities")
(include-book "foundations")
(include-book "type-set")
(include-book "rewrite")
(include-book "simplify")
(include-book "induct")
(include-book "prove")
(include-book "database")

; ---------------------------------------------------------------------------
|#

(in-package "PACO")

; This file is actually empty!  The portculis, set up by paco.acl2,
; includes "database", which includes "prove", etc.
