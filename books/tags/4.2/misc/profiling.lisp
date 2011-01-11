; This book provides profiling support for certain host Lisps.  Currently it
; supports only CCL and SBCL.  As of this writing (October 2010) it appears
; that profiling an entire package is much more efficient in SBCL than it is in
; CCL.

; Example usage:

; (with-profiling "ACL2" (mini-proveall)) ; efficient in SBCL, slow in CCL
; (with-profiling '(rewrite assoc-eq) (mini-proveall))

; This file defines the form (with-profiling fns form).  Fns is evaluated, and
; the result should be either a function symbol, a list of function symbols, or
; a package name.  The indicated symbols are profiled, where a package name
; indicates all function symbols in that package (not including symbols
; imported from another package).

(in-package "ACL2")

(defttag :profiling)

(progn!
 (set-raw-mode t)
 (load (concatenate 'string (cbd) "profiling-raw.lsp")))

(defmacro-last with-profiling)
