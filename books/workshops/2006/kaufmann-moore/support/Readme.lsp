; The Makefile has modified the default value of INHIBIT from Makefile-generic
; in order that we see warnings in the .out files.  We should see
; Double-rewrite warnings there that correspond exactly to comments about
; Double-rewrite (notice the upper-case D) in the .lisp files.

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
austel.lisp
greve1.lisp
greve2.lisp
greve3.lisp
mini-proveall-plus.lisp
mini-proveall.lisp
rhs1-iff.acl2
rhs1-iff.lisp
rhs1.acl2
rhs1.lisp
rhs2.acl2
rhs2.lisp
smith1.lisp
sumners1.lisp
warnings.acl2
warnings.lisp
")
 (:TITLE    "Double Rewriting for Equivalential Reasoning in ACL2")
 (:AUTHOR/S "Matt Kaufmann and J Moore") ; non-empty list of author strings
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "rewriting" "congruences" "equivalence relations" "double-rewrite")
 (:ABSTRACT "
This directory contains supporting materials to illustrate double-rewrite.  An
abstract of the corresponding ACL2 workshop submission is as follows:

Several users have had problems using equivalence-based rewriting in ACL2
because the ACL2 rewriter caches its results.  We describe this problem in some
detail, together with a solution implemented in ACL2 Version 2.9.4.  The
solution consists of a new primitive, double-rewrite}, together with
a new warning to suggest possible use of this primitive.")
  (:PERMISSION ; author/s permission for distribution and copying:
"Double-rewrite supporting materials
Copyright (C) 2006 Matt Kaufmann and J Moore
License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
"))
