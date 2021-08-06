; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; This file, init.lisp, is the standard KCL init file.  We use this
; tiny init file, which indirects to akcl-init.lisp, so that we can
; avoid loading in the full init file if it has already been loaded.

; This file need not be distributed with ACL2 and is unimportant for
; the correct operation of ACL2.  This file is loaded automatically by
; ACKL when it starts up, but not by ACL2 when running in any other
; Common Lisp.

; Bob Boyer sometimes uses the following for debugging in CCL:

;(declaim (optimize (safety 3)))
;(setq *print-level* 10)
;(setq *print-length* 10)
;(setq *compile-verbose* t)
;(setq *compile-print* t)
;(setq *load-print* t)
;(setq *load-verbose* t)
;(setq ccl:*trace-print-level* 10)
;(setq ccl:*trace-print-length* 10)
;(setq ccl::*backtrace-print-length* 10)
;(setq ccl::*backtrace-print-level* 10)

; We formerly pushed :hons onto *features* as part of the "make" process.  But
; that caused build failures when not using "make".  For "classic" ACL2(c)
; (which is no longer supported but might work) without support for hash-cons
; and fast-alists, comment out this form.  We could consider using getenv$-raw
; to conditionalize this push on environment variable ACL2_HONS, though
; getenv$-raw would need to be defined at this point (currently it is defined
; in acl2-fns.lisp, which is loaded by acl2.lisp, acl2-init.lisp, which is
; loaded below.  If you thus delay setting this :hons feature, be careful that
; none of that code loaded before doing so depends on that feature!
; Of course, it might be best simply to eliminate this feature, both by
; eliminating the push onto features below and by searching for its use in the
; source code and the books, especially to remove code guarded by #-hons.  But
; that seems unnecessarily painful and prone to omissions, and could affect
; proprietary books that we cannot fix ourselves.
(push :hons *features*)

(unless (find-package "ACL2")

; File acl2r.lisp is created by GNUmakefile, though the user could create it
; directly.  Its name derives from its initial purpose, which was simply to
; push :non-standard-analysis onto *features*.  We use it now for all sorts of
; things, though; see GNUmakefile.

  (if (probe-file "acl2r.lisp") (load "acl2r.lisp"))
  #+sbcl ; keep this in sync with with-warnings-suppressed
  (handler-bind
   ((style-warning (lambda (c)
                     (declare (ignore c))
                     (invoke-restart 'muffle-warning))))
   (load "acl2-init.lisp"))
  #-sbcl
  (load "acl2-init.lisp"))

; We may need a bigger stack than the default, as evidenced by the failure of
; the event (verify-guards read-utf8-fast ...) in community book
; books/unicode/read-utf8.lisp.  We handle this issue here for GCL, and
; elsewhere for some other lisps.  However, we have seen GCL 2.6.6 on Windows
; break here, so we skip the stack adjustment for Windows.

#+gcl
(progn
  (defvar *acl2-gcl-multiply-stacks-evaluated* nil)
  (when (not *acl2-gcl-multiply-stacks-evaluated*)

; Formerly we multiplied by 2.  But the following problems then bit us in
; ACL2(h).  Certification of community book books/arithmetic-5/top.lisp caused
; a stack overflow because of function pkg-names-memoize (which however is no
; longer used); books/misc/hons-tests.lisp had a stack overflow because of a
; memoized fibonacci function call; and a stack overflow for
; books/clause-processors/SULFA/books/sat-tests/sudoku.lisp was caused by
; bad-lisp-objectp.  Another doubling fixed each of these, but wasn't enough
; for certifying books/centaur/aig/random-sim.lisp, again because of
; pkg-names-memoize.  So we now multiply by 8.  Camm Maguire has suggested that
; these problems might be solved by avoiding the use of interpreted code, and
; we considered investigating whether that might be done (e.g., by adding (comp
; t) events) in the cases above.  But we see no harm in simply increasing the
; stack size, which could be of benefit in cases where users execute uncompiled
; code.  And besides, when we started ACL2(h) built on GCL we found that
; (symbol-function 'pkg-names-memoize) is compiled.

    (setq si::*multiply-stacks* 8))
  (setq *acl2-gcl-multiply-stacks-evaluated* t))

; Suggestion from Camm Maguire, 6/28/06 (GCL 2.6.7 and beyond), for improved
; efficiency; seconded by Bob Boyer.
#+gcl
(declaim (ftype (function (seqind t) t) si::set-mv))
