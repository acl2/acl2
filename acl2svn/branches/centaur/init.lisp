; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Sciences
; University of Texas at Austin
; Austin, TX 78712-1188 U.S.A.

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

(unless (find-package "ACL2")

; File acl2r.lisp is created by the makefile, though the user could create it
; directly (which may be useful in non-Unix environment when make is not
; available).  It isn't necessary to create this file, however, when one is
; building a standard image, since all it does it push :non-standard-analysis
; onto *features*.  (It IS necessary however, when building a standard image,
; NOT to have acl2r.lisp around if it pushes that feature!)

  (if (probe-file "acl2r.lisp") (load "acl2r.lisp"))
  #+sbcl ; keep this in sync with with-warnings-suppressed
  (handler-bind
   (#+ansi-cl
    (style-warning (lambda (c)
                     (declare (ignore c))
                     (invoke-restart 'muffle-warning))))
   (load "acl2-init.lisp"))
  #-sbcl
  (load "acl2-init.lisp"))

; We may need a bigger stack than the default, as evidenced by the failure of
; the event (verify-guards read-utf8-fast ...) in books/unicode/read-utf8.lisp.
; We handle this issue here for GCL, and elsewhere for some other lisps.
; However, we have seen GCL 2.6.6 on Windows break here, so we skip the stack
; adjustment for Windows.

#+(and gcl (not mswindows))
(progn
  (defvar *acl2-gcl-multiply-stacks-evaluated* nil)
  (when (not *acl2-gcl-multiply-stacks-evaluated*)
    (setq si::*multiply-stacks* 2))
  (setq *acl2-gcl-multiply-stacks-evaluated* t))

; Suggestion from Camm Maguire, 6/28/06 (GCL 2.6.7 and beyond), for improved
; efficiency; seconded by Bob Boyer.
#+gcl
(when (acl2::gcl-version->= 2 6 7)
  (declaim (ftype (function (seqind t) t) si::set-mv)))
