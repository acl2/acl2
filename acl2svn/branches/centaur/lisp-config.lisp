; ACL2 Version 6.0 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2012, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Regarding authorship of ACL2 in general:

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; lisp-config.lisp -- configures various Lisp settings, e.g., for garbage
; collection.

; This file was originally developed by Bob Boyer, Warren Hunt, Sol Swords, and
; Jared Davis, with the help of Gary Byers.

; Note: this file is not currently used by ACL2.  Perhaps Matt may eventually
; incorporate it into ACL2 in some way.






; This file can be given to CCL to rebuild it with new memory settings.
; Typical usage is:
;
;    - Download CCL from SVN
;    - Rebuild CCL from Sources, i.e., (rebuild-ccl :full t), (quit), as
;      explained in the CCL manual, Chapter 2.2
;    - Then, while still in your CCL directory:
;        ./lx86cl64 -n < [...]/acl2/books/centaur/ccl-config.lsp
;
; This should clobber your existing lx86cl64 image and replace it with a new
; one that has larger default stack sizes and better garbage collection
; settings for doing proofs using ACL2(h) and the Centaur Books.
;
; Afterward, you can verify that your image has been modified by looking at the
; value of ccl::*initial-listener-default-control-stack-size*; it should now be
; much larger.

(in-package :ccl)

; Disable ephemeral garbage colelction because it seems to be unacceptably slow
; for ACL2(h).
(egc nil)

; Turn on verbose garbage collection
(gc-verbose t t)

; Set up default stack sizes.  You can override these later with the -Z option
; but only all together.  If we are running on a 32-bit platform (e.g., a
; 32-bit PowerPC Apple computer) we set the stack size more modestly.  If we
; are on a 64-bit platform, we set the stack sizes to large values.
;
; These stack sizes apply to the first (initial) Lisp listener thread, where
; the bulk of ACL2 computations take place.

(let ((stack-size (if (< most-positive-fixnum (expt 2 34))
                      (expt 2 23)
                    (expt 2 28))))

  (setq *initial-listener-default-control-stack-size* stack-size)
  (setq *initial-listener-default-value-stack-size*   stack-size)

  ;; The temp stack probably doesn't need to be as large as the others.  When
  ;; CCL comes out of the box, it's half the size of the others.
  (setq *initial-listener-default-temp-stack-size* (floor stack-size 2)))

; Set up the garbage collector to wait until 1 GB has been allocated on a
; 32-bit system, or 2 GB on a 64-bit system.
(set-lisp-heap-gc-threshold (if (< most-positive-fixnum (expt 2 34))
                                (expt 2 30)
                              (expt 2 31)))

(use-lisp-heap-gc-threshold)

; [Bob]: These control the saving of DEFUN bodies.  This is turned off by Matt
; in ACL2 because it slows down the ACL2 regression by 8%.  We now do the same.
(setq *save-definitions* nil)
(setq *fasl-save-definitions* nil)

; [Bob]: This makes CCL exit on Ctrl+D, which is really convenient.  Please do
; not remove it.
(setq *quit-on-eof* t)

(save-application *heap-image-name*)

(quit)