; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "workshops/2020/coglio-westfold/schematic-example" :dir :system)
(include-book "workshops/2020/coglio-westfold/integer-example" :dir :system)
(include-book "workshops/2020/coglio-westfold/loop-example" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file collects the ISODATA examples from the ACL2-2020 Workshop paper,
; so that they are certified every time this [books]/kestrel/apt directory is.

; Note added 9/8/2021 by Matt K.: The workshop books above no longer include
; the present directory's isodata.lisp.  Instead they include that workshop
; books directory's version of isodata.lisp, which ideally won't undergo
; further changes.  The reason that the workshop book's directory was made to
; include its own isodata.lisp was so that its own isodata.lisp can include its
; own directed-untranslate.lisp -- or more precisely,
; books/workshops/2017/coglio-kaufmann-smith/support/directed-untranslate.lisp
; -- which was crafted to work with the simplify-defun implementation in that
; 2017 directory, which is used in the 2020 directory.  This became necessary
; when directed-untranslate was modified so that it no longer gives certain
; special attention to MBT, which wasn't really appropriate as a
; directed-untranslate feature but assisted in simplify-defun, and is no longer
; necessary now that simplify-defun gives its own special handling to MBT.
