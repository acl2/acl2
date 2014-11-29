; Copyright (C) 2014, ForrestHunt, Inc.
; Written by Matt Kaufmann, November, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; NOTE: We assume that feature :acl2-loop-only is false (as it is by default in
; CCL).

; NOTE: For Lisps that don't compile on-the-fly, we would want to compile this
; file, and some modifications to it might be necessary.  But we can't compile
; it in its current form, because of an in-package below.  This can easily be
; solved by splitting into two files.

; Replace the following string with a path to the directory containing
; the relevant ACL2 source files (see just below).
(unless (and (boundp 'COMMON-LISP-USER::*acl2-dir*)
             (or (stringp COMMON-LISP-USER::*acl2-dir*)
                 (pathnamep COMMON-LISP-USER::*acl2-dir*)))
  (error "COMMON-LISP-USER::*acl2-dir* needs to be set to a directory,
or pathname of such, containing relevant ACL2 source files."))

(when (stringp COMMON-LISP-USER::*acl2-dir*)
  (setq COMMON-LISP-USER::*acl2-dir*
        (pathname COMMON-LISP-USER::*acl2-dir*)))

(let ((*default-pathname-defaults* COMMON-LISP-USER::*acl2-dir*))

; Note that loading ACL2 source file init.lisp also loads these ACL2 source
; files:

; acl2-fns.lisp
; acl2-init.lisp
; acl2.lisp
; acl2r.lisp

  (load "init.lisp"))

(let ((*default-pathname-defaults* *load-truename*))
  (acl2::with-warnings-suppressed
   (load "load-toothbrush-2.lsp")))

