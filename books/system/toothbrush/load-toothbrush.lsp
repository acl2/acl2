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
(unless (boundp 'COMMON-LISP-USER::*acl2-dir*)
  (error "COMMON-LISP-USER::*acl2-dir* needs to be set to a directory
containing relevant ACL2 source files."))

(let ((*default-pathname-defaults* COMMON-LISP-USER::*acl2-dir*))
  (load "init.lisp"))

(in-package "ACL2")

(defmacro def-errors (&rest fns)
  (cons 'progn
        (loop for fn in fns collect
              `(defun ,fn (&rest args)
                 (declare (ignore args))
                 (error "Not implemented in toothbrush: ~s" ',fn)))))

(defmacro def-nils (&rest fns)
  (cons 'progn
        (loop for fn in fns collect
              `(defun ,fn (&rest args)
                 (declare (ignore args))
                 nil))))

(def-nils
  CHECK-PROPOSED-IMPORTS ; Presumably the check was already done!
  MEMOIZE-LOOK-UP-DEF ; !! should fix when toothbrush can memoize
  )

(def-errors

; These were obtained by looking at warnings from loading load-toothbrush.lsp.
; In each case, we don't expect the callers to themselves be called.

  CLEAR-MEMOIZE-TABLES
  ACL2-DEFAULTS-TABLE-LOCAL-CTX-P
  TT-START
  TT-STOP
  TT-PRINT?
  TT-END
  TT-INIT
  LD-FN
  CERT-OP
  UNRELATIVIZE-BOOK-PATH
  SER-ENCODE-TO-STREAM
  RETRACT-WORLD1
  EXTEND-WORLD1
  THE-LIVE-VAR
  SET-W!
  ONEIFY ; called in mv-let-for-with-local-stobj

; !! We should revisit the following when we are ready to implement memoization
; in the toothbrush (without using tables and world).
; Note that memoize will just be a table call for now, hence nil.

; In each case, we show the responsible caller.  The def-errors form near the
; end of this file makes each of those cause an error when called.

  CANONICAL-SIBLING         ; UPDATE-MEMO-ENTRIES-FOR-ATTACHMENTS
  STRICT-MERGE-SORT-SYMBOL-< ; UPDATE-MEMO-ENTRIES-FOR-ATTACHMENTS
  EXT-ANCESTORS-ATTACHMENTS  ; UPDATE-MEMO-ENTRY-FOR-ATTACHMENTS
  EXT-ANC-ATTACHMENTS-VALID-P ; UPDATE-MEMO-ENTRY-FOR-ATTACHMENTS
  MAYBE-UNTRACE!              ; UNMEMOIZE-FN
  MAYBE-UNTRACE!              ; UNMEMOIZE-FN
  EXT-ANCESTORS-ATTACHMENTS   ; MEMOIZE-FN
  CONCRETE-STOBJ              ; MEMOIZE-FN
  CONGRUENT-STOBJ-REP         ; MEMOIZE-FN
  EXT-ANCESTORS-ATTACHMENTS   ; MEMOIZE-FN
  CONCRETE-STOBJ              ; MEMOIZE-FN
  CONGRUENT-STOBJ-REP         ; MEMOIZE-FN
  MAYBE-UNTRACE!              ; MEMOIZE-FN-INIT
  MAYBE-UNTRACE!              ; MEMOIZE-FN-INIT
  CLTL-DEF-FROM-NAME          ; MEMOIZE-LOOK-UP-DEF
  NOTE-FNS-IN-FILE            ; INITIALIZE-NEVER-MEMOIZE-HT
  NOTE-FNS-IN-FILE            ; INITIALIZE-NEVER-MEMOIZE-HT

  )

; Replacement definition (needed for caller THROW-NONEXEC-ERROR):
(defun-one-output print-list-without-stobj-arrays (lst)
  lst)

; Replacement definition (needed for caller THROW-RAW-EV-FNCALL):
(defun ev-fncall-msg (val wrld user-stobj-alist)
  (declare (ignore wrld user-stobj-alist))
  (format nil "ev-fncall-msg: ~s" val))

(let ((*default-pathname-defaults* COMMON-LISP-USER::*acl2-dir*))
  (load "axioms.lisp")
  (load "basis-a.lisp")
  #+hons
  (progn (load "hons.lisp")
         (load "hons-raw.lisp")
         (load "memoize.lisp")
         (load "memoize-raw.lisp")))

#+hons ; memoize only here
(def-errors

; !! We should revisit the following when we are ready to implement memoization
; in the toothbrush (without using tables and world).
; Note that memoize will just be a table call for now, hence nil.

  INITIALIZE-NEVER-MEMOIZE-HT ; avoid call of NOTE-FNS-IN-FILE
  MEMOIZE-FN
  UNMEMOIZE-FN
  UPDATE-MEMO-ENTRIES-FOR-ATTACHMENTS
  UPDATE-MEMO-ENTRY-FOR-ATTACHMENTS
  )
