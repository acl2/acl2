(in-package "ACL2")

(defmacro def-errors (&rest fns)

; For explanation, see the calls of def-errors below.

  (cons 'with-suppression
        (loop for fn in fns collect
              `(defun ,fn (&rest args)
                 (declare (ignore args))
                 (error "Not implemented in toothbrush: ~s" ',fn)))))

(defmacro def-nils (&rest fns)

; Generate a definition for each fn in fns that simply returns nil.  We should
; only do so when there is good reason, of course!

  (cons 'with-suppression
        (loop for fn in fns collect
              `(defun ,fn (&rest args)
                 (declare (ignore args))
                 nil))))

(def-nils
  CHECK-PROPOSED-IMPORTS ; Presumably the check was already done!
  MEMOIZE-LOOK-UP-DEF ; !! We should fix this when toothbrush can memoize.
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
  ONEIFY ; called in mv-let-for-with-local-stobj, but not with toothbrush
  INITIALIZE-DMR-INTERVAL-USED ; called by set-waterfall-parallelism-fn
  HARD-ERROR-IS-ERROR ; needs macro channel-to-string, which is defined late
  CCL-INITIALIZE-GC-STRATEGY ; called by set-gc-strategy-fn
  REMOVE-ADJACENT-DUPLICATES-EQ ; called by defpkg-raw1
  )

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

; In each case below, we show the responsible caller.  The def-errors form near
; the end of this file makes each of those cause an error when called.

  CANONICAL-SIBLING         ; UPDATE-MEMO-ENTRIES-FOR-ATTACHMENTS
  STRICT-MERGE-SORT-SYMBOL-< ; UPDATE-MEMO-ENTRIES-FOR-ATTACHMENTS
  EXT-ANCESTORS-ATTACHMENTS  ; UPDATE-MEMO-ENTRY-FOR-ATTACHMENTS, MEMOIZE-FN
  EXT-ANC-ATTACHMENTS-VALID-P ; UPDATE-MEMO-ENTRY-FOR-ATTACHMENTS
  MAYBE-UNTRACE!              ; UNMEMOIZE-FN, MEMOIZE-FN-INIT
  CONCRETE-STOBJ              ; MEMOIZE-FN
  CONGRUENT-STOBJ-REP         ; MEMOIZE-FN
  CLTL-DEF-FROM-NAME          ; MEMOIZE-LOOK-UP-DEF
  NOTE-FNS-IN-FILE            ; INITIALIZE-NEVER-MEMOIZE-HT
  )

; Replacement definition (needed for caller THROW-NONEXEC-ERROR):
(defun-one-output print-list-without-stobj-arrays (lst)
  lst)

; Replacement definition (needed for caller THROW-RAW-EV-FNCALL):
(defun ev-fncall-msg (val wrld user-stobj-alist)
  (declare (ignore wrld user-stobj-alist))
  (format nil "ev-fncall-msg: ~s" val))

(our-with-compilation-unit

; Warning: The order of files below should respect the order in
; acl2::*acl2-files*, in order to avoid the possibility of a file trying to use
; the value of a constant that isn't yet defined.

 (let ((*default-pathname-defaults* COMMON-LISP-USER::*acl2-dir*))
   #+acl2-par (load "multi-threading-raw.lisp")
   (load "axioms.lisp")
   #+hons (load "hons.lisp")
   #+hons (load "hons-raw.lisp")
   (load "basis-a.lisp")
   #+hons (load "memoize.lisp")
   #+acl2-par (load "parallel.lisp")
   #+acl2-par (load "futures-raw.lisp")
   #+acl2-par (load "parallel-raw.lisp")
   #+hons (load "memoize-raw.lisp")))

; Code for saving an image.

; For SBCL, it seems a bit challenging to get setenv$ defined.  I tried what's
; below, and some variants of it, but kept getting errors.  If anyone gets
; serious about using the toothbrush, it would be good to fix this.
#-sbcl
(setenv$ "ACL2_SNAPSHOT_INFO"
         "PLEASE NOTE: This \"toothbrush\" contains only a part of ACL2")
#||
#+sbcl
(require :sb-posix)
#+sbcl
(funcall (intern "PUTENV" "SB-POSIX")
         "ACL2_SNAPSHOT_INFO=PLEASE NOTE: This \"toothbrush\" contains only a part of ACL2")
||#

(setq *saved-build-date-lst*
      (list (saved-build-date-string)))

; Redefinition:
(defun lp ()
  (cond (*lp-ever-entered-p*
         (format t "WARNING: This is a toothbrush image, not ACL2.~%")
         (format t "         Your call of LP is thus a no-op.~%"))
        (t ; first time entered

; NOTE: The following relies on the user having moved into the desired package
; before saving with save-exec.

         (eval `(in-package ,*startup-package-name*))
         (setq *lp-ever-entered-p* t)))
  nil)

; Replacement definition (needed for caller SAVE-EXEC-FN)
; (WARNING: This restricts us to Unix),
; to avoid an error from looking up the os in the world:
(defun os (wrld)
  (declare (ignore wrld))
  :UNIX)
