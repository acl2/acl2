; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; At first, we operate ACL2 as a standalone program
;; simply by sending it a form that generates and checks the theorem
;; and that exits with the appropriate status.
;; On my linux box this appears to take real time 0.014 for the overhead
;; (if we pre-load leo-acl2/top).
;; Later we can do things like have a server and put it in a Docker container.

;; Example call:
;;   echo '(tgc "/tmp/th.lisp" "/tmp/before.json" "/tmp/after.json")' | tgc_acl2
;;
;; If /tmp/th.lisp is successfully created and certified, tgc_acl2 should
;; return with status 0, and there should be a new nonempty file /tmp/th.cert.
;; Both indicators should be checked by the caller, because there are
;; some unlikely error scenarios that could cause one or the other indicator
;; seem correct.

;; For development testing:
;; Should succeed:
;;   cp ~/leo-acl2/testing/theorem-template.tl /tmp/theorem-template.tl
;;   echo '(include-book "~/leo-acl2/top") (tgc "/tmp/" "/tmp/th.lisp" "/tmp/before.json" "/tmp/after.json")' | ~/acl2/saved_acl2 ; echo $?
;; Should fail (didn't do the canonicalization):
;;   echo '(include-book "~/leo-acl2/top") (tgc "/tmp/" "/tmp/th.lisp" "/tmp/before.json" "/tmp/before.json")' | ~/acl2/saved_acl2 ; echo $?

;; For a more real example,
;; * load up "stages" (ast-stages-dev, and then pull from main as well)
;; * un-inline the input file from ~/leo/tests/compiler/circuits/inline_member_pass.leo
;;   to ~/leo/tests/compiler/circuits/input/inline.in
;; * mkdir ~/tmp/tmp ; cd ~/tmp/tmp
;;   stages -a --file ~/leo/tests/compiler/circuits/inline_member_pass.leo --input ~/leo/tests/compiler/circuits/input/inline.in
;;   The previous command should have created three files, initial.json,
;;   canonicalization.json, and type_inference.json
;;* cp ~/leo-acl2/testing/theorem-template.tl /tmp/tmp/theorem-template.tl
;;  echo '(include-book "~/leo-acl2/top") (tgc "/tmp/tmp/" "/tmp/tmp/th.lisp" "/tmp/tmp/initial.json" "/tmp/tmp/canonicalization.json")' | ~/acl2/saved_acl2 ; echo $?

;; To build the book in for faster startup, after `cert.pl top`
;; cd ~/leo-acl2
;; ACL2_CUSTOMIZATION=NONE $ACL2
;; (include-book "top")
;; :q
;; (save-exec "leo-acl2" "Included leo-acl2/top")
;; - Maybe next time better to do it somewhere else, because that creates the script
;;   ~/leo-acl2/leo-acl2 and the bundle file ~/leo-acl2/leo-acl2.lx86cl64
;; But then this is faster:
;;   cd /tmp
;;   cp ~/leo-acl2/testing/theorem-template.tl /tmp/tmp/theorem-template.tl
;;   echo '(tgc "/tmp/tmp/" "/tmp/tmp/th.lisp" "/tmp/tmp/initial.json" "/tmp/tmp/canonicalization.json")' | ~/leo-acl2/leo-acl2 ; echo $?
;; About 0.2 seconds.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "theorem-files")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; tgc = theorem-generate-and-check

;; TODO: decide what to do with a possible already-existing theorem file
(defun check-theorem-file (f)
  ;; For now, just check that it is at least 7 chars long
  ;; and that it starts with a slash and ends in ".lisp"
  (and (stringp f)
       (let ((len (length f)))
         (and (>= len 7)
              (eql (char f 0) #\/)
              (equal (subseq f (- len 5) len) ".lisp")))))

;; Need this because certify-book does not evaluate its file argument
(defun strip-.lisp (f)
  (subseq f 0 (- (length f) 5)))

;; Do we really need this?  Maybe not.  We want relative dirs to be
;; auto-extended to $PWD; just let things be relative to the
;; PWD when the lisp was started. - EM 2021-07-11
(defun add-dir-if-f-relative (f dir)
  (b* (((unless (stringp f)) f) ; just return f if not a string
       ((when (equal f "")) dir) ; just return dir if f is empty string
       ((when (equal (char f 0) #\/))
        f)  ; just return f if f starts with slash
       ((unless (stringp dir))
        f))  ; just return f if dir is not a string
    (string-append dir f)))

;; See also the tgc script where STAGE controls which template file is used.
;; This constant contains information mapping the tgc arguments by position
;; to the template variables.
(defconst *tgc-stage-arguments*
  '(;; See theorem-template-parsing.tl
    ("parsing" "leo-source-file" "initial-json-file"
     "leo-source-file-hash" "initial-json-file-hash")
; Unsupported for now:
;    ;; See theorem-template-canonicalization.tl
;    ("canonicalization" "initial-json-file" "canonicalization-json-file"
;     "initial-json-file-hash" "canonicalization-json-file-hash")
;    ;; See theorem-template-type-inference.tl
;    ("type-inference" "canonicalization-json-file" "type-inferenced-json-file"
;     "canonicalization-json-file-hash" "type-inferenced-json-file-hash")
    ))

(set-state-ok t)

;; Essay on why theorem-file must be an absolute path for tgc.
;; The tgc macro expands into something including a call to certify-book.
;; Certify-book does not evaluate its book file argument, so the string passed
;; to certify book must be computed by the macro expansion.
;; Additionally, certify-book's argument, if relative, is relative to cbd, not PWD.
;; But to generate the theorem file in make-theorem-file, if the file name is relative
;; write-strings-to-file extends the filename to be in PWD.
;; So if we wanted to allow a relative path here, we would have to extend it
;; the same way as make-theorem-file does.
;; In order to do that, we need to do (getenv$ "PWD" state).
;; However, the macro expansion is not allowed to refer to state.
;; Hence, the tgc macro requires that theorem-file be absolute.

;; theorem-file is used in two different contexts with different default directories.
;; In the file I/O context (as in make-thorem-file), relative paths are relative to $PWD,
;; which is the directory that was current when ACL2 was started.
;; In the certify-book context, relative paths are relative to (cbd).

;; WARNING: this macro is probably not suitable for inclusion in a book
;;          that is certified, for a number of reasons.
;; Note: macroexpansion can not refer to state (although it can generate
;;       things that refer to state).
(defmacro tgc (stage template-file theorem-file &rest template-arg-vals)
  `(b* ((template-args (cdr (assoc-equal ,stage *tgc-stage-arguments*)))
        ((unless (equal (len template-args) (len ',template-arg-vals)))
         (progn$ (cw "ERROR: tgc: wrong number of template argument values for STAGE")
                 (exit 1)
                 state))
        (tf ,theorem-file)
        (t-binds (pairlis$ template-args ',template-arg-vals))
        ((unless (check-theorem-file tf))
         (progn$ (cw "ERROR: tf must start with \"/\" (slash)  and end in \".lisp\"")
                 (exit 1)
                 state))
        ((mv erp state)
         (leo-early::make-theorem-file ,template-file tf t-binds state))
        ((when erp)
         (progn$ (cw "ERROR: when making theorem file ~x0 for stage ~x1"
                     tf ,stage)
                 (exit 1)
                 state))
        ((mv erp file-certified state)
         ;; certify-book does not evaluate its arguments, so the file name must be prebuilt
         ;; NOTE: we can probably remove  :oslib and :leo-test-files if we only load top into the tgc image.
         ;; Even better would be if we can remove all ttags from the build that goes into the tgc image.
         (with-output :off :all (certify-book ,(strip-.lisp theorem-file) ? t :ttags (:open-output-channel! :oslib :leo-test-files))))
        ((when (or erp (null file-certified)))
         (progn$ (cw "ERROR: when certifying theorem file ~x0"
                     tf)
                 (exit 1)
                 state)))
     (progn$ (cw "SUCCESS: certified theorem file ~x0" tf)
             (exit 0)
             state)))
