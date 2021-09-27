; cert.pl build system
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>
;
; NOTE: This file is not part of the standard ACL2 books build process; it is
; part of an experimental build system.  The ACL2 developers do not maintain
; this file.

(in-package "ACL2")

(mv-let (channel state)
  (open-output-channel "Makefile-features" :character state)
  (if (not channel)
      (progn$
       (er hard? '|Makefile-features| "Error opening Makefile-features?")
       state)
    (let* ((state (princ$ "export ACL2_FEATURES_DETECTED := 1" channel state))
           (state (newline channel state))
           (state (princ$ #-(and gcl (not ansi-cl)) "export ACL2_HAS_ANSI := 1"
                          #+(and gcl (not ansi-cl)) "export ACL2_HAS_ANSI := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HAS_ANSI" channel state))
           (state (newline channel state))
           (state (princ$ #+acl2-par "export ACL2_HAS_PARALLEL := 1"
                          #-acl2-par "export ACL2_HAS_PARALLEL := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HAS_PARALLEL" channel state))
           (state (newline channel state))
           (state (princ$ #+non-standard-analysis "export ACL2_HAS_REALS := 1"
                          #-non-standard-analysis "export ACL2_HAS_REALS := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HAS_REALS" channel state))
           (state (newline channel state))
           (state (princ$ #+acl2-devel "export ACL2_HAS_ACL2_DEVEL := 1"
                          #-acl2-devel "export ACL2_HAS_ACL2_DEVEL := "
                          channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HAS_ACL2_DEVEL" channel state))
           (state (newline channel state))
           (state (princ$ "export ACL2_COMP_EXT := " channel state))
           (state (princ$ (@ compiled-file-extension) channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_COMP_EXT" channel state))
           (state (newline channel state))
           (state (princ$ "export ACL2_HOST_LISP := " channel state))
           (host-lisp (symbol-name (@ host-lisp)))
           (state (princ$ host-lisp channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_HOST_LISP" channel state))
           (state (newline channel state))
           (state (princ$ "export USE_QUICKLISP ?= " channel state))
           (state (princ$ (if (equal host-lisp "GCL") "0" "1") channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += USE_QUICKLISP" channel state))
           (state (newline channel state))
           (state (princ$ "export ACL2_THINKS_BOOK_DIR_IS := " channel state))
           (state (princ$ (f-get-global 'system-books-dir state) channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_THINKS_BOOK_DIR_IS" channel state))
           (state (newline channel state))
; Matt K. mod: It seems to be too much trouble to arrange that the
; @useless-runes.lsp files be used for ACL2(r) and ACL2(p) in addition to ACL2.
           #-(or acl2-par non-standard-analysis)
           (state (princ$ "export ACL2_USELESS_RUNES ?= -25" channel state))
           (state (newline channel state))
           (state (princ$ "EXPORTED_VARS += ACL2_USELESS_RUNES" channel state))
           (state (newline channel state))
           (state (close-output-channel channel state)))
      state)))

(defun write-file-if-obj-differs (filename object state)
  ;; Reads the given file and checks whether the first object it contains
  ;; equals the given object.  If not, overwrites that file with the given
  ;; object.
  (declare (xargs :mode :program :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (mv-let (need-to-write-file-p state)
      (if channel
          (mv-let (eof val state)
            (read-object channel state)
            (let ((state (close-input-channel channel state)))
              (if (and (not eof) (equal val object))
                  ;; File was read and object matches.
                  (mv nil state)
                ;; No object in the file or didn't match.
                (mv t state))))
        ;; File didn't exist.
        (mv t state))

      (if need-to-write-file-p
          (mv-let (channel state)
            (open-output-channel filename :object state)
            (if channel
                (let* ((state (print-object$ object channel state)))
                  (prog2$ (cw "Wrote ~s0~%" filename)
                          (close-output-channel channel state)))
              (prog2$ (cw "Error writing to ~s0~%" filename)
                      state)))
        (prog2$ (cw "No need to write ~s0~%" filename)
                state)))))

(write-file-if-obj-differs "first-order-like-terms-and-out-arities.certdep"
                           *first-order-like-terms-and-out-arities*
                           state)

(write-file-if-obj-differs "acl2-exports.certdep"
                           *acl2-exports*
                           state)

(write-file-if-obj-differs "acl2-version.certdep"
                           (f-get-global 'acl2-version state)
                           state)

(write-file-if-obj-differs "ground-zero-theory.certdep"
                           (let ((world (w state))) (current-theory 'acl2::ground-zero))
                           state)


#||
(set-raw-mode-on!)

;; Based on note-fns-in-form from interface-raw.lsp
(defun collect-defrecs-in-form (form acc)
  (and (consp form)
       (case (car form)
         (defrec (cons (cadr form) acc))
         (save-def (collect-defrecs-in-form (cadr form) acc))
         ((when-pass-2)
          (progn (loop for x in (cdr form)
                       do (setq acc (collect-defrecs-in-form x acc)))
                 acc))
         ((encapsulate when)
          (progn (loop for x in (cddr form)
                       do (setq acc (collect-defrecs-in-form x acc)))
                 acc))
         (partial-encapsulate
          (progn (loop for x in (cdddr form)
                       do (setq acc (collect-defrecs-in-form x acc)))
                 acc))
         ((skip-proofs local)
          (collect-defrecs-in-form (cadr form) acc))
         (t acc))))

(defun collect-defrecs-in-file (filename acc)
  (with-open-file
    (str filename :direction :input)
    (let ((avrc (cons nil nil))
          x)
      (loop while (not (eq (setq x (read str nil avrc))
                           avrc))
            do
            (setq acc (collect-defrecs-in-form x acc)))
      acc)))

(defun collect-defrecs-in-files (filenames acc)
  (loop for filename in filenames
        do (setq acc (collect-defrecs-in-file (concatenate 'string "../../" filename ".lisp")
                                              acc)))
  acc)

(defconst *defrecs*
  (time$ (collect-defrecs-in-files *acl2-files* nil)))

||#

(defconst *defrecs*
  '(CL-CACHE-LINE CL-CACHE
    LD-PROMPT-MEMO SAR ABSSTOBJ-METHOD
    CERT-OBJ HCOMP-BOOK-HT-ENTRY GOAL
    PC-STATE LAMBDA-INFO LOOP$-ALIST-ENTRY
    TRANSLATE-CERT-DATA-RECORD ABSSTOBJ-INFO
    DEFERRED-TTAG-NOTE TESTS-AND-CALL
    LDD-STATUS COMMAND-NUMBER-BASELINE-INFO
    PROVED-FUNCTIONAL-INSTANCES-ALIST-ENTRY
    CLAUSE-PROCESSOR-HINT
    POOL-ELEMENT GOAL-TREE JUSTIFICATION
    TESTS-AND-CALLS TESTS-AND-ALISTS
    CANDIDATE BDDSPV BDD-RULE BDDNOTE
    GAG-STATE GAG-INFO PROVE-SPEC-VAR
    FC-ACTIVATION RW-CACHE-ENTRY
    EXPAND-HINT BUILT-IN-CLAUSE
    INDUCTION-RULE GENERALIZE-RULE
    ELIM-RULE FORWARD-CHAINING-RULE GFRAME
    STEP-LIMIT-RECORD METAFUNCTION-CONTEXT
    REWRITE-CONSTANT CURRENT-LITERAL
    LINEAR-LEMMA REWRITE-RULE
    PEQUIVS-PROPERTY PEQUIV-INFO
    PEQUIV-PATTERN PEQUIV CONGRUENCE-RULE
    BOUNDER-CORRECTNESS BIG-SWITCH-RULE
    SIGNATURE-RULE TAU TAU-INTERVAL
    SUMMARY-DATA TYPE-SET-INVERTER-RULE
    ACCP-ENTRY ACCP-INFO ANCESTOR
    TYPE-PRESCRIPTION RECOGNIZER-TUPLE
    CLAUSE-ID CERTIFY-BOOK-INFO
    THEORY-INVARIANT-RECORD
    ENABLED-STRUCTURE
    LINEAR-POT POLY FC-DERIVATION ASSUMPTION
    ASSUMNOTE HISTORY-ENTRY APPLY$-BADGE
    COMMAND-TUPLE ATTACHMENT-COMPONENT
    ATTACHMENT MEMO-MAX-SIZES-ENTRY
    MEMOIZE-INFO-HT-ENTRY
    DEF-BODY DEFSTOBJ-TEMPLATE
    DEFSTOBJ-FIELD-TEMPLATE
    DEFSTOBJ-REDUNDANT-RAW-LISP-DISCRIMINATOR-VALUE
    STATE-VARS IO-RECORD))

(defun write-defrec-certdeps (defrecs state)
  (declare (xargs :mode :program :stobjs state))
  (if (atom defrecs)
      state
    (let* ((x (car defrecs))
           (body (getpropc (record-maker-function-name x) 'macro-body :none (w state)))
           (state (if (eq body :none)
                      state
                    (write-file-if-obj-differs
                     (concatenate 'string "defrec-certdeps/" (symbol-name x) ".certdep")
                     (getpropc (record-maker-function-name x) 'macro-body nil (w state))
                     state))))
      (write-defrec-certdeps (cdr defrecs) state))))

(write-defrec-certdeps *defrecs* state)

(good-bye 0)

