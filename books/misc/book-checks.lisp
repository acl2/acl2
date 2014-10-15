; Checking theories for libraries
; Copyright (C) 2013 Centaur Technology
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


; book-checks.lisp
;
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; This book provides some utilities for checking that libraries don't
;; enable/disable existing rules unexpectedly.

;; :RULE-STATUS-CHANGES <command-descriptor> shows a list of rules that
;;   - existed before the command
;;   - have a different enabled status after the command than before.
;; :RULE-STATUS-CHANGES-SINCE <command-descriptor> is similar but shows the
;;   rules whose status changed after the command.
;; :FIND-THEORY-CHANGES <rune> <command-descriptor> shows the events within the
;;   given command that caused the given rune to become enabled/disabled.  Each
;;   entry shows whether it was enabled/disabled and the hierarchy of nested
;;   events under which it happened.
;; :FIND-THEORY-CHANGES-SINCE <rune> <command-descriptor> shows the events since
;;   the given command that caused the given rune to become enabled/disabled.

;; Here a command-descriptor is the sort of thing you give to ACL2 history
;; queries like :pcb, :pbt, etc.  So, :x, :x-1, 1, 2, function-name, theorem-name, etc.

(program)
(set-state-ok t)

;; All this is really doing is computing the two set differences
;; prev-enabled - (existent ^ post-enabled)
;; and
;; (existent ^ post-enabled) - prev-enabled
;; so this could probably be made quite a bit faster if necessary.
;; On the other hand, it'd be nice not to include any other books in this book
;; in order to do so.
(defun collect-rule-status-changes (existent prev-enabled post-enabled)
  (if (atom existent)
      nil
    (let ((prev (consp (member-equal (car existent) prev-enabled)))
          (post (consp (member-equal (car existent) post-enabled))))
      (if (eq prev post)
          (collect-rule-status-changes (cdr existent) prev-enabled post-enabled)
        (cons (list (if prev 'disable 'enable) (car existent))
              (collect-rule-status-changes (cdr existent) prev-enabled post-enabled))))))

(defun rule-status-changes-between (prev-wrld curr-wrld)
  (declare (xargs :mode :program))
  (let* ((curr-theory (current-theory1 curr-wrld nil nil))
         (prev-theory (current-theory1 prev-wrld nil nil))
         (prev-univ (universal-theory-fn1 prev-wrld nil nil)))
    (collect-rule-status-changes prev-univ prev-theory curr-theory)))

(defun rule-status-changes-fn (cd state)
  (declare (xargs :mode :program :stobjs state))
  (er-let*
   ((cmd-wrld (acl2::er-decode-cd cd (w state) 'rule-status-changes
                                  state)))
   (let ((prev-wrld (scan-to-command (cdr cmd-wrld))))
     (value (rule-status-changes-between prev-wrld cmd-wrld)))))

(defun rule-status-changes-since-fn (cd state)
  (declare (xargs :mode :program :stobjs state))
  (er-let*
   ((cmd-wrld (acl2::er-decode-cd cd (w state) 'rule-status-changes
                                  state)))
   (value (rule-status-changes-between cmd-wrld (w state)))))

(defmacro rule-status-changes (cd)
  `(rule-status-changes-fn ,cd state))

(defmacro rule-status-changes-since (cd)
  `(rule-status-changes-since-fn ,cd state))




(defun scan-world-for-theory-changes (rune enabled-before depth stack wrld)
  (if (atom wrld)
      (mv enabled-before nil)
    (case (caar wrld)
      (CURRENT-THEORY
       (mv-let (prev-enabled rest)
         (scan-world-for-theory-changes
          rune enabled-before depth stack (cdr wrld))
         (let* ((post-enabled (consp (member-equal rune (cddar wrld)))))
           (if (eq prev-enabled post-enabled)
               (mv prev-enabled rest)
             (mv post-enabled (cons (cons (if post-enabled 'enable 'disable)
                                          stack)
                                    rest))))))
      (acl2::event-landmark
       (let* ((new-depth (if (consp (caddar wrld))
                             (cdr (caddar wrld))
                           0))
              (stack (cons (nthcdr 4 (car wrld))
                           (nthcdr (+ 1 (- depth new-depth)) stack))))
         (scan-world-for-theory-changes
          rune enabled-before new-depth stack (cdr wrld))))
      (otherwise
       (scan-world-for-theory-changes
        rune enabled-before depth stack (cdr wrld))))))

(defun find-theory-changes-since-fn (rune cd state)
  (er-let*
   ((cmd-wrld (acl2::er-decode-cd cd (w state) 'find-theory-change-since
                                  state)))
   (let* ((enabled-before (consp (member-equal rune (current-theory1 cmd-wrld nil nil))))
          (segment (take (- (len (w state)) (len cmd-wrld)) (w state))))
     (mv-let (enabled res)
       (scan-world-for-theory-changes rune enabled-before 0 nil segment)
       (declare (ignore enabled))
       (value res)))))

(defun find-theory-changes-fn (rune cd state)
  (er-let*
   ((cmd-wrld (acl2::er-decode-cd cd (w state) 'find-theory-change-since state)))
   (let* ((prev-wrld (scan-to-command (cdr cmd-wrld)))
          (enabled-before (consp (member-equal rune (current-theory1 prev-wrld nil nil))))
          (segment (take (- (len cmd-wrld) (len prev-wrld)) cmd-wrld)))
     (mv-let (enabled res)
       (scan-world-for-theory-changes rune enabled-before 0 nil segment)
       (declare (ignore enabled))
       (value res)))))


(defmacro find-theory-changes (rune cd)
  `(find-theory-changes-fn ,rune ,cd state))

(defmacro find-theory-changes-since (rune cd)
  `(find-theory-changes-since-fn ,rune ,cd state))

;; Example use:
;; (include-book "misc/book-checks" :dir :system)
;; (include-book "centaur/gl/gl" :dir :system)
;; :rule-status-changes :x
;;   ->
;; ((DISABLE (:DEFINITION META-EXTRACT-GLOBAL-FACT+))
;;  (DISABLE (:DEFINITION META-EXTRACT-CONTEXTUAL-FACT))
;;  (DISABLE (:DEFINITION ACL2::DUMB-NEGATE-LIT))
;;  (DISABLE (:DEFINITION CONJOIN-CLAUSES))
;;  (DISABLE (:INDUCTION DISJOIN))
;;  (DISABLE (:DEFINITION DISJOIN))
;;  (DISABLE (:DEFINITION ACL2::DISJOIN2))
;;  (DISABLE (:INDUCTION CONJOIN))
;;  (DISABLE (:DEFINITION CONJOIN))
;;  (DISABLE (:DEFINITION ACL2::CONJOIN2))
;;  (DISABLE (:REWRITE DEFAULT-CDR))
;;  (DISABLE (:REWRITE DEFAULT-CAR))
;;  (DISABLE (:INDUCTION INTERSECTION-EQUAL))
;;  (DISABLE (:DEFINITION INTERSECTION-EQUAL))
;;  (DISABLE (:INDUCTION MV-NTH))
;;  (DISABLE (:DEFINITION MV-NTH))
;;  (DISABLE (:DEFINITION CHAR<))
;;  (DISABLE (:INDUCTION INTERSECTP-EQUAL))
;;  (DISABLE (:DEFINITION INTERSECTP-EQUAL))
;;  (DISABLE (:TYPE-PRESCRIPTION TAKE))
;;  (DISABLE (:DEFINITION TAKE))
;;  (DISABLE (:INDUCTION SET-DIFFERENCE-EQUAL))
;;  (DISABLE (:DEFINITION SET-DIFFERENCE-EQUAL))
;;  (DISABLE (:REWRITE UPPER-CASE-P-CHAR-UPCASE))
;;  (DISABLE (:REWRITE LOWER-CASE-P-CHAR-DOWNCASE))
;;  (DISABLE (:REWRITE COERCE-INVERSE-2))
;;  (DISABLE (:REWRITE COERCE-INVERSE-1))
;;  (DISABLE (:INDUCTION SUBSETP-EQUAL))
;;  (DISABLE (:DEFINITION SUBSETP-EQUAL))
;;  (DISABLE (:INDUCTION MAKE-CHARACTER-LIST))
;;  (DISABLE (:DEFINITION MAKE-CHARACTER-LIST))
;;  (DISABLE (:DEFINITION LENGTH)))

;; (acl2::find-theory-changes (:definition meta-extract-global-fact+) :x)
;; ((DISABLE
;;   (IN-THEORY (DISABLE META-EXTRACT-CONTEXTUAL-FACT
;;                       META-EXTRACT-GLOBAL-FACT))
;;   (INCLUDE-BOOK
;;    "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/clause-processors/meta-extract-user.lisp"
;;    :DIR :SYSTEM)
;;   (INCLUDE-BOOK
;;    "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/misc/interp-function-lookup.lisp")
;;   (INCLUDE-BOOK
;;     "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/misc/defapply.lisp")
;;   (INCLUDE-BOOK
;;    "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/gl/generic-geval.lisp")
;;   (INCLUDE-BOOK
;;        "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/gl/gtypes.lisp")
;;   (INCLUDE-BOOK
;;    "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/gl/general-objects.lisp")
;;   (INCLUDE-BOOK
;;      "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/gl/ite-merge.lisp")
;;   (INCLUDE-BOOK
;;        "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/gl/g-if.lisp")
;;   (INCLUDE-BOOK
;;       "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/gl/g-logapp.lisp")
;;   (INCLUDE-BOOK
;;        "/n_mounts/f0-fs18/fv2/sswords/e/acl2/books/centaur/gl/gl.lisp")))
