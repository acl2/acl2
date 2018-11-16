;; ===================================================================
;; 
;; Copyright (C) 2018, David Greve
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms of
;; the 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.
;; 
;; ===================================================================
(in-package "ACL2")

;; ===================================================================
;;
;; Trying to use tau in an extended metafunction context
;;
;; ===================================================================

;; ===================================================================
;;
;; Functions to build a tau-alist and a calist
;;
;; NOTE: We simply use 'nil for both in the current example.  It is
;; not clear that building these data structures helps in computing
;; tau in our case.
;;
;; ===================================================================

;; We use this to compute a tau-alist from a list of triples.
;; Modified from (tau-clause1p triples tau-alist type-alist pot-lst ens wrld calist) in tau.lisp
(defun tau-alist-rec (triples tau-alist type-alist pot-lst ens wrld calist)
  (declare (xargs :mode :program))
  (cond
   ((endp triples) (mv tau-alist calist))
   (t (mv-let
       (contradictionp mbt mbf tau-alist calist)
       (tau-assume nil (caddr (car triples))
                   tau-alist type-alist pot-lst
                   ens wrld calist)
       (declare (ignore contradictionp mbf mbt))
       (tau-alist-rec (cdr triples) tau-alist type-alist pot-lst ens wrld calist)))))

;; We use this to compute a tau-alist from a clause.
;; Modified from (tau-clausep clause ens wrld state calist) in prove.lisp:
(defun tau-alist (clause type-alist pot-lst ens wrld)
  (declare (xargs :mode :program))
  (let ((triples (merge-sort-car-<
                  (annotate-clause-with-key-numbers clause
                                                    (len clause)
                                                    0 wrld))))
    (tau-alist-rec triples nil type-alist pot-lst ens wrld nil)))

;; ===================================================================
;;
;; Functions to try to call into tau
;;
;; ===================================================================

;; A program mode function that returns the decoded tau of term 
(defun get-term-tau-program (term mfc ens wrld)
  (declare (xargs :mode :program))
  (let ((type-alist (mfc-type-alist mfc))
        (pot-lst    (access metafunction-context mfc :simplify-clause-pot-lst))
        ;; (clause     (access rewrite-constant
        ;;                     (access metafunction-context mfc :rcnst)
        ;;                     :current-clause))
        )
    ;;(mv-let (tau-alist calist) (tau-alist clause type-alist pot-lst ens wrld)
    (let ((tau-alist nil)
          (calist    nil))
      (mv-let (tau calist) (tau-term term tau-alist type-alist pot-lst ens wrld calist)
        (declare (ignore calist))
        (decode-tau tau term)))))

(set-state-ok t)

;; We use this to jump the :logic / :program divide
(defun get-term-tau (term mfc state)
  (let ((ens        (f-get-global 'global-enabled-structure state))
        (wrld       (w state)))
    ;;
    ;; This doesn't work in stock ACL2.  
    ;; See the HACK note below for our workaround.
    ;;
    (mv-let (hit res) (magic-ev-fncall 'get-term-tau-program `(,term ,mfc ,ens ,wrld) state t t)
      (declare (ignore hit))
      res)))

;; ===================================================================
;;
;; A simple logical theory with a tau-like rule ..
;;
;; ===================================================================

(defun foo (x)
  (ifix x))

(defthm foo-signature
  (implies
   (natp x)
   (natp (foo x)))
  :rule-classes (:type-prescription))

(in-theory (disable foo))

(defstub pred (x) nil)

;; ===================================================================
;;
;; A drop dead simple extended meta-function that tries to compute
;; the tau of the given trigger term ..
;;
;; ===================================================================

(defevaluator tau-eval tau-eval-list
  (
   (foo x)
   (hide x)
   ))

(set-irrelevant-formals-ok t)

(defun mf-tau (term mfc state)
  (let ((zed (cw "computed tau : ~x0~%" (get-term-tau term mfc state))))
    (declare (ignore zed))
    `(hide ,term)))

(defun mf-tau-hyp (term mfc state)
  (declare (ignore term mfc state))
  *t*)

(defthm *meta*-mf-compute-tau
  (implies (and (pseudo-termp x)
                (alistp a)
                (tau-eval (mf-tau-hyp x mfc state) a) 
                )
           (equal (tau-eval x a)
                  (tau-eval (mf-tau x mfc state) a)))
  :hints (("Goal" :expand (:Free (x) (hide x))))
  :rule-classes ((:meta :trigger-fns (foo))))

;; ===================================================================
;;
;; HACK Note:
;;
;; Our experiement fails on stock ACL2 because magic-ev-fncall enters
;; "safe-mode" and we get the following error:
;; 
;; HARD ACL2 ERROR in PROGRAM-ONLY:  The call
;; (EV-FNCALL-W-BODY O-FINP (0) <world> NIL NIL T ...)
;; is an illegal call of a function that has been marked as ``program-
;; only,'' presumably because it has special raw Lisp code and safe-mode
;; is active.  See :DOC program-only for further explanation and a link
;; to possible workarounds.
;; (See :DOC set-iprint to be able to see elided values in this message.)
;;
;;
;; To run it successfully, we modify magic-ev-funcall as follows:
;;
;; ===================================================================

(progn 
(defttag :unsafe-mode)  
(progn! (set-raw-mode t)

(defun magic-ev-fncall (fn args state hard-error-returns-nilp aok)
  (let* ((wrld (w state))
         (programp/stobjs-out
          (ev-fncall-w-guard fn args wrld
                             (f-get-global 'temp-touchable-fns state))))
    (cond
     (programp/stobjs-out
      (if (car programp/stobjs-out)

;;           (state-free-global-let*
;;            ((safe-mode t))                ;; <<-- enters safe mode
;;            (raw-ev-fncall-simple fn args
;;                                  wrld
;;                                  hard-error-returns-nilp
;;                                  aok
;;                                  t
;;                                  (cdr programp/stobjs-out)))
;;
          (raw-ev-fncall-simple fn args     ;; <<-- no safe mode
                                wrld
                                hard-error-returns-nilp
                                aok
                                t
                                (cdr programp/stobjs-out))
        (raw-ev-fncall-simple fn args wrld hard-error-returns-nilp aok nil
                              (cdr programp/stobjs-out))))
     (t
      (let ((msg
             (msg "~%~%Meta-level function Problem: Magic-ev-fncall attempted ~
                   to apply ~X02 to argument list ~X12.  This is illegal ~
                   because ~@3.  The meta-level function computation was ~
                   ignored.~%~%"
                  fn
                  args
                  (abbrev-evisc-tuple *the-live-state*)
                  (cond
                   ((not (symbolp fn))
                    (msg "~x0 is not a symbol" fn))
                   ((not (true-listp args))
                    (msg "that argument list is not a true list"))
                   ((eq (getpropc fn 'formals t wrld) t)
                    (msg "~x0 is not a known function symbol in the current ~
                          ACL2 logical world"
                         fn))
                   ((not (eql (length args)
                              (length (getpropc fn 'formals t wrld))))
                    (msg "the length of that argument list is ~x0, but ~x1 ~
                          takes ~x2 arguments"
                         (length args)
                         fn
                         (length (getpropc fn 'formals t wrld))))
                   (t

; Since we don't expect many direct calls of magic-ev-fncall and we have
; covered most cases above, we leave it up to the user to investigate which
; part of ev-fncall-w-guard fails.  The condition (all-nils stobjs-in) from
; ev-fncall-w-guard1 is automatically met here, since stobjs could not be put
; into the list, args.

                    (msg "even though the call of ~x0 is well-formed, it ~
                          fails to satisfy ~x1"
                         fn
                         'ev-fncall-w-guard))))))
        (mv t msg))))))
))

;; ===================================================================
;;
;; We can watch all the action take place with the following (thm ..)
;;
;; ===================================================================

#+joe
(trace$ get-term-tau-program)

#+joe
(thm 
 (implies
  (and
   (natp x)
   (pred (foo x)))
  (< 3 (foo x))))

;; After making the change to magic-ev-fncall, our meta-function
;; generates the following output when the above 'thm' is submitted:
;;
;; computed tau : 
;; (AND (ACL2-NUMBERP (FOO X))
;;      (INTEGERP (FOO X))
;;      (RATIONALP (FOO X))
;;      (EQLABLEP (FOO X))
;;      (NATP (FOO X))
;;      (O-FINP (FOO X))
;;      (32-BIT-INTEGERP (FOO X))
;;      (FILE-CLOCK-P (FOO X))
;;      (<= 0 (FOO X))
;;      (<= (FOO X) 3)
;;      (NOT (CHARACTERP (FOO X)))
;;      (NOT (COMPLEX-RATIONALP (FOO X)))
;;      (NOT (CONSP (FOO X)))
;;      (NOT (STRINGP (FOO X)))
;;      (NOT (SYMBOLP (FOO X)))
;;      (NOT (MINUSP (FOO X)))
;;      (NOT (BOOLEANP (FOO X)))
;;      (NOT (WEAK-IO-RECORD-P (FOO X)))
;;      (NOT (WEAK-CURRENT-LITERAL-P (FOO X)))
;;      (NOT (WEAK-ABSSTOBJ-INFO-P (FOO X)))
;;      (NOT (PROPER-CONSP (FOO X)))
;;      (NOT (IMPROPER-CONSP (FOO X)))
;;      (NOT (STANDARD-CHAR-P (FOO X)))
;;      (NOT (ALPHA-CHAR-P (FOO X)))
;;      (NOT (UPPER-CASE-P (FOO X)))
;;      (NOT (LOWER-CASE-P (FOO X)))
;;      (NOT (KEYWORDP (FOO X)))
;;      (NOT (OPEN-CHANNEL1 (FOO X)))
;;      (NOT (READABLE-FILE (FOO X)))
;;      (NOT (WRITTEN-FILE (FOO X)))
;;      (NOT (READ-FILE-LISTP1 (FOO X)))
;;      (NOT (WRITABLE-FILE-LISTP1 (FOO X)))
;;      (NOT (BAD-ATOM (FOO X))))

