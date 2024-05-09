; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file other-events.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun chk-embedded-event-form (form orig-form wrld ctx state names
                                     in-local-flg in-encapsulatep
#|
                                     make-event-chk)
|#
                                     make-event-chk ;patch;
; patch file: new argument to extend *expansion-stack*
                                     &optional ext-exp) ;patch;

; WARNING: Keep this in sync with destructure-expansion, elide-locals-rec,
; make-include-books-absolute, and find-first-non-local-name.

; Note: For a test of this function, see the reference to foo.lisp below.

; Orig-form is used for error reporting.  It is either nil, indicating that
; errors should refer to form, or else it is a form from a superior call of
; this function.  So it is typical, though not required, to call this with
; orig-form = nil at the top level.  If we encounter a macro call and orig-form
; is nil, then we set orig-form to the macro call so that the user can see that
; macro call if the check fails.

; This function checks that form is a tree whose tips are calls of the symbols
; listed in names, and whose interior nodes are each of one of the following
; forms.

; (local &)
; (skip-proofs &)
; (with-cbd dir form) ; dir a string
; (with-current-package pkg form) ; pkg a string
; (with-guard-checking-event g &) ; g in *guard-checking-values*; (quote g) ok
; (with-output ... &)
; (with-prover-step-limit ... &)
; (with-prover-time-limit ... &)
; (make-event #)

; where each & is checked.  The # forms above are unrestricted, although the
; result of expanding the argument of make-event (by evaluation) is checked.
; Note that both 'encapsulate and 'progn are typically in names, and their
; sub-events aren't checked by this function until evaluation time.

; Formerly we also checked here that include-book is only applied to absolute
; pathnames.  That was important for insuring that the book that has been read
; into the certification world is not dependent upon :cbd.  Remember that
; (include-book "file") will find its way into the portcullis of the book we
; are certifying and there is no way of knowing in the portcullis which
; directory that book comes from if it doesn't explicitly say.  However, we now
; use fix-portcullis-cmds to modify include-book forms that use relative
; pathnames so that they use absolute pathnames instead, or cause an error
; trying.

; We allow defaxioms, skip-proofs, and defttags in the portcullis, but we mark
; the book's certificate appropriately.

; In-local-flg is used to enforce restrictions in the context of LOCAL on the
; use of (table acl2-defaults-table ...), either directly or by way of events
; such as defun-mode events and set-compile-fns that set this table.  A non-nil
; value of in-local-flg means that we are in the scope of LOCAL.  In that case,
; if we are lexically within an encapsulate but not LOCAL when restricted to
; the nearest such encapsulate, then in-local-flg is 'local-encapsulate.
; Otherwise, if we are in the scope of LOCAL, but we are in an included book
; and not in the scope of LOCAL with respect to that book, then in-local-flg is
; 'local-include-book.

; Moreover, we do not allow local defaxiom events.  Imagine locally including a
; book that has nil as a defaxiom.  You can prove anything you want in your
; book, and then when you later include the book, there will be no trace of the
; defaxiom in your logical world!

; We do not check that the tips are well-formed calls of the named functions
; (though we do ensure that they are all true lists).

; If names is primitive-event-macros and form can be translated and evaluated
; without error, then it is in fact an embedded event form as described in :DOC
; embedded-event-form.

; We sometimes call this function with names extended by the addition of
; 'DEFPKG.

; If form is rejected, the error message is that printed by str, with #\0 bound
; to the subform (of form) that was rejected.

; We return a value triple (mv erp val state).  If erp is nil then val is the
; event form to be evaluated.  Generally that is the result of macroexpanding
; the input form.  However, if (perhaps after some macroexpansion) form is a
; call of local that should be skipped, then val is nil.

  (let* ((er-str

; Below, the additional er arguments are as follows:
; ~@1: a reason specific to the context, or "" if none is called for.
; ~@2: original form message.
; ~@3: additional explanation, or "".

          "The form ~x0 is not an embedded event form~@1.  See :DOC ~
           embedded-event-form.~@2~@3")
         (local-str "The form ~x0 is not an embedded event form in the ~
                     context of LOCAL~@1.  See :DOC embedded-event-form.~@2~@3")
         (encap-str "The form ~x0 is not an embedded event form in the ~
                     context of ENCAPSULATE~@1.  See :DOC ~
                     embedded-event-form.~@2~@3"))
    (cond ((or (atom form)
               (not (symbolp (car form)))
               (not (true-listp (cdr form))))
           (er soft ctx er-str
               form
               ""
               (chk-embedded-event-form-orig-form-msg orig-form state)
               ""))
          ((and (eq (car form) 'local)
                (consp (cdr form))
                (null (cddr form)))
           (cond
            ((eq (ld-skip-proofsp state) 'include-book)

; Keep this in sync with the definition of the macro local; if we evaluate the
; cadr of the form there, then we need to check it here.

             (value nil))
            (t
; patch file addition:
             (when ext-exp (push-expansion-stack (car form))) ;patch;
             (er-let* ((new-form (chk-embedded-event-form
                                  (cadr form) orig-form wrld ctx state names
                                  t in-encapsulatep
#|
                                  make-event-chk)))
|#
; patch file addition of ext-exp argument:
                                  make-event-chk ext-exp))) ;patch;
                      (value (and new-form (list (car form) new-form)))))))
          ((and (eq in-local-flg t)
                (consp form)
                (eq (car form) 'table)
                (consp (cdr form))
                (eq (cadr form) 'acl2-defaults-table))
           (er soft ctx local-str
               form
               " because it sets the acl2-defaults-table in a local context.  ~
                A local context is not useful when setting this table, since ~
                the acl2-defaults-table is restored upon completion of ~
                encapsulate, include-book, and certify-book forms; that is, ~
                no changes to the acl2-defaults-table are exported"
               (chk-embedded-event-form-orig-form-msg orig-form state)
               ""))
          ((and (eq in-local-flg t)
                (consp form)
                (member-eq (car form)
                           *acl2-defaults-table-macros*))
           (er soft ctx local-str
               form
               " because it implicitly sets the acl2-defaults-table in a ~
                local context; see :DOC acl2-defaults-table, in particular ~
                the explanation about this error message"
               (chk-embedded-event-form-orig-form-msg orig-form state)
               ""))
          ((and in-local-flg (eq (car form) 'defaxiom))
           (er soft ctx local-str
               form
               " because it adds an axiom whose traces will disappear"
               (chk-embedded-event-form-orig-form-msg orig-form state)
               ""))
          ((and in-encapsulatep (eq (car form) 'defaxiom))
           (er soft ctx encap-str
               form
               " because we do not permit defaxiom events in the scope of an ~
                encapsulate"
               (chk-embedded-event-form-orig-form-msg orig-form state)
               ""))
          ((and in-local-flg
                (member-eq (car form) '(add-include-book-dir!
                                        delete-include-book-dir!)))
           (er soft ctx local-str
               form
               (msg " (see :DOC ~x0)" (car form))
               (chk-embedded-event-form-orig-form-msg orig-form state)
               ""))
; patch file: Allow non-local include-book in encapsulate.
          #+skip ;patch;
          ((and (eq (car form) 'include-book)
                in-encapsulatep
                (or (eq in-local-flg nil)
                    (eq in-local-flg 'local-encapsulate)))

; Through Version_4.2, the error message below added: "We fear that such forms
; will generate unduly large constraints that will impede the successful use of
; :functional-instance lemma instances."  However, this message was printed
; even for encapsulates with empty signatures.

; It is probably sound in principle to lift this restriction, but in that case
; case we will need to visit all parts of the code which could be based on the
; assumption that include-book forms are always local to encapsulate events.
; See for example the comment about encapsulate in make-include-books-absolute;
; the paragraph labeled (2) in the Essay on Hidden Packages (file axioms.lisp);
; and the comment about "all include-books are local" near the end of
; encapsulate-fn.  By no means do we claim that these examples are exhaustive!
; Even if we decide to loosen this restriction, we might want to leave it in
; place for encapsulates with non-empty signatures, for the reason explained in
; the "We fear" quote above.

           (er soft ctx encap-str
               form
               " because we do not permit non-local include-book forms in the ~
                scope of an encapsulate.  Consider moving your include-book ~
                form outside the encapsulates, or else making it local"
               (chk-embedded-event-form-orig-form-msg orig-form state)
               ""))
          ((member-eq (car form) names)

; Names is often primitive-event-macros or an extension, and hence
; contains encapsulate and include-book.  This is quite reasonable,
; since they do their own checking.  And because they restore the
; acl2-defaults-table when they complete, we don't have to worry that
; they are sneaking in a ``local defun-mode.''

           (value form))
          ((and (eq (car form) 'skip-proofs)
                (consp (cdr form))
                (null (cddr form)))
; patch file addition:
           (when ext-exp (push-expansion-stack (car form))) ;patch;
           (pprogn
            (cond ((global-val 'embedded-event-lst wrld)
                   (warning$ ctx "Skip-proofs"
                             "ACL2 has encountered a SKIP-PROOFS form, ~x0, ~
                              in the context of a book or an encapsulate ~
                              event.  Therefore, no logical claims may be ~
                              soundly made in this context.  See :DOC ~
                              SKIP-PROOFS."
                             form))
                  (t state))
            (er-let* ((new-form (chk-embedded-event-form
                                 (cadr form) orig-form wrld ctx state names
                                 in-local-flg in-encapsulatep
#|
                                 make-event-chk)))
|#
; patch file addition of ext-exp argument:
                                 make-event-chk ext-exp))) ;patch;
                     (value (and new-form (list (car form) new-form))))))
          ((and (member-eq (car form) '(with-cbd
                                        with-current-package
                                        with-guard-checking-event
                                        with-output
                                        with-prover-step-limit
                                        with-prover-time-limit))
                (true-listp form))

; The macro being called will check the details of the form structure.

           (cond
            ((and (eq (car form) 'with-guard-checking-event)
                  (or (atom (cdr form))
                      (let ((val (cadr form)))
                        (not (case-match val
                               (('quote x)
                                (member-eq x *guard-checking-values*))
                               (& (member-eq val *guard-checking-values*)))))))
             (er soft ctx er-str
                 form
                 ""
                 (chk-embedded-event-form-orig-form-msg orig-form state)
                 (msg "~|The macro ~x0 requires the second argument to be a ~
                       constant from the list ~x1, or of the form (QUOTE X) ~
                       for such a constant, X."
                      'with-guard-checking-event
                      *guard-checking-values*)))
            ((and (member-eq (car form) '(with-cbd with-current-package))
                  (not (stringp (cadr form))))
             (er soft ctx er-str
                 form
                 ""
                 (chk-embedded-event-form-orig-form-msg orig-form state)
                 (msg "~|The macro ~x0 requires the second argument to be a ~
                       string when used in an event context."
                      (car form))))
#|
            (t (er-let* ((new-form (chk-embedded-event-form
|#
; patch file addition:
            (t (when ext-exp (push-expansion-stack (car form))) ;patch;
               (er-let* ((new-form (chk-embedded-event-form ;patch;
                                    (car (last form))
                                    orig-form wrld ctx state
                                    names in-local-flg
#|
                                    in-encapsulatep make-event-chk)))
|#
; patch file addition of ext-exp argument:
                                    in-encapsulatep make-event-chk ext-exp))) ;patch;
                 (value (and new-form
                             (append (butlast form 1)
                                     (list new-form))))))))
          ((eq (car form) 'make-event)
           (cond ((and make-event-chk

; Here we are doing just a bit of a sanity check.  It's not used when
; redefinition is active, nor is it complete; see below.  But it's cheap and
; it could catch some errors.

                       (not (and (true-listp form)
                                 (or (consp (cadr (member-eq :check-expansion
                                                             form)))
                                     (consp (cadr (member-eq :expansion?
                                                             form))))))

; We avoid this check when redefinition is active, and here's why.  Consider
; the following example.  In the first pass of encapsulate there are no calls
; of make-event so the resulting expansion-alist is empty.  But in the second
; pass, process-embedded-events is called with make-event-chk = t, which
; *would* result in the error below when (foo) is evaluated (because no
; make-event expansion was saved for (foo) in the first pass) -- except, we
; avoid this check when redefinition is active.

;   (redef!)
;   (encapsulate ()
;     (defmacro foo () '(make-event '(defun f (x) x)))
;     (local (defmacro foo () '(defun f (x) (cons x x))))
;     (foo))

; Moreover, this check is not complete.  Consider the following variant of the
; example just above, the only difference being the progn wrapper.

;   (redef!)
;   (encapsulate ()
;     (defmacro foo () '(progn (make-event '(defun f (x) x))))
;     (local (defmacro foo () '(defun f (x) (cons x x))))
;     (foo))

; Because of the progn wrapper, chk-embedded-event-form is called on the
; make-event call with make-event-chk = nil.  So even if we were to avoid the
; redefinition check below, we would not get an error here.

                       (not (ld-redefinition-action state)))
                  (er soft ctx
                      "Either the :check-expansion or :expansion? argument of ~
                       make-event is normally a consp in the present context. ~
                       ~ This is not surprising in some cases, for example, ~
                       when including an uncertified book or calling ~x0 ~
                       explicitly.  But other cases could be evidence of an ~
                       ACL2 bug; consider contacting the ACL2 implementors.  ~
                       Current form:~|~%~X12"
                      'record-expansion
                      form
                      nil))
; patch file note: Expansion-stack is modified in make-event-fn, not here:
                 (t (value form))))
          ((eq (car form) 'record-expansion) ; a macro that we handle specially
           (cond ((not (and (cdr form)
                            (cddr form)
                            (null (cdddr form))))
                  (er soft ctx
                      "The macro ~x0 takes two arguments, so ~x1 is illegal."
                      'record-expansion
                      form))
#|
                 (t (er-progn
|#
; patch file addition:
                 (t (when ext-exp (push-expansion-stack (car form))) ;patch;
                    (er-progn ;patch;
                     (chk-embedded-event-form (cadr form)
                                              nil
                                              wrld ctx state names
                                              in-local-flg
#|
                                              in-encapsulatep nil)
|#
; patch file addition of ext-exp argument:
                                              in-encapsulatep nil nil) ;patch;
                     (chk-embedded-event-form (caddr form)
                                              (or orig-form form)
                                              wrld ctx state names
                                              in-local-flg
#|
                                              in-encapsulatep t)))))
|#
; patch file addition of ext-exp argument:
                                              in-encapsulatep t ext-exp))))) ;patch;
          ((getpropc (car form) 'macro-body nil wrld)
           (cond
            ((member-eq (car form)
                        '(mv mv-let translate-and-test with-local-stobj
                             with-global-stobj))
             (er soft ctx er-str
                 form
                 ""
                 (chk-embedded-event-form-orig-form-msg orig-form state)
                 (msg "~|Calls of the macro ~x0 do not generate an event, ~
                       because this macro has special meaning that is not ~
                       handled by ACL2's event-generation mechanism."
                      (car form))))
            (t
; patch file addition:
             (when ext-exp (push-expansion-stack (car form))) ;patch;
             (er-let*
              ((expansion (macroexpand1 form ctx state)))
              (chk-embedded-event-form expansion
                                       (or orig-form form)
                                       wrld ctx state names
                                       in-local-flg
#|
                                       in-encapsulatep make-event-chk)))))
|#
                                       in-encapsulatep make-event-chk ;patch;
; patch file addition of ext-exp argument:
                                       ext-exp))))) ;patch;
          (t (er soft ctx er-str
                 form
                 ""
                 (chk-embedded-event-form-orig-form-msg orig-form state)
                 "")))))

(defun eval-event-lst (index expansion-alist ev-lst quietp environment
                             in-local-flg last-val other-control kpa
                             caller ctx channel state)

; This function takes a true list of forms, ev-lst, and successively evals each
; one, cascading state through successive elements.  However, it insists that
; each form is an embedded-event-form.  We return a tuple (mv erp value
; expansion-alist kpa-result state), where erp is 'non-event if some member of
; ev-lst is not an embedded event form and otherwise is as explained below.  If
; erp is nil, then: value is the final value (or nil if ev-lst is empty);
; expansion-alist associates the (+ index n)th member E of ev-lst with its
; expansion if there was any make-event expansion subsidiary to E, ordered by
; index from smallest to largest (accumulated in reverse order); and kpa-result
; is derived from kpa as described below.  If erp is not nil, then let n be the
; (zero-based) index of the event in ev-lst that translated or evaluated to
; some (mv erp0 ...) with non-nil erp0.  Then we return (mv t (+ index n)
; state) if the error was during translation, else (mv (list erp0) (+ index n)
; state).  Except, in the special case that there is no error but we find that
; make-event was called under some non-embedded-event form, we return (mv
; 'make-event-problem (+ index n) state).

; Environment is a list containing at most one of 'certify-book or 'pcert, and
; also perhaps 'encapsulate indicate whether we are under a certify-book
; (possibly doing provisional certification) and/or an encapsulate.  Note that
; 'certify-book is not present when certify-book has been called only to write
; out a .acl2x file.

; Other-control is either :non-event-ok, used for progn!, or else t or nil for
; the make-event-chk in chk-embedded-event-form.

; Kpa is generally nil and not of interest, in which case kpa-result (mentioned
; above) is also nil.  However, if eval-event-lst is being called on behalf of
; certify-book, then kpa is initially the known-package-alist just before
; evaluation of the forms in the book.  As soon as a different (hence larger)
; known-package-alist is observed, kpa is changed to the current index, i.e.,
; the index of the event that caused this change to the known-package-alist;
; and this parameter is not changed on subsequent recursive calls and is
; ultimately returned.  Ultimately certify-book will cdr away that many
; expansion-alist entries before calling pkg-names.

; Caller is as in process-embedded-events.  We introduced this argument on the
; advent of setting world global 'cert-replay.  (It wasn't sufficient to query
; the environment argument for this purpose, because we don't want to set
; 'cert-replay here when processing events under a progn.)

; Channel is generally (proofs-co state), but doesn't have to be.

; A non-nil value of quietp suppresses printing of the event and the result.

  (flet ((event-macros (caller)
                       (if (eq caller
                               'eval-some-portcullis-cmds)
                           (cons 'defpkg (primitive-event-macros))
                         (primitive-event-macros))))
    (cond
     ((null ev-lst)
      (pprogn (f-put-global 'last-make-event-expansion nil state)
              (mv nil last-val (reverse expansion-alist) kpa state)))
     (t
      (let ((old-wrld (w state)))
        (pprogn
         (cond
          (quietp state)
          (t
           (io? event nil state
                (channel ev-lst)
                (fms "~%~@0~sr ~@1~*2~#3~[~Q45~/~]~|"
                     (list
                      (cons #\0 (f-get-global 'current-package state))
                      (cons #\1 (defun-mode-prompt-string state))
                      (cons #\2 (list "" ">" ">" ">"
                                      (make-list-ac
                                       (1+ (f-get-global 'ld-level state))
                                       nil nil)))
                      (cons #\3 (if (eq (ld-pre-eval-print state) :never)
                                    1
                                  0))
                      (cons #\4 (car ev-lst))
                      (cons #\5 (term-evisc-tuple nil state))
                      (cons #\r
                            #+:non-standard-analysis
                            (if (f-get-global 'script-mode state)
                                ""
                              "(r)")
                            #-:non-standard-analysis ""))
                     channel state nil))))
         (let (tmp-expansion-stack) ; patch file: added let-binding ;patch;
           (mv-let
             (erp form state)
             (let ((*expansion-stack* *expansion-stack*)) ; patch file: added let-binding ;patch;
               (multiple-value-prog1 ; patch file addition ;patch;
                (cond ((eq other-control :non-event-ok)
                       (mv nil (car ev-lst) state))
                      (t (chk-embedded-event-form (car ev-lst)
                                                  nil
                                                  (w state)
                                                  ctx state
                                                  (event-macros caller)
                                                  in-local-flg
                                                  (member-eq 'encapsulate
                                                             environment)
#|
                                             other-control)))
|#
                                                  other-control ;patch;
; patch file addition of ext-exp argument:
                                                  (member-eq caller ;patch;
                                                             '(encapsulate-pass-1 ;patch;
                                                               progn-fn1 ;patch;
                                                               certify-book))))) ;patch;
; patch file addition:
                (setq tmp-expansion-stack *expansion-stack*))) ;patch;
             (cond
              (erp (pprogn (f-put-global 'last-make-event-expansion nil state)
                           (mv 'non-event index nil nil state)))
              ((null form)
               (eval-event-lst (1+ index) expansion-alist (cdr ev-lst) quietp
                               environment in-local-flg nil other-control kpa
                               caller ctx channel state))
              (t
               (mv-let
                 (erp trans-ans state)
                 (pprogn (f-put-global 'last-make-event-expansion nil state)
                         (if (raw-mode-p state)
                             (acl2-raw-eval form state)

; We avoid the user-stobjs-modified-warning here, since it seems unreasonable
; to warn about the event's result if a user stobj is changed.  Rather, if the
; event itself does evaluation that changes a user stobjs, then that event
; should be held responsible for any such warning.  Thus, make-event takes such
; responsibility for its expansion phase; it is sensitive to LD special
; ld-user-stobjs-modified-warning (see protected-eval and make-event-fn2).

#|
                           (trans-eval-no-warning form ctx state t)))
|#
; patch file: added binding
                    (let ((*expansion-stack* tmp-expansion-stack)) ;patch;
                      (trans-eval-no-warning form ctx state t)))) ;patch;

; If erp is nil, trans-ans is
; ((nil nil state) . (erp' val' replaced-state))
; because ev-lst contains nothing but embedded event forms.

                 (let* ((tuple
                         (cond ((eq other-control :non-event-ok)
                                (let* ((stobjs-out (car trans-ans))
                                       (result (replace-stobjs stobjs-out
                                                               (cdr trans-ans))))
                                  (if (null (cdr stobjs-out)) ; single value
                                      (list nil result)
                                    result)))
                               (t (cdr trans-ans))))
                        (erp-prime (car tuple))
                        (val-prime (cadr tuple)))
                   (cond
                    ((or erp erp-prime)
                     (pprogn
                      (cond ((and (consp (car ev-lst))
                                  (eq (car (car ev-lst)) 'record-expansion))
                             (let ((chan (proofs-co state)))
                               (io? error nil state (chan ev-lst)
                                    (fmt-abbrev "~%Note: The error reported above ~
                                           occurred when processing the ~
                                           make-event expansion of the form ~
                                           ~x0."
                                                (list (cons #\0
                                                            (cadr (car ev-lst))))
                                                0 chan state "~|~%"))))
                            (t state))
                      (f-put-global 'last-make-event-expansion nil state)
                      (mv (if erp t (list erp-prime)) index nil kpa state)))
                    (t
                     (pprogn
                      (cond (quietp state)
                            (t (io? summary nil state
                                    (val-prime channel)
                                    (cond
                                     ((member-eq
                                       'value
                                       (f-get-global 'inhibited-summary-types
                                                     state))
                                      state)
                                     (t
                                      (mv-let
                                        (col state)
                                        (fmt1 "~y0"
                                              (list (cons #\0 val-prime))
                                              0 channel state
                                              (ld-evisc-tuple state))
                                        (declare (ignore col))
                                        state))))))
                      (mv-let
                        (erp expansion0 state)

; We need to cause an error if we have an expansion but are not properly
; tracking expansions.  For purposes of seeing if such tracking is being done,
; it should suffice to do the check in the present world rather than the world
; present before evaluating the form.

                        (get-and-chk-last-make-event-expansion
                         (car ev-lst) (w state) ctx state (event-macros caller))
                        (cond
                         (erp (pprogn
                               (f-put-global 'last-make-event-expansion
                                             nil
                                             state)
                               (mv 'make-event-problem index nil nil state)))
                         (t
                          (mv-let
                            (erp ignored-val state)
                            (cond
                             ((and (eq caller 'certify-book)
                                   (eq (global-val 'cert-replay (w state)) t))
                              (pprogn
                               (set-w 'extension
                                      (global-set 'cert-replay
                                                  (cons index old-wrld)
                                                  (w state))
                                      state)
                               (maybe-add-event-landmark state)))
                             (t (value nil)))
                            (declare (ignore ignored-val))
                            (cond
                             (erp ; very surprising
                              (mv 'make-event-problem index nil nil state))
                             (t
                              (eval-event-lst
                               (1+ index)
                               (cond
                                (expansion0
                                 (acons index
                                        (make-record-expansion?
                                         (car ev-lst)
                                         (mv-let (wrappers base-form)
                                           (destructure-expansion form)
                                           (declare (ignore base-form))
                                           (rebuild-expansion wrappers
                                                              expansion0))

; We only need to add record-expansion when directly under an encapsulate, to
; check redundancy.  See the Essay on Make-event.

                                         (member-eq caller
                                                    '(encapsulate-pass-1
                                                      encapsulate-pass-2)))
                                        expansion-alist))
                                (t expansion-alist))
                               (cdr ev-lst) quietp
                               environment in-local-flg val-prime
                               other-control
                               (cond ((or (null kpa)
                                          (integerp kpa)
                                          (equal kpa
                                                 (known-package-alist state)))
                                      kpa)
                                     (t index))
                               caller ctx channel state)))))))))))))))))))))
  ) ;patch;

(defun process-embedded-events (caller acl2-defaults-table skip-proofsp pkg
                                       ee-entry ev-lst index make-event-chk
                                       cert-data ctx state)

; Warning: This function uses set-w and hence may only be called within a
; revert-world-on-error.  See the statement of policy in set-w.

; This function is the heart of the second pass of encapsulate, include-book,
; and certify-book.  Caller is in fact one of the symbols 'encapsulate-pass-1,
; 'encapsulate-pass-2, 'include-book, 'certify-book, 'defstobj, or
; 'defabsstobj.  Note: There is no function encapsulate-pass-1, but it is still
; a ``caller.''

; Acl2-defaults-table is either a legal alist value for acl2-defaults-table or
; else is one of :do-not-install or :do-not-install!.  If an alist, then we may
; install a suitable acl2-defaults-table before executing the events in ev-lst,
; and the given acl2-defaults-table is installed as the acl2-defaults-table (if
; it is not already there) after executing those events.  But the latter of
; these is skipped if acl2-defaults-table is :do-not-install, and both are
; skipped if acl2-defaults-table is :do-not-install!.

; The name ee-entry stands for ``embedded-event-lst'' entry.  It is consed onto
; the embedded-event-lst for the duration of the processing of ev-lst.  The
; length of that list indicates how deep these evs are.  For example, if the
; embedded-event-lst is

;   ((defstobj ...)
;    (encapsulate nil)
;    (include-book ...)
;    (encapsulate ((p (x y) (nil nil) (nil)) ...)))

; then the ev-lst is the ``body'' of a defstobj, which occurs in the body of an
; encapsulate, which is in an include-book, which is in an encapsulate.

; The shape of an ee-entry is entirely up to the callers and the customers of
; the embedded-event-lst, with three exceptions:
; (a) the ee-entry must always be a consp;
; (b) if the car of the ee-entry is 'encapsulate then the cadr is the internal
;     form signatures of the functions being constrained; and
; (c) if the car of the ee-entry is 'include-book then the cadr is the
;     full-book-name.
; We refer to the signatures in (b) as insigs below and think of insigs as nil
; for all ee-entries other than encapsulates.

; Ev-lst is the list of alleged events.  Pkg is the value we should use for
; current-package while we are processing the events.  This affects how forms
; are prettyprinted.  It also affects how the prompt looks.

; We first extend the current world of state by insigs (if caller is
; 'encapsulate-pass-2) and extend the embedded event list by ee-entry.  We then
; extend further by doing each of events in ev-lst while ld-skip-proofsp is set
; to skip-proofsp, checking that they are indeed embedded-event-forms.  If that
; succeeds, we restore embedded-event-lst, install the world, and return.

; If caller is not 'encapsulate-pass-2, then the return value includes an
; expansion-alist that records the result of expanding away every make-event
; call encountered in the course of processing the given ev-lst.  Each pair (n
; . ev) in expansion-alist asserts that ev is the result of expanding away
; every make-event call during evaluation of the nth member of ev-lst (starting
; with index for the initial member of ev-lst), though if no such expansion
; took place then this pair is omitted.  If caller is 'certify-book, then the
; return value is the cons of this expansion-alist onto either the initial
; known-package-alist, if that has not changed, or else onto the index of the
; first event that changed the known-package-alist (where the initial
; in-package event has index 0).

; If caller is 'encapsulate-pass-2, then since the final world is in STATE, we
; use the value component of the non-erroneous return triple to return the
; world extended by the signatures (and the incremented depth).  That world,
; called proto-wrld3 in the encapsulate essay and below, is useful only for
; computing (via difference) the names introduced by the embedded events.  We
; still need the expansion-alist described in the preceding paragraph, and we
; also need the value returned by the last event.  So the value returned for
; 'encapsulate-pass-2 is a triple consisting of that value, the
; expansion-alist, and this proto-wrld3.

; If an error is caused by the attempt to embed the events, we print a warning
; message explaining and pass the error up.

; The world names used here are consistent with the encapsulate essay.

  (let* ((wrld1 (w state))
         (kpa (known-package-alist state))
         (old-embedded-event-lst
          (global-val 'embedded-event-lst wrld1))
         (new-embedded-event-lst
          (cons ee-entry old-embedded-event-lst))
         (in-local-flg (f-get-global 'in-local-flg state))

; We now declare the signatures of the hidden functions (when we're in pass 2
; of encapsulate), producing what we here call proto-wrld3.  We also extend the
; embedded event list by ee-entry.  After installing that world in state we'll
; execute the embedded events on it to produce the wrld3 of the encapsulation
; essay.

         (proto-wrld3
          (global-set 'embedded-event-lst new-embedded-event-lst
                      (cond
                       ((eq caller 'encapsulate-pass-2)
                        (intro-udf-lst (cadr ee-entry) (cddr ee-entry)
                                       in-local-flg wrld1 state))
                       (t wrld1))))
; patch file addition:
         (*expansion-stack* (if (eq caller 'encapsulate-pass-1) ;patch;
                                (cons 'encapsulate *expansion-stack*) ;patch;
                              *expansion-stack*)) ;patch;
         (state (set-w 'extension proto-wrld3 state)))
    (er-progn
     (cond ((not (find-non-hidden-package-entry pkg kpa))
            (er soft 'in-package
                "The argument to IN-PACKAGE must be a known package name, but ~
                 ~x0 is not.  The known packages are~*1"
                pkg
                (tilde-*-&v-strings
                 '&
                 (strip-non-hidden-package-names kpa)
                 #\.)))
           (t (value nil)))

; If we really executed an (in-package-fn pkg state) it would do the check
; above and cause an error if pkg was unknown.  But we just bind
; current-package to pkg (with "unwind protection") and so we have to make the
; check ourselves.

     (mv-let (erp val/expansion-alist/final-kpa state)
       (state-global-let*
        ((current-package pkg)
         (cert-data cert-data)
         (skip-proofs-by-system

; When we pass in a non-nil value of skip-proofsp, we generally set
; skip-proofs-by-system to a non-nil value here so that install-event will not
; store a 'skip-proofs-seen marker in the world saying that the user has
; specified the skipping of proofs.  However, if we are already skipping proofs
; by other than the system, then we do not want to make such an exception.

          (let ((user-skip-proofsp
                 (and (ld-skip-proofsp state)
                      (not (f-get-global 'skip-proofs-by-system state)))))
            (and (not user-skip-proofsp)
                 skip-proofsp)))
         (ld-skip-proofsp skip-proofsp)
         (ld-always-skip-top-level-locals nil))
        (er-progn

; Once upon a time, under the same conditions on caller as shown below, we
; added '(logic) to the front of ev-lst before doing the eval-event-lst below.
; But if the caller is an include-book inside a LOCAL, then the (LOGIC) event
; at the front is rejected by chk-embedded-event-form.  One might wonder
; whether an erroneous ev-lst would have left us in a different state than
; here.  The answer is no.  If ev-lst causes an error, eval-event-lst returns
; whatever the state was at the time of the error and does not do any cleanup.
; The error is passed up to the revert-world-on-error we know is above us,
; which will undo the (logic) as well as anything else we changed.

; The above remark deals with include-book, but the issue is similar for
; defstobj except that we also need to handle ignored and irrelevant formals as
; well.  Actually we may only need to handle these in the case that we do not
; allow defstobj array resizing, for the resizing and length field functions.
; But for simplicity, we always lay them down for defstobj and defabsstobj.

         (cond ((eq acl2-defaults-table :do-not-install!)
                (value nil))
               ((eq caller 'include-book)

; The following is equivalent to (logic), without the PROGN (value :invisible).
; The PROGN is illegal in Common Lisp code because its ACL2 semantics differs
; from its CLTL semantics.  Furthermore, we can't write (TABLE
; acl2-defaults-table :defun-mode :logic) because, like PROGN, its CLTL
; semantics is different.

                (state-global-let*
                 ((inhibit-output-lst (cons 'summary
                                            (@ inhibit-output-lst))))
                 (table-fn 'acl2-defaults-table
                           '(:defun-mode :logic)
                           state
                           '(table acl2-defaults-table
                                   :defun-mode :logic))))
               ((member-eq caller ; see comments above
                           '(defstobj defabsstobj))
                (state-global-let*
                 ((inhibit-output-lst (cons 'summary
                                            (@ inhibit-output-lst))))
                 (er-progn (table-fn 'acl2-defaults-table
                                     '(:defun-mode :logic)
                                     state
                                     '(table acl2-defaults-table
                                             :defun-mode :logic))
                           (table-fn 'acl2-defaults-table
                                     '(:ignore-ok t)
                                     state
                                     '(table acl2-defaults-table
                                             :ignore-ok t))
                           (table-fn 'acl2-defaults-table
                                     '(:irrelevant-formals-ok t)
                                     state
                                     '(table acl2-defaults-table
                                             :irrelevant-formals-ok
                                             t)))))
               (t
                (value nil)))
         (mv-let
           (erp val expansion-alist final-kpa state)
           (pprogn
            (cond ((or (eq caller 'encapsulate-pass-1)
                       (eq caller 'certify-book))
                   (pprogn (f-put-global 'redo-flat-succ nil state)
                           (f-put-global 'redo-flat-fail nil state)))
                  (t state))
            (eval-event-lst index nil
                            ev-lst
                            (and (ld-skip-proofsp state)
                                 (not (eq caller 'certify-book)))
                            (eval-event-lst-environment
                             (in-encapsulatep new-embedded-event-lst
                                              nil)
                             state)
                            in-local-flg
                            nil make-event-chk
                            (cond ((eq caller 'certify-book) kpa)
                                  (t nil))
                            caller ctx (proofs-co state) state))
           (cond (erp (pprogn
                       (cond ((or (eq caller 'encapsulate-pass-1)
                                  (eq caller 'certify-book))
                              (update-for-redo-flat (- val index)
                                                    ev-lst
                                                    state))
                             (t state))
                       (mv erp val state)))
                 (t (er-progn
                     (if (member-eq acl2-defaults-table
                                    '(:do-not-install :do-not-install!))
                         (value nil)
                       (maybe-install-acl2-defaults-table
                        acl2-defaults-table state))
                     (value (list* val expansion-alist final-kpa))))))))
       (cond
        (erp

; The evaluation of the embedded events caused an error.  If skip-proofsp is t,
; then we have a local incompatibility (because we know the events were
; successfully processed while not skipping proofs earlier).  If skip-proofsp
; is nil, we simply have an inappropriate ev-lst.

         (cond
          ((member-eq caller '(defstobj defabsstobj))
           (value (er hard ctx
                      "An error has occurred while ~x0 was defining the ~
                       supporting functions.  This is supposed to be ~
                       impossible!  Please report this error to the ACL2 ~
                       implementors."
                      caller)))
          (t
           (pprogn
            (warning$ ctx nil
                      (cond
                       ((or (eq skip-proofsp nil)
                            (eq skip-proofsp t))
                        "The attempted ~x0 has failed while trying to ~
                         establish the admissibility of one of the (local or ~
                         non-local) forms in ~#1~[the body of the ~
                         ENCAPSULATE~/the book to be certified~].")
                       ((eq caller 'encapsulate-pass-2)
                        "The error reported above is the manifestation of a ~
                         local incompatibility.  See :DOC ~
                         local-incompatibility.  The attempted ~x0 has failed.")
                       (t "The error reported above indicates that this book ~
                           is incompatible with the current logical world.  ~
                           The attempted ~x0 has failed."))
                      (if (or (eq caller 'encapsulate-pass-1)
                              (eq caller 'encapsulate-pass-2))
                          'encapsulate
                        caller)
                      (if (eq caller 'encapsulate-pass-1) 0 1))
            (mv t nil state)))))
        (t

; The evaluation caused no error.  The world inside state is the current one
; (because nothing but events were evaluated and they each install the world).
; Pop the embedded event list and install that world.  We let our caller extend
; it with constraints if that is necessary.  We return proto-wrld3 so the
; caller can compute the difference attributable to the embedded events.  This
; is how the constraints are determined.

         (let ((state
                (set-w 'extension
                       (global-set 'embedded-event-lst
                                   old-embedded-event-lst
                                   (w state))
                       state)))
           (cond ((eq caller 'encapsulate-pass-2)
                  (value (list* (car val/expansion-alist/final-kpa)
                                (cadr val/expansion-alist/final-kpa)
                                proto-wrld3)))
                 ((eq caller 'certify-book)
                  (value (cdr val/expansion-alist/final-kpa)))
                 (t (value
                     (cadr val/expansion-alist/final-kpa)))))))))))
