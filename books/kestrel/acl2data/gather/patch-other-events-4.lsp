; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file other-events.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun make-event-fn2 (expansion0 whole-form in-encapsulatep check-expansion
                                  wrld ctx state)
  (mv-let
    (do-proofsp expansion0)
    (case-match expansion0
      ((':DO-PROOFS x)
       (mv (ld-skip-proofsp state)
           x))
      (& (mv nil expansion0)))
    (er-let* ((expansion1a ; apply macroexpansion to get embedded event form
               (do-proofs?

; This wrapper of do-proofs? avoids errors in checking expansions when
; ld-skip-proofsp is 'include-book.  See the "Very Technical Remark" in
; community book  books/make-event/read-from-file.lisp.

                check-expansion
                t ; use-always-do-proofs (part of expansion)
                (chk-embedded-event-form
                 expansion0 whole-form wrld ctx state (primitive-event-macros)
                 (f-get-global 'in-local-flg state)
                 in-encapsulatep
#|
                 nil)))
|#
; patch file addition of ext-exp argument:
                 nil t))) ;patch;
              (expansion1b
               (value (or expansion1a

; Else the alleged embedded event form, from the expansion, is nil, presumably
; because of local.

                          *local-value-triple-elided*)))
              (stobjs-out-and-raw-result
               (do-proofs?
                do-proofsp
                nil ; use-always-do-proofs (nil, as this is eval of expansion)
                (trans-eval-default-warning

; Note that expansion1b is guaranteed to be an embedded event form, which (as
; checked just below) must evaluate to an error triple.

                 expansion1b
                 ctx state t))))
      (let ((raw-result (cdr stobjs-out-and-raw-result)))
        (cond ((car raw-result)
               (silent-error state))
              (t (let ((expansion1
                        (if (f-get-global 'boot-strap-flg state)
                            expansion1b
                          (make-include-books-absolute
                           expansion1b
                           (cbd)
                           nil
                           (primitive-event-macros)
                           nil ctx state))))
                   (value (list* expansion1
                                 (car stobjs-out-and-raw-result)
                                 (cadr raw-result))))))))))

(defun make-event-fn2-lst (expansion-lst whole-form in-encapsulatep
                                         check-expansion on-behalf-of wrld ctx
                                         state)
  (cond ((atom expansion-lst)
         (cond ((member-eq on-behalf-of '(:quiet :quiet!))
                (silent-error state))
               (t (er soft ctx
                      "Evaluation failed for all expansions."))))
        (t (pprogn
            (cond
             ((f-get-global 'make-event-debug state)
              (fms "Attempting evaluation of next expansion:~|~Y01"
                   (list (cons #\0 (car expansion-lst))
                         (cons #\1 (abbrev-evisc-tuple state)))
                   (proofs-co state)
                   state
                   nil))
             (t state))
            (let (tmp-expansion-stack) ; patch file: added binding ;patch;
              (mv-let
                (erp val state)
                (let ((*expansion-stack *expansion-stack)) ; patch file: added binding ;patch;
                  (multiple-value-prog1 ; patch file addition ;patch;
                   (make-event-fn2 (car expansion-lst)
                                   whole-form in-encapsulatep check-expansion
                                   wrld ctx state)
; patch file addition:
                   (setq tmp-expansion-stack *expansion-stack))) ;patch;
                (cond (erp (make-event-fn2-lst (cdr expansion-lst)
                                               whole-form in-encapsulatep
                                               check-expansion on-behalf-of
                                               wrld ctx state))
#|
                      (t (value val))))))))
|#
; patch file addition:
                      (t (setq *expansion-stack tmp-expansion-stack) ;patch;
                         (value val)))))))) ;patch;
  ) ;patch;

(defun make-event-fn (form expansion? check-expansion on-behalf-of
                           save-event-data whole-form state)
  (let ((ctx (make-event-ctx whole-form))
; patch file addition:
        (*expansion-stack* (cons 'make-event *expansion-stack*)) ;patch;
        #-acl2-loop-only
        (old-kpa (known-package-alist state)))
    (with-ctx-summarized
     ctx
     (cond
      ((and (eq (cert-op state) :convert-pcert)
            (not (f-get-global 'in-local-flg state))
            (not (consp check-expansion))
            (not expansion?)

; This case should not happen, because all make-event forms should already be
; expanded away when we do the Convert procedure of provisional certification,
; since a suitable expansion-alist should have been stored in the .pcert0 file.
; We include this check just for robustness.

            (eql (f-get-global 'make-event-debug-depth state)

; We only enforce the above consp requirement at the top-level.  If we have
; (make-event ... :check-expansion exp ...), and this event is admissible
; (perhaps when skipping proofs) then we know that the result will be exp and
; will be independent of the current state.  In particular, exp will not be a
; call of make-event if form is admissible.

                 0))
       (er soft ctx
           "Implementation error: You should not be seeing this message!  ~
            Please contact the ACL2 implementors.~|~%Make-event expansion is ~
            illegal during the Convert procedure of provisional certification ~
            (unless :check-expansion is supplied a consp argument or ~
            :expansion? is supplied a non-nil argument).  The form ~x0 is ~
            thus illegal.  The use of a .acl2x file can sometimes solve this ~
            problem.  See :DOC provisional-certification."
           whole-form))
      ((not (or (eq check-expansion nil)
                (eq check-expansion t)
                (consp check-expansion)))
       (er soft ctx
           "The check-expansion flag of make-event must be t, nil, or a cons ~
            pair.  The following check-expansion flag is thus illegal: ~x0.  ~
            See :DOC make-event."
           check-expansion))
      ((and expansion?
            (consp check-expansion))

; We considered allowing :EXPANSION? FORM1 and :CHECK-EXPANSION FORM2 (where
; FORM2 is not nil or t), and if someone presents a natural example for which
; this would be useful, we might do so.  But the semantics of this would be
; potentially confusing.  Which one is consulted when including a book or
; running in raw Lisp?  If FORM1 = FORM2, this looks redundant.  Otherwise,
; this is, oddly, inherently contradictory, in the sense that FORM1 should
; never be the expansion (unless one is deliberately arranging for evaluation
; of the make-event call to fail -- but there are simpler ways to do that).

; If we decide to support the combination of expansion? and (consp
; check-expansion), then we need to be careful to handle that combination --
; something we don't do now, but we code defensively, giving priority to (consp
; check-expansion).

       (er soft ctx
           "It is illegal to supply a non-nil value for the keyword argument ~
            :EXPANSION? of make-event when keyword argument :CHECK-EXPANSION ~
            is give a value other than T or NIL.  If you think you have a ~
            reason why such a combination should be supported, please contact ~
            the ACL2 implementors."))
      (t
       (revert-world-on-error
        (let* ((make-event-debug (f-get-global 'make-event-debug state))
               (new-debug-depth (1+ (f-get-global 'make-event-debug-depth state)))
               (wrld (w state)))
          (er-let*
              ((expansion0/new-kpa/new-ttags-seen
                (pprogn
                 (if make-event-debug
                     (make-event-debug-pre new-debug-depth form on-behalf-of
                                           state)
                   state)
                 (state-global-let*
                  ((make-event-debug-depth new-debug-depth))
                  (cond
                   ((and expansion?
                         (eq (ld-skip-proofsp state) 'include-book)
                         (not (f-get-global 'including-uncertified-p state))

; Even if expansion? is specified, we do not assume it's right if
; check-expansion is t.

                         (assert$ (iff check-expansion

; In code above, we disallowed the combination of non-nil expansion? with a
; consp value of :check-expansion.

                                       (eq check-expansion t))
                                  (not (eq check-expansion t))))
                    (value (list* expansion? nil nil)))
                   (t
                    (do-proofs?
                     (or check-expansion

; For example, a must-fail form in community book books/make-event/defspec.lisp
; will fail during the Pcertify process of provisional certification unless we
; turn proofs on during expansion at that point.  It's reasonable to do proofs
; under make-event expansion during the Pcertify process: after all, we need
; the expansion done in order for other books to include the make-event's book
; with the .pcert0 certificate, and also proofs might well be necessary in
; order to come up with the correct expansion (else why do them?).  We could
; indeed always do proofs, but it's pretty common to do proofs only during
; certification as a way of validating some code.  So our approach is only to
; move proofs from the Convert procedure to the Pcertify procedure.

                         (eq (cert-op state) :create-pcert))
                     t ; use-always-do-proofs (for the main expansion here)

; Just below, the use of protected-eval ensures, among other things, that
; global cert-data won't be consulted.  To see why, imagine that a defun for
; foo is evaluated here during make-event expansion with non-nil
; :check-expansion while including a book, where a different defun of foo
; occurs later at the top level of the book.

                     (protected-eval form on-behalf-of ctx state t)))))))
               (expansion0 (value (car expansion0/new-kpa/new-ttags-seen)))
               (new-kpa (value (cadr expansion0/new-kpa/new-ttags-seen)))
               (new-ttags-seen
                (value (cddr expansion0/new-kpa/new-ttags-seen)))
               (need-event-landmark-p
                (pprogn
                 (if make-event-debug
                     (make-event-debug-post new-debug-depth expansion0 state)
                   state)
                 (cond ((or (null new-ttags-seen)

; The condition above holds when the new ttags-seen is nil or was not computed.
; Either way, no addition has been made to the value of world global
; 'ttags-seen.

                            (equal new-ttags-seen
                                   (global-val 'ttags-seen wrld)))
                        (value nil))
                       (t (pprogn
                           (set-w 'extension
                                  (global-set 'ttags-seen new-ttags-seen
                                              wrld)
                                  state)
                           (value t))))))
               (wrld0 (value (w state)))
; patch note: The following can extend *expansion-stack*.
               (expansion1/stobjs-out/result
                (make-event-fn1
                 expansion0 whole-form
                 (in-encapsulatep (global-val 'embedded-event-lst wrld0) nil)
                 check-expansion on-behalf-of wrld0 ctx state)))
            (let* ((expansion1 (car expansion1/stobjs-out/result))
                   (stobjs-out (cadr expansion1/stobjs-out/result))
                   (result (cddr expansion1/stobjs-out/result))
                   (expansion2
                    (cond
                     ((f-get-global 'last-make-event-expansion state)
                      (mv-let
                        (wrappers base)
                        (destructure-expansion expansion1)

; At this point we know that (car base) is from the list '(make-event progn
; progn! encapsulate); indeed, just after the release of v3-5, we ran a
; regression in community book books/make-event with the code C below replaced
; by (assert$ (member-eq (car base) X) C), where X is the above quoted list.
; However, we do not add that assertion, so that for example the ccg book of
; ACL2s can create make-event expansions out of events other than the four
; types above, e.g., defun.

                        (declare (ignore base))
                        (rebuild-expansion
                         wrappers
                         (ultimate-expansion
                          (f-get-global 'last-make-event-expansion state)))))
                     (t (ultimate-expansion expansion1)))))
              (assert$
               (equal stobjs-out *error-triple-sig*) ; evaluated an event form
               (let ((expected-expansion (if (consp check-expansion)
                                             check-expansion
                                           (and (eq (ld-skip-proofsp state)
                                                    'include-book)
                                                check-expansion
                                                expansion?))))
                 (cond ((and expected-expansion
                             (not (equal expected-expansion ; easy try first
                                         expansion2))
                             (not (equal (ultimate-expansion
                                          expected-expansion)
                                         expansion2)))
                        (er soft ctx
                            "The current MAKE-EVENT expansion differs from ~
                              the expected (original or specified) expansion. ~
                              ~ See :DOC make-event.~|~%~|~%Make-event ~
                              argument:~|~%~y0~|~%Expected ~
                              expansion:~|~%~y1~|~%Current expansion:~|~%~y2~|"
                            form
                            expected-expansion
                            expansion2))
                       (t
                        (let ((actual-expansion
                               (cond
                                ((or (consp check-expansion)
                                     (equal expansion?
                                            expansion2) ; easy try first
                                     (equal (ultimate-expansion
                                             expansion?)
                                            expansion2))

; The original make-event form does not generate a make-event replacement (see
; :doc make-event).

                                 nil)
                                (check-expansion
                                 (assert$
                                  (eq check-expansion t) ; from macro guard
                                  (list* 'make-event form

; Note that we deliberately omit :expansion? here, even if it was supplied
; originally.  If :expansion? had been supplied and appropropriate, then we
; would be in the previous case, where we don't generate a make-event around
; the expansion.

                                         :check-expansion expansion2
                                         (and on-behalf-of
                                              `(:on-behalf-of
                                                ,on-behalf-of)))))
                                (t expansion2))))
                          #-acl2-loop-only
                          (let ((msg

; We now may check the expansion to see if an unknown package appears.  The
; following example shows why this can be important.  Consider a book "foo"
; with this event.

; (make-event
;  (er-progn
;   (include-book "foo2") ; introduces "MY-PKG"
;   (assign bad (intern$ "ABC" "MY-PKG"))
;   (value `(make-event
;            (list 'defconst '*a*
;                  (list 'length
;                        (list 'symbol-name
;                              (list 'quote ',(@ bad)))))))))
;

; where "foo2" is as follows, with the indicated portcullis command:

; (in-package "ACL2")
;
; ; (defpkg "MY-PKG" nil)
;
; (defun foo (x)
;   x)

; In ACL2 Version_3.4, we certified these books; but then, in a new ACL2
; session, we got a raw Lisp error about unknown packages when we try to
; include "foo".

; On the other hand, the bad-lisp-objectp test is potentially expensive for
; large objects such as are encountered at Centaur Tech. in March 2010.  The
; value returned by expansion can be expected to be a good lisp object in the
; world installed at the end of expansion, so if expansion doesn't extend the
; world with any new packages, then we can avoid this check.

                                 (and (not (eq old-kpa new-kpa))
                                      (bad-lisp-objectp actual-expansion))))
                            (when msg
                              (er hard ctx
                                  "Make-event expansion for the form ~x0 has ~
                                    produced an illegal object for the ~
                                    current ACL2 world.  ~@1"
                                  form
                                  msg)))
                          (er-progn
                           (cond ((f-get-global 'boot-strap-flg state)

; In the boot-strap, we prevent make-event from storing an expansion, since
; otherwise we get an error for (when-pass-2 ... (make-event ...) ...), because
; make-event is not in an event context.

                                  (pprogn
                                   (if (in-encapsulatep
                                        (global-val 'embedded-event-lst
                                                    (w state))
                                        nil)
                                       (er soft ctx
                                           "Illegal form:~|~x0~|~%Make-event ~
                                             is illegal inside an encapsulate ~
                                             when in the boot-strap. See the ~
                                             relevant discussion in ~
                                             make-event-fn."
                                           form)
                                     (value nil))))
                                 (t
                                  (pprogn
                                   (f-put-global 'last-make-event-expansion
                                                 actual-expansion
                                                 state)
                                   (value nil))))
                           (pprogn
                            (cond
                             ((f-get-global 'make-event-debug state)
                              (fms "Saving make-event replacement into state ~
                                    global 'last-make-event-expansion (debug ~
                                    level ~
                                    ~x0):~|Form:~|~X13~|Expansion:~|~X23~|"
                                   (list (cons #\0 new-debug-depth)
                                         (cons #\1 form)
                                         (cons #\2 actual-expansion)
                                         (cons #\3 (abbrev-evisc-tuple state)))
                                   (proofs-co state)
                                   state
                                   nil))
                             (t state))
                            (er-progn
                             (cond (need-event-landmark-p ; optimization

; We lay down an event landmark if we aren't already looking at one.  Before we
; did so, an error was reported by print-redefinition-warning in the following
; example, because we weren't looking at an event landmark.

; (redef!)
; (make-event (er-progn (defttag t)
;                       (value '(value-triple nil))))

                                    (maybe-add-event-landmark state))
                                   (t (value nil)))
                             (value result)))))))))))))))
     :event-type (if save-event-data
                     'make-event-save-event-data
                   'make-event))))
