; This book provides a few basic checks on our handling of state inside
; computed hints, override hints, and custom keyword hints, when
; waterfall-parallelism is enabled.

; This book is only meant as a test suite and should not be included in any
; other book.

; See hint-tests.acl2 for how to certify this book

(in-package "ACL2")

#+acl2-par
(progn

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

;==============================================================================
; Computed Hints
;==============================================================================

;;;;;;;;;;;;;;;;;;;;;;;;
; Computed hint test 1 ;
;;;;;;;;;;;;;;;;;;;;;;;;

(set-default-hints '(("Goal" :do-not-induct t)))

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(defun my-non-modifying-computed-hint (id state)
  (declare (xargs :mode :program :stobjs state))
  (declare (ignore state))
  (if (equal id *initial-clause-id*)
      '(:induct t)
    nil))

(must-fail

; Check that the default hint that tells ACL2 to not induct is firing.

 (thm (equal (append (append x y) z)
             (append x (append y z)))))

(must-succeed

; Check that the computed hint (that doesn't modify state) overrules the
; default hint.

 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints ((my-non-modifying-computed-hint id state))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-succeed

; With waterfall parallelism enabled, check that the computed hint (that
; doesn't modify state) overrules the default hint.

 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints ((my-non-modifying-computed-hint id state))))

;;;;;;;;;;;;;;;;;;;;;;;;
; Computed hint test 2 ;
;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(defun my-state-modifying-computed-hint (id state)
  (declare (xargs :mode :program :stobjs state))
  (pprogn
   (fms "*** MODIFYING STATE. ***~%" nil *standard-co* state nil)
   (if (equal id *initial-clause-id*)
       (value '(:induct t))
     (value nil))))

(must-succeed
 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints ((my-state-modifying-computed-hint id state))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

; The following commented form only works on development versions that occur
; after the release of ACL2 4.3.  As such, it is commented out for now, since
; ACL2 4.3.X has yet to be released.

(must-fail
 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints ((my-state-modifying-computed-hint id state))))

; Check that defthm's also fail

(must-fail
 (defthm assoc-append
   (equal (append (append x y) z)
          (append x (append y z)))
   :hints ((my-state-modifying-computed-hint id state))))

;;;;;;;;;;;;;;;;;;;;;;;;
; Computed hint test 3 ;
;;;;;;;;;;;;;;;;;;;;;;;;

(defun my-non-modifying-computed-hint2 (id state)
  (declare (xargs :mode :program :stobjs state))
  (if (and (equal id *initial-clause-id*)
           (f-get-global 'acl2-version state))
      '(:induct t)
    nil))

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(must-succeed

; Check that we don't receive a message about state being unbound.

 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints ((my-non-modifying-computed-hint2 id state))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-succeed

; Check that we don't receive a message about state being unbound.

 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints ((my-non-modifying-computed-hint2 id state))))

(set-default-hints nil)


;==============================================================================
; Override-hints
;==============================================================================

;;;;;;;;;;;;;;;;;;;;;;;;
; Override hint test 1 ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Test our ability to toggle waterfall-parallelism when an override-hint is
; present.

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(set-override-hints
 '((append '(:no-thanks t) keyword-alist)))

(must-fail
 (make-event (er-progn (set-waterfall-parallelism :full)
                       (value '(value-triple nil)))))

(set-override-hints nil)

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(set-override-hints
 '((append '(:no-thanks t) keyword-alist)))

; Matt K. mod: This failed until the change on August 16, 2020, that allows
; (set-waterfall-parallelism nil) to succeed even with override-hints in place.
(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(set-override-hints nil)

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

;;;;;;;;;;;;;;;;;;;;;;;;
; Override hint test 2 ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Test our ability to add override-hints that do not modify state and our
; ability to add override-hints that do modify state.

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(must-succeed
 (set-override-hints

; Disables the "Thanks for the hint" message

  '((append '(:no-thanks t) keyword-alist))))

(set-override-hints

; Basically the same as above, except that we will see a message printed for
; every attempt to select a hint.

 '((mv-let (col state)
           (fmx "~%**Applying override hints**")
           (declare (ignore col))
           (value (append '(:no-thanks t) keyword-alist)))))

(must-succeed
 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints (("Goal" :induct t))))

(set-override-hints nil)

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-succeed
 (set-override-hints
  '((append '(:no-thanks t) keyword-alist))))

(must-fail
 (set-override-hints
  '((mv-let (col state)
            (fmx "~%**Applying override hints**")
            (declare (ignore col))
            (value (append '(:no-thanks t) keyword-alist))))))


(make-event (er-progn (set-waterfall-parallelism

; so we see "Thanks for the hint" messages

                       :full)
                      (value '(value-triple nil))))

(must-succeed
 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints (("Goal" :induct t))))

; set an override-hint to disable the "Thanks for the hint" message

(set-override-hints
 '((append '(:no-thanks t) keyword-alist)))

(must-fail

; The proof will still fail, because we haven't enabled the use of waterfall
; parallelism hacks (of which, override hints is one).

 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints (("Goal" :induct t))))

(defttag :waterfall-parallelism-hacks)

(set-waterfall-parallelism-hacks-enabled t)

(must-succeed

; The proof will succeed, but the "Thanks for the hint" message shouldn't be
; printed.

 (thm (equal (append (append x y) z)
             (append x (append y z)))
      :hints (("Goal" :induct t))))

(set-override-hints nil)

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(set-waterfall-parallelism-hacks-enabled nil)

(defttag nil)

;==============================================================================
; Custom-keyword-hints
;==============================================================================

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Custom-keyword-hint test 1 ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

; Install some custom-keyword-hints

(add-custom-keyword-hint :no-thanks-state-in-generator-and-checker
                         (mv-let (col state)
                                 (fmx "~%**Applying custom-keyword hint**")
                                 (declare (ignore col))
                                 (if (equal clause clause)
                                     (value (splice-keyword-alist
                                             :no-thanks-state-in-generator-and-checker
                                             '(:no-thanks t)
                                             keyword-alist))
                                   (value keyword-alist))))

(must-fail
 (add-custom-keyword-hint :no-thanks-state-in-generator-only
                          (mv-let (col state)
                                  (fmx "~%**Applying custom-keyword hint**")
                                  (declare (ignore col))
                                  (if (equal clause clause)
                                      (value (splice-keyword-alist
                                              :no-thanks-state-in-generator-and-checker
                                              '(:no-thanks t)
                                              keyword-alist))
                                    (value keyword-alist)))

; We don't support returning a single value in the checker

                          :checker t))

(must-fail
 (add-custom-keyword-hint :no-thanks-fail
                          (if (equal clause clause)
                              (splice-keyword-alist
                               :no-thanks-ns
                               `(:ERROR ,(msg "The value ~x0 is illegal!" val))
                               keyword-alist)
                            nil)
                          :checker t))

(add-custom-keyword-hint :no-thanks-state-in-checker
                         (prog2$
                          (cw "**Applying custom-keyword hint**")
                          (if (equal clause clause)
                              (splice-keyword-alist
                               :no-thanks-state-in-checker
                               '(:no-thanks t)
                               keyword-alist)
                            keyword-alist))
                         :checker (prog2$ (cw "This non-default checker ~
                                               doesn't modify state, but it ~
                                               does return it ~%")
                                          (value t)))

(add-custom-keyword-hint :no-thanks-default-checker1
                         (prog2$
                          (cw "**Applying custom-keyword hint**")
                          (if (equal clause clause)
                             (splice-keyword-alist
                              :no-thanks-default-checker1
                              '(:no-thanks t)
                              keyword-alist)
                           keyword-alist)))

(add-custom-keyword-hint :no-thanks-default-checker2
                         (prog2$
                          (cw "**Applying custom-keyword hint**")
                          (if (equal clause clause)
                              (splice-keyword-alist
                               :no-thanks-default-checker2
                               '(:no-thanks t)
                               keyword-alist)
                            keyword-alist))

; This custom-keyword hint should work because it's the default checker (which
; in reality, is the same as the :no-thanks-ns test).

                         :checker (value t))
(must-succeed
 (thm
  (equal (append (append a b) c)
         (append a (append b c)))
  :hints (("Goal" :induct t :no-thanks-state-in-generator-and-checker nil))))

(must-succeed
 (thm
  (equal (append (append a b) c)
         (append a (append b c)))
  :hints (("Goal" :induct t :no-thanks-state-in-checker nil))))

(must-succeed
 (thm
  (equal (append (append a b) c)
         (append a (append b c)))
  :hints (("Goal" :induct t :no-thanks-default-checker1 nil))))

(must-succeed
 (thm
  (equal (append (append a b) c)
         (append a (append b c)))
  :hints (("Goal" :induct t :no-thanks-default-checker2 nil))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-fail
  (thm
   (equal (append (append a b) c)
          (append a (append b c)))
   :hints (("Goal" :induct t :no-thanks-state-in-generator-and-checker nil))))

(must-fail
 (thm
  (equal (append (append a b) c)
         (append a (append b c)))
  :hints (("Goal" :induct t :no-thanks-state-in-checker nil))))

(must-succeed
 (thm
  (equal (append (append a b) c)
         (append a (append b c)))
  :hints (("Goal" :induct t :no-thanks-default-checker1 nil))))

(must-succeed
 (thm
  (equal (append (append a b) c)
         (append a (append b c)))
  :hints (("Goal" :induct t :no-thanks-default-checker2 nil))))


;==============================================================================
; Clause-processors
;==============================================================================

;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Clause processor test 1 ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

; A simple example taken from :DOC clause-processor

(defun note-fact-clause-processor (cl term)
  (declare (xargs :guard t)) ; optional, for better efficiency
  (list (cons (list 'not term)
              cl)
        (list term)))

(defevaluator evl0 evl0-list
  ((not x) (if x y z)))

(defthm correctness-of-note-fact-clause-processor
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl0 (conjoin-clauses
                       (note-fact-clause-processor cl term))
                      a))
           (evl0 (disjoin cl) a))
  :rule-classes :clause-processor)

(must-succeed
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor clause '(equal a a))))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))


(must-succeed
 (thm (equal (car (cons x y))
            x)
     :hints
     (("Goal"
       :clause-processor
       (note-fact-clause-processor clause '(equal a a))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Clause processor test 2 ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun note-fact-clause-processor-modifies-state (cl term state)
  (declare (xargs :guard (state-p state) :stobjs state))
  (pprogn (prog2$ (cw "**Modifying state inside a clause-processor**")
                  (f-put-global 'throw-this-away 43 state))
          (mv nil (list (cons (list 'not term)
                          cl)
                    (list term))
              state)))

(defevaluator evl1 evl1-list
  ((not x) (if x y z)))

(defthm correctness-of-note-fact-clause-processor-modifies-state
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl1 (conjoin-clauses
                       (clauses-result
                        (note-fact-clause-processor-modifies-state cl term state)))
                      a))
           (evl1 (disjoin cl) a))
  :rule-classes :clause-processor )

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(must-succeed
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state clause '(equal a a) state)))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state clause '(equal a a) state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Clause processor test 3 ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(defun note-fact-clause-processor-modifies-state2 (cl term state)
  (declare (xargs :guard (state-p state) :stobjs state)) ; optional, for better efficiency
  (pprogn (prog2$ (cw "**Modifying state inside a clause-processor**")
                  (f-put-global 'throw-this-away 43 state))
          (mv t (list (cons (list 'not term)
                            cl)
                      (list term))
              state)))

(defthm correctness-of-note-fact-clause-processor-modifies-state2
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl1 (conjoin-clauses
                       (clauses-result
                        (note-fact-clause-processor-modifies-state2 cl term state)))
                      a))
           (evl1 (disjoin cl) a))
  :rule-classes :clause-processor )

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state2 clause '(equal a a)
                                                    state)))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state2 clause '(equal a a)
                                                    state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Clause processor test 4 ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(defun note-fact-clause-processor-modifies-state3 (cl term state)
  (declare (xargs :guard (state-p state) :stobjs state)) ; optional, for better efficiency
  (pprogn (prog2$ (cw "**Modifying state inside a clause-processor**")
                  (f-put-global 'throw-this-away 43 state))
          (mv t (list "this can be anything, because clauses-result will ~
                       ignore it whenever erp is t"
                      (cons (list 'not term)
                            cl)
                      (list term))
              state)))

(defthm correctness-of-note-fact-clause-processor-modifies-state3
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl1 (conjoin-clauses
                       (clauses-result
                        (note-fact-clause-processor-modifies-state3 cl term state)))
                      a))
           (evl1 (disjoin cl) a))
  :rule-classes :clause-processor )

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state3 clause '(equal a a) state)))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state3 clause '(equal a a) state)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Clause processor test 5 ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :waterfall-parallelism-hacks)

(set-waterfall-parallelism-hacks-enabled t)

; Here we reuse a definition from clause processor test 2

(must-succeed
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state clause '(equal a a) state)))))

(set-waterfall-parallelism-hacks-enabled nil)

(defttag nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Clause processor test 6 ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun note-fact-clause-processor-modifies-state6 (cl term)
;  (declare (xargs :guard t)) ; optional, for better efficiency
  (prog2$ (er hard 'note-fact-clause-processor-modifies-state6
              "Example of causing an error without modifying state.")
          (list (cons (list 'not term) cl)
                (list term))))

(defthm correctness-of-note-fact-clause-processor-modifies-state6
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl1 (conjoin-clauses
                       (note-fact-clause-processor-modifies-state6 cl term))
                      a))
           (evl1 (disjoin cl) a))
  :rule-classes :clause-processor )

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state6 clause '(equal a a))))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state6 clause '(equal a a))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Clause processor test 7 ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun note-fact-clause-processor-modifies-state7 (cl term)
  (declare (xargs :guard t)) ; optional, for better efficiency
  (prog2$ (er hard? 'note-fact-clause-processor-modifies-state7
              "Example of causing an error without modifying state but still ~
               being able to verfiy guards.")
          (list (cons (list 'not term) cl)
                (list term))))

(defthm correctness-of-note-fact-clause-processor-modifies-state7
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl1 (conjoin-clauses
                       (note-fact-clause-processor-modifies-state7 cl term))
                      a))
           (evl1 (disjoin cl) a))
  :rule-classes :clause-processor )

(make-event (er-progn (set-waterfall-parallelism nil)
                      (value '(value-triple nil))))

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state7 clause '(equal a a))))))

(make-event (er-progn (set-waterfall-parallelism :full)
                      (value '(value-triple nil))))

(must-fail
 (thm (equal (car (cons x y))
             x)
      :hints
      (("Goal"
        :clause-processor
        (note-fact-clause-processor-modifies-state7 clause '(equal a a))))))

) ; end progn

#|

; Here I include some notes that I had once written concerning the hints this
; book tests.  I leave these notes as evidence that clearing up our story was a
; good thing to do.


  At this time, such an attempt to modify ~il[state] may result in
  a sub-optimal error message.

  We do not formerly support ~il[computed-hints], ~il[override-hints], or
  ~il[custom-keyword-hints] that modify state while waterfall parallelism is
  enabled.  The following three paragraphs elaborate upon this lack of support.
  ~l[error-triples-and-parallelism] for how to avoid modifying state when you
  need to signal an error.

  ~il[Computed-hints] are supported in the following way.  It is fine to have a
  computed hint that modifies state and only use it while
  ~il[waterfall-parallelism] is disabled.  It is also fine to have a computed
  hint that does not modify state and switch between enabled and disabled
  waterfall parallelism.  However, using a computed hint that modifies state
  while waterfall parallelism is enabled should result in an error.

  We support ~il[custom-keyword-hints] in the same way that we support
  ~il[computed-hints].

  Since ~il[override-hints] are currently checked for state modification when
  they are added to the default-hints-table (and not when the proof is actually
  attempted), there is currently no way for us to determine whether an override
  hint is acceptable.  As such, using override hints while
  waterfall-parallelism is enabled requires the presence of a ~il[trust-tag].
  ~pl[set-waterfall-parallelism-hacks-enabled] for a blessed way of installing
  such a trust-tag.


  "We intend to support ~il[computed-hints] that do not modify
  ~il[state] (including allowing computed hints to read ~il[state]).  And we
  would like to eventually disable computed hints that modify state whenever
  waterfall parallelism is enabled.  However, we currently only check to make
  sure a computed hint does not modify ~il[state] when it is added to the
  default hints table.  As such, it is possible to add a computed hint that
  modifies state, enable waterfall parallelism, and then use that computed hint
  inside a proof.  Note that any resulting unsoundess will not work when you
  certify your book with waterfall-parallelism disabled."


  The support for ~il[Override-hints] is also similar to the support of
  computed-hints.  It is fine to have an override hint that modifies state and
  only use it while ~il[waterfall-parallelism] is disabled.  It is also fine to
  have an override hint that does not modify state and switch between enabled
  and disabled waterfall parallelism.  However, toggling waterfall parallelism
  while using an override hint that modifies state is unsupported (and if you
  try to add an override hint that modifies state while waterfall parallelism
  is enabled, you will receive a error message).

  In practice, there are currently no additional checks that ensure
  ~il[custom-keyword-hints] do not modify state while waterfall parallelism is
  enabled.  In short, they will probably work as you expect.

  Our intent is to support ~il[computed-hints] and ~il[custom-keyword-hints]
  that do not modify state.

  Using a computed-hint that does not modify state is the same, regardless of
  whether waterfall parallelism is enabled.  It is our intent that the user
  will receive an error message if a computed-hint tries to modify state while
  waterfall parallelism is enabled.

  Using ~il[custom-keyword-hints] is trickier.  We have tried to simplify the
  management of custom-keyword-hints by creating a version of
  ~il[add-custom-keyword-hint] for use whenever ~il[waterfall-parallelism] is
  enabled.  This macro is named ~il[add-custom-keyword-hint@par].  Our intent
  is the following:  any custom-keyword-hint added with add-custom-keyword-hint@par
  can be used in either

  that if the user tries to use a custom-keyword-hint added with
  add-custom-keyword-hint (with no @par suffix) while waterfall parallelism is
  enabled, that the user will receive an error.


; Taken from translate-hint-expression -- the following form is useful for
; tracing functions relevant to debugging the processing of computed, override,
; and custom-keyword hints.

(trace$
 (TRANSLATE-HINTS+1)
 (TRANSLATE-HINTS+1@PAR)
 (TRANSLATE-HINTS2)
 (TRANSLATE-HINTS2@PAR)
 (TRANSLATE-HINTS1)
 (APPLY-OVERRIDE-HINTS@PAR)
 (APPLY-OVERRIDE-HINTS)
 (TRANSLATE-X-HINT-VALUE)
 (TRANSLATE-X-HINT-VALUE@PAR)
 (TRANSLATE-CUSTOM-KEYWORD-HINT)
 (TRANSLATE-CUSTOM-KEYWORD-HINT@PAR)
 (CUSTOM-KEYWORD-HINT-INTERPRETER@PAR)
 (CUSTOM-KEYWORD-HINT-INTERPRETER)
 (TRANSLATE-SIMPLE-OR-ERROR-TRIPLE)
 (TRANSLATE-SIMPLE-OR-ERROR-TRIPLE@PAR)
 (XTRANS-EVAL)
 (XTRANS-EVAL-WITH-EV-W)
 (EVAL-AND-TRANSLATE-HINT-EXPRESSION)
 (EVAL-AND-TRANSLATE-HINT-EXPRESSION@PAR)
 (TRANSLATE-HINT-EXPRESSION@PAR)
 (TRANSLATE-HINT-EXPRESSION)
 (TRANSLATE-HINTS1@PAR)
 (WATERFALL)
 (FIND-APPLICABLE-HINT-SETTINGS1)
 (FIND-APPLICABLE-HINT-SETTINGS1@PAR)
 (XTRANS-EVAL@PAR)
 (SIMPLE-TRANSLATE-AND-EVAL@PAR)
 (SIMPLE-TRANSLATE-AND-EVAL)
 (TRANSLATE-HINTS)
 (TRANSLATE-HINTS+)
 (THM-FN)
 (FORMAL-VALUE-TRIPLE)
 (FORMAL-VALUE-TRIPLE@PAR)
 (EVAL-CLAUSE-PROCESSOR)
 (EVAL-CLAUSE-PROCESSOR@PAR)
 (APPLY-TOP-HINTS-CLAUSE@PAR)
 (APPLY-TOP-HINTS-CLAUSE)
 (WATERFALL-STEP1)
 (WATERFALL-STEP1@par)
 (waterfall-step)
 (waterfall-step@par)
 (translate1)
 (translate1@par)
 (translate)
 (translate@par)
 (translate-doc)
 (translate-clause-processor-hint)
 (translate-clause-processor-hint@par)
 (translate1-cmp))




; Here are also some parallelism warts related to whether our call to ev-w
; maintained the invariant that state was not modified.


from ev-w-for-trans-eval

; Parallelism wart: The call of this function in eval-clause-processor@par can
; lead to an ev-w call below that violates the input requirement on ev-w,
; namely that we don't modify stobjs.  The parallelism wart in
; xtrans-eval-with-ev-w explains a similar issue with custom keyword hints that
; we have already begun to address.  But in the present situation, we can
; easily permit a computed hint that modifies state without recording that
; modification in the logic.  Perhaps that's not so important for the
; #+acl2-par code, but it's certainly a logical wart at the least that should
; be documented.  Alternately, we could "do the right thing" and prohibit
; computed hints that modify state or stobjs.


from xtrans-eval-with-ev-w

; Parallelism wart: this function calls ev-w in a way that violates the
; contract that state is not part of one of ev-w's arguments ("alist").  As
; such, while this implementation "works", it is unlikely that it is both sound
; and as "user friendly" as it should be.  We insist that we do not modify
; state here, causing an error otherwise, thus avoiding for example the case
; where a computed hint sets a state global differently in two different
; threads.  We should make sure that there are clear error messages and
; documentation, pointing out that instead of (er soft ...)  they could use
; (er@par soft ...), for example.  How can we carry out this plan (which may
; have in fact already been carried out, at least in part)?  Below we see that
; if trans-flg is true, then we call a function that translates; we should be
; sure to arrange that no stobj (user-defined, or state) is returned, and
; indeed we probably already do that in our comparison against *cmp-sig*.  The
; other case is that trans-flg is nil.  We can either arrange that such callers
; only give us a uterm whose value doesn't include a stobj (user-defined, or
; state), or perhaps just call term-stobjs-out on uterm (probably with alist
; argument of nil -- careful though, not sure it's really complete -- maybe it
; was just for printing heuristics -- if it's not suitable, then maybe call
; translate on uterm) and ensure that it produces an appropriate value (in
; particular, not returning a stobj; maybe in fact we'll insist on stobjs-out
; of either '(nil) or *cmp-sig*).  Another parallelism wart related to custom
; keyword hints may be found in add-custom-keyword-hint@par.

places that call xtrans-eval@par with trans-flg set to nil:

apply-override-hint -- in this case find-applicable-hint-settings1
translates the hint by calling translate-hint@par... well maybe that's
wrong.  I suggest that because it passes 'override-hint to
translate-hint@par.]

eval-and-translate-hint-expression -- called from
process-backtrack-hint, eval-and-translate-hint-expression, and
find-applicable-hint-settings1


; Parallelism wart: we currently discard any changes to the world of the live
; state.  But if we restrict to terms that don't modify state, as discussed in
; the parallelism wart above, then there is no issue because state hasn't
; changed.  Otherwise, if we cheat, the world could indeed change out from
; under us, which is just one example of the evils of cheating by modifying
; state under the hood.


from custom-keyword-hint-interpreter1

; Parallelism wart: Why doesn't the following cause an error when we try to
; pass in a term that we think has output signature of a value triple?  (More
; generally, see the parallelism wart just above the Essay on the Design of
; Custom Keyword Hints.)  For example, try the following.  (You may see a
; parallelism hazard, which might or might not be relevant; but what currently
; seems surprising is that we don't even see a traced call of xtrans-eval@par
; with trans-flg = t.)  Aha -- the answer is that someone else is calling
; xtrans-eval@par, not this function.  Hmmm, needs further investigation.


from eval-and-translate-hint-expression

; Parallelism wart: a fourth inaccuracy in the above description is that in the
; #+acl2-par case, sometimes term (the third component of the input, tuple)
; returns a pair rather than an error triple.  Indeed, this term could have
; been created by translate-hint-expression@par, which in #+acl2-par returns an
; error-value pair rather than a triple.  We need this different return
; signature, because we do not want to allow hints that modify state when
; executing the waterfall in parallel.  See the parallelism wart in
; translate-hint-expression for details of a bug that further complicates the
; #+acl2-par story on hints.

from axioms.lisp

; Parallelism wart: Finish dealing with custom keyword hints, and update the
; following essay as necessary.  See also the parallelism wart in
; custom-keyword-hint-interpreter1.

; Essay on the Design of Custom Keyword Hints

; Parallelism wart: the comment below starting with "Val must be of the
; form..." will need to be updated once we finalize the way custom keyword
; hints work in ACL2(p).


from add-custom-keyword-hint@par

; Parallelism wart: we do not currently handle custom keyword hints in a
; graceful or disciplined manner.  The only promise we currently maintain is
; that they work in #-acl2-par and in #+acl2-par in the serial mode of the
; parallelized waterfall.  We should develop a cleaner explanation for how
; custom-keyword-hints interact with the parallelized waterfall and then
; document it.  Another parallelism wart related to custom keyword hints may be
; found in xtrans-eval-with-ev-w.


from waterfall-printing-value-for-parallelism-value

; Parallelism wart: either support the reading of state by computed hints, or
; explicitly disallow it with a user-friendly error message; modify :doc
; unsupported-waterfall-parallelism-features accordingly.


from eval-clause-processor@par

; Parallelism wart: See the parallelism wart in ev-w-for-trans-eval.


from translate-hint-expression

; Parallelism wart: there is a bug in ACL2(p) related to translating computed
; hints.  To replicate this bug, run the following example.  Note that
; translate-hint is being called before entering the waterfall, which means
; that formal-value-triple (without the @par suffix) is always being called,
; regardless of whether waterfall parallelism is enabled.  This is wrong.  If
; waterfall parallelism is enabled, we should be calling
; formal-value-triple@par.  To fix this, we would need to modify thm-fn and
; probably defthm-fn to call a version of translate-hints+ (and its
; subfunctions) that account for whether waterfall parallelism is enabled.

; (trace$ (formal-value-triple@par)
;         (formal-value-triple)
;         (thm-fn)n
;         (translate-hints+)
;         (translate-hints)
;         (translate-hint-expression)
;         (translate-simple-or-error-triple)
;         (simple-translate-and-eval)
;         (xtrans-eval)
;         (eval-and-translate-hint-expression)
;         (translate-hint-expression@par)
;         (translate-simple-or-error-triple@par)
;         (simple-translate-and-eval@par)
;         (xtrans-eval@par)
;         (eval-and-translate-hint-expression@par)
;         (find-applicable-hint-settings1@par)
;         (find-applicable-hint-settings1)
;         (waterfall))



|#
