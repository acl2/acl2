; A version of unroll-spec that uses rewriter-basic.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also unroll-spec.lisp.
;; See also def-simplified.lisp.

(include-book "rewriter-basic")
(include-book "rule-lists")
(include-book "choose-rules")
(include-book "dag-to-term")
(include-book "pure-dags")
(include-book "dag-size-fast") ; for dag-or-quotep-size-less-thanp
(include-book "dag-to-term-with-lets")
(include-book "rules-in-rule-lists")
(include-book "interpreted-function-alists")
(include-book "make-evaluator") ; for make-acons-nest (todo: reduce)
;; for get-non-built-in-supporting-fns-list (todo: reduce):
(include-book "evaluator") ;; since this calls dag-val-with-axe-evaluator to embed the resulting dag in a function, introduces a skip-proofs
(include-book "kestrel/utilities/check-boolean" :dir :system)
;; (include-book "kestrel/lists-light/group-rules" :dir :system)
(include-book "kestrel/utilities/defmacrodoc" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/utilities/strip-stars-from-name" :dir :system)
(include-book "kestrel/utilities/system/fresh-names" :dir :system) ;drop?
(include-book "kestrel/utilities/supporting-functions" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)
(include-book "dag-info")
(include-book "kestrel/axe/util2" :dir :system) ; not strictly needed but brings in symbolic-list

;; If asked to create a theorem, this uses skip-proofs to introduce it.

;move to rule-lists.lisp
(defun unroll-spec-basic-rules ()
  (set-difference-eq
   (append (base-rules)
           (amazing-rules-bv)
           (leftrotate-intro-rules) ; perhaps not needed if the specs already use rotate ops
           (list-rules) ; or we could allow the list functions to open (if both, watch for loops with list-rules and the list function openers)
           ;; (introduce-bv-array-rules)
           ;; '(list-to-byte-array) ;; todo: add to a rule set (whatever mentions list-to-bv-array)
           (if-becomes-bvif-rules) ; since we want the resulting DAG to be pure
           ;; Handle nth of a 2-d array:
           '(nth-becomes-nth-to-unroll-for-2d-array
             nth-to-unroll-opener
             collect-constants-over-<-2
             ;; group-base group-unroll ; I guess we get these automatically from calling opener-rules-for-fns
             len-of-group ;; these are not needed if we unroll group/ungroup
             consp-of-group
             nth-of-group
             ungroup-of-cons)
           ;; (bv-array-rules-simple)
           ;; (list-to-bv-array-rules)
           ;; (set-difference-eq (core-rules-bv)
           ;;                    ;; these are kind of like trim rules, and can make the result worse:
           ;;                    '(;BVCHOP-OF-BVPLUS
           ;;                      BVCHOP-OF-bvuminus
           ;;                      ))
           ;; (unsigned-byte-p-forced-rules)
           )
   ;; can lead to blowup in lifting md5:
   (bvplus-rules)))

(ensure-rules-known (unroll-spec-basic-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund filter-function-names (names wrld)
  (declare (xargs :guard (and (symbol-listp names)
                              (plist-worldp wrld))))
  (if (endp names)
      nil
    (let ((name (first names)))
      (if (function-symbolp name wrld)
          (cons name
                (filter-function-names (rest names) wrld))
        (filter-function-names (rest names) wrld)))))

(local
  (defthm symbol-listp-of-filter-function-names
    (implies (symbol-listp names)
             (symbol-listp (filter-function-names names wrld)))
    :hints (("Goal" :in-theory (enable filter-function-names)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Add more options, such as :print-interval, to pass through to simp-term
;; Returns (mv erp event state)
;; This function has invariant-risk but still seems quite fast.
(defun unroll-spec-basic-fn (defconst-name ;should begin and end with *
                              term
                              rules
                              ;;rule-alists
                              extra-rules
                              remove-rules
                              assumptions
                              interpreted-function-alist
                              monitor
                              memoizep
                              count-hits
                              normalize-xors
                              produce-function
                              disable-function
                              function-type
                              function-params
                              produce-theorem
                              print
                              whole-form
                              state)
  (declare (xargs :guard (and (symbolp defconst-name)
                              ;; term is an untranlated term
                              (or (eq :standard rules)
                                  (eq :auto rules)
                                  (symbol-listp rules))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (or (eq :bytes assumptions)
                                  (eq :bits assumptions)
                                  (true-listp assumptions) ; untranslated terms
                                  )
                              (or (eq :auto interpreted-function-alist)
                                  (interpreted-function-alistp interpreted-function-alist))
                              (symbol-listp monitor)
                              (booleanp memoizep)
                              (booleanp count-hits)
                              (booleanp normalize-xors)
                              (booleanp disable-function)
                              (member-eq function-type '(:term :lets :embedded-dag :auto))
                              (or (symbol-listp function-params)
                                  (eq :auto function-params))
                              (booleanp produce-theorem))
                  :stobjs state
                  :mode :program ;; because this calls translate-term, translate-terms, submit-events-quiet, and fresh-name-in-world-with-$s (todo: factor)
                  ))
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ((when (and (not produce-function)
                   (not (eq :auto function-params))))
        (er hard? 'unroll-spec-basic-fn ":function-params should not be given if :produce-function is nil.")
        (mv (erp-t) nil state))
       ((when (and (not produce-function)
                   disable-function))
        (er hard? 'unroll-spec-basic-fn ":disable-function should not be true if :produce-function is nil.")
        (mv (erp-t) nil state))
       ((mv start-time state) (get-real-time state))
       (- (cw "~%(Unrolling spec:~%"))
       (term (translate-term term 'unroll-spec-basic-fn (w state)))
       (term-vars (all-vars term))
       (assumptions (if (eq :bits assumptions)
                        (progn$ (cw "NOTE: Assuming all ~x0 vars in the term are bits.~%" (len term-vars))
                                (bit-hyps term-vars) ; actually calls to unsigned-byte-p
                                )
                      (if (eq :bytes assumptions)
                          (progn$ (cw "NOTE: Assuming all ~x0 vars in the term are bytes.~%" (len term-vars))
                                  (byte-hyps term-vars) ; actually calls to unsigned-byte-p
                                  )
                        (translate-terms assumptions 'unroll-spec-basic-fn (w state)))))
       ;; Compute the base set of rules (from which we remove the remove-rules and to which we add the extra-rules) and also
       ;; any opener events:
       ((mv pre-events base-rules)
        (if (eq rules :standard)
            ;; Use the :standard rule set, which is (unroll-spec-basic-rules):
            (mv nil (unroll-spec-basic-rules))
          (if (eq :auto rules)
              (b* (((mv defined-supporting-fns
                        & ;undefined-fns
                        & ;stopper-fns-encountered
                        )
                    (fns-supporting-term term
                                         ;; Don't open these functions:
                                         (append '(leftrotate
                                                   nth update-nth len true-listp
                                                   nthcdr ; opener could loop with nth-of-cdr, etc.
                                                   firstn
                                                   take
                                                   append
                                                   list-to-bv-array
                                                   ifix nfix
                                                   floor mod
                                                   mv-nth
                                                   binary-logand
                                                   binary-logior
                                                   lognot
                                                   logorc1
                                                   binary-logeqv ; maybe
                                                   binary-logxor
                                                   integer-length
                                                   ;; group ; might as well unroll this
                                                   ;; ungroup ; might as well unroll this
                                                   fix
                                                   expt
                                                   repeat
                                                   make-list-ac
                                                   )
                                                 *bv-and-array-fns-we-can-translate*)
                                         (w state)))
                   ((mv opener-events opener-rule-names)
                    (opener-rules-for-fns defined-supporting-fns t '-for-unroll-spec-basic nil nil state))
                   (- (cw "Will use the following ~x0 additional opener rules: ~X12~%" (len opener-rule-names) opener-rule-names nil))
                   ;; todo: could loop with the openers (e.g., )?
                   (rule-names (append (unroll-spec-basic-rules)
                                       opener-rule-names)))
                (mv opener-events rule-names))
            ;; rules is an explicit list of rules:
            (mv nil rules))))
       ;; Add the :extra-rules and remove the :remove-rules:
       (rules (union-equal extra-rules base-rules))
       (rules (set-difference-equal rules remove-rules))
       ;; Submit any needed defopener rules:
       (state (submit-events-quiet pre-events state))
       ;; Make the rule-alist:
       ((mv erp rule-alist) (make-rule-alist rules (w state)))
       ((when erp) (mv erp nil state))
       ;; Create the interpreted-function-alist:
       (interpreted-function-alist
        (if (eq :auto interpreted-function-alist)
            ;; Since we're expanding these functions, we might as well also evaluate them
            ;; todo: also add recursive functions that we are unrolling?
            ;; todo: also add functions that may be introduced by rules?
            (make-complete-interpreted-function-alist
             (set-difference-eq (filter-function-names rules (w state))
                                ;; we can already evaluate these:
                                *axe-evaluator-basic-fns-and-aliases*)
             (w state))
          ;; The user supplied one, so use it:
          interpreted-function-alist))
       ;; Call the rewriter:
       ((mv erp dag)
        (simplify-term-basic term
                             assumptions
                             rule-alist
                             interpreted-function-alist
                             (known-booleans (w state))
                             nil
                             monitor
                             nil ; fns-to-elide
                             memoizep
                             count-hits
                             print
                             normalize-xors))
       ((when erp) (mv erp nil state))
       ((when (quotep dag)) ;; TODO: Should we allow this?
        (er hard? 'unroll-spec-basic-fn "Spec unexpectedly rewrote to the constant ~x0." dag)
        (mv :unexpected-quotep nil state))
       ;; Make a theorem if the term is small enough.  We must use skip-proofs
       ;; because Axe does not yet produce an ACL2 proof. TODO: We could
       ;; support adding the theorem even if the DAG is large if we use
       ;; dag-val-with-axe-evaluator to express the theorem.
       (dag-vars (dag-vars dag)) ;todo: check these (what should be allowed)?
       (dag-fns (dag-fns dag))
       ;; build the function:
       (function-name (intern-in-package-of-symbol
                       ;;todo: why is the re-interning needed here?
                       (symbol-name (fresh-name-in-world-with-$s (strip-stars-from-name defconst-name) nil (w state)))
                       defconst-name))
       (function-params (if (eq :auto function-params)
                            dag-vars
                          ;; the function-params given should be a permutation of the dag-vars
                          (let ((diff1 (set-difference-eq dag-vars function-params))
                                (diff2 (set-difference-eq function-params dag-vars)))
                            (if (or diff1 diff1)
                                (er hard? 'unroll-spec-basic-fn "Mismatch between supplied :function-params and the variables of the dag.  Dag has ~x0 vars.  :function-params has ~x1 vars.
Entries only in DAG: ~X23.  Entries only in :function-params: ~X45."
                                    (len dag-vars)
                                    (len function-params)
                                    diff1 nil
                                    diff2 nil)
                              function-params))))
       ;; Handle a :function-type of :auto
       (function-type (if (eq :auto function-type)
                          (if (dag-or-quotep-size-less-thanp dag 1000)
                              :term
                            :embedded-dag)
                        function-type))
       (function-body (and produce-function
                           (if (eq :term function-type)
                               (dag-to-term dag)
                             (if (eq :embedded-dag function-type)
                                 `(dag-val-with-axe-evaluator ,defconst-name
                                                              ,(make-acons-nest dag-vars)
                                                              ',(make-interpreted-function-alist (get-non-built-in-supporting-fns-list dag-fns *axe-evaluator-functions* (w state)) (w state))
                                                              '0 ;array depth (not very important)
                                                              )
                               ;; function-type must be :lets:
                               (dag-to-term-with-lets dag)))))
       (evaluator-neededp (and produce-function
                               (eq :embedded-dag function-type)))
       (new-term (and produce-theorem (dag-to-term dag)))
       (defconst-name-string (symbol-name defconst-name))
       (theorem-name (and produce-theorem (pack$ (subseq defconst-name-string 1 (- (length defconst-name-string) 1)) '-unroll-spec-basic-theorem)))
       (theorem (and produce-theorem
                     `(skip-proofs
                       (defthm ,theorem-name
                         (implies (and ,@assumptions)
                                  (equal ,term
                                         ,new-term))
                         ;; Use :rule-classes nil if it can't be a theorem
                         ;; TODO: Use a more thorough check of whether it's a valid rewrite rule (if no change, ACL2 will reject the rule)
                         ,@(if (equal new-term term) '(:rule-classes nil) nil)))))
       (items-created (append (list defconst-name)
                              (if produce-function (list function-name) nil)
                              (if produce-theorem (list theorem-name) nil)))
       (defun-variant (if disable-function 'defund 'defun))
       ((mv end-time state) (get-real-time state))
       (- (if (= 1 (len items-created))
              (cw "Created ~x0.~%~%" (first items-created))
            (cw "Created ~x0 items: ~X12.~%~%" (len items-created) items-created nil)))
       ;; (- (cw "Info on unrolled spec DAG:~%"))
       (- (print-dag-info dag defconst-name nil))
       (- (if (dag-is-purep-aux dag :all t) ; prints any non-pure nodes
              (cw "~x0 is a pure dag.~%" defconst-name)
            (cw "~%WARNING: ~x0 is not a pure dag (see above)!~%" defconst-name)))
       (- (progn$ (cw "~%SPEC UNROLLING FINISHED (")
                  (print-to-hundredths (- end-time start-time))
                  (cw "s).") ; s = seconds
                  ))
       (- (cw ")~%~%")))
    (mv (erp-nil)
        ;; If dag is a quoted constant, then it gets doubly quoted here.  This
        ;; makes sense: You unquote this thing and either get a DAG or a quoted
        ;; constant, as usual:
        `(progn ,@(and evaluator-neededp '((include-book "kestrel/axe/evaluator" :dir :system))) ; has skip-proofs, so only included if needed
                (defconst ,defconst-name ',dag)
                ,@(and produce-function `((,defun-variant ,function-name ,function-params ,function-body)))
                ,@(and produce-theorem (list theorem))
                (with-output :off :all (table unroll-spec-basic-table ',whole-form ':fake))
                (value-triple :invisible)
                ;; (value-triple ',items-created) ;todo: use cw-event and then return :invisible here?
                )
        state)))

(defmacrodoc unroll-spec-basic (&whole whole-form
                                       defconst-name ;; The name of the DAG constant to create
                                       term          ;; The term to simplify
                                       &key
                                       ;; Options that affect the meaning of the result:
                                       (assumptions 'nil)
                                       (interpreted-function-alist ':auto) ;; todo: instead, pass in extra-interpreted-fns?  and bring in their subfunctions too...
                                       ;; Options that affect how the rewriting goes:
                                       (rules ':standard) ;to completely replace the usual set of rules
                                       ;; (rule-alists) ;to completely replace the usual set of rules (TODO: default should be auto?)
                                       (extra-rules 'nil) ; to add to the usual set of rules
                                       (remove-rules 'nil) ; to remove from to the usual set of rules
                                       (normalize-xors 'nil)
                                       ;; Options that affect performance:
                                       (memoizep 't)
                                       ;; Options for debugging:
                                       (monitor 'nil)
                                       (count-hits 'nil)
                                       (print 'nil)
                                       ;; Options that affect what is produced:
                                       (produce-function 'nil)
                                       (disable-function 'nil) ;todo: consider making 't the default
                                       (function-type ':auto)
                                       (function-params ':auto)
                                       (produce-theorem 'nil)
                                       (local 't)
                                       )
  (let ((form `(make-event-quiet (unroll-spec-basic-fn ',defconst-name
                                                       ,term
                                                       ,rules
                                                       ;; ,rule-alists
                                                       ,extra-rules
                                                       ,remove-rules
                                                       ,assumptions
                                                       ,interpreted-function-alist
                                                       ,monitor
                                                       ,memoizep
                                                       ,count-hits
                                                       ,normalize-xors
                                                       ,produce-function
                                                       ,disable-function
                                                       ,function-type
                                                       ,function-params
                                                       ,produce-theorem
                                                       ,print
                                                       ',whole-form
                                                       state))))
    (if (check-boolean local)
        `(local ,form)
      form))
  :parents (axe) ; or can we consider this a lifter?
  :short "Open functions and unroll recursion in a spec."
  :args ((defconst-name
           "The name of the constant to create.  This constant will represent the computation in DAG form.  A function may also created (its name is obtained by stripping the stars from the defconst name).")
         (term "The term to simplify.")
         (assumptions "Assumptions to use when unrolling (a list of untranslated terms over the variables in the supplied term, and perhaps additional variables).  Or one of the special symbols :bytes or :bits, meaning to assume that all free variables in the supplied term are bytes or bits, respectively.")
         (interpreted-function-alist "Definitions of non-built-in functions to evaluate, or :auto.")
         (rules "The basic set of rules to use (a list of symbols), or :standard (meaning to use the standard set), or :auto (meaning to try to open functions until only supported Axe operations [on bit-vectors, booleans, arrays, etc.] remain).")
         (extra-rules "Rules to add to the base set of rules.")
         (remove-rules "Rules to remove from the base set of rules.")
         (memoizep "Whether to memoize during rewriting.")
         (monitor "Rules to monitor, a list of symbols.")
         (count-hits "Whether to count rule hits rewriting")
         (print "How much to print, a print-level")
         (normalize-xors "Whether to normalize nests of calls of @('bvxor') and @('bitxor').")
         (produce-function "Whether to produce a function (in addition to a defconst).")
         (disable-function "Whether to disable the produced function.")
         (function-type "How to create a function for the DAG (:term, :embedded-dag, :lets, or :auto).")
         (function-params "The param to use for the produced function (specifies their order).")
         (produce-theorem "Whether to create a theorem stating that the dag is equal to the orignal term (using skip-proofs).")
         (local "Whether to make the result of @('unroll-spec-basic') local to the enclosing book (or @('encapsulate')).  This prevents a large DAG from being stored in the @(tsee certificate) of the book, but it means that the result of @('unroll-spec-basic') is not accessible from other books.  Usually, the default value of @('t') is appropriate, because the book that calls @('unroll-spec-basic') is not included by other books."))
  :description ("Given a specification, unroll all recursion, yielding a DAG that only includes bit-vector and array operations."
                "To decide which rewrite rules to use, the tool starts with either the @(':rules') if supplied, or a basic default set of rules, @('unroll-spec-basic-rules').  Then the @(':extra-rules') are added and then the @(':remove-rules') are removed."))
