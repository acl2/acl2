; A version of unroll-spec that uses rewriter-basic.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
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
(include-book "dag-size-fast") ; for dag-or-quotep-size-less-thanp
(include-book "dag-to-term-with-lets")
(include-book "rules-in-rule-lists")
(include-book "evaluator") ;; since this calls dag-val-with-axe-evaluator to embed the resulting dag in a function, introduces a skip-proofs
(include-book "kestrel/utilities/check-boolean" :dir :system)
(include-book "kestrel/utilities/defmacrodoc" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/utilities/strip-stars-from-name" :dir :system)
(include-book "kestrel/utilities/system/fresh-names" :dir :system) ;drop?
(include-book "kestrel/utilities/supporting-functions" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "dag-info")

;; If asked to create a theorem, this uses skip-proofs to introduce it.

(defun unroll-spec-basic-rules ()
  (append (base-rules)
          (amazing-rules-bv)
          (leftrotate-intro-rules) ; perhaps not needed if the specs already use rotate ops
          (list-rules)
          ;; (introduce-bv-array-rules)
          ;; '(list-to-byte-array) ;; todo: add to a rule set (whatever mentions list-to-bv-array)
          ))

(ensure-rules-known (unroll-spec-basic-rules))

;dup
(defconst *bv-and-array-fns-we-can-translate*
  '(equal getbit bvchop ;$inline
          slice
          bvcat
          bvplus bvuminus bvminus bvmult
          bitor bitand bitxor bitnot
          bvor bvand bvxor bvnot
          bvsx bv-array-read bv-array-write bvif
          leftrotate32
          boolor booland ;boolxor
          not
          bvlt                       ;new
          sbvlt                      ;new
          ))

(defund filter-function-names (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (plist-worldp wrld))))
  (if (endp rule-names)
      nil
    (let ((rule-name (first rule-names)))
      (if (function-symbolp rule-name wrld)
          (cons rule-name
                (filter-function-names (rest rule-names) wrld))
        (filter-function-names (rest rule-names) wrld)))))

(defthm symbol-listp-of-filter-function-names
  (implies (symbol-listp rule-names)
           (symbol-listp (filter-function-names rule-names wrld)))
  :hints (("Goal" :in-theory (enable filter-function-names))))

;; TODO: Add more options, such as :print-interval, to pass through to simp-term
;; Returns (mv erp event state)
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
                              ;; (pseudo-termp term) ;; really an untranlated term
                              (or (eq :standard rules)
                                  (eq :auto rules)
                                  (symbol-listp rules))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              ;; (pseudo-term-listp assumptions) ;; untranslated terms
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
                  :mode :program ;; because this calls translate (todo: factor that out)
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
       (- (cw "~%(Unrolling spec:~%"))
       (term (translate-term term 'unroll-spec-basic-fn (w state)))
       (assumptions (translate-terms assumptions 'unroll-spec-basic-fn (w state)))
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
                                         (append '(leftrotate ; don't open leftrotate
                                                   nth update-nth len true-listp
                                                   nthcdr ; opener could loop with nth-of-cdr, etc.
                                                   firstn
                                                   take
                                                   list-to-bv-array
                                                   ifix nfix
                                                   floor mod
                                                   )
                                                 *bv-and-array-fns-we-can-translate*)
                                         (w state)))
                   ((mv opener-events opener-rule-names)
                    (opener-rules-for-fns defined-supporting-fns t '-for-unroll-spec-basic nil nil state))
                   (- (cw "Will use the following ~x0 additional opener rules: ~X12~%" (len opener-rule-names) opener-rule-names nil))
                   ;; todo: name this rule set?:  what else should go in it
                   ;; try to use unroll-spec-basic-rules here
                   ;; todo: could loop with the openers (e.g., )?
                   (rule-names (append '(;consp-of-cons  ; about primitives ; todo: when else might be needed?
                                         ;car-cons
                                         ;cdr-cons
                                         )
                                       (bv-array-rules-simple)
                                       (list-to-bv-array-rules)
                                       (type-rules) ; give us type facts about bv ops
                                       (set-difference-eq (core-rules-bv)
                                                          ;; these are kind of like trim rules, and can make the result worse:
                                                          '(;BVCHOP-OF-BVPLUS
                                                            BVCHOP-OF-bvuminus
                                                            ))
                                       (list-rules) ; or we could allow the list functions to open (if both, watch for loops with list-rules and the list function openers)
                                       (unsigned-byte-p-forced-rules)
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
                             monitor
                             memoizep
                             count-hits
                             print
                             normalize-xors
                             (w state)))
       ((when erp) (mv erp nil state))
       ((when (quotep dag))
        (er hard? 'unroll-spec-basic-fn "Spec unexpectedly rewrote to the constant ~x0." dag)
        (mv :unexpected-quotep nil state))
       ;; Make a theorem if the term is small enough.  We must use skip-proofs
       ;; because Axe does not yet produce an ACL2 proof. TODO: We could
       ;; support adding the theorem even if the DAG is large is we use
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
       (function-body (if (eq :term function-type)
                          (dag-to-term dag)
                        (if (eq :embedded-dag function-type)
                            `(dag-val-with-axe-evaluator ,defconst-name
                                                         ,(make-acons-nest dag-vars)
                                                         ',(make-interpreted-function-alist (get-non-built-in-supporting-fns-list dag-fns (w state)) (w state))
                                                         '0 ;array depth (not very important)
                                                         )
                          ;; function-type must be :lets:
                          (dag-to-term-with-lets dag))))
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
       (- (cw "Unrolling finished.~%"))
       ;; (- (cw "Info on unrolled spec DAG:~%"))
       (- (print-dag-info dag defconst-name nil))
       (- (cw ")~%")))
    (mv (erp-nil)
        ;; If dag is a quoted constant, then it gets doubly quoted here.  This
        ;; makes sense: You unquote this thing and either get a DAG or a quoted
        ;; constant, as usual:
        `(progn (defconst ,defconst-name ',dag)
                ,@(and produce-function `((,defun-variant ,function-name ,function-params ,function-body)))
                ,@(and produce-theorem (list theorem))
                (with-output :off :all (table unroll-spec-basic-table ',whole-form ':fake))
                (value-triple ',items-created) ;todo: use cw-event and then return :invisible here?
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
         (assumptions "Assumptions to use when unrolling")
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
                "To decide which rewrite rules to use, the tool starts with either the @(':rules') if supplied, or a basic default set of rules, @('unroll-spec-basic-rules').  Then the @(':extra-rules') are added and then @(':remove-rules') are removed."))
