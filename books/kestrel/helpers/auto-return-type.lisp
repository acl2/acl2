; A tool to auto-generate return-type theorems for functions.
;
; Copyright (C) 2020-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in auto-return-type-tests.lisp.

;; STATUS: In-progress

;; TODO: Handle functions that return multiple values (challenging example:
;; FNS-SUPPORTING-FNS-AUX with no types about the accs).

;; TODO: Handle more kinds of patterns

;; TODO: Handle non-unary predicates

;; TODO: Consider making :type-prescription rules when appropriate.

;; TODO: Add assumptions about other params that seem necessary for the
;; theorems to hold (do some analysis to see which may be relevant -- may need
;; to also look at the tests that guard the branches).

;; TODO: When generating return type theorems for a function, it may first be
;; necessary to generate, or at least check for, return-type theorems for
;; subfunctions.

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "tools/prove-dollar" :dir :system)
(include-book "kestrel/utilities/conjunctions" :dir :system)
(include-book "kestrel/terms-light/expand-lambdas-in-term" :dir :system)

;; todo: this must exist somewhere
(defun make-conj (conjuncts)
  (declare (xargs :guard (true-listp conjuncts)))
  (if (endp conjuncts)
      *t*
    (if (endp (rest conjuncts))
        (first conjuncts)
      `(and ,@conjuncts))))

(defun maybe-step-limitp (lim)
  (declare (xargs :guard t))
  (or (null lim)
      (natp lim)))

;; Returns (mv successp state).
(defund try-proof (form hints step-limit verbose state)
  (declare (xargs :mode :program ; because this calls prove$
                  :guard (and (maybe-step-limitp step-limit)
                              (booleanp verbose))
                  :stobjs state))
  (b* ((- (and verbose (cw "(Trying:~X01~%..." form nil)))
       ((mv & successp state)
        (prove$ form
                :hints hints
                :step-limit step-limit
                ))
       (- (and verbose (if successp (cw "Success.)~%") (cw "Failed.)~%")))))
    (mv successp state)))

;; Given an existing function, the tool uses its structure and guard to attempt
;; to guess and prove suitable return type theorems.  If successful, it returns
;; the generated theorem, with hints, suitable for pasting into your file.

;;todo: think about whether we care whether the list-pred only recognizes true-lists.
;;todo: we could check whether the list-pred actually recognizes a list of things that satisfy the element pred (either by checking the definition or trying some proofs).
(defmacro register-list-predicate (element-pred list-pred)
  `(progn
     ;; Sanity check:
     (thm (implies (and (,list-pred l)
                        (member-equal x l))
                   (,element-pred x))
          :hints (("Goal" :in-theory (enable ,list-pred))))

     ;; This table maps element predicates to their corresponding list predicates:
     (table pred-to-list-pred ',element-pred ',list-pred)
     ;; This table maps list predicates to their corresponding element predicates:
     (table list-pred-to-pred ',list-pred ',element-pred)))

;; TODO: Auto-populate these tables!

;; Register pseudo-term-listp as the list predicate for things that satisfy
;; pseudo-termp:
(register-list-predicate pseudo-termp pseudo-term-listp)
(register-list-predicate integerp integer-listp)
(register-list-predicate string string-listp)
(register-list-predicate rationalp rational-listp)
(register-list-predicate symbolp symbol-listp)
(register-list-predicate characterp character-listp)
(register-list-predicate standard-char-p standard-char-listp)
(register-list-predicate true-listp true-list-listp)
(register-list-predicate pseudo-termp pseudo-term-listp)
(register-list-predicate natp nat-listp)
(register-list-predicate posp pos-listp)
(register-list-predicate eqlablep eqlable-listp)
(register-list-predicate booleanp boolean-listp)
(register-list-predicate acl2-numberp acl2-number-listp)

(defund extract-branches (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (or (variablep term)
          (quotep term))
      (list term)
    (if (eq 'if (ffn-symb term))
        (append (extract-branches (farg2 term))
                (extract-branches (farg3 term)))
      (list term))))

(defthm pseudo-term-listp-of-extract-branches
  (implies (pseudo-termp term)
           (pseudo-term-listp (extract-branches term)))
  :hints (("Goal" :in-theory (enable extract-branches))))

(defund remove-calls-to (fn terms)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-listp terms))))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (if (and (consp term)
               (call-of fn term))
          (remove-calls-to fn (rest terms))
        (cons term (remove-calls-to fn (rest terms)))))))

(defthm pseudo-term-listp-of-remove-calls-to
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (remove-calls-to fn terms)))
  :hints (("Goal" :in-theory (enable remove-calls-to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; returns a conjunct or nil
;; todo: generalize from just finding unary calls
;; todo: Instead of this, consider calling guard-conjunct-for-formals.
(defund guard-conjunct-for-formal (guard-conjuncts formal)
  (declare (xargs :guard (and (pseudo-term-listp guard-conjuncts)
                              (symbolp formal))))
  (if (endp guard-conjuncts)
      nil
    (let ((guard-conjunct (first guard-conjuncts)))
      (if (and (consp guard-conjunct)
               (not (eq 'quote (ffn-symb guard-conjunct)))
               (= 1 (len (fargs guard-conjunct)))
               (eq formal (farg1 guard-conjunct)))
          guard-conjunct
        (guard-conjunct-for-formal (rest guard-conjuncts) formal)))))

(defthm pseudo-termp-of-guard-conjunct-for-formal
  (implies (pseudo-term-listp guard-conjuncts) ;(guard-conjunct-for-formal guard-conjuncts formal)
           (pseudo-termp (guard-conjunct-for-formal guard-conjuncts formal)))
  :hints (("Goal" :in-theory (enable guard-conjunct-for-formal))))

(defund guard-conjuncts-for-formal (guard-conjuncts formal)
  (declare (xargs :guard (and (pseudo-term-listp guard-conjuncts)
                              (symbolp formal))))
  (if (endp guard-conjuncts)
      nil
    (let ((guard-conjunct (first guard-conjuncts)))
      (if (and (consp guard-conjunct)
               (not (eq 'quote (ffn-symb guard-conjunct)))
               (= 1 (len (fargs guard-conjunct)))
               (eq formal (farg1 guard-conjunct)))
          (cons guard-conjunct (guard-conjuncts-for-formal (rest guard-conjuncts) formal))
        (guard-conjuncts-for-formal (rest guard-conjuncts) formal)))))

(defthm pseudo-term-listp-of-guard-conjuncts-for-formal
  (implies (pseudo-term-listp guard-conjuncts) ;(guard-conjunct-for-formal guard-conjuncts formal)
           (pseudo-term-listp (guard-conjuncts-for-formal guard-conjuncts formal)))
  :hints (("Goal" :in-theory (enable guard-conjuncts-for-formal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv defthms state).
(defun theorems-for-returned-formal-aux (guard-conjuncts-for-formal formal guard-conjuncts fn rv suffix step-limit verbose acc state)
  (declare (xargs :guard (and (symbolp formal)
                              (pseudo-term-listp guard-conjuncts)
                              (symbolp fn)
                              (symbol-listp rv)
                              (stringp suffix)
                              (maybe-step-limitp step-limit)
                              (booleanp verbose))
                  :mode :program ; because this ultimately calls prove$
                  :stobjs state))
  (if (endp guard-conjuncts-for-formal)
      (mv (reverse acc) state)
    (b* ((guard-conjunct-for-formal (first guard-conjuncts-for-formal))
         (pred (ffn-symb guard-conjunct-for-formal))
         (possible-theorem-body `(implies ,(make-conj guard-conjuncts) ;; consider try just guard-conjunct-for-formal, or at least try to reduce this
                                          ,(sublis-var-simple (acons formal rv nil)
                                                              guard-conjunct-for-formal)))
         (hints `(("Goal" :in-theory (enable ,fn))))
         ((mv successp state)
          (try-proof possible-theorem-body hints step-limit verbose state)))
      (if successp
          (theorems-for-returned-formal-aux (rest guard-conjuncts-for-formal) formal guard-conjuncts fn rv suffix step-limit verbose
                                            (cons  `(defthm ,(pack$ pred '-of- fn suffix)
                                                      ,possible-theorem-body
                                                      :hints ,hints)
                                                   acc)
                                            state)
        (theorems-for-returned-formal-aux (rest guard-conjuncts-for-formal) formal guard-conjuncts fn rv suffix step-limit verbose
                                          acc
                                          state)))))

;; If one of the branches just returns the formal, look for guard
;; conjuncts for that formal and try to show that the whole RV satisfies
;; them.
;; Returns (mv theorems state).
(defun theorems-for-returned-formal (formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state)
  (declare (xargs :stobjs state
                  :mode :program ; because this ultimately calls prove$
                  :guard (and (symbolp formal)
                              (pseudo-term-listp guard-conjuncts)
                              (pseudo-term-listp non-self-branches)
                              (symbolp fn)
                              (symbol-listp rv)
                              (stringp suffix)
                              (maybe-step-limitp step-limit)
                              (booleanp verbose))))
  (if (member-eq formal non-self-branches)
      (theorems-for-returned-formal-aux (guard-conjuncts-for-formal guard-conjuncts formal) ; todo: might have to prove sets of these properties together...
                                        formal guard-conjuncts fn rv suffix step-limit verbose nil state)
    (mv nil state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun some-term-conses-itemp (item terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (if (and (call-of 'cons term)
               (= 2 (len (fargs term)))
               (equal item (farg1 term)))
          t
        (some-term-conses-itemp item (rest terms))))))

;; If one of the branches conses the formal onto something, look for a guard
;; conjunct for that formal, see if it the predicate has a list version, and
;; try to show that the whole RV satisfies the list predicate.  Returns (mv theorems state).
(defun theorems-for-returned-consed-formal (formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state)
  (declare (xargs :stobjs state
                  :mode :program ; because this ultimately calls prove$
                  :guard (and (symbolp formal)
                              (pseudo-term-listp guard-conjuncts)
                              (pseudo-term-listp non-self-branches)
                              (symbolp fn)
                              (stringp suffix)
                              (maybe-step-limitp step-limit)
                              (booleanp verbose))))
  (if (not (some-term-conses-itemp formal non-self-branches))
      (mv nil state)
    (let ((guard-conjunct-for-formal (guard-conjunct-for-formal guard-conjuncts formal))) ;todo what if more than one?
      (if (not guard-conjunct-for-formal)
          (mv nil state)
        (let* ((item-pred (ffn-symb guard-conjunct-for-formal))
               (list-pred (lookup-eq item-pred (table-alist 'pred-to-list-pred (w state)))))
          (if (not list-pred)
              (mv nil state)
            ;; todo: check the other branches for sanity
            (b* ((possible-theorem-body `(implies ,guard-conjunct-for-formal ;ttodo: possibly include more guard conjuncts here...
                                                  ,(sublis-var-simple (acons :x rv nil)
                                                                  `(,list-pred :x))))
                 (hints `(("Goal" :in-theory (enable ,fn))))
                 ((mv successp state)
                  (try-proof possible-theorem-body hints step-limit verbose state)))
              (if successp
                  (mv (list `(defthm ,(pack$ list-pred '-of- fn suffix)
                               ,possible-theorem-body
                               :hints ,hints))
                      state)
                (mv nil state)))))))))

(defun some-term-conses-the-carp (item terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (if (and (call-of 'cons term)
               (= 2 (len (fargs term)))
               (equal `(car ,item) (farg1 term)))
          t
        (some-term-conses-the-carp item (rest terms))))))

;; If one of the branches conses the car of the formal onto something, look for
;; a guard conjunct for that formal (todo: check that it is a list pred), and
;; try to show that the whole RV satisfies the list predicate.  Returns (mv
;; theorems state).
;; TODO: Consider also guessing that the length doesn't increase.
(defun theorems-for-returned-consed-car (formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state)
  (declare (xargs :stobjs state
                  :mode :program ; because this ultimately calls prove$
                  :guard (and (symbolp formal)
                              (pseudo-term-listp guard-conjuncts)
                              (pseudo-term-listp non-self-branches)
                              (symbolp fn)
                              (stringp suffix)
                              (maybe-step-limitp step-limit)
                              (booleanp verbose))))
  (if (not (some-term-conses-the-carp formal non-self-branches))
      (mv nil state)
    (let ((guard-conjunct-for-formal (guard-conjunct-for-formal guard-conjuncts formal))) ;todo what if more than one?
      (if (not guard-conjunct-for-formal)
          (mv nil state)
        (let* ((item-pred (ffn-symb guard-conjunct-for-formal)))
          ;; todo: check the other branches for sanity
          (b* ((possible-theorem-body `(implies ,guard-conjunct-for-formal ;ttodo: possibly include more guard conjuncts here...
                                                ,(sublis-var-simple (acons :x rv nil)
                                                                `(,item-pred :x))))
               (hints `(("Goal" :in-theory (enable ,fn))))
               ((mv successp state)
                (try-proof possible-theorem-body hints step-limit verbose state)))
            (if successp
                (mv (list `(defthm ,(pack$ item-pred '-of- fn suffix)
                             ,possible-theorem-body
                             :hints ,hints))
                    state)
              (mv nil state))))))))

;; If one of the branches is just the car of the formal, look for a guard
;; conjunct for that formal that is a call to a list-pred, and try to show that
;; the whole RV satisfies the corresponding item predicate.  Returns (mv
;; theorems state).
;; TODO: What if there is another branch, such as nil?
(defun theorems-for-returned-car (formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state)
  (declare (xargs :stobjs state
                  :mode :program ; because this ultimately calls prove$
                  :guard (and (symbolp formal)
                              (pseudo-term-listp guard-conjuncts)
                              (pseudo-term-listp non-self-branches)
                              (symbolp fn)
                              (stringp suffix)
                              (maybe-step-limitp step-limit)
                              (booleanp verbose))))
  (if (not (member-equal `(car ,formal) non-self-branches))
      (mv nil state)
    (let ((guard-conjunct-for-formal (guard-conjunct-for-formal guard-conjuncts formal))) ;todo what if more than one?
      (if (not guard-conjunct-for-formal)
          (mv nil state)
        (let* ((list-pred (ffn-symb guard-conjunct-for-formal))
               (item-pred (lookup-eq list-pred (table-alist 'list-pred-to-pred (w state)))))
          (if (not item-pred)
              (mv nil state)
            ;; todo: check the other branches for sanity
            (b* ((possible-theorem-body `(implies ,guard-conjunct-for-formal ;ttodo: possibly include more guard conjuncts here...
                                                  ,(sublis-var-simple (acons :x rv nil)
                                                                  `(,item-pred :x))))
                 (hints `(("Goal" :in-theory (enable ,fn))))
                 ((mv successp state)
                  (try-proof possible-theorem-body hints step-limit verbose state)))
              (if successp
                  (mv (list `(defthm ,(pack$ item-pred '-of- fn suffix)
                               ,possible-theorem-body
                               :hints ,hints))
                      state)
                (mv nil state)))))))))

;; Returns (mv theorems state).
(defun return-type-theorems-based-on-formal (formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state)
  (declare (xargs :stobjs state
                  :mode :program ; because this ultimately calls prove$
                  :guard (and (symbolp formal)
                              (pseudo-term-listp guard-conjuncts)
                              (pseudo-term-listp non-self-branches)
                              (symbolp fn)
                              (stringp suffix) ; either of the form -XXX or the empty string
                              (maybe-step-limitp step-limit)
                              (booleanp verbose)
                              )))
  (b* (((mv theorems1 state) (theorems-for-returned-formal formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state))
       ((mv theorems2 state) (theorems-for-returned-consed-formal formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state))
       ((mv theorems3 state) (theorems-for-returned-consed-car formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state))
       ((mv theorems4 state) (theorems-for-returned-car formal guard-conjuncts non-self-branches fn rv suffix step-limit verbose state)))
    (mv (append theorems1
                theorems2
                theorems3
                theorems4)
        state)))

;; If one branch simply returns a formal, try to prove that the function has the same type as that formal.
;; TODO: handle non-unary type predicates.
;; Returns (mv theorems state) where THEOREMS is a list of theorems (possibly nil).
(defun return-type-theorems-based-on-formals (formals guard-conjuncts non-self-branches fn rv suffix step-limit verbose state)
  (declare (xargs :stobjs state
                  :mode :program ; because this ultimately calls prove$
                  :guard (and (symbol-listp formals)
                              (pseudo-term-listp guard-conjuncts)
                              (pseudo-term-listp non-self-branches)
                              (symbolp fn)
                              (stringp suffix) ; either of the form -XXX or the empty string
                              (maybe-step-limitp step-limit)
                              (booleanp verbose)
                              )))
  (if (endp formals)
      (mv nil state)
    (b* (((mv first-formal-theorems state)
          (return-type-theorems-based-on-formal (first formals) guard-conjuncts non-self-branches fn rv suffix step-limit verbose state))
         ((mv rest-formal-theorems state)
          (return-type-theorems-based-on-formals (rest formals) guard-conjuncts non-self-branches fn rv suffix step-limit verbose state)))
      (mv (append first-formal-theorems rest-formal-theorems)
          state))))

;; Returns (mv erp event state)
(defun auto-return-type-fn (fn suffix step-limit verbose state)
  (declare (xargs :stobjs state
                  :mode :program
                  :guard (and (symbolp fn)
                              ;; suffix?
                              (maybe-step-limitp step-limit)
                              (booleanp verbose))))
  (b* (((when (not (symbolp fn)))
        (er hard? 'auto-return-type-fn "~x0 is not a symbol." fn)
        (mv (erp-t) nil state))
       (body (fn-body fn t (w state)))
       (body (expand-lambdas-in-term body))
       (branches (extract-branches body))
       (- (cw "Body has ~x0 branches.~%" (len branches)))
       ;; We can remove tail calls because they will match whatever type we are deriving:
       (non-self-branches (remove-calls-to fn branches))
       (- (cw "Body has ~x0 non-self branches.~%" (len non-self-branches)))
       (formals (fn-formals fn (w state)))
       (guard (fn-guard fn (w state))) ;todo: what about declared types?
       ((when (not (pseudo-termp guard))) ;todo: improve fn-guard
        (er hard? 'auto-return-type-fn "bad guard.")
        (mv (erp-t) nil state))
       (guard-conjuncts (get-conjuncts guard))
       ;; (- (cw "Guard conjuncts: ~x0~%" guard-conjuncts))
       (suffix (if suffix (symbol-name (pack$ '- suffix)) ""))
       ((mv return-type-theorems-based-on-formals state)
        (return-type-theorems-based-on-formals formals guard-conjuncts non-self-branches fn `(,fn ,@formals) suffix step-limit verbose state))
       ((when (not return-type-theorems-based-on-formals))
        (er hard? 'auto-return-type-fn "No return type theorems found.")
        (mv (erp-t)
            nil
            state)))
    (mv (erp-nil)
        `(progn ,@return-type-theorems-based-on-formals)
        state)))

;; Make but do not submit the return-type theorems:
(defmacro auto-return-type (fn
                            &key
                            (suffix 'nil)
                            (step-limit '100000)
                            (verbose 't))
  `(auto-return-type-fn ',fn ',suffix ',step-limit ',verbose state))

;; Make and submit the return-type theorems:
(defmacro submit-auto-return-type (fn
                                   &key
                                   (suffix 'nil)
                                   (step-limit '100000)
                                   (verbose 't))
  `(make-event (auto-return-type-fn ',fn ',suffix ',step-limit ',verbose state)))

;; TODO: Add a version that takes multiple functions (or perhaps all functions)?
