; A transformations to arrange IFs for a C loop function
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Only deals with top-level if structure
;; Helps get the body to be a "loop term".  See :doc ATC.

;; See tests in arrange-ifs-and-mbts-tests.lisp.

;; TODO: Work harder to lift MBT upward in the nest

(include-book "utilities/def-equality-transformation")
(include-book "kestrel/untranslated-terms/conjuncts-of-uterm" :dir :system)
(include-book "kestrel/untranslated-terms/conjuncts-and-disjuncts" :dir :system)
(include-book "kestrel/utilities/negate-form" :dir :system) ; compare to negate-term?
(include-book "std/basic/mbt-dollar" :dir :system) ; since this tool knows about mbt$
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(defund negate-forms (forms)
  (declare (xargs :guard (true-listp forms)))
  (if (endp forms)
      forms
    (cons (negate-form (first forms))
          (negate-forms (rest forms)))))

(local
 (defthm true-listp-of-negate-forms
   (implies (true-listp forms)
            (true-listp (negate-forms forms)))
   :hints (("Goal" :in-theory (enable negate-forms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; move

;; returns an untranslated term
(defun make-untranslated-disjunction (disjuncts)
  (declare (xargs :guard (true-listp disjuncts)))
  (if (endp disjuncts)
      nil ; don't need to quote
    (if (endp (rest disjuncts))
        (first disjuncts)
      `(or ,@disjuncts))))

;; returns an untranslated term
(defun make-untranslated-conjunction (conjuncts)
  (declare (xargs :guard (true-listp conjuncts)))
  (if (endp conjuncts)
      t ; don't need to quote
    (if (endp (rest conjuncts))
        (first conjuncts)
      `(and ,@conjuncts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund call-of-notp (form)
  (declare (xargs :guard t))
  (and (consp form)
       (eq 'not (ffn-symb form))
       (consp (fargs form))
       (null (cdr (fargs form)))))

(defun calls-of-notp (forms)
  (declare (xargs :guard t))
  (if (not (consp forms))
      (null forms)
    (and (call-of-notp (first forms))
         (calls-of-notp (rest forms)))))

(defthm calls-of-notp-forward-to-true-listp
  (implies (calls-of-notp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable calls-of-notp))))

(local
 ;; Avoids a nested induction.
 (defthm calls-of-notp-of-rev
   (implies (true-listp x)
            (equal (calls-of-notp (rev x))
                   (calls-of-notp x)))
   :hints (("Goal" :in-theory (enable calls-of-notp)
                   :induct (true-listp x)))))

(defun strip-nots (forms)
  (declare (xargs :guard (calls-of-notp forms)
                  :guard-hints (("Goal" :in-theory (enable call-of-notp)))))
  (if (endp forms)
      nil
    (cons (farg1 (first forms))
          (strip-nots (rest forms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes an (untranslated) call of MBT or MBT$.
(defund mbt-callp (term)
  (declare (xargs :guard t))
  (and (or (call-of 'mbt term)
           (call-of 'mbt$ term))
       (true-listp term) ; not always necessary to check
       (consp (fargs term))))

; looks for (RETURN-LAST 'MBE1-RAW 'T <x>)
(defund translated-mbt-callp (term)
  (declare (xargs :guard t))
  (and (call-of 'return-last term)
       (true-listp term) ; not always necessary to check
       (consp (cddr (fargs term)))
       (equal ''mbe1-raw (first (fargs term)))
       (equal ''t (second (fargs term)))))

(defund maybe-translated-mbt-callp (term)
  (declare (xargs :guard t))
  (or (mbt-callp term)
      (translated-mbt-callp term)))

(defund maybe-translated-mbt-callsp (forms)
  (declare (xargs :guard t))
  (if (not (consp forms))
      (null forms)
    (and (maybe-translated-mbt-callp (first forms))
         (maybe-translated-mbt-callsp (rest forms)))))

(defthm maybe-translated-mbt-callsp-forward-to-true-listp
  (implies (maybe-translated-mbt-callsp forms)
           (true-listp forms))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable maybe-translated-mbt-callsp))))

(local
 ;; Avoids a nested induction.
 (defthm maybe-translated-mbt-callsp-of-rev-mbts
   (implies (true-listp mbts)
            (equal (maybe-translated-mbt-callsp (rev mbts))
                   (maybe-translated-mbt-callsp mbts)))
   :hints (("Goal" :in-theory (enable maybe-translated-mbt-callsp)
            :induct (true-listp mbts)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extracts the argument of an (untranslated) call to MBT.
(defund mbt-arg (term)
  (declare (xargs :guard (and (mbt-callp term)
                              (call-of 'mbt term))
                  :guard-hints (("Goal" :in-theory (enable mbt-callp)))))
  (first (fargs term)))

;; Extracts the argument of an (untranslated) call to MBT$.
(defund mbt$-arg (term)
  (declare (xargs :guard (and (mbt-callp term)
                              (call-of 'mbt$ term))
                  :guard-hints (("Goal" :in-theory (enable mbt-callp)))))
  (list 'if (first (fargs term)) 't 'nil))

;; Extracts the argument of a (translated) call to MBT.
(defund translated-mbt-arg (term)
  (declare (xargs :guard (translated-mbt-callp term)
                  :guard-hints (("Goal" :in-theory (enable translated-mbt-callp)))))
  (third (fargs term)))

;; Extracts the argument of a call of MBT (translated or untranslated).
(defund maybe-translated-mbt-arg (term)
  (declare (xargs :guard (maybe-translated-mbt-callp term)
                  :guard-hints (("Goal" :in-theory (enable maybe-translated-mbt-callp
                                                           mbt-callp
                                                           translated-mbt-callp)))))
  (cond ((eq 'mbt (ffn-symb term)) (mbt-arg term))
        ((eq 'mbt$ (ffn-symb term)) (mbt$-arg term))
        (t (translated-mbt-arg term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extracts the args of a list of (translated) calls to MBT.
(defund maybe-translated-mbt-args (terms)
  (declare (xargs :guard (maybe-translated-mbt-callsp terms)
                  :guard-hints (("Goal" :in-theory (enable maybe-translated-mbt-callsp)))))
  (if (endp terms)
      nil
    (cons (maybe-translated-mbt-arg (first terms))
          (maybe-translated-mbt-args (rest terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund negated-maybe-translated-mbt-callp (term)
  (declare (xargs :guard t))
  (and (call-of 'not term)
       (true-listp term)
       (= 1 (len (fargs term)))
       (maybe-translated-mbt-callp (farg1 term))))

(defun negated-maybe-translated-mbt-callsp (forms)
  (declare (xargs :guard t))
  (if (not (consp forms))
      (null forms)
    (and (negated-maybe-translated-mbt-callp (first forms))
         (negated-maybe-translated-mbt-callsp (rest forms)))))

(local
 (defthm call-of-notp-forward-to-length-2
   (implies (call-of-notp term)
            (equal 2 (len term)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable call-of-notp)))))

(local
 (defthm negated-maybe-translated-mbt-callp-forward-to-call-of-notp
   (implies (negated-maybe-translated-mbt-callp term)
            (call-of-notp term))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable negated-maybe-translated-mbt-callp call-of-notp)))))

(local
 (defthm negated-maybe-translated-mbt-callp-forward-to-consp
   (implies (negated-maybe-translated-mbt-callp term)
            (consp term))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable negated-maybe-translated-mbt-callp)))))

(local
 ;; Avoids a nested induction.
 (defthm negated-maybe-translated-mbt-callsp-of-rev-when-negated-maybe-translated-mbt-callsp
   (implies (negated-maybe-translated-mbt-callsp x)
            (negated-maybe-translated-mbt-callsp (rev x)))
   :hints (("Goal" :in-theory (enable negated-maybe-translated-mbt-callsp)))))

(local
 ;; Avoids a nested induction.
 (defthm negated-maybe-translated-mbt-callsp-of-rev
   (implies (true-listp x)
            (equal (negated-maybe-translated-mbt-callsp (rev x))
                   (negated-maybe-translated-mbt-callsp x)))
   :hints (("Goal" :in-theory (enable negated-maybe-translated-mbt-callsp)
                    :induct (true-listp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv mbts others).
(defund split-out-mbts (terms mbts others)
  (declare (xargs :guard (and (true-listp terms)
                              (true-listp mbts)
                              (true-listp others))))
  (if (endp terms)
      (mv (reverse mbts) (reverse others))
    (let ((term (first terms)))
      (if (maybe-translated-mbt-callp term)
          (split-out-mbts (rest terms) (cons term mbts) others)
        (split-out-mbts (rest terms) mbts (cons term others))))))

;; Ex: (split-out-mbts '(x (foo y) (mbt (bar x y)) (return-last 'mbe1-raw 't (baz y x))) nil nil)

(local
 (defthm true-listp-of-mv-nth-0-of-split-out-mbts
   (implies (true-listp mbts)
            (true-listp (mv-nth 0 (split-out-mbts terms mbts others))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-out-mbts)))))

(local
 (defthm maybe-translated-mbt-callsp-of-mv-nth-0-of-split-out-mbts
   (implies (maybe-translated-mbt-callsp mbts)
            (maybe-translated-mbt-callsp (mv-nth 0 (split-out-mbts terms mbts others))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-out-mbts maybe-translated-mbt-callsp)))))

(local
 (defthm true-listp-of-mv-nth-1-of-split-out-mbts
   (implies (true-listp others)
            (true-listp (mv-nth 1 (split-out-mbts terms negated-mbts others))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-out-mbts)))))

(local
 (defthm len-of-mv-nth-0-of-split-out-mbts
   (equal (+ (len (mv-nth 0 (split-out-mbts terms negated-mbts others)))
             (len (mv-nth 1 (split-out-mbts terms negated-mbts others))))
          (+ (len terms) (len negated-mbts) (len others)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable split-out-mbts)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv negated-mbts others).
(defund split-out-negated-mbts (terms negated-mbts others)
  (declare (xargs :guard (and (true-listp terms)
                              (true-listp negated-mbts)
                              (true-listp others))))
  (if (endp terms)
      (mv (reverse negated-mbts) (reverse others))
    (let ((term (first terms)))
      (if (negated-maybe-translated-mbt-callp term)
          (split-out-negated-mbts (rest terms) (cons term negated-mbts) others)
        (split-out-negated-mbts (rest terms) negated-mbts (cons term others))))))

;; Ex: (split-out-negated-mbts '(x (foo y) (mbt (bar x y)) (not (return-last 'mbe1-raw 't (baz y x)))) nil nil)

(local
 (defthm true-listp-of-mv-nth-0-of-split-out-negated-mbts
   (implies (true-listp negated-mbts)
            (true-listp (mv-nth 0 (split-out-negated-mbts terms negated-mbts others))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-out-negated-mbts)))))

(local
 (defthm calls-of-notp-of-mv-nth-0-of-split-out-negated-mbts
   (implies (calls-of-notp negated-mbts)
            (calls-of-notp (mv-nth 0 (split-out-negated-mbts terms negated-mbts others))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-out-negated-mbts)))))

(local
 (defthm negated-maybe-translated-mbt-callsp-of-mv-nth-0-of-split-out-negated-mbts
   (implies (negated-maybe-translated-mbt-callsp negated-mbts)
            (negated-maybe-translated-mbt-callsp (mv-nth 0 (split-out-negated-mbts terms negated-mbts others))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-out-negated-mbts)))))

(defthm maybe-translated-mbt-callsp-of-strip-nots-when-negated-maybe-translated-mbt-callsp
  (implies (negated-maybe-translated-mbt-callsp negated-mbts)
           (maybe-translated-mbt-callsp (strip-nots negated-mbts)))
  :hints (("Goal" :in-theory (enable negated-maybe-translated-mbt-callsp strip-nots negated-maybe-translated-mbt-callp
                                     maybe-translated-mbt-callsp))))

(local
 (defthm true-listp-of-mv-nth-1-of-split-out-negated-mbts
   (implies (true-listp others)
            (true-listp (mv-nth 1 (split-out-negated-mbts terms negated-mbts others))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable split-out-negated-mbts)))))

(local
 (defthm len-of-mv-nth-0-of-split-out-negated-mbts
   (equal (+ (len (mv-nth 0 (split-out-negated-mbts terms negated-mbts others)))
             (len (mv-nth 1 (split-out-negated-mbts terms negated-mbts others))))
          (+ (len terms) (len negated-mbts) (len others)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable split-out-negated-mbts)))))

;move
(defun conjoin-uterms (uterm1 uterm2)
  (declare (xargs :guard t))
  (let ((conjuncts (union-equal-alt (conjuncts-of-uterm uterm1) (conjuncts-of-uterm uterm2))))
    (if (not (consp conjuncts))
        't ;; an AND of no conjuncts is true
      (if (not (consp (rest conjuncts)))
          (first conjuncts) ;; single conjunct
        `(and ,@conjuncts)))))

;; Turn (if (mbt <x>) (if (mbt <y>) <then> <else>) <else>) into
;; (if (mbt (and <x> <y>)) <then> <else>)
;; The arguments may be translated or untranslated.
(defund make-if-combining-mbts (test then else)
  (declare (xargs :guard t))
  (if (and (maybe-translated-mbt-callp test)
           (call-of 'if then)
           (= 3 (len (fargs then)))
           (maybe-translated-mbt-callp (farg1 then))
           (equal else (farg3 then)))
      `(if (mbt ,(conjoin-uterms (maybe-translated-mbt-arg test) (maybe-translated-mbt-arg (farg1 then))))
           ,(farg2 then)
         ,else)
    ;; no special handling:
    `(if ,test ,then ,else)))

(local (in-theory (disable macro-namep w global-table state-p)))

;; If UTERM is a call of CONS, expand the COND to expose IFs.  Only handles top-level CONDs
(defund maybe-expand-cond (uterm state)
  (declare (xargs :stobjs state))
  (if (call-of 'cond uterm)
      (b* (((when (not (true-listp uterm)))
            (er hard? 'maybe-expand-cond "Bad uterm: ~x0." uterm))
           ((when (not (and (macro-namep 'cond (w state))
                            (pseudo-termp (fgetprop 'cond 'guard ''t (w state))))))
            (er hard? 'maybe-expand-cond "Bad info for CONS in state.")))
        (magic-macroexpand1$$ uterm 'maybe-expand-cond (w state) state))
    uterm))

;; This does the following:
;; 1. For an IF test that is a conjunction of multiple MBTs, make a single MBT call on the conjunction.
;; 1b. If there are other non-MBT conjuncts, put them in a separate, inner IF.
;; 2. For an IF test that is a disjunction of multiple negated MBTs, drop the negations, make a single MBT that is a conjunction, and swap the then and else branches.
;; 2b. If there are other non-negated-MBT conjuncts, put them in an inner IF.
;; Else branches of MBTs are not handled, as they usually have no restrictions imposed by ATC.
;; It handles top-level IF and COND nests.  TODO: Handle other macros that expand to IF?
;; Returns a translated term except some MBTs and ANDs may have been put in.
(defund arrange-ifs-and-mbts-core-function-aux (term ; untranslated
                                               count
                                               state ; because of maybe-expand-cond
                                               )
  (declare (xargs :guard (natp count)
                  :stobjs state
                  :measure (nfix count)))
  (b* (((when (zp count))
        (er hard? 'arrange-ifs-and-mbts-core-function-aux "Recursion limit reached."))
       (term (maybe-expand-cond term state)) ; turn a top-level COND into an IF nest
       )
    (if (and (call-of 'if term)
             ;; (true-listp term)
             (= 3 (len (fargs term))))
        ;; A call of IF:
        (let* ((test (farg1 term))
               (then-branch (farg2 term))
               (else-branch (farg3 term))
               (test-conjuncts (conjuncts-of-uterm2 test))
               (test-disjuncts (disjuncts-of-uterm2 test)))
          (if (< 1 (len test-conjuncts)) ;; (if <conjunction> <then-branch> <else-branch>)
              (b* (((mv mbts others) (split-out-mbts test-conjuncts nil nil)))
                (if (endp mbts)
                    ;; There are no MBT conjuncts, so do nothing:
                    term
                  (if (endp others)
                      ;; There are only MBT conjuncts, so we bascially have (if (and (mbt ..) (mbt ..) ...) <then> <else>)
                      ;; We make (if (mbt (and .. .. ...)) <then> <else>) and we don't have to process the <else> branch.
                      (make-if-combining-mbts `(mbt ,(make-untranslated-conjunction (maybe-translated-mbt-args mbts)))
                                              (arrange-ifs-and-mbts-core-function-aux then-branch (+ -1 count) state)
                                              else-branch)
                    ;; there are both mbts and other disjuncts:
                    ;; so we have (if (and (mbt ..) (mbt ..) ... other1 other2 ...) <then> <else>)
                    ;; We make (if (and (mbt ..) (mbt ..) ...) (if (and other1 other2 ...) <then> <else>) <else>).
                    ;; TODO: What if the guards make this reordering of the tests give a guard error?:
                    `(if (mbt ,(make-untranslated-conjunction (maybe-translated-mbt-args mbts)))
                         (if ,(make-untranslated-conjunction others)
                             ,(arrange-ifs-and-mbts-core-function-aux then-branch (+ -1 count) state)
                           ,else-branch)
                       ,else-branch))))
            (if (< 1 (len test-disjuncts)) ;; (if <disjunction> <then-branch> <else-branch>)
                (b* (((mv negated-mbts others) (split-out-negated-mbts test-disjuncts nil nil)))
                  (if (endp negated-mbts)
                      ;; There are no negated MBT disjuncts, so do nothing:
                      term
                    (if (endp others)
                        ;; There are only negated MBT disjuncts, so we basically have (if (or (not (mbt ..)) ... (not (mbt ..))) <then> <else>)
                        ;; This is like (if (and (mbt ...) ... (mbt ..)) <else> <then>) and we don't have to process the <then> branch.
                        (make-if-combining-mbts `(mbt ,(make-untranslated-conjunction (maybe-translated-mbt-args (strip-nots negated-mbts))))
                                                (arrange-ifs-and-mbts-core-function-aux else-branch (+ -1 count) state)
                                                then-branch)
                      ;; there are both negated-mbts and other disjuncts:
                      ;; so we have (if (or (not (mbt ..)) (not (mbt ..)) ... other1 other2 ...) <then> <else>)
                      ;; so this is (if (and (mbt ..) (mbt ..) ... (not other1) (not other2) ...) <else> <then>)
                      ;; and we make (if (and (mbt ..) (mbt ..) ...) (if (and (not other1) (not other2)) <else> <then>) <then>).
                      ;; TODO: What if the guards means this reordering of the tests gives a guard error?:
                      `(if (mbt ,(make-untranslated-conjunction (maybe-translated-mbt-args (strip-nots negated-mbts))))
                           (if ,(make-untranslated-conjunction (negate-forms others))
                               ,(arrange-ifs-and-mbts-core-function-aux else-branch (+ -1 count) state)
                             ,then-branch)
                         ,then-branch))))
              ;; neither a conjunction nor a disjunction:
              (if (maybe-translated-mbt-callp test) ;; (if <mbt-call> <then-branch> <else-branch>)
                  ;; Arrange IFs in the <then-branch>, then re-make the IF (possibly combining).
                  ;; We need not process the <else-branch>, since ATC allows it to be any ACL2 term:
                  (make-if-combining-mbts test (arrange-ifs-and-mbts-core-function-aux then-branch (+ -1 count) state) else-branch)
                (if (negated-maybe-translated-mbt-callp test) ;; (if <negated-mbt-call> <then-branch> <else-branch>)
                    ;; For ATC, an MBT can't be negated, so we un-negate it and switch the branches.
                    ;; We need not process the <then-branch>, since ATC allows it to be any ACL2 term:
                    (make-if-combining-mbts (farg1 test) (arrange-ifs-and-mbts-core-function-aux else-branch (+ -1 count) state) then-branch)
                  ;; No special handling:
                  term)))))
      ;; Not an IF or COND:
      term)))

;; Transforms a function body.  Returns the new body.
;; We call translate-term here and then do the rest of the work in the :logic-mode helper function.
(defund arrange-ifs-and-mbts-core-function (fn
                                            untranslated-body
                                            state)
  (declare (xargs :guard (symbolp fn)
                  :stobjs state)
           (ignore fn))
  (let* ((new-body (arrange-ifs-and-mbts-core-function-aux untranslated-body 1000000000 state)))
    new-body))

;; Make the full transformation:
(def-equality-transformation
  arrange-ifs-and-mbts ; name of the transformation to create
  arrange-ifs-and-mbts-core-function ; core function to transform a function body
  ;; transform-specific required args:
  ()
  ;; transform-specific keyword args and defaults:
  ()
  :transform-specific-arg-descriptions ())
