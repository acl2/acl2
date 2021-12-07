; A JVM lifter for use when not unrolling
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Tool for lifting JVM code to logic.  See documentation in doc.lisp.

;fixme pass in a flag to prevent this: "Decompiling didn't work. Unrolling the loop:..." from happening.  instead, it should throw an error

;;FFFIXME this book can make some big assumptions which could render the decompiled
;;code incorrect.
;;the decompiler can discard paths that include the throwing of exceptions (and
;;maybe other errors)..  also, all loops are assumed to terminate .. how else do
;;we cheat? fixme make some of these options that can be turned off?

;FIXME if the dags involved here will be big, perhaps they should be stored as dag-arrays?

;some stuff below may not be used?

;fixme add check that no error branches remain when they should all be gone
;;fixme make sure the rules used to generate the invars are the same as used to prove them!

;;fixme - handle loops with multiple exit points
;;  e.g, the first loop in org.bouncycastle.crypto.digests.GeneralDigest.update([BII)V (at PC 16)

;;fixme handle the case when a loop is not executed at all..

;; TODO: Add support for lifting code that contains recursive calls.

;; TODO: Make the order of parameters in loop functions (e.g., those that come from heap-update-triples) more predictable/stable.

;; TODO: Print a warning or error if user attempts to lift a recursive function

(include-book "kestrel/jvm/control-flow" :dir :system)
(include-book "kestrel/jvm/load-class" :dir :system)
(include-book "rule-lists-jvm")
(include-book "rules-in-rule-lists-jvm") ;include less?  but some of these rules are now used during decompilation?
(include-book "lifter-utilities")
(include-book "kestrel/utilities/get-vars-from-term" :dir :system)
(include-book "kestrel/utilities/ints-in-range" :dir :system)
(include-book "lifter-utilities3")
(include-book "../rewriter" :ttags :all)
(include-book "../make-axe-rules2")
(include-book "../dag-to-term-with-lets")
;(include-book "kestrel/bv/arith" :dir :system) ;todo?
(include-book "jvm-rules-axe2") ;for smart if handling
(include-book "../math-rules")
(include-book "kestrel/untranslated-terms-old/untranslated-terms" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/alists-light/lookup-equal-safe" :dir :system)
(include-book "kestrel/utilities/auto-termination" :dir :system)
(include-book "../prune") ;for maybe-prune-dag
(include-book "kestrel/jvm/symbolic-execution2" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/bv-lists/bv-array-conversions" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))

;; for speed:
(local (in-theory (disable acl2-count
                           consp-from-len-cheap
                           all-natp-when-nat-listp
                           nat-listp)))

(in-theory (disable dag-to-term
                    top-nodenum
                    w
                    CAR-BECOMES-NTH-OF-0 ;move up
                    weak-dagp-aux ;for speed
                    ))

;dup
(defun my-pack-list (item lst)
  (if (endp lst)
      nil
    (cons (pack$ item (car lst))
          (my-pack-list item (cdr lst)))))

;dup
;doesn't go inside lambda bodies - is that okay?
;not exhaustive!
;reorder params to more closely resemble sublis-var-simple?
(mutual-recursion
 (defun replace-in-term2 (term alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (alistp alist))))
   (let* ((match (assoc-equal term alist)))
     (if match
         (cdr match) ;could recur on this...
       (if (atom term)
           term
         (if (quotep term)
             term
           (cons (ffn-symb term)
                 (replace-in-terms2 (fargs term) alist)))))))

 (defun replace-in-terms2 (terms alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (alistp alist))))
   (if (endp terms)
       nil
     (cons (replace-in-term2 (car terms) alist)
           (replace-in-terms2 (cdr terms) alist)))))

(defthm myif-of-myif-of-myif-same-tests
  (equal (myif test (myif test2 (myif test tp ep) ep2) ep3)
         (myif test (myif test2 tp ep2) ep3))
  :hints (("Goal" :in-theory (enable myif))))

;; Maximum size allowed for various terms (e.g., in bodies of generated
;; functions).  Terms larger than this will be represented as embedded DAGs.
;; TODO: Consider raising this limit.
(defconst *max-term-size* 100)

;; Convert DAG-LST to an equivalent term, using an embedded DAG if it the term
;; would be larger than max-term-size.
(defun dag-to-term-limited (dag
                            max-term-size     ;nil means no limit
                            use-lets-in-terms ;boolean
                            interpreted-function-alist ;todo, check that this includes definitions for all non-built-in functions (and all functions they call, etc.)
                            )
  (declare (xargs :guard (and (or (and (pseudo-dagp dag)
                                       (< (len dag) 2147483647))
                                  (myquotep dag))
                              (or (null max-term-size)
                                  (natp max-term-size))
                              (booleanp use-lets-in-terms)
                              (interpreted-function-alistp interpreted-function-alist))
                  :guard-hints (("Goal" :in-theory (enable CAR-OF-CAR-WHEN-PSEUDO-DAGP-CHEAP)))))
  (if (quotep dag)
      dag
    (if (not max-term-size) ;no limit = always make a term
        ;; todo: only print the message if an embedded DAG would normally have been used?
        (if use-lets-in-terms
            (prog2$ (cw "Converting DAG to a term (without an embedded DAG) since max-term-size is nil.  Using lets for compactness.~%")
                    (dag-to-term-with-lets dag))
          (prog2$ (cw "Converting DAG to a term (without an embedded DAG) since max-term-size is nil.  Term size will be ~x0.~%" (dag-size-fast dag))
                  (dag-to-term dag)))
      ;; Max term size is a natural number:
      (if (dag-or-quotep-size-less-thanp dag max-term-size)
          (dag-to-term dag) ;todo: respect use-lets-in-terms here as well?
        ;; term would be too big, so use an embedded dag:
        (let ((dag-vars (dag-vars dag)))
          `(dag-val-with-axe-evaluator ',dag
                                       ,(make-acons-nest dag-vars)
                                       ',interpreted-function-alist ;todo: trim this down to only what is needed
                                       '0))))))

(defun remove-duplicates-equal2-aux (lst seen-items)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp seen-items))))
  (if (endp lst)
      nil
    (if (member-equal (first lst) seen-items)
        (remove-duplicates-equal2-aux (rest lst) seen-items)
      (cons-with-hint (first lst)
                      (remove-duplicates-equal2-aux (rest lst)
                                                    (cons (first lst) seen-items))
                      lst))))

;; This version keeps the first occurence if there are duplicates
(defun remove-duplicates-equal2 (lst)
  (declare (xargs :guard (true-listp lst)))
  (remove-duplicates-equal2-aux lst nil))

;;;
;;; loop-designators
;;;

;; A loop-designator designates a particular loop within a collection of
;; classes.  It is just the pc-designator for the code location at the top of the
;; loop.  Example: ("com.foo.bar.ClassName" "methodname" "(I)I" 20)
(defund loop-designatorp (des)
  (declare (xargs :guard t))
  (pc-designatorp des))

;(assert-event (loop-designatorp '("com.foo.bar.ClassName" "methodname" "(I)I" 20)))

(defund make-loop-designator (class-name method-name method-descriptor loop-top-pc)
  (declare (xargs :guard (and (jvm::class-namep class-name)
                              (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor)
                              (jvm::pcp loop-top-pc))))
  (make-pc-designator class-name method-name method-descriptor loop-top-pc))

(local (in-theory (disable jvm::method-descriptorp jvm::method-namep)))

(defthm loop-designatorp-of-make-loop-designator
  (implies (and (jvm::class-namep class-name)
                (jvm::method-namep method-name)
                (jvm::method-descriptorp method-descriptor)
                (jvm::pcp pc))
           (loop-designatorp (make-loop-designator class-name method-name method-descriptor pc)))
  :hints (("Goal" :in-theory (enable loop-designatorp make-loop-designator
                                     make-pc-designator ;why?
                                     ))))

(defforall-simple loop-designatorp)
(verify-guards all-loop-designatorp)

;;;
;;; loop-ids
;;;

;; A loop-id is either a full loop-designator or a PC that can be elaborated to
;; a full loop-designator (e.g., by assuming it is in the main method being
;; lifted).
(defund loop-idp (loop-id)
  (declare (xargs :guard t))
  (or (loop-designatorp loop-id)
      (jvm::pcp loop-id)))

(defforall-simple loop-idp)
(verify-guards all-loop-idp)

;; Elaborate a loop-id (which may just be a PC) into a full loop designator.
(defun elaborate-loop-id (loop-id class-name method-name method-descriptor keyword-context)
  (declare (xargs :guard (and (loop-idp loop-id)
                              (jvm::class-namep class-name)
                              (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor))))
  (if (loop-designatorp loop-id) ;already a loop-designator
      loop-id
    (if (jvm::pcp loop-id) ;a natp is taken to be a PC in the main method being lifted
        (make-loop-designator class-name method-name method-descriptor loop-id)
      (er hard 'elaborate-loop-ids "Bad loop-id, ~x0, in supplied ~x1" loop-id keyword-context))))

;; (defun elaborate-loop-ids (loop-ids class-name method-name method-descriptor keyword-context)
;;   (declare (xargs :guard (and (all-loop-idp loop-ids)
;;                               (true-listp loop-ids)
;;                               (jvm::class-namep class-name)
;;                               (jvm::method-namep method-name)
;;                               (jvm::method-descriptorp method-descriptor))))
;;   (if (endp loop-ids)
;;       nil
;;     (cons (elaborate-loop-id (first loop-ids) class-name method-name method-descriptor keyword-context)
;;           (elaborate-loop-ids (rest loop-ids) class-name method-name method-descriptor keyword-context))))

;;;
;;; loop-function-ids (before elaboration)
;;;

;; A loop-function-designator is either the name of a loop function, or a
;; loop-id which stands for all functions created by lifting that loop (perhaps
;; in multiple contexts):
(defund loop-function-idp (item)
  (declare (xargs :guard t))
  (or (symbolp item)
      (loop-idp item)))

(defforall-simple loop-function-idp)
(verify-guards all-loop-function-idp)

;;;
;;; loop-function-designators (after elaboration)
;;;

(defun loop-function-designatorp (item)
  (declare (xargs :guard t))
  (or (symbolp item)
      (loop-designatorp item)))

(defforall-simple loop-function-designatorp)
(verify-guards all-loop-function-designatorp)

;; Elaborate a loop-function-id (if it is a loop-id that needs to be elaborated).  Returns a loop-function-designator.
(defun elaborate-loop-function-id (loop-function-id class-name method-name method-descriptor keyword-context)
  (declare (xargs :guard (and (loop-function-idp loop-function-id)
                              (jvm::class-namep class-name)
                              (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor))))
  (if (symbolp loop-function-id)
      loop-function-id ;it's already a symbol naming a specific loop function
    (elaborate-loop-id loop-function-id class-name method-name method-descriptor keyword-context)))

(defthm loop-function-designatorp-of-elaborate-loop-id
  (implies (and (loop-function-idp loop-function-id)
                (jvm::class-namep class-name)
                (jvm::method-namep method-name)
                (jvm::method-descriptorp method-descriptor))
           (loop-function-designatorp (elaborate-loop-id loop-id class-name method-name method-descriptor keyword-context))))

;; Elaborate any loop function designators that are loop-ids that needs to be
;; elaborated (i.e., just PCs). Returns a list of loop-function-designators.
(defun elaborate-loop-function-ids (loop-function-ids class-name method-name method-descriptor keyword-context)
  (declare (xargs :guard (and (all-loop-function-idp loop-function-ids)
                              (true-listp loop-function-ids)
                              (jvm::class-namep class-name)
                              (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor))))
  (if (endp loop-function-ids)
      nil
    (cons (elaborate-loop-function-id (first loop-function-ids) class-name method-name method-descriptor keyword-context)
          (elaborate-loop-function-ids (rest loop-function-ids) class-name method-name method-descriptor keyword-context))))

;; In the first component of each doublet, replace a loop-id that is just a PC with a full loop designator.
;; (Also, make it into a true alist.)
;todo: could also allow a loop number somehow, maybe: (:loop 1) -- but what about allowing the users to name loops? -- these would both be tricky to elaborate ahead of time..
(defun elaborate-loop-function-ids-in-doublets (doublets class-name method-name method-descriptor keyword-context)
  (declare (xargs :guard (and (doublet-listp doublets)
                              (all-loop-function-idp (strip-cars doublets))
                              (jvm::class-namep class-name)
                              (jvm::method-namep method-name)
                              (jvm::method-descriptorp method-descriptor))))
  (let* ((loop-function-ids (strip-cars doublets))
         (loop-designators (elaborate-loop-function-ids loop-function-ids class-name method-name method-descriptor keyword-context))
         (vals (strip-cadrs doublets)))
    (pairlis$ loop-designators vals)))

(defun lookup-loop-function (loop-function-name loop-designator alist default)
  (declare (xargs :guard (and (symbolp loop-function-name)
                              (loop-designatorp loop-designator)
                              (alistp alist)
                              (all-loop-function-designatorp (strip-cars alist)))))
  ;; First lookup the loop function by name.  If no match, lookup the loop-designator
  (let ((res (assoc-eq loop-function-name alist)))
    (if res
        (cdr res)
      (let ((res (assoc-equal loop-designator alist)))
        (if res
            (cdr res)
          default)))))

;;;
;;; The :measures option
;;;

;; A measure-item is either :skip (meaning skip the termination proof), :auto
;; (meaning use the with-auto-termination tool), :acl2 (meaning let ACL2 guess
;; a measure), or an untranslated term over the single variable PARAMS.
(defun measure-itemp (item state)
  (declare (xargs :stobjs state :mode :program))
  (or (eq :skip item)
      (eq :auto item)
      (eq :acl2 item)
      (and ;(untranslated-termp item)
           (let ((term (translate-term item 'measure-itemp (w state))))
             (subsetp-eq (get-vars-from-term term)
                         '(params))))))

(defun all-measure-itemp (items state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom items)
      t
    (and (measure-itemp (first items) state)
         (all-measure-itemp (rest items) state))))

;; ;; A measures-option is either :skip, meaning to skip all measures, :auto,
;; ;; meaning to use with-auto-termination, or an alist whose keys are loop-designators and whose values are
;; ;; measures (terms over the single var 'params), :skip, :auto, or :acl2 (let ACL2 guess the measure)
;; (defun measures-optionp (alist state)
;;   (declare (xargs :stobjs state
;;                    :mode :program))
;;   (or (eq :skip alist)
;;       (eq :auto alist)
;;       (and (alistp alist) ;the lifter takes an list of doubles, but here in the decompiler, this is an alist... TODO: change that?
;;            (all-loop-designatorp (strip-cars alist))
;;            (all-measure-itemp (strip-cdrs alist) state))))

;; TODO: Allow a single term and use it for all measures (perhaps just one) -- will need to discriminate a lambda term from a doublet list
(defun measuresp (measures state)
  (declare (xargs :stobjs state :mode :program)) ;:program mode because this calls translate
  (or (eq :skip measures)
      (eq :auto measures)
      (eq :acl2 measures)
      (and (doublet-listp measures)
           (all-loop-function-idp (strip-cars measures))
           (all-measure-itemp (strip-cadrs measures) state))))

;; Returns an alist from loop-function-designators to measure-items.
(defun elaborate-measures-option (measures method-class method-name method-descriptor)
  (if (eq :skip measures)
      :skip
    (if (eq :auto measures)
        :auto
      (if (eq :acl2 measures)
          :acl2
        (elaborate-loop-function-ids-in-doublets measures method-class method-name method-descriptor :measures)))))

;;;
;;; The :measure-hints option
;;;

(defun measure-hintsp (measure-hints)
  (declare (xargs :guard t))
  (and (doublet-listp measure-hints)
       (all-loop-function-idp (strip-cars measure-hints))
       ;; todo: check (strip-cadrs measure-hints)?
       ))

;;;
;;; The :loop-guards option:
;;;

(defun loop-guardsp (loop-guards)
  (declare (xargs :guard t))
  (and (doublet-listp loop-guards)
       (all-loop-function-idp (strip-cars loop-guards))
       ;; todo: check (strip-cadrs loop-guards) ? thread through state?  attempt to translate it?
       ))

;;;
;;; The :invariants option:
;;;

(defforall-simple untranslated-term-listp)
(verify-guards all-untranslated-term-listp)

(defun invariantsp (x)
  (declare (xargs :guard t))
  (and (doublet-listp x)
       (all-loop-function-idp (strip-cars x))
       (all-untranslated-term-listp (strip-cadrs x))))

;;;
;;; The :excluded-locals option:
;;;

(defforall-simple nat-listp)
(verify-guards all-nat-listp)

(defun excluded-localsp (x)
  (declare (xargs :guard t))
  (and (doublet-listp x)
       (all-loop-function-idp (strip-cars x))
       (all-nat-listp (strip-cadrs x))))

;;;
;;; The :postludes option:
;;;

(defun postludesp (x)
  (declare (xargs :guard t))
  (and (doublet-listp x)
       (all-loop-function-idp (strip-cars x))
       (all-consp (strip-cadrs x)) ;todo: strengthen? (these are events, often progns)
       ))

;; We can rewrite an application of this to determine which of 2 values is
;; bigger or whether they are equal.
(defun comparison (x y)
  (if (< x y)
      '<
    (if (> x y)
        '>
      'equal)))

;; ;for this we want to ignore the error branches (since an error branch doesn't really have a PC)
;; (defconst-computed-simple *get-pc-from-dag-axe-rule-set*
;;   (make-axe-rules '(get-pc
;;                     jvm::pc-of-make-frame
;;                     JVM::top-frame-OF-PUSH-frame ;what about pop of push?
;;                     JVM::TOP-operand-OF-PUSH-operand
;;                     )
;;                   (w state)))

(defconst-computed-simple *address-axe-rule-alist*
  (make-rule-alist! (append (new-ad-rules) ;need at least the not-null-refp rules
                           (address-rules))
                   (w state)))

(defconst-computed-simple *get-local-axe-rule-alist*
  (make-rule-alist! (get-local-rules) (w state)))

(defun state-component-extraction-rules ()
  (append (jvm-simplification-rules)
          ;; TODO: Uncomment
          ;; '(initialized-classes-of-myif
          ;;   intern-table-of-myif
          ;;   class-table-of-myif
          ;;   monitor-table-of-myif
          ;;   heapref-table-of-myif)
          ;;(yet-more-rules-jvm) ;needed to push IFs, or we could open up JVM::thread-top-frame, JVM::CALL-STACK, etc.
          (amazing-rules-spec-and-dag)
          (map-rules)))

(ensure-rules-known (state-component-extraction-rules))

;use this more?
(defconst-computed-simple *state-component-extraction-axe-rule-alist*
  (make-rule-alist! (state-component-extraction-rules) (w state)))

(defconst-computed-simple *stack-height-axe-rule-alist*
  (make-rule-alist!
   (append (jvm-simplification-rules)
           '(equal-when-bound-dag
             LEN-EQUAL-IMPOSSIBLE
             EQUAL-CONSTANT-+-alt
             ;LEN-OF-CALL-STACK-OF-MYIF
             ;; jvm::call-stack-size-OF-POP-frame
             jvm::call-stack-size-of-pop-frame-strong
             comparison
             <-of-+-cancel-1-2
             equal-of-same-cancel-1
             equal-of-same-cancel-2
             equal-of-same-cancel-3
             equal-of-same-cancel-4
             ACL2-NUMBERP-OF-LEN
             fix)
           (amazing-rules-spec-and-dag)
           (map-rules))
   (w state)))

(defconst-computed-simple *simplify-boolean-axe-rule-alist*
  (make-rule-alist! (append (boolean-rules)
                           (base-rules))
                   (w state)))

;;These can't be added as ACL2 theorems because they are not true:
(make-event
 `(defconst *get-rid-of-replace-me-dont-reuse-axe-rule-alist*
    ',(make-rule-alist-simple
       (list (make-axe-rule-safe '(myif test 'replace-me-dont-reuse x)
                                 'x
                                 'get-rid-of-replace-me-dont-reuse-1
                                 nil
                                 nil
                                 nil
                                 (w state))
             (make-axe-rule-safe '(myif test x 'replace-me-dont-reuse)
                                 'x
                                 'get-rid-of-replace-me-dont-reuse-2
                                 nil
                                 nil
                                 (w state)
                                 nil))
       t
       nil ;priorities
       )))

;these seem mostly safe
(defun sbvlt-rules ()
  '(sbvlt-transitive-1             ;Mon Jul  6 20:15:32 2015
    sbvlt-of-bvplus-of-1-and-0-alt ;Mon Jul  6 20:31:11 2015
    sbvlt-of-maxint-when-sbvlt     ;Mon Jul  6 20:35:45 2015
    sbvlt-transitive-free          ;mon jul  6 20:41:53 2015
    sbvlt-of-bvplus-of-1-alt       ;mon jul  6 21:04:29 2015
    sbvlt-of-bvplus-of-minus-1 ;Mon Jul  6 21:16:02 2015
    sbvlt-of-one-less ;Tue Jul  7 15:42:39 2015
    not-equal-min-int-when-not-sbvlt ;Tue Jul  7 15:45:42 2015
    ))

;these seem safe
(defun type-rules2 ()
  '(integerp-when-unsigned-byte-p-free ;mon jul  6 21:02:14 2015
    <-of-negative-when-usbp ;mon jul  6 21:11:49 2015
    ))

(def-constant-opener make-pc-designator)

;; These are for when we are not unrolling nested loops:
;; TODO: Can we just exclude the header from the segment, step once to start, and use the normal rules?
(defun run-until-exit-segment-or-hit-loop-header-rules-split ()
  '(run-until-exit-segment-or-hit-loop-header-opener-1
    run-until-exit-segment-or-hit-loop-header-opener-2
    run-until-exit-segment-or-hit-loop-header-base-case-1
    run-until-exit-segment-or-hit-loop-header-base-case-2
    run-until-exit-segment-or-hit-loop-header-base-case-3
    run-until-exit-segment-or-hit-loop-header-of-myif-split ;todo

    get-pc-designator-from-state
    get-pc-designator-from-frame
    make-pc-designator-constant-opener ;since we have to check whether the result is among the loop headers

    jvm::step-always-open))

(ensure-rules-known (run-until-exit-segment-or-hit-loop-header-rules-split))

(defun run-until-exit-segment-or-hit-loop-header-rules-smart ()
  '(run-until-exit-segment-or-hit-loop-header-base-case-1
    run-until-exit-segment-or-hit-loop-header-base-case-2
    run-until-exit-segment-or-hit-loop-header-base-case-3
    run-until-exit-segment-or-hit-loop-header-opener-1-non-myif ;todo: make non-myif versions of rules in other rule sets?
    run-until-exit-segment-or-hit-loop-header-opener-2-non-myif
    run-until-exit-segment-or-hit-loop-header-of-myif-axe
    run-until-exit-segment-or-hit-loop-header-of-myif-axe-lift

    get-pc-designator-from-state
    get-pc-designator-from-frame
    make-pc-designator-constant-opener ;since we have to check whether the result is among the loop headers
    pc-designator-pc-constant-opener
    step-state-with-pc-designator-stack-of-myif
    step-state-with-pc-designator-stack-becomes-step-axe
    step-state-with-pc-designator-stack-does-nothing-axe
    pc-designator-stack-of-state
    get-pc-designator-stack-from-call-stack-of-push-frame
    equal-of-cons-and-cons-constants

    ;; rules for comparing stack heights and lengths of pc designator lists:
    not-equal-of-cons-and-cons-when-lens-differ
    equal-of-same-cancel-3
    acl2-numberp-of-len
    len-of-get-pc-designator-stack-from-call-stack
    ;len-of-pop-frame
    not-equal-of-zero-and-call-stack-size-<-of-call-stack-size ;not-empty-call-stackp-when-<-of-call-stack-size
    right-cancellation-for-+

    jvm::step-always-open))

(ensure-rules-known (run-until-exit-segment-or-hit-loop-header-rules-smart))

;; These are for when we are unrolling nested loops:
(defun run-until-exit-segment-rules ()
  '(run-until-exit-segment-opener-1
    run-until-exit-segment-opener-2
    run-until-exit-segment-base-case-1
    run-until-exit-segment-base-case-2
    run-until-exit-segment-of-myif))

(defun lifter-rules ()
  (append
   (first-loop-top-rules)
   (sbvlt-rules)
   (type-rules2)
   '(acl2-numberp-of-logext

    ;get-pc-designator-from-state
    ;; MEMBER-BECOMES-MEMBER-EQUAL
    <-of-+-cancel-1-2 ;add
    equal-of-same-cancel-1
    equal-of-same-cancel-2
    equal-of-same-cancel-3
    equal-of-same-cancel-4

    LOGEXT-OF-BVCHOP-SMALLER-BETTER
    thread-TOP-FRAME-of-MYIF
    ;;G-DIFF-S ;use a safe version?

    myif-of-myif-of-myif-same-tests ;Wed Apr 29 16:01:54 2015
    myif-of-myif-of-boolor-same ;Mon Jul  6 20:03:23 2015
    myif-of-myif-of-boolor-same2 ;Mon Jul  6 20:05:11 2015

    myif-of-myif-of-myif-same-1 ;Mon Jul  6 20:18:24 2015
    )))

(ensure-rules-known (lifter-rules))

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;; ;returns (mv result state)
;; ;seems like overkill...
;; (defun dag-equal-term (dag term state)
;;   (declare (xargs :guard (pseudo-termp term)
;;                   :mode :program
;;                   :stobjs (state)
;;                   :verify-guards nil)) ;add a guard about dag
;;   (mv-let (simplified-equality-dag state)
;; ;call simplify-dag or something (like a quick version)?
;;     (simplify-with-rule-sets (compose-term-and-dag `(equal ,term x) 'x dag)
;;                              (list (cons :rules (make-axe-rules '(equal-same) (w state))))
;;                              (binary-* '2 (len dag))
;;                              'NIL
;;                              'NIL
;;                              'NIL
;;                              'NIL
;;                              'nil ;priorities
;;                              'nil ;interpreted-function-alist
;;                              'nil ;monitored-runes
;;                              t
;;                              nil ;memoization
;;                              nil ;use-internal-contextsp
;;                              nil nil nil nil t
;;                              'dag-equal-term
;;                              nil
;;                              state
;;                              )
;;     (mv (equal simplified-equality-dag ''t)
;;         state)))

(defun make-alist-by-seconds (pairs alist)
  (if (endp pairs)
      alist
    (let* ((pair (car pairs))
           (second (second pair))
           (current-set (lookup-equal second alist))
           (new-set (cons (first pair) current-set))
           (new-alist (acons second new-set alist)))
      (make-alist-by-seconds (cdr pairs) new-alist))))

;returns a list of lists of addresses
(defun separate-pairs-by-class-name-and-field-name (pairs)
  (strip-cdrs (make-alist-by-seconds pairs nil)))

;fixme make a compose-term-and-dags?
;(defun compose-term-and-dags (term alist)

;; Returns (mv erp dag).
(defun negate-dag (dag)
  (compose-term-and-dag '(not x) 'x dag))

;; Returns (mv erp dag).
(defun make-disequality-dag (dag1 dag2)
  (mv-let (erp dag)
    (make-equality-dag dag1 dag2)
    (if erp
        (mv erp nil)
      (negate-dag dag))))

;returns (mv erp res state)
(defun ads-dont-aliasp (ad1 ad2 assumptions rule-alist state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((- (cw "(Proving that ads ~x0 and ~x1 don't alias.~%" ad1 ad2))
       ((mv erp disequality-dag) (make-disequality-dag ad1 ad2))
       ((when erp) (mv erp nil state))
       ((mv erp result state)
        (simp-dag disequality-dag
                  :rule-alist rule-alist
                  :assumptions assumptions
                  :check-inputs nil))
       ((when erp) (mv erp nil state)))
    (if (equal result *t*)
        (progn$ (cw "Proved that they don't alias.)")
                (mv (erp-nil) t state))
      (progn$ (cw "ERROR: Failed to prove that addresses ~x0 and ~x1 don't alias. Result DAG:~%" ad1 ad2)
              (print-list result)
              (cw "Assumptions:~%")
              (print-list assumptions)
;              (cw ")")
              (hard-error 'ads-dont-aliasp "Failed alias check (see above)." nil)
              (mv (erp-t) nil state)))))

;returns (mv erp res state)
(defun ad-doesnt-alias-anyp (ad ads assumptions rule-alist state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp ads)
      (mv (erp-nil) t state)
    (mv-let (erp result state)
      (ads-dont-aliasp ad (car ads) assumptions rule-alist state)
      (if erp
          (mv erp nil state)
        (mv-let (erp result2 state)
          (ad-doesnt-alias-anyp ad (cdr ads) assumptions rule-alist state)
          (mv erp
              (and result result2)
              state))))))

;really this takes a list, not a set
;returns (mv erp res state)
(defun no-aliases-in-setp (set-of-ads assumptions rule-alist state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp set-of-ads)
      (mv (erp-nil) t state)
    (mv-let (erp result state)
      (ad-doesnt-alias-anyp (car set-of-ads) (cdr set-of-ads) assumptions rule-alist state)
      (if erp
          (mv erp nil state)
        (mv-let (erp result2 state)
          (no-aliases-in-setp (cdr set-of-ads) assumptions rule-alist state)
          (mv erp (and result result2) state))))))

;returns (mv erp res state)
(defun no-aliases-in-setsp (sets-of-ads assumptions rule-alist state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp sets-of-ads)
      (mv (erp-nil) t state)
    (mv-let (erp result state)
      (no-aliases-in-setp (car sets-of-ads) assumptions rule-alist state)
      (if erp
          (mv erp nil state)
        (mv-let (erp result2 state)
          (no-aliases-in-setsp (cdr sets-of-ads) assumptions rule-alist state)
          (mv erp (and result result2) state))))))

;; Returns (mv erp res state).
;check for possible aliases between the fields indicated by the heap-pairs (each field will be a different loop param)
;first group addresses by class-name-field-name pair (only need to check aliases if the field names are the same)
;then for each set of addresses, try to prove each pair distinct - TTODO: might need additional invariants for this?
;each pair is of the form (list address-dag class-and-field-name)
(defun no-aliasesp (heap-pairs assumptions state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (no-duplicatesp-equal heap-pairs)
      (no-aliases-in-setsp (separate-pairs-by-class-name-and-field-name heap-pairs) assumptions
                           (make-rule-alist! (append ;(new-ad-rules) drop
                                             (amazing-rules-spec-and-dag)
                                             (map-rules)
                                             ;; (jvm-semantics-rules)
                                             (jvm-simplification-rules))
                                            (w state))
                           state)
    (mv (erp-t) (hard-error 'no-aliases "redundant heap updates found - we don't handle that yet" nil) state)))

;; Returns (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;check this over
(defun process-replacement-alist (replacement-alist original-dag-len translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  (if (endp replacement-alist)
      (mv (erp-nil) translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (b* ((entry (car replacement-alist))
         (dag (car entry))
         (term (cdr entry))
         (top-nodenum (top-nodenum dag))
         ((mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (merge-nodes-into-dag-array (reverse dag) ;fixme what about embedded dags?
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                      (make-empty-array 'renaming-array (len dag))))
         ((when erp) (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         (renamed-node (aref1 'renaming-array renaming-array top-nodenum))
         )
      (if (< renamed-node original-dag-len)
          ;;the subdag is present, so merge in the term and do (aset1 'translation-array translation-array nodenum-of-dag nodenum-of-term);
          (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (merge-tree-into-dag-array term nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                       nil ;interpreted-function-alist fixme
                                       )
            (if erp
                (mv erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
              (process-replacement-alist (rest replacement-alist)
                                         original-dag-len
                                         (aset1 'translation-array translation-array renamed-node nodenum-or-quotep)
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
;the subdag wasn't present, so skip it:
        (process-replacement-alist (rest replacement-alist)
                                   original-dag-len
                                   translation-array
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

;this should have dag in the name?
;; Returns (mv erp dag-lst).
;check this over
(defun perform-replacements (dag
                             replacement-alist ;maps subdags (may have different nodenums from dag itself! but i can't other things (like a/c functions? cnt differ) ) to the terms they should be replaced with (any dag/term pair whose subdag doesn't appear in dag is ignored...
                             )
;  (declare (xargs :mode :program))
  (if (quotep dag)
      (mv (erp-nil) dag)
    ;;dag is a dag-lst:
    (let* ((dag-len (len dag))
           (dag-array (make-into-array 'dag-array dag)) ;okay to reuse the name?
           )
      (mv-let (dag-parent-array dag-constant-alist dag-variable-alist)
        (make-dag-indices 'dag-array dag-array 'dag-parent-array dag-len)
        (let* ((top-nodenum (top-nodenum dag))
               (translation-array (make-empty-array 'translation-array dag-len)))
          ;;populate translation-array with entries for the subdags that will be replaced:
          (mv-let (erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (process-replacement-alist replacement-alist dag-len translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (if erp
                (mv erp nil)
              (mv-let (erp translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (rebuild-nodes (list top-nodenum) ;initial worklist
                               translation-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                (declare (ignore dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                (if erp
                    (mv erp nil)
                  (mv (erp-nil)
                      (drop-non-supporters-array 'dag-array dag-array
                                                 (aref1 'translation-array translation-array top-nodenum)
                                                 nil))))))))))
  ;; ;call simplify-dag or something (like a quick version)?
  ;;   (simplify-with-rule-sets dag
  ;;                    (list (cons :rules nil)) ;one rule set with no rules in it
  ;;                    (* 2 (len dag))
  ;;                    nil
  ;;                    replacement-alist
  ;;                    'nil
  ;;                    'nil
  ;;                    nil
  ;;                    nil
  ;;                    'nil ;monitored-runes
  ;;                    t
  ;;                    nil ;memoization
  ;;                    nil ;use-internal-contextsp
  ;;                    nil nil nil nil t
  ;;                    state
  ;;                    )
  )

;; Returns (mv erp res).
;more efficient way to do this?
(defun perform-replacements-on-cdrs (alist replacement-alist)
  (if (endp alist)
      (mv (erp-nil) nil)
    (b* ((entry (car alist))
         (key (car entry))
         (dag (cdr entry))
         ((mv erp res)
          (perform-replacements dag replacement-alist))
         ((when erp) (mv erp nil))
         ((mv erp cdr-res)
          (perform-replacements-on-cdrs (cdr alist) replacement-alist))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (acons key res cdr-res)))))

;; (defun dag-to-term-list (dags)
;;   (if (endp dags)
;;       nil
;;     (cons (dag-to-term (car dags))
;;           (dag-to-term-list (cdr dags)))))

;; (defun get-param-terms (nums)
;;   (if (endp nums)
;;       nil
;;     (cons `(nth ',(car nums) params)
;;           (get-param-terms (cdr nums)))))


;fixme consider processing local slots in the opposite order so local nums increase along with param nums
;;returns (mv state-update-dag param-new-val-alist param-initial-val-alist replacement-equalities param-count)
;walk through the locals
;for each one that is changed, make a parameter for it, pair that param num with the dag for the updated value of the local
;and make an equality that will replace an access of the local with an access of the param
;the cdrs of param-initial-val-alist (here and elsewhere are now dags, not terms)
;; (defun process-locals (locals-count state-update-dag one-rep-dag first-loop-top-dag param-count param-new-val-alist param-initial-val-alist replacement-equalities state-var state)
;;   (declare (xargs :measure (nfix (+ 1 locals-count))))
;;   (if (or (< locals-count 0)
;;           (not (integerp locals-count)))
;;       (mv state-update-dag param-new-val-alist param-initial-val-alist replacement-equalities param-count state)
;;     (mv-let (new-local-dag state)
;;             (quick-simplify-dag (compose-term-and-dag `(get-local ',locals-count s) 's one-rep-dag state)
;;                                 ;;fixme - do this just once?
;;                                 (make-axe-rules (get-local-rules) (w state)))
;;             (let* ((get-local-term `(get-local ',locals-count ,state-var)))
;;               (mv-let (result state)
;;                       (quick-simplify-dag
;;                        (compose-term-and-dag `(equal ,get-local-term xx) 'xx new-local-dag)
;;                        (make-axe-rules (get-local-rules) (w state)))


;;                       (if (equal ''t result)
;;                           (process-locals (+ -1 locals-count)
;;                                           state-update-dag one-rep-dag first-loop-top-dag param-count param-new-val-alist param-initial-val-alist
;;                                           replacement-equalities state-var state)
;;                         (let* ((dummy (cw "Param ~x0 is local ~x1.~%" param-count locals-count))
;;                                (get-local-term `(nth ',locals-count (jvm::locals (jvm::thread-top-frame (th) ,state-var))))
;;                                (initial-value-of-local (quick-simplify-dag ;-print
;;                                                         (compose-term-and-dag get-local-term state-var first-loop-top-dag)
;;                                                         (make-axe-rules (get-local-rules)
;;                                                                      (w state)))))
;;                           (declare (ignore dummy))
;;                           (process-locals (+ -1 locals-count)
;;                                           (compose-term-and-dag
;;                                            `(update-local-in-state ',locals-count (nth ',param-count params) (th) s)
;;                                            's
;;                                            state-update-dag)
;;                                           one-rep-dag
;;                                           first-loop-top-dag
;;                                           (+ 1 param-count) ;we're making a param for this local
;;                                           (acons param-count new-local-dag param-new-val-alist)
;;                                           (acons param-count ;(dag-to-term
;;                                                  initial-value-of-local
;;                                                  ;;)
;;                                                  param-initial-val-alist)
;;                                           (cons `(equal ,get-local-term
;;                                                         (nth ',param-count params))
;;                                                 replacement-equalities)
;;                                           state-var
;;                                           state))))))))

;;returns (mv state-update-dag param-new-val-alist param-initial-val-alist replacement-equalities param-count)
;; (defun process-heap (heap-update-triples
;;                      state-update-dag
;;                      first-loop-top-dag param-count param-new-val-alist param-initial-val-alist replacement-equalities state-var state)
;;   (if (endp heap-update-triples)
;;       (mv state-update-dag param-new-val-alist param-initial-val-alist replacement-equalities param-count)
;;     (let* ((triple (car heap-update-triples))
;;            (ad-dag (first triple))
;;            (ad-term (dag-to-term ad-dag))
;;            (class-name-field-name-pair (second triple)) ;already quoted?
;;            (value-dag (third triple))
;; ;           (value-term (dag-to-term value-dag))
;;            (getfield-term `(get-field ,ad-term ,class-name-field-name-pair (jvm::heap ,state-var)))
;;            (dummy (cw "Param ~x0 is for ~X12.~%" param-count getfield-term nil))
;;            )
;;       (declare (ignore dummy))
;;       (process-heap (cdr heap-update-triples)
;;                     (compose-term-and-dag
;; ;fixme consider adding a take with the old length if
;; ;we are setting the array contents field?  since array
;; ;lengths can't change - otherwise we'd need to prove a
;; ;simple inductive theorem on the loop function in order
;; ;to know the resulting array length -- in general, how
;; ;will we handle exceptions that depend on the results of
;; ;loop functions?  -- now we generate type lemmas, so that handles the array length case, at least

;;                      `(set-field-in-state ,ad-term ,class-name-field-name-pair (nth ',param-count params) s)
;;                      's
;;                      state-update-dag)
;;                     first-loop-top-dag
;;                     (+ 1 param-count)
;;                     (acons param-count value-dag param-new-val-alist) ;or simplify the get-field expression applied to the arbitrary state?
;;                     (acons param-count
;;                            ;(dag-to-term
;;                             (simplify-dag5 (compose-term-and-dag getfield-term state-var first-loop-top-dag)
;;                                                          (append (get-local-rules)
;;                                                                                '(LIST::APPEND-ASSOCIATIVE))
;;                                                                        )
;;                             ;)
;;                            param-initial-val-alist)
;;                     (cons `(equal ,getfield-term (nth ',param-count params))
;;                           replacement-equalities)
;;                     state-var
;;                     state))))


;; ;;returns (mv state-update-dag param-new-val-alist param-initial-val-alist replacement-equalities param-count)
;; (defun process-static-field-updates (static-field-update-pairs
;;                                      state-update-dag
;;                                      first-loop-top-dag param-count param-new-val-alist
;;                                      param-initial-val-alist replacement-equalities state-var state)
;;   (if (endp static-field-update-pairs)
;;       (mv state-update-dag param-new-val-alist param-initial-val-alist replacement-equalities param-count)
;;     (let* ((pair (car static-field-update-pairs))
;;            (class-name-field-name-pair (first pair)) ;already quoted?
;;            (value-dag (second pair))
;;            (class-name (car class-name-field-name-pair))
;;            (field-name (cdr class-name-field-name-pair))
;;            (get-static-field-term `(jvm::get-static-field ,class-name ,field-name s))
;;            (dummy (cw "Param ~x0 is local ~X12.~%" param-count get-static-field-term nil))
;;            )
;;       (declare (ignore dummy))
;;       (process-static-field-updates (cdr static-field-update-pairs)
;;                                     (compose-term-and-dag
;;                                      `(jvm::setstaticfield ,class-name ,field-name (nth ',param-count params) s)
;;                                      's
;;                                      state-update-dag)
;;                                     first-loop-top-dag
;;                                     (+ 1 param-count)
;;                                     ;;or simplify the get-field expression applied to the arbitrary state???
;;                                     (acons param-count value-dag param-new-val-alist)
;;                                     (acons param-count
;;                                            ;(dag-to-term
;;                                             (simplify-dag (compose-term-and-dag get-static-field-term
;;                                                                                                 's
;;                                                                                                 first-loop-top-dag)
;;                                                                           (make-axe-rules (append
;;                                                                                         (get-local-rules)
;;                                                                                         '(LIST::APPEND-ASSOCIATIVE))
;;                                                                                        (w state)))
;;                                             ;)
;;                                            param-initial-val-alist)
;;                                     (cons `(equal (jvm::get-static-field ,class-name ,field-name (JVM::STATIC-FIELD-MAP ,state-var))
;;                                                   (nth ',param-count params))
;;                                           replacement-equalities)
;;                                     state-var state))))

;; fixme what about duplicate keys in alist? - huh?

;fixme - what is missing?

(defun jvm-destructor-fns ()
  '(NTH-NEW-AD ;new
    new-ad ;new

    len ;trying..
    get-field
    nth ;drop?
    jvm::nth-local
    ;;car and cdr?
;    bv-array-read ;removed Wed Aug 18 19:55:45 2010 (so that we make the whol array into a variable rather than each component)

    JVM::THREAD-TABLE
    JVM::HEAP
    JVM::CLASS-TABLE
    JVM::HEAPREF-TABLE
    JVM::STATIC-FIELD-MAP
    JVM::INITIALIZED-CLASSES

    JVM::thread-top-frame

    JVM::CALL-STACK
    JVM::LOCALS
    JVM::STACK
    JVM::method-info
    jvm::method-synchronizedp
    jvm::POP))

(defun vars-of-all-items (items dag-var-array)
  (if (endp items)
      nil
    (let ((item (car items)))
      (if (quotep item)
          (vars-of-all-items (cdr items) dag-var-array)
        ;otherwise, it's a nodenum:
        (let* ((vars (aref1 'dag-var-array dag-var-array item)))
          (union-eq vars (vars-of-all-items (cdr items) dag-var-array)))))))

(defun make-dag-var-array-aux (rev-dag-lst dag-var-array)
  (if (endp rev-dag-lst)
      dag-var-array
    (let* ((entry (car rev-dag-lst))
           (nodenum (car entry))
           (expr (cdr entry)))
      (if (symbolp expr)
          (make-dag-var-array-aux (cdr rev-dag-lst)
                                  (aset1 'dag-var-array dag-var-array nodenum (list expr)))
        (if (fquotep expr)
            (make-dag-var-array-aux (cdr rev-dag-lst)
                                    (aset1 'dag-var-array dag-var-array nodenum nil)) ;don't bother if it's nil?
          ;;function call
          (make-dag-var-array-aux (cdr rev-dag-lst)
                                  (aset1 'dag-var-array dag-var-array nodenum
                                         (vars-of-all-items (fargs expr) dag-var-array)
                                         )))))))

(defun make-dag-var-array (dag-lst)
  (make-dag-var-array-aux (reverse dag-lst)
                          (make-empty-array 'dag-var-array (len dag-lst))))

;; i think we should never choose a node that is not a destructor...
;think about calls of other generated functions.
;since nth is a destructor, we should replace (nth .. (loop-1-fn ..)) with a new param
;the variables in the dag are si (and any other input vars, such as inputlength) and params
;we must replace subdags so that all mentions of si (and all other variables??) are gone
;fixme - the initial dag to decompile had better not have a variable named params in it!  (Can we use :params for much of this processing?)
;what if we have something like (read param0 (heap si)) ?
;i guess we'd have to make (heap si) the parameter...
;fixme if we have (destructor1 (destructor2 ..)) which term is chosen?  don't we want the inner one, if it is a word or array?
(defun find-nodenum-of-si-dag-to-replace (dag dag-var-array)
  (if (endp dag)
      nil
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (if (and (consp expr)
               (member-eq (ffn-symb expr) (jvm-destructor-fns)))
          (let* ((nodenum (car entry))
                 (vars (aref1 'dag-var-array dag-var-array nodenum)))
;if the subdag depends on anything other than si, like param0, etc. keep looking
;and if the subdag doesn't depend on si, we don't have to handle it
            (if (and (consp vars)
                     (not (member-eq 'params vars))) ;this is not quite right?
                nodenum
              (find-nodenum-of-si-dag-to-replace (cdr dag) dag-var-array)))
        (if (and (symbolp expr)
                 (not (eq expr 'params)))
            (car entry)
          (find-nodenum-of-si-dag-to-replace (cdr dag) dag-var-array))))))

;returns:
;;       (mv dag                      ;rewrite the dag
;;           param-new-val-alist-acc  ;;possibly add some new params
;;           param-initial-val-alist  ;;possibly add some new params
;;           replacement-alist        ;;possibly add some new params
;;           param-count)
;maybe we don't want the largest expression, but rather the largest one that only has destructors?
;we want the smallest state components..

;; (skip -proofs
;;  (defun put-in-si-exprs-for-dag (dag param-new-val-alist-acc param-initial-val-alist replacement-alist param-count state)
;;    (declare (xargs :mode :program))
;;    (if (quote dag) ;new!
;;        (mv dag param-new-val-alist-acc param-initial-val-alist replacement-alist param-count state)
;;      (let* ((dag-var-array (make-dag-var-array dag))
;;             (nodenum (find-nodenum-of-si-dag-to-replace dag dag-var-array))) ;fixme is it possible that this value won't be a word or array?
;;        (if (not nodenum) ;;we didn't find a subdag that depends on only si
;;            (mv dag param-new-val-alist-acc param-initial-val-alist replacement-alist param-count state)
;;          (let ( ;(expr (lookup nodenum dag))
;;                )
;;            (let* ((si-dag (get-subdag nodenum dag))
;;                   (dummy nil ;(cw "Si-expr dag:~% ~X01~%" si-dag nil)
;;                          )
;;                   (si-term (dag-to-term si-dag)) ;would be nice to be able to give assumptions which mention part of the dag
;;                   ;;see if this term has already been given a param number
;;                   (match (lookup-equal si-term replacement-alist)) ;do less if there is a match?
;;                   (dummy2 (if (not match) (cw "Param ~x0 is ~X12.~%" param-count si-term nil) nil))
;;                   (param-term `(nth ',param-count params))
;;                   (new-term (if match match param-term))
;;                   (equality `(equal ,si-term ,new-term)))
;;              (declare (ignore dummy dummy2))
;;              ;;inefficient?:
;;              (mv-let (dag state)
;;                      (simplify-with-rule-sets dag
;;                                       (list (cons :rules 'NIL))
;;                                       (* 2 (len dag))
;;                                       nil
;;                                       (list equality)
;;                                       'NIL
;;                                       'NIL
;;                                       nil
;;                                       nil
;;                                       'nil ;monitored-runes
;;                                       t
;;                                       nil ;memoization
;;                                       nil ;use-internal-contextsp
;;                                       nil nil nil nil t state)

;;                      (if match ;this si-expression has already been given a parameter name
;;                          (put-in-si-exprs-for-dag dag param-new-val-alist-acc param-initial-val-alist replacement-alist param-count state)
;;                        ;;we are replacing a new si-expression and adding a new param for it:
;;                        (put-in-si-exprs-for-dag dag
;;                                                 (acons param-count (dagify-term param-term) param-new-val-alist-acc) ;fixme call a dagify-term that inlines constants...
;;                                                 (acons param-count si-dag ;si-term
;;                                                        param-initial-val-alist) ;is this wrong?
;;                                                 (acons si-term new-term replacement-alist)
;;                                                 (+ 1 param-count) state))))))))))

;; ;fixme make sure all vars except params got replaced!
;; ;;param-new-val-alist-orig maps parameter numbers to their new expressions, in terms of other params and si
;; ;;we need to get rid of the expressions which mention si and make them into parameters of the function too
;; ;;we add params for the largest expressions that mention only si (fixme strip of any destructors?)
;; ;;returns (mv param-new-val-alist param-initial-val-alist)
;; ;there should be no dups in the alists
;; ;in which alist are params paired with terms and in which with dags?
;; (defun process-si-exprs (param-new-val-alist-orig param-new-val-alist-acc param-initial-val-alist replacement-alist param-count)
;;   (if (endp param-new-val-alist-orig)
;;       (mv param-new-val-alist-acc param-initial-val-alist)
;;     (let* ((entry (car param-new-val-alist-orig))
;;            (param-num (car entry))
;;            (defining-dag (cdr entry))
;;            )
;;       (mv-let (dag                      ;rewrite the dag
;;                param-new-val-alist-acc  ;;possibly add some new params
;;                param-initial-val-alist  ;;possibly add some new params
;;                replacement-alist        ;;possibly add some new params
;;                param-count)
;;               (put-in-si-exprs-for-dag defining-dag param-new-val-alist-acc param-initial-val-alist replacement-alist param-count)
;;               (process-si-exprs (cdr param-new-val-alist-orig)
;;                                 (acons param-num dag param-new-val-alist-acc)
;;                                 param-initial-val-alist
;;                                 replacement-alist
;;                                 param-count)))))

;(local (in-theory (enable natp)))

;could be called just lookup-ints?
(defun lookup-params (current max alist)
  (declare (xargs :measure (nfix (+ 1 (- max current)))))
  (if (or (< max current)
          (not (natp max))
          (not (natp current)))
      nil
    (acons current
           (lookup current alist)
           (lookup-params (+ 1 current) max alist))))

;; (defun lookup-ints (current max alist)
;;   (declare (xargs :measure (nfix (+ 1 (- max current)))))
;;   (if (or (not (integerp current))
;;           (not (integerp max))
;;           (> current max))
;;       nil
;;     (cons (lookup current alist)
;;           (lookup-ints (+ 1 current) max alist))))

(defun all-pseudo-dagp-or-myquotep (dags)
  (declare (xargs :guard t))
  (if (atom dags)
      t
    (and (or (pseudo-dagp (first dags))
             (myquotep (first dags)))
         (all-pseudo-dagp-or-myquotep (rest dags)))))

;returns (mv nodenum-or-quotep dag)
;fixme deprecate or improve?
;call get-subdag?
;deprecate?
;preserves nodes in dag unless it is a quotep
(defun add-to-dag-allows-constants (expr dag)
  (declare (xargs :guard (and (dag-function-call-exprp expr)
                              (or (myquotep dag)
                                  (weak-dagp-aux dag))
                              (implies (myquotep dag)
                                       (all-myquotep (dargs expr))))))
  (if (quotep dag) ;just ignore it...
      (add-to-dag expr nil)
    (add-to-dag expr dag)))

;(skip-proofs (verify-guards get-subdag))

;fixme think this over
;fixme can the output of this have nodes that are quoted constants?
;returns a dag-lst
;improve?
;TODO: inefficient?
;; Returns (mv erp res).
(defun make-cons-nest-dag (dags)
  (declare (xargs :guard (and (true-listp dags)
                              (all-pseudo-dagp-or-myquotep dags))
                  :verify-guards nil ;todo
                  ))
  (if (endp dags)
      (mv (erp-nil) ''nil) ;(dagify-term ''nil)
    (b* (((mv erp rest-dag) (make-cons-nest-dag (cdr dags)))
         ((when erp) (mv erp nil))
         (car-dag (car dags))
         ((mv erp car-nodenum-or-quotep merged-dag)
          (merge-dag-into-dag-quick ;merge-dags-allows-constants2
           car-dag rest-dag))
         ((when erp) (mv erp nil))
         ((mv nodenum-or-quotep dag)
          ;; todo: call a blessed dag builder here:
          (add-to-dag-allows-constants `(cons ,car-nodenum-or-quotep ,(if (quotep rest-dag) rest-dag (top-nodenum rest-dag)))
                                       merged-dag)))
      (mv (erp-nil)
          (get-subdag nodenum-or-quotep dag)))))

;; ;; state-update-dag mentions params, so now we need to bind params
;; ;exit-pc is already quoted
;; (defun make-new-state-dag (state-update-dag exit-pc param-initial-val-alist fn-name)
;;   (let* ((state-update-dag (compose-term-and-dag `(set-pc ,exit-pc s) 's state-update-dag))
;;          (num-params (len param-initial-val-alist)) ;hope there are no dups... ;can this be 0?
;;          ;;inefficient:
;;          (initial-value-dags (lookup-ints 0 (+ -1 num-params) param-initial-val-alist))
;;          (initial-params (make-cons-nest-dag initial-value-dags))
;;          (function-call-dag (compose-term-and-dag `(,fn-name params) 'params initial-params)) ;slow?
;; ;         (function-call-dag (dagify-term function-call-term))
;;          (final-dag (compose-dags state-update-dag 'params function-call-dag))
;;          )
;;   final-dag))


;; ;this is used to prove the invariant in both the initial state and the one-arbitrary-rep state
;; ;each conjunct should be a predicate over the variable s (and maybe si)
;; ;state-dag should be simplified, but this wastefully simplifies it again:
;; (defun prove-invariant-conjuncts (conjuncts state-dag assumptions extra-rules prove-invar-rules state-var state)
;;   (if (endp conjuncts)
;;       t
;;     (let* ((conjunct-term (car conjuncts))
;;            (dummy (cw "Proving invariant conjunct ~x0~%" conjunct-term))
;;            (conjunct-dag (dagify-term conjunct-term)) ;combine with the compose?
;;            (simplified-conjunct (simplify-dag (compose-dags conjunct-dag state-var state-dag)
;;                                                   ;;these rules may be slow:
;;                                                   (append extra-rules
;;                                                           (make-axe-rules prove-invar-rules (w state)))
;;                                                   :assumptions assumptions ;hope this is okay
;;                                                   )))
;;       (declare (ignore dummy))
;;       (if (equal *t* simplified-conjunct)
;;           (prove-invariant-conjuncts (cdr conjuncts) state-dag assumptions extra-rules prove-invar-rules state-var state)
;;         (prog2$ (cw "Failed to prove the invariant conjunct: ~x0~% Simplified form: ~x2~%  Assumptions: ~x3~%"
;;                     conjunct-term state-dag simplified-conjunct assumptions)
;;                 (hard-error 'prove-invariant-conjuncts "!! failed to prove the conjunct above!!" nil))))))

;; ;fixme, we should probably prove these!
;; ;change this to generate theorem bodies and then change them into rules and spit them out as theorems
;; ;fixme handle the -base function... - we no longer use those?
;; ;ffixme think more about how to make sure this is true... - what about the base case?
;; ;fixme change this to handle tuples
;; (defun make-type-rule (param-number tag dag)
;;   (if (consp dag)
;;       (let* ((entry (car dag))
;;              (expr (cdr entry)))
;;         (if (and (consp expr)
;;                  (eq 'bv-array-write (ffn-symb expr)))
;;             (let ((len (dag-to-term (get-subdag (second (fargs expr)) dag))))
;;               (make-axe-rule-safe `(len (nth ',param-number (,(mypackn (list tag)) params)))
;;                              ;;we used to require this to be a quote...
;;                              len
;;                              `(:rewrite ,(mypackn (list 'generated- tag '-type-theorem (nat-to-string param-number))))
;;                              ;;sometimes this may be vacuously true:
;;                              `((equal (len (nth ',param-number params))
;;                                       ,len))
;;                              nil))
;;           (if (and (consp expr)
;;                    (eq 'bvplus (ffn-symb expr))) ;ffixme gen to any bv op
;;               (let ((width (dag-to-term (get-subdag (first (fargs expr)) dag))))
;;                 (make-axe-rule-safe `(unsigned-byte-p ,width (nth ',param-number (,(mypackn (list tag)) params)))
;;                                *t*
;;                                `(:rewrite ,(mypackn (list 'generated- tag '-type-theorem (nat-to-string param-number))))
;;                                ;;sometimes this may be vacuously true:
;;                                `((unsigned-byte-p ,width (nth ',param-number params)))
;;                                nil))
;;             nil)))
;;     nil))

;; ;i guess these are the types of the return values
;; (defun make-type-rules (defining-dags param-number tag)
;;   (declare (xargs :measure (len defining-dags)))
;;   (if (endp defining-dags)
;;       nil
;;     (let* ((dag (car defining-dags))
;;            (rule (make-type-rule param-number tag dag)))
;;       (if rule
;;           (cons rule (make-type-rules (cdr defining-dags) (+ 1 param-number) tag))
;;         (make-type-rules (cdr defining-dags) (+ 1 param-number) tag)))))

;TODO: should check that known functions in the assumptions have the right arity. do we trans them?

;; (defun find-nodenum-whose-class-is-needed (arbitrary-iteration-dag)
;;   (if (endp arbitrary-iteration-dag)
;;       nil
;;     (let* ((entry (car arbitrary-iteration-dag))
;;            (expr (cdr entry)))
;;       (if (and (consp expr)
;;                (eq 'GET-FIELD (ffn-symb expr))
;;                (equal ''(:SPECIAL-DATA . :CLASS) (second (fargs expr)))
;;                (dag-equal-term (get-subdag (third (fargs expr)) arbitrary-iteration-dag)
;;                                '(JVM::HEAP s)))
;;           (first (fargs expr))
;;         (find-nodenum-whose-class-is-needed (cdr arbitrary-iteration-dag))))))

;; (skip -proofs
;; ;returns (mv new-invariant-conjuncts arbitrary-iteration-dag)
;;  (defun run-arbitrary-loop-iteration-aux (arbitrary-iteration-dag state-dag-at-loop-header loop-pcs extra-rules
;;                                                                   arbitrary-iteration-assumptions invariant-conjuncts
;;                                                                   new-invariant-conjuncts-acc state)
;;    (let* ((dag-fns (dag-fns arbitrary-iteration-dag)))
;;      (if (not (member-eq 'run-one-loop-iteration2 dag-fns))
;;          ;;we've executed the whole loop iteration
;;          (mv new-invariant-conjuncts-acc arbitrary-iteration-dag)
;;        ;;we are not done, so try to find an object whose class we can make an assertion about (fixme why else might we fail to execute the whole loop?)
;;        (let* ((nodenum-whose-class-is-needed (find-nodenum-whose-class-is-needed arbitrary-iteration-dag)))
;;          (if (not nodenum-whose-class-is-needed)
;;              (mv nil
;;                  (hard-error 'run-arbitrary-loop-iteration-aux "We can't execute the loop, but we can't find an object whose class we need to know either. DAG: ~X01~%"
;;                              (acons #\0 arbitrary-iteration-dag (acons #\1 nil nil))
;;                              ))
;;            (let*  ((dummy (cw "Need to make an assertion about the class of node ~x0.~%" nodenum-whose-class-is-needed))
;;                    (subdag-for-node (check-dag-vars '(s) (get-subdag nodenum-whose-class-is-needed arbitrary-iteration-dag)))
;;                    (term-for-node (dag-to-term subdag-for-node))
;;                    (class-of-node (check-quotep (simplify-dag
;;                                                  (compose-term-and-dag `(get-class ,term-for-node (jvm::heap s)) 's state-dag-at-loop-header)
;;                                                  (make-axe-rules (get-local-rules) (w state)) ;fixme, these get rid of error states!
;;                                                  ;; :print :brief
;;                                                  )))
;;                    (new-conjunct `(equal (get-field ,term-for-node '(:special-data . :class) (jvm::heap s))
;;                                          ,class-of-node ;already quoted
;;                                          ))
;;                    (dummy2 (cw "Adding conjunct: ~x0" new-conjunct))
;;                    ;;ffixme - some of these need are about terms that will be simplified by further invariants...
;;                    (new-invariant-conjuncts-acc (cons new-conjunct new-invariant-conjuncts-acc))
;;                    ;;this starts all over from the beginning - should we instead just resume the run?
;;                    (new-arbitrary-iteration-dag
;;                     (prog2$ (cw "Re-executing the arbitrary loop iteration.~%") ;fixme print assumptions and invariant-conjuncts
;;                             (simplify-term
;;                              (one-iteration-term loop-pcs)
;;                              (append extra-rules ;or should this be inside the make-rules?
;;                                      (make-axe-rules (append (arbit-loop-rules)
;;                                                           '((:definition set-pc) ;can we drop some rules?
;;                                                             (:rewrite jvm::jvm-statep-of-make-state)
;;                                                             (:rewrite jvm::make-state-equal-rewrite-2)
;;                                                             (:rewrite jvm-statep-of-run-one-loop-iteration2)
;;                                                             (:rewrite bind-equal-same-rewrite2)
;;                                                             (:rewrite alist-of-thread-table-of-one-loop-iteration)
;;                                                             ))
;;                                                   (w state)))
;;                              ;; :print :brief
;;                              :assumptions (append arbitrary-iteration-assumptions
;;                                                   invariant-conjuncts
;;                                                   new-invariant-conjuncts-acc)))))
;;              (declare (ignore dummy dummy2))
;;              (run-arbitrary-loop-iteration-aux new-arbitrary-iteration-dag
;;                                                state-dag-at-loop-header
;;                                                loop-pcs
;;                                                extra-rules
;;                                                arbitrary-iteration-assumptions
;;                                                invariant-conjuncts
;;                                                new-invariant-conjuncts-acc
;;                                                state))))))))


;; ;;returns (mv new-invariant-conjuncts arbitrary-iteration-dag)
;; ;;this includes all the exception branches:
;; (defun run-arbitrary-loop-iteration (state-dag-at-loop-header loop-pcs extra-rules arbitrary-iteration-assumptions
;;                                                               invariant-conjuncts state)
;;   (let* ( ;;we start by running as far as we can:
;;          (arbitrary-iteration-dag
;;           (prog2$ (cw "Symbolically executing an arbitrary loop iteration.  Running as far as we can.~%") ;fixme print assumptions and invariant-conjuncts
;;                   (simplify-term
;;                    (one-iteration-term loop-pcs)
;;                    (append extra-rules
;;                            (make-axe-rules (append (arbit-loop-rules)
;;                                                 '((:definition set-pc) ;can we drop some rules?
;;                                                   (:rewrite jvm::jvm-statep-of-make-state)
;;                                                   (:rewrite jvm::make-state-equal-rewrite-2)
;;                                                   (:rewrite jvm-statep-of-run-one-loop-iteration2)
;;                                                   (:rewrite bind-equal-same-rewrite2)
;;                                                   (:rewrite alist-of-thread-table-of-one-loop-iteration)
;;                                                   ))
;;                                         (w state)))
;;                    :assumptions (append arbitrary-iteration-assumptions invariant-conjuncts)))))
;;     ;;then we repeatedly generate claims about classes of objects, and run again, if necessary
;;     (run-arbitrary-loop-iteration-aux arbitrary-iteration-dag state-dag-at-loop-header loop-pcs extra-rules arbitrary-iteration-assumptions invariant-conjuncts nil state)))

;; ;would be nice to avoid dags altogether in this...
;; (defun simplify-terms-using-assumptions (terms assumptions)
;;   (if (endp terms)
;;       nil
;;     (cons (dag-to-term (simplify-term (car terms)
;;                                       nil ;no rules
;;                                       :assumptions assumptions
;;                                       :priorities nil))
;;           (simplify-terms-using-assumptions (cdr terms) assumptions))))

;; decompile one loop
;; takes the DAG representing the state at the top of the loop for the first time
;; usually returns (list simplified-new-state-dag defuns-and-theorems rule)
;; simplified-new-state-dag has a recursive function in it for the loop and has advanced past the loop
;;
;fixme - in order to execute one iteration, we need to know about which classes have been initialized - we sort of handle this, but what if a class gets initialized in the first repetition?  would be better to just initialize everything at the start?  that is correct, right?

;; (defun decompile-loop (state-dag-at-loop-header
;;                        loop-pc            ;;loop-class-and-method
;;                        initial-state-hyps ;; these are about si
;;                        loop-top-hyps
;;                        loop-pcs
;;                        locals-count
;;                        tag
;;                        extra-rules ;fixme include in rule-list?
;;                        rule-list
;;                        prove-invar-rules
;;                        generated-defun-names
;;                        state)
;;   (declare (ignore generated-defun-names)
;;            (xargs :verify-guards nil
;;                   :guard (and (pseudo-term-listp initial-state-hyps)
;;                               (pseudo-term-listp loop-top-hyps))))
;;   (let* ((intialized-classes (check-quotep (simplify-dag
;;                                             (compose-term-and-dag '(JVM::initialized-classes s) 's state-dag-at-loop-header)
;;                                             (make-axe-rules (append (get-local-rules)
;;                                                                  ;;add to get-local-rules (and rename to something more generic)
;;                                                                  '((:REWRITE JVM::INITIALIZED-CLASSES-OF-MAKE-STATE)))
;;                                                          (w state)))))
;;          ;;these do need to be checked
;;          (basic-invariant-conjuncts (cons `(equal (alistp (jvm::thread-table s))
;;                                                   't)
;;                                           loop-top-hyps))

;;          (arbitrary-iteration-assumptions
;;           (append initial-state-hyps ;; since these do not mention s, they don't need to be checked after one loop rep
;;                   ;;we say that at least all the classes initialized at the first loop top state
;;                   ;;are initialized at every loop top state
;;                   ;;fixme - eventually run the class initializers first, in case one gets initialized during a loop
;;                   ;; we don't check these later, since classes can't become unitialized:
;;                   (assumptions-that-classes-are-initialized (unquote intialized-classes))))
;;          (dummy (prog2$ (cw "Assumptions:~%") (print-list arbitrary-iteration-assumptions))))
;;     (declare (ignore dummy))

;;     ;;here invariant-conjuncts are things we had to say to get the execution through (hope they turn out to be true!):
;;     (mv-let (invariant-conjuncts-about-classes arbitrary-iteration-dag)
;;             (run-arbitrary-loop-iteration (prog2$ (cw "State at loop header: ~x0~%" state-dag-at-loop-header)
;;                                                   state-dag-at-loop-header)
;;                                           loop-pcs extra-rules arbitrary-iteration-assumptions
;;                                           basic-invariant-conjuncts
;;                                           state)
;;             (let* ((dummy2 (cw "Arbitrary iteration dag: ~x0~%" arbitrary-iteration-dag))
;;                    ;;fixme does the invariant generator itself remove the error states?
;;                    (arbitrary-iteration-no-exceptions-dag
;;                     (prog2$ (cw "Removing error states:~%")
;;                             (simplify-dag
;;                              arbitrary-iteration-dag
;;                              (append extra-rules
;;                                      ;;fixme - whoa - unsound - handle this eventually
;;                                      (make-axe-rules '((:rewrite ignore-error-state-1)
;;                                                     (:rewrite ignore-error-state-2)

;; ;hmm what else should we put in here?
;;                                                     (:rewrite myif-same-branches))
;;                                                   (w state))))))
;;                    (dummy3 (cw "~x0~%" arbitrary-iteration-no-exceptions-dag))
;;                    (top-expr-of-arbitrary-iteration-no-exceptions (cdr (car arbitrary-iteration-no-exceptions-dag))))
;;               (declare (ignore dummy2 dummy3))
;;               ;;FIXME be more flexible here - what about loops with multiple exits?  run them all until the next loop?
;;               ;;we use the dag with no exceptions here, so that there are only a few branches:
;;               (if (not (eq 'myif (ffn-symb top-expr-of-arbitrary-iteration-no-exceptions)))
;;                   (hard-error 'decompile-loop "Expected top expression in the arbitrary loop expression to be a call to myif" nil)
;;                 (let*
;;                     ((test-nodenum (first (fargs top-expr-of-arbitrary-iteration-no-exceptions))) ;either the exit test or its negation
;;                      (then-part-nodenum (second (fargs top-expr-of-arbitrary-iteration-no-exceptions)))
;;                      (else-part-nodenum (third (fargs top-expr-of-arbitrary-iteration-no-exceptions)))
;;                      (then-part-dag (get-subdag then-part-nodenum arbitrary-iteration-no-exceptions-dag))
;;                      ;; this is quoted:
;;                      (then-part-pc (simplify-dag (compose-term-and-dag '(get-pc x) 'x then-part-dag)
;;                                                      *GET-PC-FROM-DAG-AXE-RULE-SET*))
;;                      (else-part-dag (get-subdag else-part-nodenum arbitrary-iteration-no-exceptions-dag))
;;                      ;; this is quoted:
;;                      (else-part-pc (simplify-dag (compose-term-and-dag '(get-pc x) 'x else-part-dag)
;;                                                      *GET-PC-FROM-DAG-AXE-RULE-SET*)))
;;                   (if (not (and (quotep then-part-pc)
;;                                 (quotep else-part-pc)
;;                                 ;;one of the PCs is the loop top:
;;                                 (or (eql (unquote then-part-pc) loop-pc)
;;                                     (eql (unquote else-part-pc) loop-pc))
;;                                 ;;and the other is outside of the loop:
;;                                 (or (not (member (unquote then-part-pc) loop-pcs))
;;                                     (not (member (unquote else-part-pc) loop-pcs)))))
;;                       (hard-error 'decompile-loop "PCs are not as expected: ~x0 ~x1. Loop pc: ~x2.  Loop pcs: ~x3.~%" (acons #\0 then-part-pc (acons #\1 else-part-pc (acons #\2 loop-pc (acons #\3 loop-pcs nil)))))

;;                     ;;Now generate the invariant, for which we need the one-rep-dag (assuming the negation of the termination test):
;;                     (let*
;;                         ((test-dag (get-subdag test-nodenum arbitrary-iteration-no-exceptions-dag))
;;                          (continuation-assumption (if (eql (unquote then-part-pc) loop-pc)
;;                                                       `(equal ,(dag-to-term test-dag) 't)
;;                                                     `(equal ,(dag-to-term test-dag) 'nil)))
;;                          (exit-pc (if (eql (unquote then-part-pc) loop-pc) else-part-pc then-part-pc))
;;                          ;;this does include the error states (I guess so we can generate invariants about the tests of ifs that
;;                          ;;have error state branches):
;;                          (loop-branch-dag (simplify-dag
;;                                            arbitrary-iteration-dag
;;                                            ;;fixme what rules do i want here? all we need to do is elimate the termination branch?
;;                                            (append extra-rules
;;                                                    (make-axe-rules (append '((:rewrite error-state-drop-params)) ;this leaves the if tests but gets rid of the other nodes passed in to the error states (msg and entire states)
;;                                                                         (arbit-loop-rules))
;;                                                                 (w state)))
;;                                            :assumptions (list continuation-assumption)))
;;                          (dummy (cw "one loop rep when we don't exit (can include error states, used to generate invariants): ~x0" loop-branch-dag))
;;                          ;;here we also consider for invariance all expressions that appear in the loop test!
;;                          ;;fixme - should we pass in the conjuncts we have so far??
;;                          ;;or use them to simplify the dag first?
;;                          (main-invariant-conjuncts (find-invariant-conjuncts state-dag-at-loop-header
;;                                                                              loop-branch-dag
;;                                                                              test-dag
;;                                                                              loop-top-hyps
;;                                                                              initial-state-hyps
;;                                                                              state))
;;                          (invariant-conjuncts (append main-invariant-conjuncts
;;                                                       basic-invariant-conjuncts))

;;                          ;;we have to simplify the invars about classes, since
;;                          ;;they may mention terms that other invars will
;;                          ;;simplify:
;;                          (invariant-conjuncts-about-classes (simplify-terms-using-assumptions invariant-conjuncts-about-classes
;;                                                                                               invariant-conjuncts))
;;                          (invariant-conjuncts (append invariant-conjuncts invariant-conjuncts-about-classes))
;;                          (invariant-conjuncts (remove-duplicates-equal invariant-conjuncts))
;;                          (dummy5 (cw "Invariant conjuncts:~%~x0~%" invariant-conjuncts))
;;                          ;;prove the invariant holds at the first iteration
;;                          (invariant-result (prove-invariant-conjuncts invariant-conjuncts
;;                                                                       state-dag-at-loop-header
;;                                                                       initial-state-hyps ;hope this is okay
;;                                                                       extra-rules
;;                                                                       prove-invar-rules
;;                                                                       's
;;                                                                       state))
;;                          )
;;                       (declare (ignore dummy dummy5))
;;                       (if (not invariant-result)
;;                           (hard-error 'decompile-loop "invariant doesn't hold at the start of the first iteration top" nil)
;;                         (prog2$
;;                          (cw "Good. The invariant holds at the start of the first iteration.~%")

;;                          ;; Prove that the invariant holds over an arbitary loop iteration:
;;                          ;; Simplify the one-rep DAG using the invariant
;;                          (let*
;;                              ( ;;we now simplify the continuation-assumption using the invariant, or it may not fire
;;                               ;; fixme make sure this is sound
;;                               (test-dag (simplify-dag
;;                                          test-dag
;;                                          (append extra-rules
;;                                                  (make-axe-rules (runes55) (w state)))
;;                                          :assumptions (cons '(equal (alistp (jvm::thread-table s)) ;fixme drop or move
;;                                                                     't)
;;                                                             (append initial-state-hyps ;; these are about si, which may show up in this?? these may tell us the length of si's arrays
;;                                                                     invariant-conjuncts))))
;; ;can the test-dag ever be huge?
;;                               (continuation-assumption
;;                                (if (eql (unquote then-part-pc) loop-pc)
;;                                    `(equal ,(dag-to-term test-dag) 't)
;;                                  `(equal ,(dag-to-term test-dag) 'nil)))
;;                               (dummy3 (cw "Continuation assumption: ~x0.~%" continuation-assumption))

;;                               ;;first we use the invariant:
;;                               (simplified-arbitrary-iteration-dag
;;                                (simplify-dag
;;                                 ;;this includes the exception branches; we hope that the invariant can eliminate them:
;;                                 arbitrary-iteration-dag
;;                                 nil ;; no rules (fixme add some myif/bvif rules)
;;                                 :assumptions (cons continuation-assumption ;assume we are not terminating - fixme drop this?
;;                                                    (cons '(equal (alistp (jvm::thread-table s)) ;fixme drop or move
;;                                                                  't)
;;                                                          (append initial-state-hyps ;; these are about si, which may show up in this?? these may tell us the length of si's arrays
;;                                                                  invariant-conjuncts)))))
;;                               (dummy7 (cw "simplified arbitrary iteration dag (after using the invariants): ~x0~%"
;;                                           simplified-arbitrary-iteration-dag))

;;                               ;;now remove error states:
;;                               (simplified-arbitrary-iteration-dag
;;                                (simplify-dag
;;                                 ;;this includes the exception branches; we hope that the invariant can eliminate them:
;;                                 arbitrary-iteration-dag
;;                                 (make-axe-rules '((:rewrite ignore-error-state-1)
;;                                                (:rewrite ignore-error-state-2))
;;                                              (w state))
;;                                 :assumptions (cons continuation-assumption ;assume we are not terminating - fixme drop this?
;;                                                    (cons '(equal (alistp (jvm::thread-table s)) ;fixme drop or move
;;                                                                  't)
;;                                                          (append initial-state-hyps ;; these are about si, which may show up in this?? these may tell us the length of si's arrays
;;                                                                  invariant-conjuncts)))))
;;                               (dummy8 (cw "simplified arbitrary iteration dag (after getting rid of error states): ~x0~%"
;;                                           simplified-arbitrary-iteration-dag))
;;                               (simplified-arbitrary-iteration-dag
;;                                ;;this has been slow??:
;;                                (simplify-dag
;;                                 simplified-arbitrary-iteration-dag ;;this includes the exception branches; we hope that the invariant can eliminate them:
;;                                 (append extra-rules
;; ;fixme, actually we cheat and remove the error states:
;; ;i wonder if we waste tons of time simplifying all the states that are arguments to the error state - we should first eliminate them whenever possible using the invariant (or at least by cheating)
;; ;we almost want top-down reasoning
;;                                         (make-axe-rules rule-list
;;                                                      (w state)))
;;                                 ;;:max-dag-size 10000000 ;drop?
;;                                 :assumptions (cons continuation-assumption ;assume we are not terminating - fixme drop this?
;;                                                    (cons '(equal (alistp (jvm::thread-table s)) ;fixme drop or move
;;                                                                  't)
;;                                                          (append initial-state-hyps ;; these are about si, which may show up in this?? these may tell us the length of si's arrays
;;                                                                  invariant-conjuncts)))))
;;                               (dummy4
;;                                (cw
;;                                 "simplified arbitrary iteration dag (after using invars, dropping errors, and simplifying): ~x0~%"
;;                                 simplified-arbitrary-iteration-dag))
;;                               (dummy5 (cw "Proving that the invariant holds on the simplified arbitrary iteration..."))
;;                               ;; Now prove the invariant on the simplified arbitrary iteration
;;                               (arbit-invariant-result
;;                                (prove-invariant-conjuncts invariant-conjuncts
;;                                                           simplified-arbitrary-iteration-dag
;;                                                           ;;assumptions:
;;                                                           (append
;;                                                            initial-state-hyps
;;                                                            (cons continuation-assumption ;assume we are not terminating
;;                                                                  (cons '(equal (alistp (jvm::thread-table s)) ;fixme drop or move
;;                                                                                't)
;;                                                                        invariant-conjuncts)))
;;                                                           extra-rules
;;                                                           prove-invar-rules
;;                                                           's
;;                                                           state))
;;                               (dummy9 (if arbit-invariant-result
;;                                           (cw "Good. The invariant holds after an arbitary iteration.~%")
;;                                         nil)))
;;                            (declare (ignore dummy3 dummy4 dummy7 dummy8 dummy5 dummy9))

;;                            (if (not arbit-invariant-result)
;;                                (hard-error 'decompile-loop
;;                                            "Failed to prove that the invariant holds for and arbitrary loop iteration!:" nil)

;;                              ;;now we start building the function that corresponds to the loop
;;                              ;;each state component changed by the loop becomes a parameter to the function
;;                              (let*
;;                                  ((static-field-map-dag (simplify-dag
;;                                                          ;;fixme what about ifs?
;;                                                          (compose-term-and-dag '(jvm::static-field-map s)
;;                                                                                's simplified-arbitrary-iteration-dag)
;;                                                          (make-axe-rules (get-local-rules)
;;                                                                       (w state))))
;;                                   (static-field-update-pairs (get-static-field-update-pairs static-field-map-dag 's 'si))

;; ;do we have to make this, or can we pass the main dag and a nodenum?
;; ;fffixme - what do we do if this has a myif for a heap subterm?
;;                                   (heap-dag (simplify-dag (compose-term-and-dag '(heap s)
;;                                                                                     's simplified-arbitrary-iteration-dag)
;;                                                               (make-axe-rules (append (get-local-rules)
;;                                                                                    '((:rewrite jvm::myif-of-set-field-1-strong)
;;                                                                                      (:rewrite jvm::myif-of-set-field-2-strong)))
;;                                                                            (w state))))
;;                                   ;;this checks that the addresses only depend on si (not s):
;;                                   ;; fixme think more about what to do if the heap doesn't change in the loop (we'll detect an invariant for the heap in terms of si)
;;                                   ;; maybe things work now
;;                                   (heap-update-triples (get-heap-update-triples heap-dag 's 'si))
;;                                   (heap-update-pairs (get-heap-update-pairs-from-triples heap-update-triples)))
;;                                (if (not (no-aliases heap-update-pairs state))
;;                                    (hard-error 'decompile-loop "Couldn't show lack of heap aliasing (pairs: ~X0)." (acons #\0 heap-update-pairs nil))
;;                                  (mv-let
;;                                   (state-update-dag param-new-val-alist param-initial-val-alist replacement-equalities param-count)
;;                                   (process-locals (prog2$ (cw "Processing locals...~%") locals-count)
;;                                                   state-dag-at-loop-header simplified-arbitrary-iteration-dag
;;                                                   state-dag-at-loop-header 0 nil nil nil 's state)
;;                                   (mv-let
;;                                    (state-update-dag param-new-val-alist param-initial-val-alist replacement-equalities
;;                                                      param-count)
;;                                    (process-heap (prog2$ (cw "Processing heap...~%") heap-update-triples)
;;                                                  state-update-dag
;;                                                  state-dag-at-loop-header param-count param-new-val-alist
;;                                                  param-initial-val-alist replacement-equalities 's state)
;; ;fixme -think about the case where an address is itself a call to get-field - we might need to rewrite multiple times?? - not an issue since ads can't be functions of s?  what if an ad is a function of a get-field of si?
;;                                    (mv-let
;;                                     (state-update-dag param-new-val-alist param-initial-val-alist
;;                                                       replacement-equalities param-count)
;;                                     (process-static-field-updates (prog2$ (cw "Processing static fields...~%") static-field-update-pairs)
;;                                                                   state-update-dag
;;                                                                   state-dag-at-loop-header param-count param-new-val-alist
;;                                                                   param-initial-val-alist replacement-equalities 's state)

;;                                     (let* (
;;                                            ;;param-new-val-alist still needs to be fixed up to use the new variable names in the defining dags
;;                                            ;;ffixme where are the state components that are read from in the loop but not modified handled? are they always si-exprs (and so handled below?)
;;                                            (param-new-val-alist (rewrite-cdrs-with-assumptions param-new-val-alist replacement-equalities))

;;                                            ;; i think at this point all mentions to s may be gone (each state component of s is unchanged and turned into an expression over si or is written to by the loop and handled above?) fixme think about this - if it's true, add a check for remaining s's here?
;;                                            (dummy (cw "Param new value alist: ~X01" param-new-val-alist nil))
;;                                            )
;;                                       (declare (ignore dummy))
;;                                       (mv-let
;;                                        (param-new-val-alist param-initial-val-alist)
;;                                        (process-si-exprs (prog2$ (cw "Processing si exprs.~%")
;;                                                                  param-new-val-alist)
;;                                                          nil
;;                                                          param-initial-val-alist
;;                                                          nil
;;                                                          param-count)
;;                                        (let* ((dummy100 (cw "Param-new-value-alist after si-expr fixup: ~X01"
;;                                                             param-new-val-alist nil))
;;                                               (max-param (maxelem (strip-cars param-new-val-alist)))
;;                                               (param-new-val-alist (lookup-params 0 max-param param-new-val-alist)) ;sorts and remove dups
;;                                               (defining-dags (strip-cdrs param-new-val-alist))
;; ;whoa! this blows up for dags with a lot of sharing:
;;                                               (defining-terms (dag-to-term-list ;-efficient
;;                                                                defining-dags
;; ;generated-defun-names
;;                                                                ))
;;                                               (dummy1000 (cw "defining terms: ~X01" defining-terms nil))
;;                                               ;; this uses the test-dag simplied using the invariant
;;                                               (termination-test-dag (if (eql (unquote then-part-pc) loop-pc)
;;                                                                         ;;fixme simplify this (maybe with not-of-not)?
;;                                                                         (compose-term-and-dag '(not x) 'x test-dag)
;;                                                                       test-dag))
;;                                               (dummy2 (cw "Termination test: ~x0~%" termination-test-dag))
;;                                               ;;replace the vars in the termination test (fixme make sure none remain):
;; ;this doesn't seem to be quite working; maybe the test mentions a subterm of some larger term that got replaced?
;;                                               (termination-test-dag (simplify-with-rule-sets termination-test-dag
;;                                                                                     (list (cons :rules 'NIL))
;;                                                                                     (* 2 (len termination-test-dag))
;;                                                                                     nil
;;                                                                                     replacement-equalities
;;                                                                                     NIL
;;                                                                                     NIL
;;                                                                                     nil
;;                                                                                     nil
;;                                                                                     'nil ;monitored-runes
;;                                                                                     t
;;                                                                                     nil ;memoization
;;                                                                                     nil ;use-internal-contextsp
;;                                                                                     nil nil nil
;;                                                                                     ))
;;                                               (constant-opener-theorem-body
;;                                                `(implies (syntaxp (quotep params))
;;                                                          (equal (,(mypackn (list tag)) params)
;;                                                                 (if (,(mypackn (list tag '-exit-test)) params)
;;                                                                     (,(mypackn (list tag '-base)) params)
;;                                                                   (,(mypackn (list tag)) (,(mypackn (list tag '-update))
;;                                                                                           params))))))
;;                                               (defuns-and-theorems
;;                                                 `((defun ,(mypackn (list tag '-update))
;;                                                     (params) ;fixme better function name
;;                                                     ;;,@(get-param-terms si-expr-varnums))
;;                                                     ,(make-cons-nest defining-terms))

;;                                                   (defun ,(mypackn (list tag '-exit-test)) (params)
;;                                                     ,(dag-to-term termination-test-dag))

;;                                                   ;; (defun loop-measure (params)
;;                                                   ;;   ..)
;;                                                   ;;fixme handle more interesting base cases
;;                                                   (defun ,(mypackn (list tag '-base)) (params)
;;                                                     params)

;;                                                   (skip -proofs
;;                                                    (defund ,(mypackn (list tag)) (params)
;;                                                      ;;    (declare (xargs :measure (rc6-imp-unrolled-tail-aux-measure params)
;;                                                      ;;                    :hints (("Goal" :in-theory (enable dag-val2-no-array eval-fn eval-fn-binary)))
;;                                                      ;;                    ))
;;                                                      (if (,(mypackn (list tag '-exit-test)) params)
;;                                                          (,(mypackn (list tag '-base)) params)
;;                                                        (,(mypackn (list tag)) (,(mypackn (list tag '-update)) params)))))


;;                                                   ;;opener theorem for the loop for constant args:
;;                                                   (defthmd ,(mypackn (list tag '-opener))
;;                                                     ,constant-opener-theorem-body
;;                                                     :hints (("Goal" :in-theory
;;                                                              (e/d (,(mypackn (list tag)))
;;                                                                   (,(mypackn (list tag '-base))
;;                                                                    ,(mypackn (list tag '-exit-test))
;;                                                                    ,(mypackn (list tag '-update)))))))))
;;                                               (type-rules (make-type-rules defining-dags 0 tag))
;;                                               (dummy7 (cw "Generated type rules: ~x0~%" type-rules))
;;                                               (rules
;;                                                (append (list
;;                                                         ;;opener for the exit test:
;;                                                         (make-axe-rule-safe `(,(mypackn (list tag '-exit-test)) params)
;;                                                                        (dag-to-term termination-test-dag)
;;                                                                        `(:definition ,(mypackn (list tag '-exit-test)))
;;                                                                        nil nil)

;;                                                         ;;opener for the base case:
;;                                                         (make-axe-rule-safe `(,(mypackn (list tag '-base)) params)
;;                                                                        'params
;;                                                                        `(:definition ,(mypackn (list tag '-base)))
;;                                                                        nil nil)

;;                                                         ;;opener for the update function:
;;                                                         (make-axe-rule-safe `(,(mypackn (list tag '-update)) params)
;;                                                                        (make-cons-nest defining-terms)
;;                                                                        `(:definition ,(mypackn (list tag '-update)))
;;                                                                        nil nil))
;;                                                        ;;constant opener:
;;                                                        (make-axe-rules-from-theorem-safe constant-opener-theorem-body
;;                                                                                 `(:rewrite ,(mypackn (list tag '-constant-opener)))
;;                                                                                 nil)
;;                                                        ))

;;                                               (new-state-dag (make-new-state-dag state-update-dag
;;                                                                                  exit-pc
;;                                                                                  param-initial-val-alist
;;                                                                                  (mypackn (list tag))))

;;                                               (simplified-new-state-dag
;;                                                (simplify-dag new-state-dag
;;                                                                  (append
;;                                                                   extra-rules
;;                                                                   (make-axe-rules
;;                                                                    (append
;;                                                                     (get-local-rules)
;;                                                                     '((:definition update-local-in-state)
;;                                                                       (:definition set-field-in-state)
;;                                                                       (:definition set-pc)
;;                                                                       ))
;;                                                                    (w state))))))
;;                                          (declare (ignore dummy2 dummy7 dummy100 dummy1000))

;;                                          ;; fixme what if the termination test depends on other stuff?

;;                                          (list simplified-new-state-dag
;;                                                defuns-and-theorems
;;                                                (append type-rules rules))))))))))))))))))))))


;; (mv-let
;;                                 (param-new-val-alist var-to-si-expr-alist)
;;                                 (put-in-si-exprs param-new-val-alist
;;                                                  nil
;;                                                  nil
;;                                                  param-count)
;;                                 ;;check here that only new vars are in fixed-up-new-value-alist
;;                                   (let* ( ;(all-changed-vars (strip-cars fixed-up-new-value-alist))
;;                                          (si-expr-varnums (strip-cdrs var-to-si-expr-alist))
;; ;     (all-vars (append all-changed-vars si-expr-varnums))
;;                                          )

;;                                     (list defun
;;                                           fixed-up-new-value-alist
;;                                           var-to-si-expr-alist
;;                                           new-value-alist
;;                                           heap-update-triples
;;                                           locals-dag-alist
;;                                           heap-dag
;;                                           static-field-map-dag
;;                                           simplified-arbitrary-iteration-dag
;; ;invariant-at-first-loop-top
;; ;invariant-for-arbitrary-loop
;; ;'term-test-dag termination-test-dag
;; ;'loop-branch-dag loop-branch-dag
;;                                           ;;'termination-branch-dag termination-branch-dag
;;                                           )))))))))))))))))))))



;; get all the locals (up to local count) and note which ones changed
;; get the static area
;; get the heap

;; FIXME think about aliasing in the heap - also think about when there's a single write but the address depends on s... -- done?

;; (defun common-hyps ()
;;   '(
;;     ;;these are always the same:
;;     (equal (jvm::get-status (jvm::binding (th) (jvm::thread-table s))) ':scheduled)
;;     ;; the call stack has at least one frame:
;;     (equal (equal '0 (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table s));(jvm::call-stack (th) s)
;;                       )) 'nil)))

;; (defun make-loop-top-hyps (header-pc code class-name method-name method-descriptor)
;;   (append `((equal (jvm::pc (jvm::thread-top-frame (th) s)) ',header-pc)
;;             (equal (jvm::program (jvm::thread-top-frame (th) s)) ',code) ...method-info...
;;             (equal (jvm::class-and-method (jvm::thread-top-frame (th) s))
;;                    ...',(s :class-name class-name
;;                        (s :method-name-and-descriptor (cons method-name method-descriptor)
;;                           nil))))
;;           (common-hyps)))

;; (defun can-prove-we-are-not-in-the-loop (state-dag class-name method-name method-descriptor loop-pcs state)
;;   (let ((loop-designator-from-state
;;          (simplify-dag
;;           (compose-term-and-dag `(loop-designator-from-state s)
;;                                 's
;;                                 state-dag)
;;           ;;fixme?
;;           (make-axe-rules (first-loop-top-rules) (w state)))))
;;     (and (quotep loop-designator-from-state)
;;          (let ((loop-designator-from-state (unquote loop-designator-from-state)))
;;            (or (not (member (fourth loop-designator-from-state) loop-pcs))
;;                (not (equal class-name (first loop-designator-from-state)))
;;                (not (equal method-name (second loop-designator-from-state)))
;;                (not (equal method-descriptor (third loop-designator-from-state))))))))

;; ;;returns (mv exited-from-stack-height-flg state-dag)
;; ;;if exited-from-stack-height-flg is nil, then state-dag is at the header of a real loop (one that we can't show doesn't execute)
;; ;;if exited-from-stack-height-flg is t, then state-dag has exited from the stack height
;; (skip -proofs
;;  (defun skip-loops-that-dont-execute (state-dag si-hyps loop-infos generated-rules state)
;;    ;;see whether we've exited:
;;    (let ((call-stack-less-than-flg (simplify-dag
;;                                     (compose-term-and-dag '(< (len (JVM::CALL-STACK (th) s)) (len (JVM::CALL-STACK (th) si)))
;;                                                           's
;;                                                           state-dag)
;;                                     (append generated-rules
;;                                             (make-axe-rules
;;                                              (append (jvm-semantics-rules)
;;                                                      (jvm-simplification-rules)
;;                                                      (amazing-rules-spec-and-dag)(map-rules))
;;                                              (w state))) ;fixme where else might we need these assumptions?
;;                                     :assumptions si-hyps)))
;;      (if (not (quotep call-stack-less-than-flg))
;;          (mv nil
;;              (prog2$ (cw "Call stack less than flag: ~x0" call-stack-less-than-flg)
;;                      (hard-error 'skip-loops-that-dont-execute
;;                                  "We expected the call stack test to rewrite to a constant, but we got the above" nil)))
;;        ;; if we have returned from the stack-height, we are done
;;        (if (equal *t* call-stack-less-than-flg)
;;            (mv t state-dag)
;;          ;;We have not exited.
;;          ;;So see if we can just execute past the loop (because it doesn't execute at all):
;;          (let* ( ;figure out which loop we are in:
;;                 (loop-loop-designator-from-state (safe-unquote2 'skip-loops-that-dont-execute
;;                                                                       (simplify-dag
;;                                                                        (compose-term-and-dag '(loop-designator-from-state s)
;;                                                                                              's
;;                                                                                              state-dag)
;;                                                                        (make-axe-rules (first-loop-top-rules) (w state)) ;ffixme
;;                                                                        )))
;;                 ;;(header-pc (fourth loop-loop-designator-from-state))
;;                 (class-name (first loop-loop-designator-from-state))
;;                 (method-name (second loop-loop-designator-from-state))
;;                 (method-descriptor (third loop-loop-designator-from-state))
;;                 (loop-pcs (lookup-equal loop-loop-designator-from-state loop-infos))

;;                 ;;now try to execute past it:
;;                 (possible-state-at-next-loop-header-dag
;;                  (simplify-dag
;;                   (compose-term-and-dag
;;                    `(run-until-return-from-stack-height-or-until-hit-loop-header
;;                      (len (jvm::call-stack (th) si))
;;                      ',(strip-cars loop-infos) ;these are the loop-headers
;;                      ;;step the state once to get it past the current loop-header:
;;                      (jvm::step (th) s))
;;                    's
;;                    state-dag)
;;                   (append generated-rules
;;                           (make-axe-rules (first-loop-top-rules)
;;                                        (w state))) ;fixme?
;;                   :assumptions si-hyps)))
;;            ;;fixme - what exactly do we want for the test here?
;;            (if (can-prove-we-are-not-in-the-loop possible-state-at-next-loop-header-dag
;;                                                  class-name method-name method-descriptor loop-pcs state)
;;                ;;we skipped the current loop (it must not execute), so keep trying to skip loops:
;;                (skip-loops-that-dont-execute (prog2$ (cw "Skipping a loop that does not execute!~%")
;;                                                      possible-state-at-next-loop-header-dag)
;;                                              si-hyps
;;                                              loop-infos
;;                                              generated-rules
;;                                              state)
;;              ;;we have found a real loop (or maybe we have branched?):
;;              (mv nil ;we didn't exit
;;                  state-dag))))))))

;; (defun get-defun-names (items)
;;   (if (endp items)
;;       nil
;;     (let ((item (car items)))
;;       (if (eq 'defun (first item))
;;           (cons (second item)
;;                 (get-defun-names (cdr items)))
;;         (get-defun-names (cdr items))))))

;fixme what about loops inside conditionals?
;; (skip- proofs
;;  (defun decompile-loops-aux (state-dag loop-defuns-and-theorems-acc tag loop-count loop-infos si-hyps class-info-map
;;                                        extra-loop-top-hyps ;bozo - these are in terms of s
;;                                        generated-rules ;these are dag rules (not just runes)
;;                                        rule-list prove-invar-rules
;;                                        state)
;;    (declare (xargs :measure 1)) ;fixme fake measure
;;    (let* ((dummy (cw "Running until next loop or exit.~%"))
;;           (loop-headers (strip-cars loop-infos))
;;           (state-dag
;;            (simplify-dag
;;             (compose-term-and-dag
;;              `(run-until-return-from-stack-height-or-until-hit-loop-header
;;                (len (jvm::call-stack (th) si))
;;                ',loop-headers
;;                s)
;;              's
;;              state-dag)
;;             (append generated-rules
;;                     (make-axe-rules (first-loop-top-rules)
;;                                  (w state))) ;fixme
;;             :assumptions si-hyps))
;;           (dummy2 (cw "Done.~%"))
;;           )
;;      (declare (ignore dummy dummy2))
;;      ;; now we skip any loops that we can show don't execute:
;;      (mv-let
;;       (exited-from-stack-height-flg state-dag)
;;       (skip-loops-that-dont-execute state-dag si-hyps loop-infos generated-rules state)
;;       ;;test whether we've exited:
;;       (if exited-from-stack-height-flg
;;           ;;if so, we are done!
;;           (list state-dag loop-defuns-and-theorems-acc generated-rules (+ -1 loop-count))
;;         ;;otherwise, we are at a real loop header, so decompile the loop, and repeat
;;         (let* ( ;(dummy2 (cw "State at loop header: ~x0~%" state-at-loop-header-dag))
;;                (loop-loop-designator-from-state (safe-unquote2 'decompile-loops-aux
;;                                                                      (simplify-dag
;;                                                                       (compose-term-and-dag '(loop-designator-from-state s)
;;                                                                                             's
;;                                                                                             state-dag)
;;                                                                       (make-axe-rules (first-loop-top-rules) (w state)) ;ffixme
;;                                                                       )))
;;                (header-pc (fourth loop-loop-designator-from-state))
;;                (class-name (first loop-loop-designator-from-state))
;;                (method-name (second loop-loop-designator-from-state))
;;                (method-descriptor (third loop-loop-designator-from-state))
;;                ;;now get the list of PCs for the loop header we are at
;;                (all-loop-pcs (lookup-equal loop-loop-designator-from-state loop-infos))
;;                (dummy3 (cw "Loop number ~x0 is in ~s1 (at PC ~x2).~%"
;;                            loop-count
;;                            (concatenate 'string class-name "." method-name method-descriptor)
;;                            header-pc))
;;                (class-info (g-safe class-name class-info-map))
;;                (methods-for-class (jvm::class-decl-methods class-info))
;;                (method-info (g-safe (cons method-name method-descriptor)
;;                                     methods-for-class))
;;                (locals-count (g-safe :max-locals method-info)) ;fixme what if there are locals that haven't been initialized yet? will we prove invariants about them?
;;                (program (g-safe :program method-info))
;;                (loop-top-hyps (append extra-loop-top-hyps
;;                                       (make-loop-top-hyps header-pc program class-name method-name method-descriptor)))
;;                (dummy4 (cw "Loop top hyps are: ~x0~%.  Decompiling loop..." loop-top-hyps))
;;                (loop-stuff (decompile-loop state-dag
;;                                            header-pc
;;                                            si-hyps
;;                                            loop-top-hyps
;;                                            all-loop-pcs
;;                                            locals-count
;;                                            (mypackn (list tag '-loop- loop-count))
;;                                            generated-rules
;;                                            rule-list prove-invar-rules
;;                                            (get-defun-names loop-defuns-and-theorems-acc)
;;                                            state))
;;                (state-dag (first loop-stuff))
;;                (dummy6 (cw "State dag for this loop: ~x0~%" state-dag))
;;                (defuns-and-theorems-for-loop (second loop-stuff))
;;                (dummy7 (cw "defuns and theorems for this loop: ~x0~%" defuns-and-theorems-for-loop))
;;                (rules (third loop-stuff))
;;                (dummy8 (cw "rules for this loop: ~x0~%" rules))
;;                )
;;           (declare (ignore                  ;dummy2
;;                     dummy3 dummy4           ;dummy5
;;                     dummy6 dummy7 dummy8))
;;           (decompile-loops-aux state-dag
;;                                (append loop-defuns-and-theorems-acc defuns-and-theorems-for-loop)
;;                                tag
;;                                (+ 1 loop-count)
;;                                loop-infos
;;                                si-hyps class-info-map
;;                                extra-loop-top-hyps
;;                                (append rules generated-rules)
;;                                rule-list prove-invar-rules
;;                                state)))))))

;;Decompile the loops in a program
;;SI-HYPS are the hypotheses about the initial state, SI.  They must ensure that we know how to run SI (e.g., they must specify its PC, etc.).
;;TAG is a symbol that names the program (and gets appended to the generated stuff)
;;LOOP-INFOS indicates what PCs make up each loop
;format of each "loop-info:
;; ((header-pc class-name method-name method-descriptor) . pcs)

;;CLASS-INFO-MAP is a map from fully-qualifies class names to class-info records
;;fixme - can we get rid of extra-loop-top-hyps - fixme - at least, one should have to indicate which loop they are for
;returns (list state-at-loop-header-dag loop-defuns-and-theorems-acc generated-rules number-of-loops)
;; (defun decompile-loops (si-hyps tag loop-infos class-info-map extra-loop-top-hyps rules rule-list prove-invar-rules state)
;;   (decompile-loops-aux (dagify-term 'si) ;; the initial state-dag is just the variable si
;;                        nil               ;; initial loop-defuns-and-theorems-acc
;;                        tag
;;                        1 ;; initial loop-count
;;                        loop-infos
;;                        si-hyps
;;                        class-info-map
;;                        extra-loop-top-hyps
;;                        rules ;;nil ;; initial generated-rules
;;                        rule-list prove-invar-rules
;;                        state))

;; (defun get-defun-names-from-event (event)
;;   (if (not (consp event))
;;       nil ;error?
;;     (if (member-eq (ffn-symb event) '(defun defund))
;;         (list (second event))
;;       (if (eq (ffn-symb event) 'skip-proofs)
;;           (get-defun-names-from-event (second event))
;;         nil))))

;; (defun get-defun-names-from-events (events)
;;   (if (endp events)
;;       nil
;;     (append (get-defun-names-from-event (car events))
;;             (get-defun-names-from-events (cdr events)))))

;; (defun make-fake-measures (tag loops-left)
;;   (if (zp loops-left)
;;       nil
;;     (cons `(defund ,(mypackn (list tag '-loop- (nat-to-string loops-left) '-measure))
;;              (params)
;;              (nfix (nth 0 params))) ;fixme fake
;;           (make-fake-measures tag (+ -1 loops-left)))))

;; ;rename param!
;; ;loop numbers start at 1
;; (defun convert-loops-to-head-recursive-aux (tag loops-left)
;;   (declare (xargs :measure (nfix (+ 1 loops-left))))
;;   (if (zp loops-left)
;;       nil
;;     (append (convert-to-head-recursive-events (mypackn (list tag '-loop- (nat-to-string loops-left)))
;;                                               (mypackn (list tag '-loop- (nat-to-string loops-left) '-exit-test))
;;                                               (mypackn (list tag '-loop- (nat-to-string loops-left) '-measure))
;;                                               (mypackn (list tag '-loop- (nat-to-string loops-left) '-update))
;;                                               (mypackn (list tag '-loop- (nat-to-string loops-left) '-base))

;;                                               nil ;reps-hints
;;                                               )
;;             (convert-loops-to-head-recursive-aux tag (+ -1 loops-left)))))

;; ;loop numbers start at 1
;; (defun convert-loops-to-head-recursive (tag loops-left fake-measures-flg)
;;   `(progn ,@(append (if fake-measures-flg
;;                         (make-fake-measures tag loops-left)
;;                       nil)
;;                     (convert-loops-to-head-recursive-aux tag loops-left))))

;; ;fixme this also includes the head, base, and exit-test rules
;; (defun conversion-to-head-rules (tag count)
;;   (if (zp count)
;;       nil
;;     (append `(,(pack$ tag '-LOOP- (nat-to-string count) '-BECOMES- tag '-LOOP- (nat-to-string count) '-HEAD)
;;               ,(pack$ tag '-LOOP- (nat-to-string count) '-head)
;;               ,(pack$ tag '-LOOP- (nat-to-string count) '-base)
;;               ,(pack$ tag '-LOOP- (nat-to-string count) '-exit-test)
;;               )
;;             (conversion-to-head-rules tag (+ -1 count)))))

;; (defun reps-function-name (tag loop-number)
;;   (pack$ tag '-loop- (nat-to-string loop-number) '-reps))

;; (defun exit-test-function-name (tag loop-number)
;;   (pack$ tag '-loop- (nat-to-string loop-number) '-exit-test))

;; (defun update-function-name (tag loop-number)
;;   (pack$ tag '-LOOP- (nat-to-string loop-number) '-update))

;; (defun loop-funs-to-execute (tag count)
;;   (if (zp count)
;;       nil
;;     (append `(
;;               ,(reps-function-name tag count)
;;               ,(exit-test-function-name tag count)
;;               ,(update-function-name tag count)
;;               ,(pack$ tag '-LOOP- (nat-to-string count) '-head-aux)
;;               )
;;             (loop-funs-to-execute tag (+ -1 count)))))

;; (defun reps-function-base-cases (tag count)
;;   (if (zp count)
;;       nil
;;     (cons `(:rewrite ,(mypackn (list tag (nat-to-string count) '-head-aux-base-case)))
;;           (reps-function-base-cases tag (+ -1 count)))))

;; (defun pull-into-dag-rules ()
;;   '(quotep
;;     TOP-NODENUM
;;     LIST::NTH-OF-CONS
;;     DAG-VAL-WITH-AXE-EVALUATOR
;;     CAR-CONS
;;     acons
;;     cdr-cons
;;     DAG-VAL2-NO-ARRAY
;;     EVAL-DAG2-NO-ARRAY-opener
;;     EVAL-DAG-WITH-AXE-EVALUATOR
;;     axe-evaluator
;;     (TOP-NODENUM)
;;     EVAL-FN
;;     GET-ARG-VALS-NO-ARRAY
;;     (MEMBER-EQ)
;;     (QUOTEP)
;;     (equal)
;;     (zp)
;;     (endp)
;;     (nfix)
;;     ASSOC-EQUAL-OF-CONS
;;     LOOKUP-EQ-BECOMES-LOOKUP-EQUAL
;;     LOOKUP-EQUAL
;;     LOOKUP-BECOMES-LOOKUP-EQUAL
;;     EVAL-FN-BINARY
;;     EVAL-FN-ternARY))

;; ;gen the 32
;; (defthm ALL-UNSIGNED-BYTE-P-of-DAG-VAL-WITH-AXE-EVALUATOR-32
;;   (implies (and (not (quotep dag))
;;                 (not (QUOTEP (CAAR DAG)))) ;why?
;;            (equal (ALL-UNSIGNED-BYTE-P 32 (DAG-VAL-WITH-AXE-EVALUATOR dag alist fn-alist))
;;                   (DAG-VAL-WITH-AXE-EVALUATOR (cons `(,(+ 1 (top-nodenum dag)) ALL-UNSIGNED-BYTE-P '32 ,(top-nodenum dag))
;;                                                      dag)
;;                                                alist fn-alist)))
;;   :hints
;;   (("Goal" :in-theory (union-theories (theory 'minimal-theory)
;;                                       (pull-into-dag-rules)))))

;; (defthm len-of-DAG-VAL-WITH-AXE-EVALUATOR
;;   (implies (and (not (QUOTEP dag))
;;                 (not (QUOTEP (caar dag)))) ;why?
;;            (equal (len (DAG-VAL-WITH-AXE-EVALUATOR dag alist fn-alist))
;;                   (DAG-VAL-WITH-AXE-EVALUATOR (cons `(,(+ 1 (top-nodenum dag)) len ,(top-nodenum dag))
;;                                                      dag)
;;                                                alist fn-alist)))
;;   :hints
;;   (("Goal" :in-theory (union-theories (theory 'minimal-theory)
;;                                       (pull-into-dag-rules)))))

;; (defthm true-listp-of-DAG-VAL-WITH-AXE-EVALUATOR
;;   (implies (and (not (QUOTEP dag))
;; ;                (consp dag)
;;                 (not (QUOTEP (caar dag)))) ;why?
;;            (equal (true-listp (DAG-VAL-WITH-AXE-EVALUATOR dag alist fn-alist))
;;                   (DAG-VAL-WITH-AXE-EVALUATOR (cons `(,(+ 1 (top-nodenum dag)) true-listp ,(top-nodenum dag))
;;                                                      dag)
;;                                                alist fn-alist)))
;;   :hints
;;   (("Goal" :in-theory (union-theories (theory 'minimal-theory)
;;                                       (pull-into-dag-rules)))))

;; (defthm nth-of-DAG-VAL-WITH-AXE-EVALUATOR
;;   (implies (and (not (QUOTEP (CAAR DAG))) ;why?
;;                 (consp dag)
;;                ; (natp n)
;;                 )
;;            (equal (nth 3 (DAG-VAL-WITH-AXE-EVALUATOR dag alist fn-alist))
;;                   (DAG-VAL-WITH-AXE-EVALUATOR (cons `(,(+ 1 (top-nodenum dag)) nth '3 ,(top-nodenum dag))
;;                                                      dag)
;;                                                alist fn-alist)))
;;   :hints
;;   (("Goal" :in-theory (union-theories (theory 'minimal-theory)
;;                                       (append '(natp nfix) (pull-into-dag-rules))))))
;fffixme

;; (defconst-computed-simple *priorities-table*
;;   (TABLE-ALIST 'AXE-RULE-PRIORITIES-TABLE
;;                (W STATE)))

;; (defconst-computed-simple *rules-for-dag-simp*
;;   (make-axe-rules (amazing-rules-bv) (w state)))

;; ;simplify the dag argument to DAG-VAL-WITH-AXE-EVALUATOR - but when??
;; (skip- proofs
;;  (defthm DAG-VAL-WITH-AXE-EVALUATOR-simplify-dag
;;    (implies (and (equal new-dag (quick-simplify-dag dag
;;                                                     *rules-for-dag-simp*
;;                                                     :priorities *priorities-table*  ;otherwise, this contains the free variable state...
;;                                                     ))
;;                  (not (equal dag new-dag)))
;;             (equal (DAG-VAL-WITH-AXE-EVALUATOR dag alist fn-alist)
;;                    (DAG-VAL-WITH-AXE-EVALUATOR new-dag alist fn-alist)))))

;; (defthm DAG-VAL-WITH-AXE-EVALUATOR-when-dag-is-quotep
;;   (implies (quotep dag)
;;            (equal (DAG-VAL-WITH-AXE-EVALUATOR dag alist fn-alist)
;;                   (unquote dag)))
;;   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
;;                                              '(TOP-NODENUM
;;                                                LIST::NTH-OF-CONS
;;                                                DAG-VAL-WITH-AXE-EVALUATOR
;;                                                CAR-CONS
;;                                                acons
;;                                                cdr-cons
;;                                                DAG-VAL2-NO-ARRAY
;;                                                EVAL-DAG2-NO-ARRAY-opener
;;                                                EVAL-DAG-WITH-AXE-EVALUATOR
;;                                                axe-evaluator
;;                                                (TOP-NODENUM)
;;                                                EVAL-FN
;;                                                GET-ARG-VALS-NO-ARRAY
;;                                                (MEMBER-EQ)
;;                                                (QUOTEP)
;;                                                (equal)
;;                                                (zp)
;;                                                (endp)
;;                                                (nfix)
;;                                                ASSOC-EQUAL-OF-CONS
;;                                                LOOKUP-EQ-BECOMES-LOOKUP-EQUAL
;;                                                LOOKUP-EQUAL
;;                                                LOOKUP-BECOMES-LOOKUP-EQUAL
;;                                                EVAL-FN-BINARY
;;                                                EVAL-FN-ternARY)))))


;;;
;;; Support for storing lifter progress upon failure
;;;

(defun store-partial-lift (generated-events-acc state)
  (declare (xargs :stobjs state))
  (f-put-global 'lifter-events generated-events-acc state))

;; Return an event including all the stuff generated by the most recent failed
;; lifter call that stored generated events when it failed (note: not all
;; lifter failures store events yet).
(defun partial-lift-event (state)
  (declare (xargs :stobjs state))
  (if (not (boundp-global 'lifter-events state))
      (er hard? 'lifter-events "No stored lifter events.")
    (let ((events (f-get-global 'lifter-events state)))
      `(progn ,@events))))

;;; This submits any events generated by the lifter so far when the lifter
;;; fails in certain ways (but not all ways).  The user can call (partial-lift)
;;; to submit these events and quickly get into a state where necessary things
;;; are defined to help debug lifter problems.
(defmacro partial-lift ()
  `(make-event (partial-lift-event state)))

;this stuff was in the book "decompiler2":

;this must exist somewhere else?
(defun swap-pairs (alist)
  (if (endp alist)
      nil
    (let* ((entry (car alist))
           (key (car entry))
           (val (cdr entry))
           (entry (cons val key)))
      (cons entry
            (swap-pairs (cdr alist))))))

;fixme think about these
(defun standard-hyps (state-term)
  (append (standard-hyps-basic state-term)
          `((memberp '"java.lang.Object" (JVM::INITIALIZED-CLASSES ,state-term))
            (memberp '"java.lang.System" (JVM::INITIALIZED-CLASSES ,state-term))
            ;; where should this go?
            ;;this was too strong - it says that no other class is initialized...
            ;;     ;;putting this back in temporarily:
            ;;         (equal (JVM::INITIALIZED-CLASSES ,state-term)
            ;;                '("java.lang.Object" "java.lang.System"))
            )))

;returns (mv erp result state)
;pass in the thread id?
(defun get-dag-pc (dag hyps state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((mv erp dag2)
        (compose-term-and-dag `(JVM::pc (jvm::thread-top-frame (th) replace-me))
                              'replace-me
                              dag))
       ((when erp) (mv erp nil state)))
    (quick-simp-dag dag2
                    :rule-alist *state-component-extraction-axe-rule-alist*
                    :assumptions hyps
                    :remove-duplicate-rulesp nil)))

;fixme add guards (once had a method-descriptor with a lowercase i by mistake)
;todo: check the vars in the code hyps?!
(defun code-hyps (pc method-info class-name method-name method-descriptor state-term)
  `((equal (jvm::pc (jvm::thread-top-frame (th) ,state-term)) ',pc)
    (equal (jvm::method-info (jvm::thread-top-frame (th) ,state-term))
           ',method-info)
    (equal (jvm::method-designator (jvm::thread-top-frame (th) ,state-term))
           ',(jvm::make-method-designator class-name method-name method-descriptor))))

;these will not be returned as addresses to guess/check remain unchanged:
;check for a term of the form (nth <non-constant> (get-field <ad> '("ARRAY" "contents" . "dummy-descriptor") heap))
(defun bad-array-row-termp (term)
  (and (call-of 'nth term)
       (not (quotep (farg1 term))) ;if the n is constant, it's probably safe to include the term (TODO: remove this exception once we properly handle 2-d arrays; this causes a param to be added to the function for each row of the array accessed with a constant row number)
       (let ((parent-array-contents (farg2 term)))
         (and (call-of 'GET-FIELD parent-array-contents)
              (equal ''("ARRAY" "contents" . "dummy-descriptor") (farg2 parent-array-contents))))))

(assert-event
 (bad-array-row-termp '(NTH (jvm::NTH-local '2 (JVM::LOCALS (JVM::thread-top-frame (th) S1)))
                        (GET-FIELD (NTH-NEW-AD '50 (RKEYS (JVM::HEAP S0)))
                                   '("ARRAY" "contents" . "dummy-descriptor")
                                   (JVM::HEAP S1)))))

;this returns terms, not dags - hope that is okay
;fixme what about when the jvm model breaks the get-field/set-field abstraction for efficiency - should probably just take that out?
(defun get-addresses-from-dag (dag)
  (if (endp dag)
      nil
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (if (and (consp expr)
               (member-eq (ffn-symb expr) '(get-field set-field)))
          (let ((ad-term (dag-to-term (get-subdag (farg1 expr) dag))))
            (if (bad-array-row-termp ad-term)  ;don't include any terms that represent rows of multi-dim arrays (since these often change during the body of a loop)
                (progn$ (cw "NOTE: get-addresses-from-dag is excluding a problematic 2-d array term.")
                        (get-addresses-from-dag (cdr dag)))
              (add-to-set-equal ad-term
                                (get-addresses-from-dag (cdr dag)))))
        (get-addresses-from-dag (cdr dag))))))

;TODO: rename
;; Returns (mv erp result state).
;the exprs are over state-var (now previous-state-vars my occur too? what about input vars?)
;for each expr we make a claim that it is equal to the result of putting in initial-state-dag for state-var
;fixme - should we simplify these?
(defun make-unchangedness-invariants-for-exprs (exprs state-var initial-state-dag acc extra-vars state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp exprs)
      (mv (erp-nil) acc state)
    (let* ((expr (first exprs))
           (vars (get-vars-from-term expr)))
      (if (or (not (member-eq state-var vars)) ;;skip this address term, because it has already been "pushed back"
              (and (consp expr) (eq 'addressfix (ffn-symb expr))) ;skip calls to addressfix (just do it for the argument) ; fixme think about this
              )
          (make-unchangedness-invariants-for-exprs (rest exprs)
                                                   state-var initial-state-dag
                                                   acc extra-vars
                                                   state)
        (b* (((mv erp dag2)
              (compose-term-and-dag-safe expr state-var initial-state-dag :extra-vars extra-vars))
             ((when erp) (mv erp nil state))
             ((mv erp result state) (quick-simp-dag dag2 :rules (rule-list-1001)))
             ((when erp) (mv erp nil state)))
          (make-unchangedness-invariants-for-exprs (rest exprs)
                                                   state-var initial-state-dag
                                                   (cons `(equal ,expr
                                                                 ,(dag-to-term result))
                                                         acc)
                                                   extra-vars
                                                   state))))))

;returns (mv erp result state)
;fixme pass in ifns?
(defun simplify-all-terms-with-assumption (terms assumption-term state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp terms)
      (mv (erp-nil) nil state)
    (b* ((term (first terms))
         ((mv erp dag) (dagify-term2 term))
         ((when erp) (mv erp nil state))
         ((mv erp result state)
          (quick-simp-dag dag
                          ;;fixme - what rules do we want here? none?
                          :rules nil
                          :assumptions (list assumption-term)))
         ((when erp) (mv erp nil state))
         ((mv erp rest-result state)
          (simplify-all-terms-with-assumption (rest terms) assumption-term state))
         ((when erp) (mv erp nil state)))
      (mv (erp-nil)
          (cons (dag-to-term result)
                rest-result)
          state))))

;; Returns (mv erp provedp simplified-conjuncts state).
;replaces state-var with one-rep-dag in each conjunct and then tries to prove it
;prove that one-rep-dag preserves all the conjuncts, assuming the hyps and the conjuncts-to-simplify
(defun prove-invariant-conjuncts (conjuncts
                                  hyps
                                  one-rep-dag
                                  conjuncts-to-simplify ;rename hyps-to-simplify?
                                  rule-alist
                                  state-var interpreted-function-alist
                                  print state)
  (declare (xargs :mode :program :stobjs (state))
;           (irrelevant print)
           )
  (if (endp conjuncts)
      (mv (erp-nil) t conjuncts-to-simplify state) ;proved them all
    (b* ((conjunct (first conjuncts))
         (- (prog2$ (cw "(Proving invariant conjunct:~%")
                    (if print (cw "~x0~%" conjunct) (cw ":elided~%"))))
         (assumptions (append conjuncts-to-simplify ;hope this is okay
                              hyps))
         ((mv erp conjunct-after-one-rep-dag) (compose-term-and-dag conjunct state-var one-rep-dag)) ;return a dag-array to avoid converting back to an array below?
         ((when erp) (mv erp nil nil state))
         ((mv erp simplified-conjunct-after-one-rep state)
          (simp-dag
           conjunct-after-one-rep-dag
           ;;these rules may be slow:
           :rule-alist rule-alist
           :slack-amount 1000 ;new
           :assumptions assumptions
           :interpreted-function-alist interpreted-function-alist ;Thu Jul 29 02:57:42 2010
           :simplify-xorsp nil
           :remove-duplicate-rulesp nil
           :check-inputs nil))
         ((when erp) (mv erp nil nil state)))
      (if (equal *t* simplified-conjunct-after-one-rep)
          (prog2$ (cw "proved it.)~%")
                  (mv-let (erp result state)
                    ;;do we need to do this?
                    (simplify-all-terms-with-assumption (remove-equal conjunct conjuncts-to-simplify)
                                                        conjunct
                                                        state)
                    (if erp
                        (mv erp nil nil state)
                      (prove-invariant-conjuncts (rest conjuncts) hyps one-rep-dag
                                                 ;;we don't want to use the term to simplify itself:
                                                 (cons conjunct
                                                       result)
                                                 rule-alist state-var interpreted-function-alist print state))))
        ;;fffixme call the prover - would split into cases, etc. or do mitering?
        (progn$ (cw "  Failed to prove the invariant conjunct: ~x0~% Simplified form: ~x1~%  Assumptions: ~x2)~%"
                    conjunct simplified-conjunct-after-one-rep assumptions)
                (mv (erp-nil) nil nil state))))))

;todo: compare to prove-invariant-conjuncts
;; Returns (mv erp failed-conjuncts state).
;replaces state-var with one-rep-dag in each conjunct and then tries to prove it
;prove that one-rep-dag preserves all the conjuncts over state-var, assumung the assumptions
(defun prove-candidate-invars (candidate-invars
                               assumptions ; these are over state-var?
                               one-rep-dag rule-alist state-var
                               interpreted-function-alist
                               print monitored-symbols
                               use-prover-for-invars
                               this-loop-number
                               failed-candidate-invars-acc ;the ones that have failed so far
                               state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp candidate-invars)
      (mv (erp-nil) failed-candidate-invars-acc state)
    (b* ((conjunct-term (first candidate-invars))
         (- (cw " (Attempting to prove candidate invariant for loop ~x0: ~x1~%" this-loop-number conjunct-term))
         ((mv erp conjunct-after-one-rep-dag) (compose-term-and-dag conjunct-term state-var one-rep-dag)) ;return a dag-array to avoid converting back to an array below?
         ((when erp) (mv erp nil state))
         ((mv erp simplified-conjunct-after-one-rep state)
          (simp-dag
           conjunct-after-one-rep-dag
           ;;these rules may be slow:
           :rule-alist rule-alist
           :interpreted-function-alist interpreted-function-alist ;new
           :slack-amount 1000                                     ;new
           :assumptions assumptions ;hope this is okay
           :monitor monitored-symbols
           :simplify-xorsp nil
           :print nil ;print ;:verbose2 ;todo reduce printing
           :remove-duplicate-rulesp nil
           :check-inputs nil))
         ((when erp) (mv erp nil state)))
      (if (equal *t* simplified-conjunct-after-one-rep)
          (prog2$
           (cw " Proved candidate invariant.)~%")
           (prove-candidate-invars (rest candidate-invars) assumptions one-rep-dag rule-alist state-var
                                   interpreted-function-alist print monitored-symbols use-prover-for-invars this-loop-number failed-candidate-invars-acc state))
        (b* ((- (cw "  (Rewriting alone could not prove it:~%"))
             (- (cw "   (Simplified form: ~x0)~%" (if (dag-or-quotep-size-less-thanp simplified-conjunct-after-one-rep 1000)
                                                      (dag-to-term simplified-conjunct-after-one-rep)
                                                    simplified-conjunct-after-one-rep)))
             (- (cw "   (Assumptions: ~x0))~%" (if print assumptions :elided)))
             ((mv erp result state)
              (if use-prover-for-invars
                  (prog2$ (cw "  (Trying the Axe prover:~%")
                          (prove-dag-with-axe-prover simplified-conjunct-after-one-rep ;might as well start with the simplified conjunct
                                                     assumptions ;terms we can assume non-nil
                                                     (list rule-alist)
                                                     interpreted-function-alist
                                                     monitored-symbols
                                                     print
                                                     "INVAR"
                                                     nil ;context-array-name
                                                     nil ;context-array
                                                     0
                                                     nil ;context ;a contextp over nodes in context-array
                                                     6000 ;max-conflicts
                                                     nil  ;print-max-conflicts-goalp
                                                     nil  ;options
                                                     state))
                (progn$ (cw "  (Axe prover disabled: consider setting :use-prover-for-invars.)~%")
                        (mv (erp-nil) :failed state))))
             ((when erp) (mv erp nil state))
             (- (and use-prover-for-invars (cw "Done calling the Axe Prover.)~%"))))
          (if (eq :proved result)
              (prog2$
               (cw " Proved candidate invariant using the Axe Prover.)~%")
               (prove-candidate-invars (rest candidate-invars) assumptions one-rep-dag rule-alist state-var
                                       interpreted-function-alist print
                                       monitored-symbols use-prover-for-invars this-loop-number
                                       failed-candidate-invars-acc
                                       state))
            (prog2$ (cw "Failed to prove candidate invariant for loop ~x0: (~x1).)~%" this-loop-number result)
                    (prove-candidate-invars (rest candidate-invars) assumptions one-rep-dag rule-alist state-var
                                            interpreted-function-alist print
                                            monitored-symbols use-prover-for-invars this-loop-number
                                            (cons conjunct-term failed-candidate-invars-acc)
                                            state))))))))

;; Returns (mv erp candidate-invars-that-hold-initially state).
;; (But actually, this throws a hard error if anything fails to prove).
(defun filter-candidate-invars-that-hold-initially-aux (candidate-invars
                                                        assumptions ; these are over state-var?
                                                        loop-top-state-dag rule-alist state-var
                                                        interpreted-function-alist
                                                        print monitored-symbols
                                                        candidate-invars-acc ;the ones that have been proved so far
                                                        generated-events-acc ;to be stored in the state in case of failure, covers the entire lift
                                                        state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (if (endp candidate-invars)
      (mv (erp-nil) candidate-invars-acc state)
    (b* ((candidate-invar (first candidate-invars))
         (- (cw " (Attempting to prove that candidate invariant holds initially ~x0.~%" candidate-invar))
         ((mv erp candidate-invar-at-loop-top-dag)
          (compose-term-and-dag candidate-invar state-var loop-top-state-dag)) ;return a dag-array to avoid converting back to an array below?
         ((when erp) (mv erp nil state))
         ((mv erp simplified-candidate-invar-at-loop-top state)
          (simp-dag candidate-invar-at-loop-top-dag
                    ;;these rules may be slow:
                    :rule-alist rule-alist
                    :interpreted-function-alist interpreted-function-alist ;new
                    :slack-amount 1000                                     ;new
                    :assumptions assumptions ;hope this is okay
                    :monitor monitored-symbols
                    :simplify-xorsp nil
                    :print print ;:verbose2 ;todo reduce printing
                    :remove-duplicate-rulesp nil
                    :check-inputs nil))
         ((when erp) (mv erp nil state)))
      (if (equal *t* simplified-candidate-invar-at-loop-top)
          (prog2$
           (cw " Proved that candidate invar holds initially.)~%")
           (filter-candidate-invars-that-hold-initially-aux (rest candidate-invars) assumptions loop-top-state-dag rule-alist state-var
                                                            interpreted-function-alist print monitored-symbols (cons candidate-invar candidate-invars-acc)
                                                            generated-events-acc
                                                            state))
        ;;fffixme call the prover?!
        (b* ((- (cw "~%Failed to prove that invar holds initially: (Simplified form: ~x0)~%(Assumptions: ~x1))~%"
                    (if (dag-or-quotep-size-less-thanp simplified-candidate-invar-at-loop-top 1000)
                        (dag-to-term simplified-candidate-invar-at-loop-top)
                      simplified-candidate-invar-at-loop-top)
                    assumptions ;(if print assumptions :elided)
                    ))
             (state (store-partial-lift generated-events-acc state))
             (- (hard-error 'filter-candidate-invars-that-hold-initially-aux "Failed to prove that an invariant holds initially (see above)." nil)))
          ;; For now, this is never called since we throw an error above:
          (filter-candidate-invars-that-hold-initially-aux (rest candidate-invars) assumptions loop-top-state-dag rule-alist state-var
                                                           interpreted-function-alist print
                                                           monitored-symbols
                                                           candidate-invars-acc
                                                           generated-events-acc
                                                           state))))))

;; Returns (mv erp candidate-invars-that-hold-initially state).
;; (But actually, this throws a hard error if anything fails to prove).
(defun filter-candidate-invars-that-hold-initially (candidate-invars
                                                    assumptions ; these are over state-var?
                                                    loop-top-state-dag rule-alist state-var
                                                    interpreted-function-alist
                                                    print monitored-symbols
                                                    candidate-invars-acc ;the ones that have been proved so far
                                                    generated-events-acc ;to be stored in the state in case of failure, covers the entire lift
                                                    state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((- (cw "(Checking that candidate invariants hold initially:~%"))
       ((mv erp candidate-invars-that-hold-initially state)
        (filter-candidate-invars-that-hold-initially-aux candidate-invars
                                                         assumptions
                                                         loop-top-state-dag rule-alist state-var
                                                         interpreted-function-alist
                                                         print monitored-symbols
                                                         candidate-invars-acc
                                                         generated-events-acc
                                                         state))
       ((when erp) (mv erp nil state))
       (- (cw "Done checking that candidate invariants hold initially.)~%")))
    (mv (erp-nil) candidate-invars-that-hold-initially state)))

;; ;ffixme apply some rules!
;; (defun compose-cdr-dags (alist state-var state-dag state)
;;   (declare (xargs :mode :program :stobjs state))
;;   (if (endp alist)
;;       (mv nil state)
;;     (let* ((entry (car alist))
;;            (key (car entry))
;;            (dag (cdr entry)))
;;       (mv-let (dag state)
;;               (compose-dags dag state-var state-dag state)
;;               (mv-let (dag state)
;; ;call simplify-dag or something (like a quick version)?
;;                       (simplify-with-rule-sets dag
;;                                        (list (cons :rules (make-axe-rules (rule-list-1001) (w state))))
;;                                        (* 10 (len dag))
;;                                        nil
;;                                        nil
;;                                        'nil
;;                                        'nil
;;                                        nil
;;                                        nil
;;                                        'nil ;monitored-runes
;;                                        nil  ;consider making this t
;;                                        nil  ;memoize
;;                                        nil  ;use-internal-contextsp
;;                                        nil nil nil nil t
;;                                        state)
;; ;             (new-term (dag-to-term dag))
;;                       (mv-let (result state)
;;                               (compose-cdr-dags (cdr alist) state-var state-dag state)
;;                               (mv (cons (cons key dag) result
;;                                         ) state)))))))

;; ;fixme make sure all vars except params got replaced!
;; ;;param-new-val-alist-orig maps parameter numbers to their new expressions, in terms of other params and si
;; ;;we need to get rid of the expressions which mention si and make them into parameters of the function too
;; ;;we add params for the largest expressions that mention only si (fixme strip of any destructors?)
;; ;;returns (mv param-new-val-alist param-initial-val-alist replacement-alist)
;; ;there should be no dups in the alists
;; ;in which alist are params paired with terms and in which with dags?
;; (defun remove-vars-other-than-params (param-new-val-alist-orig param-new-val-alist-acc
;;                                                                param-initial-val-alist replacement-alist param-count state)
;;   (declare (xargs :mode :program :stobjs state))
;;   (if (endp param-new-val-alist-orig)
;;       (mv param-new-val-alist-acc param-initial-val-alist replacement-alist state)
;;     (let* ((entry (car param-new-val-alist-orig))
;;            (param-num (car entry))
;;            (defining-dag (cdr entry))
;;            )
;;       (mv-let (dag                      ;rewrite the dag
;;                param-new-val-alist-acc  ;;possibly add some new params
;;                param-initial-val-alist  ;;possibly add some new params
;;                replacement-alist        ;;possibly add some new params
;;                param-count state)
;;               (put-in-si-exprs-for-dag defining-dag param-new-val-alist-acc param-initial-val-alist replacement-alist param-count state)
;;               (remove-vars-other-than-params (cdr param-new-val-alist-orig)
;;                                              (acons param-num dag param-new-val-alist-acc)
;;                                              param-initial-val-alist
;;                                              replacement-alist
;;                                              param-count state)))))

;result may be quoted
;returns (mv erp result state)
(defun get-pc-of-nodenum (nodenum dag state)
  (declare (xargs :mode :program :stobjs (state)))
  (get-dag-pc (drop-nodes-past nodenum dag) nil ;bozo
              state))

;; Returns (mv erp res state).
;result may be quoted (e.g., '<, 'equal, or '>)
;fixme what hyps do we need?
;use this more?
;state-var must not be replace-me
(defun stack-height-comparison (dag state-var state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((mv erp dag2)
        (compose-term-and-dag-safe `(comparison (jvm::call-stack-size (jvm::call-stack (th) replace-me))
                                                (jvm::call-stack-size (jvm::call-stack (th) ,state-var)))
                                   'replace-me
                                   dag
                                   :extra-vars (list state-var)))
       ((when erp) (mv erp nil state)))
    (quick-simp-dag
     dag2
     :rule-alist *stack-height-axe-rule-alist* ;fixme where else might we need these assumptions?
     :assumptions (standard-hyps-basic state-var) ;fixme overkill
     :remove-duplicate-rulesp nil)))

;; Returns (mv erp res state).
(defun stack-height-comparison-for-nodenum (nodenum dag state-var state)
  (declare (xargs :mode :program :stobjs (state)))
  (stack-height-comparison (drop-nodes-past nodenum dag) state-var state))

; dag is a myif nest with states at the leaves.
;states which have exited the loop are made into Ts
;states back at the loop top are made into NILs
;anything else is an error
;fixme should this walk the structure of the myif nest (perhaps keeping a list of processed nodes)?
;; Returns (mv erp dag state).
(defun replace-states-with-t-and-nil (dag loop-pc ;other-loop-pcs ;fixme use this to determine whether we have exited the loop?
                                          state-var state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp dag)
      (mv (erp-nil) nil state)
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (if (not (and (consp expr)
                    (eq 'jvm::make-state (ffn-symb expr))))
          ;;not a make-state:
          (mv-let (erp result state)
            (replace-states-with-t-and-nil (cdr dag) loop-pc ;other-loop-pcs
                                           state-var state)
            (if erp
                (mv erp nil state)
              (mv (erp-nil) (cons entry result) state)))
        (let* ((nodenum (car entry)))
          (mv-let (erp stack-height-comparison state)
            (stack-height-comparison-for-nodenum nodenum dag state-var state)
            (if erp
                (mv erp nil state)
              (if (eq '< (safe-unquote stack-height-comparison))
                  ;;exited method (and so exited loop)
                  (mv-let (erp result state)
                    (replace-states-with-t-and-nil (cdr dag) loop-pc ;other-loop-pcs
                                                   state-var state)
                    (if erp
                        (mv erp nil state)
                      (mv (erp-nil)
                          (cons (cons nodenum ''t)
                                result)
                          state)))
                (if (eq '> (safe-unquote stack-height-comparison))
                    (mv (erp-t)
                        (hard-error 'replace-states-with-t-and-nil
                                    "Unexpected stack height (did the run not finish?)"
                                    nil)
                        state)
                  ;;otherwise, the stack height is the same, so check the PC:
                  (mv-let (erp pc state)
                    (get-pc-of-nodenum nodenum dag state)
                    (if erp
                        (mv erp nil state)
                      (let ((pc (safe-unquote2 'replace-states-with-t-and-nil pc)))
                        (if (eql pc loop-pc)
                            ;; back to top of loop
                            (mv-let (erp result state)
                              (replace-states-with-t-and-nil (cdr dag) loop-pc ;other-loop-pcs
                                                             state-var state)
                              (if erp
                                  (mv erp nil state)
                                (mv (erp-nil) (cons (cons nodenum ''nil) result) state)))
                          ;;exited the loop
                          (mv-let (erp result state)
                            (replace-states-with-t-and-nil (cdr dag) loop-pc ;other-loop-pcs
                                                           state-var state)
                            (if erp
                                (mv erp nil state)
                              (mv (erp-nil) (cons (cons nodenum ''t) result) state))))))))))))))))

;; Returns (mv erp res state).
;; body-dag is a myif nest with states at the leaves
;; to compute the termination test, we put in t for all states that have exited the loop and nil for all states that have not
(defun get-termination-test-dag (body-dag loop-pc ;other-loop-pcs
                                          state-var state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (quotep body-dag)
      (mv (erp-t) (hard-error 'get-termination-test-dag "unexpected quotep" nil) state)
    (mv-let (erp body-dag state)
      (replace-states-with-t-and-nil body-dag loop-pc ;other-loop-pcs
                                     state-var state)
      (if erp
          (mv erp nil state)
        (quick-simp-dag body-dag
                        :rule-alist *simplify-boolean-axe-rule-alist*
                        :remove-duplicate-rulesp nil)))))

;; Returns (mv erp res state).
;puts in 'replace-me-dont-reuse for states that are back at the top of the loop
(defun replace-loop-states (dag loop-pc ;other-loop-pcs
                                state-var state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp dag)
      (mv (erp-nil) nil state)
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (if (not (and (consp expr)
                    (eq 'jvm::make-state (ffn-symb expr))))
          ;;not a make-state:
          (mv-let (erp result state)
            (replace-loop-states (cdr dag) loop-pc ;other-loop-pcs
                                 state-var state)
            (if erp
                (mv erp nil state)
              (mv (erp-nil) (cons entry result) state)))
        (let* ((nodenum (car entry)))
          (mv-let (erp sh state)
            (stack-height-comparison-for-nodenum nodenum dag state-var state)
            (if erp
                (mv erp nil state)
              (let ((stack-height-comparison (safe-unquote sh)))
                (if (eq '< stack-height-comparison)
                    ;;exited method (and so exited loop)
                    (mv-let (erp result state)
                      (replace-loop-states (cdr dag) loop-pc ;other-loop-pcs
                                           state-var state)
                      (if erp
                          (mv erp nil state)
                        (mv (erp-nil)
                            (cons entry result)
                            state)))
                  (if (eq '> stack-height-comparison)
                      (mv (erp-t)
                          (hard-error 'replace-loop-states
                                      "Unexpected stack height (did the run not finish?)"
                                      nil)
                          state)
                    ;;otherwise, the stack height is the same
                    (mv-let (erp pc state)
                      (get-pc-of-nodenum nodenum dag state)
                      (if erp
                          (mv erp nil state)
                        (let* ((pc (safe-unquote2 'replace-loop-states pc)))
                          (if (eql pc loop-pc)
                              ;; back to top of loop:
                              (mv-let (erp result state)
                                (replace-loop-states (cdr dag) loop-pc ;other-loop-pcs
                                                     state-var state)
                                (if erp
                                    (mv erp nil state)
                                  (mv (erp-nil) (cons (cons nodenum ''replace-me-dont-reuse) result) state)))
                            ;;exited the loop
                            (mv-let (erp result state)
                              (replace-loop-states (cdr dag) loop-pc ;other-loop-pcs
                                                   state-var state)
                              (if erp
                                  (mv erp nil state)
                                (mv (erp-nil)
                                    (cons entry
                                          result) state)))))))))))))))))

;; Returns (mv erp res state).
;puts in 'replace-me-dont-reuse for all branches that are not back at the top of the loop?
;fixme instead of handling every node in the dag, walk through the top ite nest?
(defun replace-non-loop-states (dag loop-pc ;other-loop-pcs
                                    state-var state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp dag)
      (mv (erp-nil) nil state)
    (let* ((entry (car dag))
           (expr (cdr entry)))
      (if (not (call-of 'jvm::make-state expr))
          ;;not a make-state:
          (mv-let (erp result state)
            (replace-non-loop-states (cdr dag) loop-pc ;other-loop-pcs
                                     state-var state)
            (if erp
                (mv erp nil state)
              (mv (erp-nil) (cons entry result) state)))
        (let* ((nodenum (car entry)))
          (mv-let (erp sh state)
            (stack-height-comparison-for-nodenum nodenum dag state-var state)
            (if erp
                (mv erp nil state)
              (let ((stack-height-comparison (safe-unquote sh)))
                (if (eq '< stack-height-comparison)
                    ;;exited method (and so exited loop)
                    (mv-let (erp result state)
                      (replace-non-loop-states (cdr dag) loop-pc ;other-loop-pcs
                                               state-var state)
                      (if erp
                          (mv erp nil state)
                        (mv (erp-nil)
                            (cons (cons nodenum ''replace-me-dont-reuse)
                                  result) state)))
                  (if (eq '> stack-height-comparison)
                      (mv (erp-t)
                          (hard-error 'replace-non-loop-states
                                      "Unexpected stack height (did the run not finish?)"
                                      nil)
                          state)
                    (mv-let (erp pc state)
                      (get-pc-of-nodenum nodenum dag state)
                      (if erp
                          (mv erp nil state)
                        (let ((pc (safe-unquote2 'replace-non-loop-states pc)))
                          ;;otherwise, the stack height is the same
                          (if (eql pc loop-pc)
                              ;; back to top of loop
                              (mv-let (erp result state)
                                (replace-non-loop-states (cdr dag) loop-pc ;other-loop-pcs
                                                         state-var state)
                                (if erp
                                    (mv erp nil state)
                                  (mv (erp-nil)
                                      (cons entry result)
                                      state)))
                            ;;exited the loop
                            (mv-let (erp result state)
                              (replace-non-loop-states (cdr dag) loop-pc ;other-loop-pcs
                                                       state-var state)
                              (if erp
                                  (mv erp nil state)
                                (mv (erp-nil)
                                    (cons (cons nodenum ''replace-me-dont-reuse)
                                          result)
                                    state)))))))))))))))))

;; Returns (mv erp one-rep-dag state).
(defun get-one-rep-dag (body-dag loop-pc ;other-loop-pcs
                                 state-var state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (quotep body-dag)
      (mv (erp-t) (hard-error 'get-one-rep-dag "unexpected quotep" nil) state)
;this uses rewriting to get rid of the non-loop branches - a bit awkward?
    (mv-let (erp body-dag state)
      (replace-non-loop-states body-dag loop-pc ;other-loop-pcs
                               state-var state)
      (if erp
          (mv erp nil state)
        (quick-simp-dag body-dag
                        :rule-alist *get-rid-of-replace-me-dont-reuse-axe-rule-alist*
                        :remove-duplicate-rulesp nil)))))

;; Returns (mv erp exit-dag state).
(defun get-exit-dag (body-dag loop-pc ;other-loop-pcs
                              state-var state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (quotep body-dag)
      (mv (erp-t) (hard-error 'get-exit-dag "unexpected quotep" nil) state)
    ;;this uses rewriting to get rid of the loop branches - a bit awkward?
    (mv-let (erp body-dag state)
      (replace-loop-states body-dag loop-pc ;other-loop-pcs
                           state-var state)
      (if erp
          (mv erp nil state)
        (quick-simp-dag body-dag
                        :rule-alist
                        (add-to-rule-alist! '(myif-same-branches) ;should anything else be included here?
                                           *get-rid-of-replace-me-dont-reuse-axe-rule-alist*
                                           (w state))
                        :remove-duplicate-rulesp nil)))))

;; Returns (mv erp heap-dag state).
(defun get-heap-dag (state-dag state)
  (declare (xargs :mode :program :stobjs (state)))
  (quick-simp-composed-term-and-dag `(jvm::heap replace-me) 'replace-me state-dag
                                    :rule-alist *state-component-extraction-axe-rule-alist*))

;returns (mv erp local-dag state)
(defun get-local-dag (localnum state-dag state)
  (declare (xargs :mode :program :stobjs (state)))
  (quick-simp-composed-term-and-dag `(jvm::nth-local ',localnum (jvm::locals (jvm::thread-top-frame (th) s))) 's state-dag
                                    :rule-alist *get-local-axe-rule-alist*
                                    :remove-duplicate-rulesp nil))

;; TODO: consider processing local slots in the opposite order so local nums increase along with param nums (the changed param numbering would likely break existing derivations)
;; TODO: Consider normalizing local update nests to always use update-local and then using the nest to guide the operation of this function.
;; Returns (mv erp next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist state)
;Walk through the locals (in decreasing order).  TODO: What about locals that take 2 slots?  Maybe ok since a long/double is stored in only the lower-numbered slot?
;For each one that is changed in the one-rep-dag, assign a parameter number to it, pair that paramnum with the dag for the updated value of the local,
;and pair the paramnum with the initial expr for the param (which will be used later to get its initial value),
(defun make-loop-parameters-for-locals (local-num
                                        pc
                                        local-variable-table
                                        state-var
                                        excluded-locals ; :auto or a list of local slow numbers
                                        one-rep-dag
                                        next-param-number
                                        updated-state-term
                                        paramnum-update-alist
                                        paramnum-extractor-alist
                                        paramnum-name-alist
                                        state)
  (declare (xargs :mode :program :measure (nfix (+ 1 local-num)) :stobjs (state)))
  (if (not (natp local-num))
      (mv (erp-nil) next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist state)
    (b* ((local-name-and-type (lookup-in-local-variable-table local-num pc local-variable-table)) ;might be nil
         (local-name (first local-name-and-type))
         (local-type (second local-name-and-type))
         ;; Decide whether to exclude the local (TODO: Think about soundness: How to ensure the local is not use after the loop?)
         (exclude-reason (if (eq :auto excluded-locals)
                             (if local-variable-table
                                 (if (not local-name) ;; Exclude because the local-variable-table indicates the local is out of scope
                                     "not in scope at the loop top"
                                   nil)
                               nil ;don't exclude since there is no local-variable-table (TODO: Could do use-def analysis in this case)
                               )
                           ;; An explicit list of excluded-locals has been given:
                           (if (member local-num excluded-locals) ;; The user has said to skip this local (TODO: This is for locals that are always written before being read (e.g., ones allocated inside the loop - do some analysis to find these (e.g., see if a read term of the local on the initial state exists in the DAG) - what if the local is written but not read in the loop but is read *after* the loop.  fixme is all this sound?  should we put in a stub?
                               "explicitly excluded"
                             nil))))
      (if exclude-reason
          (progn$ (cw "(Skipping excluded local ~x0 (~s1).)~%" local-num exclude-reason)
                  (make-loop-parameters-for-locals (+ -1 local-num) pc local-variable-table state-var excluded-locals one-rep-dag next-param-number updated-state-term
                                                   paramnum-update-alist paramnum-extractor-alist paramnum-name-alist state))
        (b* ((initial-local-term `(jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) ,state-var))))
             ((mv erp initial-local-dag) (dagify-term2 initial-local-term))
             ((when erp) (mv erp nil nil nil nil nil state))
             ((mv erp updated-local-dag state)
              (get-local-dag local-num one-rep-dag state))
             ((when erp) (mv erp nil nil nil nil nil state))
             ;; Check whether the local has been changed by the loop body:
             ;;can we avoid this call to the rewriter?
             ((mv erp unchanged-check-result state)
              (quick-simp-composed-term-and-dag `(equal ,initial-local-term xx) 'xx updated-local-dag
                                                :rule-alist *get-local-axe-rule-alist*
                                                :remove-duplicate-rulesp nil))
             ((when erp) (mv erp nil nil nil nil nil state))
             (unchangedp (equal ''t unchanged-check-result)))
          (if unchangedp
              ;; Later we handle read-only locals
              (progn$ (cw "(Skipping unchanged local ~x0.)~%" local-num)
                      (make-loop-parameters-for-locals (+ -1 local-num) pc local-variable-table state-var excluded-locals one-rep-dag next-param-number updated-state-term
                                                       paramnum-update-alist paramnum-extractor-alist paramnum-name-alist state))
            ;;ffixme the local may not be live during the whole loop and so may not be assigned a slot at this pc (it may be a temporary that is written before it is read)
            ;;look for any name for that slot at any pc in the loop - can there be more than 1? ffixme  (or always exclude such things - now we have to use the excluded-locals-alist to do that)
            (b* ((- (cw "(Param ~x0 is ~s1 (local #~x2), of type ~s3.)~%" next-param-number (or local-name :unknown-name) local-num (or local-type :unknown-type))))
              (make-loop-parameters-for-locals (+ -1 local-num)
                                               pc local-variable-table state-var excluded-locals one-rep-dag
                                               (+ 1 next-param-number)
                                               `(update-local-in-state ',local-num (nth ',next-param-number :loop-function-result) (th) ,updated-state-term)
                                               (acons next-param-number updated-local-dag paramnum-update-alist)
                                               (acons next-param-number initial-local-dag paramnum-extractor-alist)
                                               (acons next-param-number (or local-name :unknown-name) paramnum-name-alist)
                                               state))))))))

;returns a list of triples (one for each nested call to set-field) of the form (address-dag class-field-pair value-dag)
;HEAP-NODENUM should be the nodenum of a heap term in HEAP-DAG which is a nest of set-fields around BASE-TERM
;The outermost updates appear first in the TRIPLES returned.
(defun get-heap-update-triples-aux (heap-nodenum heap-dag base-term previous-state-vars)
  (declare (xargs :mode :program)) ;todo
  (if (dag-equal-term-at-node heap-dag base-term heap-nodenum) ;ffixme can the state-var here be instead a previous state-var ;only if the heap doesn't change?
      nil
    (let* ((expr (lookup heap-nodenum heap-dag)))
      (if (call-of 'set-field expr)
          (let* ((ad (first (fargs expr)))
                 (class-field-pair (check-quotep (second (fargs expr))))
                 (value (third (fargs expr)))
                 (heap-nodenum (fourth (fargs expr)))
                 (ad-dag (check-dag-vars previous-state-vars (get-subdag ad heap-dag))) ;for now the address being written to must not depend on s
                 (value-dag (get-subdag value heap-dag)))
            (cons (list ad-dag class-field-pair value-dag)
                  (get-heap-update-triples-aux heap-nodenum heap-dag base-term previous-state-vars)))
        (er hard? 'get-heap-update-triples-aux "unexpected heap term at nodenum ~x0 in dag ~X12" heap-nodenum heap-dag nil)))))

;returns a list of triples (one for each nested call to set-field) of the form (address-dag class-field-pair value-dag)
;HEAP-DAG should be the subdag corresponding to a heap term
;The outermost updates appear first in the TRIPLES returned.
(defun get-heap-update-triples (heap-dag state-var previous-state-vars)
  (declare (xargs :mode :program))
;check whether the heap doesn't depend on state-var
;fixme, can the heap be a quotep?
;fixme what if the heap changes but not in a way that depends on s?
  ;; todo: use this get-subdag below (or don't compute it here)?
  ;; todo: drop this check (can it ever happen?)?
  (if (subsetp-eq (dag-vars (get-subdag (top-nodenum heap-dag) heap-dag)) previous-state-vars) ;todo: what about inputs?
      (prog2$ (er hard 'get-heap-update-triples "Heap check failed: ~x0." heap-dag)
              nil)
    (get-heap-update-triples-aux (top-nodenum heap-dag) heap-dag `(jvm::heap ,state-var) previous-state-vars)))

;; These have the addresses and class-name-field-name-pairs but not the values
(defun get-heap-update-pairs-from-triples (heap-update-triples)
  (if (endp heap-update-triples)
      nil
    (cons (firstn 2 (car heap-update-triples))
          (get-heap-update-pairs-from-triples (cdr heap-update-triples)))))

;; We process the heap updates indicated by HEAP-UPDATE-TRIPLES by making a loop parameter for each one.
;;returns (mv erp updated-state-term paramnum-update-alist paramnum-extractor-alist next-param-number paramnum-name-alist)
;TODO: really this should process the triples in the other order (to make the first triple be the outermost update).
;;well, we now prove that no addresses alias...
(defun make-loop-parameters-for-fields (heap-update-triples updated-state-term next-param-num paramnum-update-alist paramnum-extractor-alist paramnum-name-alist state-var)
  (if (endp heap-update-triples)
      (mv (erp-nil) updated-state-term paramnum-update-alist paramnum-extractor-alist next-param-num paramnum-name-alist)
    (b* ((triple (first heap-update-triples))
         (ad-dag (first triple))
         (ad-term (dag-to-term ad-dag))               ;can we skip this?
         (class-name-field-id-pair (second triple))   ;already quoted?
         (value-dag (third triple))
;fixme consider adding a take with the old length if
;we are setting the array contents field?  since array
;lengths can't change - otherwise we'd need to prove a
;simple inductive theorem on the loop function in order
;to know the resulting array length -- in general, how
;will we handle exceptions that depend on the results of
;loop functions?  -- now we generate type lemmas, so that handles the array length case, at least
         (getfield-term `(get-field ,ad-term ,class-name-field-id-pair (jvm::heap ,state-var)))
         (- (cw "Param ~x0 is ~X12.~%" next-param-num getfield-term nil))
         (updated-state-term `(set-field-in-state ,ad-term ,class-name-field-id-pair (nth ',next-param-num :loop-function-result) ,updated-state-term)) ;we wrap a set-field around the old updated-state-term
         (paramnum-update-alist (acons next-param-num value-dag paramnum-update-alist)) ;check that the values coming in are right
         ((mv erp getfield-dag) (dagify-term2 getfield-term))
         ((when erp) (mv erp nil nil nil nil nil))
         (paramnum-extractor-alist (acons next-param-num getfield-dag paramnum-extractor-alist))
         (paramnum-name-alist (acons next-param-num getfield-term paramnum-name-alist)))
      (make-loop-parameters-for-fields (rest heap-update-triples) updated-state-term (+ 1 next-param-num) paramnum-update-alist paramnum-extractor-alist paramnum-name-alist state-var))))

;;TOOO: What if other state components than the locals/heap/static-fields are changed?  e.g., strings get interned in the loop?

;returns mv (static-field-update-pairs state)
;(skip-proofs
 (defun get-static-field-update-pairs-aux (nodenum dag state-var)
   (declare (xargs :mode :program))
   (if (dag-equal-term-at-node dag `(jvm::static-field-map ,state-var) nodenum) ;ffixme should we have s or si here?
       nil
     (let* ((expr (lookup nodenum dag)))
       (if (call-of 's expr) ;(and (consp expr) (eq 's (ffn-symb expr)))
           (let* ((class-field-pair (check-quotep (first (fargs expr))))
                  (value (second (fargs expr)))
                  (static-field-map-nodenum (third (fargs expr)))
                  (value-dag (get-subdag value dag))
                  )
             (cons (list class-field-pair value-dag)
                   (get-static-field-update-pairs-aux static-field-map-nodenum dag state-var)))
         (er hard? 'get-static-field-update-pairs-aux "unexpected static field map term at nodenum ~x0 in dag ~x1" nodenum dag)))))
;)

;fixme what about ifs?
;returns mv static-field-update-pairs
(defun get-static-field-update-pairs (dag state-var previous-state-vars)
   (declare (xargs :mode :program))
   ;;check whether the static field map doesn't depend on s: ;;fixme is this check appropriate?
  ;;fixme, can the static field map be a quotep?
  (if (subsetp-eq (dag-vars (get-subdag (top-nodenum dag) dag)) previous-state-vars)
      nil
    (get-static-field-update-pairs-aux (top-nodenum dag) dag state-var)))

;;returns (mv erp updated-state-term paramnum-update-alist paramnum-extractor-alist next-param-number paramnum-name-alist)
(defun make-loop-parameters-for-static-fields (static-field-update-pairs
                                               updated-state-term
                                               next-param-number
                                               paramnum-update-alist
                                               paramnum-extractor-alist
                                               paramnum-name-alist
                                               state-var)
  (if (endp static-field-update-pairs)
      (mv (erp-nil) updated-state-term paramnum-update-alist paramnum-extractor-alist next-param-number paramnum-name-alist)
    (b* ((pair (first static-field-update-pairs))
         (class-name-field-id-pair (first pair)) ;already quoted?
         (value-dag (second pair))
         (class-name (car class-name-field-id-pair))
         (field-id (cdr class-name-field-id-pair))
         (get-static-field-term `(jvm::get-static-field ,class-name ,field-id (jvm::static-field-map ,state-var)))
         (- (cw "Param ~x0 is ~X12.~%" next-param-number get-static-field-term nil))
         (updated-state-term `(jvm::setstaticfield ,class-name ,field-id
                                                   (nth ',next-param-number :loop-function-result) ,updated-state-term))
         (paramnum-update-alist (acons next-param-number value-dag paramnum-update-alist))
         ((mv erp get-static-field-dag) (dagify-term2 get-static-field-term))
         (paramnum-extractor-alist (acons next-param-number get-static-field-dag paramnum-extractor-alist))
         ((when erp) (mv erp nil nil nil nil nil))
         (paramnum-name-alist (acons next-param-number get-static-field-term paramnum-name-alist)))
      (make-loop-parameters-for-static-fields (rest static-field-update-pairs)
                                              updated-state-term
                                              (+ 1 next-param-number)
                                              ;;or simplify the get-field expression applied to the arbitrary state???
                                              paramnum-update-alist
                                              paramnum-extractor-alist
                                              paramnum-name-alist
                                              state-var))))

(defun lookup-equivalent-dag (dag alist-with-dag-keys)
  (if (endp alist-with-dag-keys)
      nil
    (let* ((entry (car alist-with-dag-keys))
           (key (car entry)))
      (if (equivalent-dags dag key)
          (cdr entry)
        (lookup-equivalent-dag dag (cdr alist-with-dag-keys))))))

;;we seek sub-expressions (in dag) that depend on vars other than params (and don't depend on params)
;;returns (mv erp dag dag-paramnum-alist next-param-number paramnum-name-alist state)
;;TTODO: Maybe we should check whether any of these are unchanged (like we do for addresses)?
;;TTODO: Need to show that none of these alias any of the changed instance fields?
;;TTTODO: This seems to depend on brittle node ordering in the DAG.  Do something better?
;(skip-proofs
(defun find-read-only-params (dag dag-paramnum-alist next-param-number paramnum-name-alist state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (quotep dag) ;fixme this is new - add support for quotep dags elsewhere?
      (mv (erp-nil) dag dag-paramnum-alist next-param-number paramnum-name-alist state)
    (let* ((dag-var-array (make-dag-var-array dag))
           (nodenum (find-nodenum-of-si-dag-to-replace dag dag-var-array))) ;fixme is it possible that this value won't be a word or array?
      (if (not nodenum) ;;we didn't find a subdag that depends on the right vars
          (mv (erp-nil) dag dag-paramnum-alist next-param-number paramnum-name-alist state)
        (b* ((si-dag (get-subdag nodenum dag))
             ;;(dummy(cw "Si-expr dag:~% ~X01~%" si-dag nil))
             ;;              (si-term (dag-to-term si-dag))
             ;;see if this term has already been given a param number
             (match (lookup-equivalent-dag si-dag dag-paramnum-alist)) ;match will be a paramnum or nil
             (si-term-or-dag (if (dag-or-quotep-size-less-thanp si-dag 1000)
                                 (dag-to-term si-dag)
                               si-dag))
             (- (and (not match) (cw "Param ~x0 is ~X12.~%" next-param-number si-term-or-dag nil)))
             (paramnum-name-alist (if (not match)
                                      (acons next-param-number
                                             si-dag ;this isn't really a name..
                                             paramnum-name-alist)
                                    paramnum-name-alist))
             (param-num (if match match next-param-number))
             (param-term `(nth ',param-num params))
             ;;(equality `(equal ,si-term ,param-term))
             ((mv erp dag) (perform-replacements dag (acons si-dag param-term nil)))
             ((when erp) (mv erp nil nil nil nil state)))
          ;; ;put in the param for the expression
          ;;          ;;inefficient?:  the whole purpose of this rewrite is just to substitute using the equality?
          ;;          (mv-let (dag state)
          ;; ;call simplify-dag or something (like a quick version)?
          ;;                  (simplify-with-rule-sets dag
          ;;                                   (list (cons :rules NIL))
          ;;                                   (* 2 (len dag))
          ;;                                   nil
          ;;                                   (list equality)
          ;;                                   NIL
          ;;                                   NIL
          ;;                                   nil
          ;;                                   nil
          ;;                                   nil ;monitored-runes
          ;;                                   nil
          ;;                                   nil  ;memoize
          ;;                                   nil  ;use-internal-contextsp
          ;;                                   nil nil nil nil t state)
          (if match ;this si-expression has already been given a parameter name
              (find-read-only-params dag dag-paramnum-alist next-param-number paramnum-name-alist state)
            ;;we are replacing a new expression and adding a new param for it:
            (find-read-only-params dag
                                   ;;fixme call a dagify-term that inlines constants...
                                   (acons si-dag next-param-number dag-paramnum-alist)
                                   (+ 1 next-param-number)
                                   paramnum-name-alist state)))))))
;)

;;returns (mv erp dags new-param-term-alist next-param-number paramnum-name-alist state)
(defun find-read-only-params-lst (dags dag-paramnum-alist next-param-number dags-acc paramnum-name-alist state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp dags)
      (mv (erp-nil) (reverse dags-acc) (swap-pairs dag-paramnum-alist) next-param-number paramnum-name-alist state)
    (mv-let (erp dag dag-paramnum-alist next-param-number paramnum-name-alist state)
      (find-read-only-params (first dags) dag-paramnum-alist next-param-number paramnum-name-alist state)
      (if erp
          (mv erp nil nil nil nil state)
        (find-read-only-params-lst (rest dags) dag-paramnum-alist next-param-number
                                   (cons dag dags-acc)
                                   paramnum-name-alist state)))))

;should have no duplicates
(defun make-replacement-alist (paramnum-dag-alist)
  (if (endp paramnum-dag-alist)
      nil
    (let* ((entry (car paramnum-dag-alist))
           (parameter-number (car entry))
           (dag (cdr entry)))
      (acons dag
             `(nth ',parameter-number params)
             (make-replacement-alist (cdr paramnum-dag-alist))))))

;; (defun make-initial-value-dags (param-term-alist loop-top-state-dag state-var state)
;;    (declare (xargs :mode :program :stobjs (state)))
;;    (if (endp param-term-alist)
;;       (mv nil state)
;;     (let* ((entry (car param-term-alist))
;;            (term (cdr entry)))
;;       (mv-let (result state)
;;               (quick-simplify-dag3 (compose-term-and-dag term state-var loop-top-state-dag)
;;                                   *get-local-axe-rule-alist*
;;                                   :remove-duplicate-rulesp nil)
;;               (mv-let (result2 state)
;;                       (make-initial-value-dags (cdr param-term-alist) loop-top-state-dag state-var state)
;;                       (mv (cons result
;;                                 result2) state))))))

;only uses the cars of the alist? just pass in the start and end numbers?
; Returns (mv erp dags).
(defun make-new-val-dags-read-only (alist)
  (if (endp alist)
      (mv (erp-nil) nil)
    (b* ((entry (car alist))
         (paramnum (car entry))
         ((mv erp dag) (dagify-term2 `(nth ',paramnum params)))
         ((when erp) (mv erp nil))
         ((mv erp rest-dags) (make-new-val-dags-read-only (cdr alist)))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons dag rest-dags)))))

;; ;it may be common for subdag-for-var to be large but main-dag to be small - as when we are extracting a tiny piece of a big dag
;; ;var-to-replace had better appear only once in main-dag?
;; (defund compose-dags2 (main-dag var-to-replace subdag-for-var)
;;   (if (quotep main-dag)
;;       main-dag
;;     (let ((nodenum-of-var (lookup var-to-replace main-dag)))
;;       (if (not nodenum-of-var)
;;           main-dag ;print error or warning?
;;         ..))))


;; (mutual-recursion
;;  (defun tree-size (tree)
;;    (if (atom tree)
;;        1
;;      (if (quotep tree)
;;          1
;;        (+ 1 (tree-size-list (cdr tree))))))
;;  (defun tree-size-list (trees)
;;    (if (endp trees)
;;        0
;;      (+ (tree-size (car trees))
;;         (tree-size-list (cdr trees))))))

;fixme pass in an interpreted-function-alist?
;(defstub eval-dag3 (dag alist) t)

;this lookup is now safe - doesn't work - missed quotep?
;the keys are symbols
(defun lookup-and-union (keys alist acc)
  (if (endp keys)
      acc
    (let* ((key (car keys))
           (val (lookup-eq-safe key alist)))
      (lookup-and-union (cdr keys)
                        alist
                        (union-equal val acc)))))



;nums is a list of numbers
;returns the largest num less that target, or nil if there is none
;if best-so-far is nil, we haven't found any number less that the target yet
(defun greatest-num-less-than-or-equal (target nums best-so-far)
  (if (endp nums)
      best-so-far
    (let* ((num (car nums)))
      (if (and (<= num target)
               (or (not best-so-far)
                   (< best-so-far num)))
          (greatest-num-less-than-or-equal target (cdr nums) num)
        (greatest-num-less-than-or-equal target (cdr nums) best-so-far)))))

;returns the line number corresponding to the PC
(defun lookup-in-line-number-table (pc line-number-table)
  ;the car is a bit gross - maybe the line number table should contain dotted pairs
  (car (lookup (greatest-num-less-than-or-equal pc (strip-cars line-number-table) nil) line-number-table)))

;returns the nodenum of the core heap, after all set-fields are stripped (will usually be (jvm::heap s0)?
(defun strip-set-field-calls (nodenum heap-dag)
  (declare (xargs :guard (and (dargp-less-than nodenum (len heap-dag))
                              (pseudo-dagp heap-dag))
                  :guard-hints (("Goal" :in-theory (e/d (CADR-BECOMES-NTH-OF-1
                                                         top-nodenum-when-pseudo-dagp)
                                                        ( ALL-<-OF-0-WHEN-NAT-LISTP
                                                          DARGP
                                                          dag-exprp-of-lookup-equal-when-pseudo-dagp
                                                          DAG-EXPRP0))
                                 :use (:instance dag-exprp-of-lookup-equal-when-pseudo-dagp
                                                 (n nodenum)
                                                 (dag heap-dag)
                                                 )))
                  :measure (nfix (+ 1 nodenum))))
  (if (quotep nodenum)
      (er hard? 'strip-set-field-calls "I am surprised to see a constant heap.")
    (let ((expr (lookup nodenum heap-dag)))
      (if (and (call-of 'set-field expr)
               (= 4 (len (dargs expr))))
          (if (consp (darg4 expr)) ;check for quotep
              (er hard? 'strip-set-field-calls "I am surprised to see a constant heap.")
            (if (not (mbt (and (natp nodenum)
                               (< (darg4 expr) nodenum))))
                (er hard? 'strip-set-field-calls "Nodenum ordering violation.")
              (strip-set-field-calls (darg4 expr) heap-dag)))
        nodenum))))

;checks for a pointer field or another thing for which we should make an unchangedness claim
;used in the decompiler
;fixme what about fake fields? array contents, monitor stuff, etc.
(defun make-unchangedness-claimp (class-name-field-id-pair class-table)
  (declare (ignore class-table)) ;fixme
  ;; (declare (xargs :guard (and (class-name-field-id-pairp class-name-field-id-pair) ;should we allow :special-data?
  ;;                             (jvm::class-tablep class-table)))) ;;also need to know that that class and that field exist in the class-table...
  (if (equal class-name-field-id-pair (array-contents-pair)) ;FIXME unless the array elems are pointers?
      nil
    (or ;(equal class-name-field-id-pair (array-type-pair)) ;don't want to guess that the array contents are unchanged.
        (let ((class-name (car class-name-field-id-pair)))
          (and (stringp class-name) ;excludes the symbol 'special-data
               (not (eq :special-data class-name)) ;now we are using the keyword :special-data
               (or ;(equal "ARRAY" class-name) ;fixme this covers the array type, which is not a pointer
                (let* ((field-id (cdr class-name-field-id-pair))
;                       (class-info (g class-name class-table))
 ;                      (field-info-alist (class-decl-non-static-fields ... class-info))
  ;                     (field-info (lookup-equal field-id field-info-alist))
                       (field-type (jvm::field-id-type field-id)))
                  (jvm::reference-typep field-type) ;it's an array or class or interface type...
                  )))))))

;fixme rename these to indicate that we are only doing this for instance fields (not static fields):

;now these claims allow the "addresses" to be NULL:

(defun addressp-claims-for-fields (field-info-alist
                                   address-term heap-core class-name)
  (if (endp field-info-alist)
      nil
    (let* ((entry (first field-info-alist))
           (field-id (car entry))
;           (field-info (cdr entry))
           (type (jvm::field-id-type field-id)))
      (if (jvm::reference-typep type)
          (cons `(address-or-nullp (get-field ,address-term ,(kwote (cons class-name field-id)) ,heap-core))
                (addressp-claims-for-fields (rest field-info-alist) address-term heap-core class-name))
        (addressp-claims-for-fields (rest field-info-alist)
                                    address-term heap-core class-name)))))

(defun addressp-claims-for-fields-of-class (class-name class-table-map address-term heap-core)
  (let* ((class-decl (g class-name class-table-map))
         (field-info-alist (jvm::class-decl-non-static-fields class-decl)))
    (addressp-claims-for-fields field-info-alist ;class-table-map
                                address-term heap-core class-name)))

(defun addressp-claims-for-fields-of-classes (all-class-names class-table-map address-term heap-core)
  (if (endp all-class-names)
      nil
    (append (addressp-claims-for-fields-of-class (first all-class-names) class-table-map address-term heap-core)
            (addressp-claims-for-fields-of-classes (rest all-class-names) class-table-map address-term heap-core))))

(defun addressp-claims-for-fields-of-object (class-name class-table-map address-term heap-core)
  (if (not (jvm::class-namep class-name)) ;excludes stuff like (:array :int)
      nil
    (let* ((superclass-names (get-superclasses class-name class-table-map))
           (all-class-names (cons class-name superclass-names))
           )
      (addressp-claims-for-fields-of-classes all-class-names class-table-map address-term heap-core))))

;nodenum points to a heap
;fffixme i hope all irrelevant set-fields will be removed before this executes - otherwise these assumptions may contradict
;can this blow up?
;pass in ifns?
;; dRreturns (mv erp invars state).
;(skip-proofs
(defun invariants-about-heap-aux (nodenum dag heap-core class-table-map extra-invarsp interpreted-function-alist acc state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (quotep nodenum)
      (mv (erp-t)
          (hard-error 'invariants-about-heap-aux "I am surprised to see a constant heap." nil)
          state)
    (let ((expr (lookup nodenum dag)))
      (if (not (call-of 'set-field expr))
          ;;it's not a call to set-field, so we've reached the "heap core"
          (mv (erp-nil) acc state)
        ;;expr is of the form (set-field AD CLASS-FIELD-PAIR VALUE HEAP):
        (let* ((address-term (farg1 expr)) ;fixme is this a term or nodenum? seems like a nodenum
               (dummy nil ;(cw "Expr: ~x0. DAG: ~x1." expr dag)
                      )
               (class-invars (if (equal ''(:SPECIAL-DATA . :CLASS) (farg2 expr))
                                 (let* ((quoted-class-name (check-quotep (farg3 expr)))
                                        (class-name (unquote quoted-class-name))
                                        (address-term (dag-to-term-aux address-term dag))
                                        (addressp-claims-for-fields (addressp-claims-for-fields-of-object class-name class-table-map address-term heap-core))
                                        )
                                   (append addressp-claims-for-fields
                                           `((equal (get-field ,address-term
                                                               '(:SPECIAL-DATA . :CLASS)
                                                               ,heap-core)
                                                    ,quoted-class-name))))
                               nil)))
          (declare (ignore dummy))
          (mv-let (erp array-length-invars state)
            ;;invariant about array length (new):
            (if (and (equal (array-contents-pair) (safe-unquote (farg2 expr)))
                     extra-invarsp ;todo is this always true? i think it's false for the lifter currently
                     )
                (mv-let (erp len-dag state)
                  (quick-simp-composed-term-and-dag '(len replace-me) 'replace-me
                                                    (get-subdag (farg3 expr) dag)
                                                    :rule-alist *get-local-axe-rule-alist*
                                                    :remove-duplicate-rulesp nil)
                  (if erp
                      (mv erp nil state)
                    (mv (erp-nil)
                        (and nil ;ffixme put back
                             `((equal (len (get-field ,(dag-to-term-aux (farg1 expr) ;the address term - could this ever blow up?
                                                                        dag)
                                                      ',(array-contents-pair)
                                                      ,heap-core))
                                      ;;(len ,(dag-to-term-aux (farg3 expr) dag))
                                      ,(wrap-dag-in-dag-val len-dag interpreted-function-alist))))
                        state)))
              (mv (erp-nil) nil state))
            (if erp
                (mv erp nil state)
              (mv-let
                (erp non-null-invars state)
                (let* ((class-name-field-id-pair (safe-unquote (farg2 expr)))
                       (class-name (car class-name-field-id-pair)))
                  (if (or (eq :special-data class-name)
                          (equal "ARRAY" class-name))
                      (mv (erp-nil) nil state)
                    (let* ((field-id (cdr class-name-field-id-pair))
                           ;;(dummy (cw "Checking for nullity: node: ~x0 pair: ~x1~%" (farg1 expr) (farg2 expr)))
                           ;; (class-info (g class-name class-table-map))
                           ;; (field-info-alist (jvm::class-decl-non-static-fields class-info))
                           ;; (field-info (lookup-equal field-id field-info-alist))
                           (type (jvm::field-id-type field-id))
                           ;;(dummy2 (cw "type ~x0~%" type))
                           (reference-fieldp (jvm::reference-typep type)))
                      ;; (declare (ignore dummy dummy2))
                      (if (not reference-fieldp)
                          ;; Not a reference field, so skip trying to prove it non-null:
                          (mv (erp-nil) nil state)
                        ;; It is a reference field, so try to prove the value written into that field to be non-null.  If successful, guess the invariant that the value in that field always stays non-null:
                        (mv-let (erp non-null-dag state)
                          (quick-simp-composed-term-and-dag '(not (null-refp replace-me)) 'replace-me
                                                      (get-subdag (farg3 expr) dag) ;the value written into the field

                                                      :rule-alist *address-axe-rule-alist* ;fixme what rules should we use here? ;;ttodo: add nullref of null-ref rule here
                                                      :remove-duplicate-rulesp nil)
                          (if erp
                              (mv erp nil state)
                            (let* ((ad-term (dag-to-term-aux (farg1 expr) ;the address term - could this ever blow up?
                                                             dag))
                                   (get-field-term `(get-field ,ad-term ,(farg2 expr) ,heap-core)))
                              (if (equal non-null-dag *t*)
                                  (prog2$ (cw "(Adding non-null invariant for field: ~x0.)~%" get-field-term)
                                          (mv (erp-nil)
                                              (list `(not (null-refp ,get-field-term)))
                                              state))
                                (prog2$ (cw "(Non-null dag for ~x0 rewrote to: ~x1.)~%" get-field-term non-null-dag)
                                        (mv (erp-nil)
                                            nil state))))))))))
                (if erp
                    (mv erp nil state)
                  (prog2$ nil ;(cw "making invars for pair ~x0~%" (farg2 expr))
                          (invariants-about-heap-aux
                           (farg4 expr)
                           dag heap-core class-table-map extra-invarsp
                           interpreted-function-alist
                           (append non-null-invars
                                   class-invars
                                   array-length-invars
;fixme put back!
                                   ;;                          ;;invariant about array type (new):
                                   ;;                          (if (equal (array-type-pair) (safe-unquote (farg2 expr)))
                                   ;;                              `((equal (get-field ,(dag-to-term-aux (farg1 expr) dag) ;the address term
                                   ;;                                                  ',(array-type-pair)
                                   ;;                                                  ,heap-core)
                                   ;;                                       ,(check-quotep (farg3 expr))))
                                   ;;                            nil)

                                   ;;unchangedness claim (new):
                                   (if (make-unchangedness-claimp (safe-unquote (farg2 expr)) class-table-map)
                                       (and extra-invarsp
                                            `((equal (get-field ,(dag-to-term-aux (farg1 expr) dag) ;the address term
                                                                ,(farg2 expr)
                                                                ,heap-core)
;fixme call dag-val..
                                                     ,(dag-to-term-aux (farg3 expr) dag))))
                                     nil)
                                   acc)
                           state)))))))))))
;)

;fixme pass in hyps?
;also now includes unchangedness claims about pointer fields (and some other fields?)
;; Returns (mv erp invars state).
;generates claims about the classes of objects in the heap of state-var, based on state-dag (which mentions previous state vars)
;fixme also adapt any hyps about the heap?
;fixme also add unchangedness hyps about locals.. - analyze the code segment?
(defun invariants-about-heap (state-dag state-var class-table-map extra-invarsp interpreted-function-alist state)
  (declare (xargs :mode :program :stobjs (state)))
  (mv-let (erp heap-dag state)
    (get-heap-dag state-dag state) ;if it's a make-state, we could just extract the right component
    (if erp
        (mv erp nil state)
      (let* ((heap-dag-top-nodenum (top-nodenum heap-dag))
             (heap-core-nodenum (strip-set-field-calls heap-dag-top-nodenum heap-dag))
             (heap-core-term (dag-to-term-aux heap-core-nodenum heap-dag)))
        (if (not (and (call-of 'jvm::heap heap-core-term)
                      (variablep (farg1 heap-core-term)) ;check that it's one of the state vars?
                      ))
            (mv (erp-t)
                (hard-error 'invariants-about-heap "unexpected heap core: ~x0." (acons #\0 heap-core-term nil))
                state)
          (invariants-about-heap-aux heap-dag-top-nodenum heap-dag `(jvm::heap ,state-var) class-table-map
                                     extra-invarsp interpreted-function-alist
                                     nil state))))))

;i think this handles long locals okay (they take up 2 consecutive slots but are always referenced using the lesser index)
;; Returns (mv erp invars state).
;fffixme handle unchanged static fields
;should we guess that the classes of the objects pointed to don't change, even if the pointers themselves change?
(defun make-unchanged-local-invars (local-slot-num ;counts down to -1
                                    locals-stored-into
                                    state-var
                                    loop-top-state-dag interpreted-function-alist
                                    acc state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (not (natp local-slot-num))
      (mv (erp-nil) acc state)
    (mv-let
      (erp initial-value-of-local-dag state)
      (get-local-dag local-slot-num loop-top-state-dag state)
      (if erp
          (mv erp nil state)
        (make-unchanged-local-invars (+ -1 local-slot-num)
                                     locals-stored-into
                                     state-var
                                     loop-top-state-dag
                                     interpreted-function-alist
                                     (if (member-equal local-slot-num locals-stored-into)
                                         ;; the local is stored into (by some instruction), so it is not unchanged:
                                         acc
                                       (cons `(equal (jvm::nth-local ',local-slot-num (jvm::locals (jvm::thread-top-frame (th) ,state-var)))
                                                     ;;,(dag-to-term initial-value-of-local-dag)
                                                     ,(wrap-dag-in-dag-val initial-value-of-local-dag interpreted-function-alist))
                                             acc))
                                     state)))))

;these help with static analysis:

;move to JVM dir?
;returns the local slot number stored into by the instruction
;fixme what about floats and doubles?
(defun local-stored-into-or-nil (inst)
  (let ((opcode (first inst)))
    (case opcode
          (:astore (farg1 inst))
          (:astore_0 0)
          (:astore_1 1)
          (:astore_2 2)
          (:astore_3 3)

          (:istore (farg1 inst))
          (:istore_0 0)
          (:istore_1 1)
          (:istore_2 2)
          (:istore_3 3)

          (:lstore (farg1 inst)) ;TODO: What about the fact that these affect 2 slots?
          (:lstore_0 0)
          (:lstore_1 1)
          (:lstore_2 2)
          (:lstore_3 3)

          (:fstore (farg1 inst))
          (:fstore_0 0)
          (:fstore_1 1)
          (:fstore_2 2)
          (:fstore_3 3)

          (:dstore (farg1 inst)) ;TODO: What about the fact that these affect 2 slots?
          (:dstore_0 0)
          (:dstore_1 1)
          (:dstore_2 2)
          (:dstore_3 3)

          (:iinc (farg1 inst))

          (otherwise nil))))

;fixme some locals may not be active yet, or will they all have been initialized?
(defun locals-stored-into (pcs code acc)
  (if (endp pcs)
      acc
    (let* ((pc (first pcs))
           (inst (lookup pc code)))
      (locals-stored-into (rest pcs)
                          code
                          (let ((local-stored-into-or-nil (local-stored-into-or-nil inst)))
                            (if local-stored-into-or-nil
                                (add-to-set-eql local-stored-into-or-nil acc)
                              acc))))))

;returns (mv erp old-fact new-fact state), or (mv nil nil state) if nothing was changed
;facts are moved into acc
;fixme don't stop iterating after a change? keep a change flag?
(defun find-a-fact-to-push-back (facts-to-push-back print acc hyps state)
  (declare (xargs :mode :program :stobjs (state))
           (ignorable print))
  (if (endp facts-to-push-back)
      (mv nil nil nil state) ;failed to push-back anything
    (b* ((fact (first facts-to-push-back))
         ((mv erp result-dag-lst state)
          (simp-term fact
                     :rules nil ;no rules
                     :assumptions (append hyps (rest facts-to-push-back) acc)
                     :check-inputs nil))
         ((when erp)
          (mv erp nil nil state))
         (result (dag-to-term result-dag-lst)) ;fixme could this ever blow up?
         )
      (if (equal result fact)
          ;;no change, so move fact to acc:
          (find-a-fact-to-push-back (rest facts-to-push-back) print (cons fact acc) hyps state)
        ;;fact was push-backed:
        (mv nil fact result state)))))

;fixme compare to improve-invars
;fixme handle boolands?
;returns (mv erp new-facts state) where new-facts is a set of facts whose conjunction is equal to the conjunction of facts
(defun push-back-facts (facts hyps print state)
  (declare (xargs :mode :program :stobjs (state)))
  (mv-let (erp old-fact new-fact state)
    (find-a-fact-to-push-back facts print nil hyps state)
    (if erp
        (mv erp nil state)
      (if (not old-fact)
          (mv nil facts state)
        (if (equal *t* new-fact)
; if the fact became t, drop it... (fixme would this ever happen if we are trying to push-back? maybe we are doing more than just push-backing - also eliminating redundancy..)
            (push-back-facts (remove-equal old-fact facts) hyps print state)
          ;; fixme what if the fact get rewritten to nil?
          (push-back-facts (cons new-fact (remove-equal old-fact facts)) hyps print state))))))

;; ;fixme may also need to adapt arefp invars, because those imply addressp.  and what else?
;; ;this just changes the heap part of the hyp (the locals, say, are not the same for s1 as for s2)
;; ;now also adapts non-null hyps
;; (defun adapt-address-hyps (hyps previous-state-var state-var)
;;   (if (endp hyps)
;;       nil
;;     (let ((hyp (first hyps)))
;;       (if (or (and (consp hyp)
;;                    (eq 'address-or-nullp (ffn-symb hyp)))
;;               (and (consp hyp)
;;                    (eq 'not (ffn-symb hyp))
;;                    (consp (farg1 hyp))
;;                    (eq 'NULL-REFP (ffn-symb (farg1 hyp)))))
;;           ;;TODO: Consider replacing the static field map of the old state var with the corresponding one of state-var
;;           (let ((new-hyp (replace-in-term2 hyp (acons `(jvm::heap ,previous-state-var) `(jvm::heap ,state-var) nil))))
;;             (if (equal new-hyp hyp)
;;                 ;;skip, because the new hyp is the same as the old one and so doesn't mention the new state var
;;                 (adapt-address-hyps (rest hyps) previous-state-var state-var)
;;               (cons new-hyp
;;                     (adapt-address-hyps (rest hyps) previous-state-var state-var))))
;;         (adapt-address-hyps (rest hyps) previous-state-var state-var)))))

;; Returns (mv erp invars state), where invars may contain a non-nullity invar.
(defun maybe-non-null-invar-for-local (local-num state-var loop-top-state-dag hyps state)
  (declare (xargs :mode :program :stobjs (state)))
  (mv-let
    (erp non-null-result-dag state)
    (quick-simp-composed-term-and-dag `(not (null-refp (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) replace-me))))) 'replace-me
                                      loop-top-state-dag
                                      :rule-alist *state-component-extraction-axe-rule-alist*
                                      :assumptions hyps
                                      :remove-duplicate-rulesp nil)
    (if erp
        (mv erp nil state)
      (if (equal *t* non-null-result-dag)
          (let ((non-nullity-invar `(not (null-refp (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) ,state-var)))))))
            (prog2$ (cw "(Adding non-null invariant for local ~x0: ~x1)~%" local-num non-nullity-invar)
                    (mv (erp-nil) (list non-nullity-invar) state)))
        (prog2$ (cw "(Failed to prove non-nullity invar for local ~x0.  Simplified dag: ~x1.)~%" local-num non-null-result-dag)
                (mv (erp-nil)
                    nil ;failure
                    state))))))

;; Returns (mv erp invars state), where invars may have a been extended with a non-negativity invar.
(defun maybe-add-non-negative-invar-for-local (local-num width state-var loop-top-state-dag hyps invars options print state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((extra-rules (g :extra-rules options))
       (remove-rules (g :remove-rules options))
       ;;(- (cw "Using extra rules: ~x0.~%" extra-rules))
       )
    (mv-let
      (erp result-dag state)
      (quick-simp-composed-term-and-dag `(not (sbvlt ',width (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) replace-me))) '0)) 'replace-me loop-top-state-dag
                                        :rule-alist (remove-from-rule-alist remove-rules (add-to-rule-alist! extra-rules *state-component-extraction-axe-rule-alist* (w state)))
                                        :assumptions hyps
                                        :monitor (g :monitor options)
                                        :remove-duplicate-rulesp nil)
      (if erp
          (mv erp nil state)
        (if (equal *t* result-dag)
            (let ((non-negative-invar `(not (sbvlt ',width (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) ,state-var))) '0))))
              (prog2$ (cw "(Adding non-negative invariant for local ~x0: ~x1)~%" local-num non-negative-invar)
                      (mv (erp-nil) (cons non-negative-invar invars) state)))
          (progn$ (cw "(Not adding non-negative invar for local ~x0 (failed to prove that it holds initially).~%" local-num)
                  (and print (prog2$ (cw "Simplified form:")
                                     (if (dag-or-quotep-size-less-thanp result-dag 1000)
                                         (cw " ~x0" (dag-to-term result-dag))
                                       (print-list result-dag))))
                  (cw ")~%")
                  (mv (erp-nil)
                      invars ;failure
                      state)))))))

;; Returns (mv erp dag state).
(defun extract-class-of-local (local-num state-dag hyps state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (quick-simp-composed-term-and-dag `(get-class (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) replace-me))) (jvm::heap replace-me)) 'replace-me
                                    state-dag
                                    :rule-alist *state-component-extraction-axe-rule-alist*
                                    :assumptions hyps
                                    :remove-duplicate-rulesp nil))

;; (defun extract-heap (state-dag hyps state)
;;   (declare (xargs :stobjs (state)
;;                   :mode :program))
;;   (quick-simplify-dag3
;;    (compose-term-and-dag `(jvm::heap replace-me) 'replace-me state-dag)
;;    *state-component-extraction-axe-rule-alist*
;;    :assumptions hyps
;;    :remove-duplicate-rulesp nil))

;; Returns (mv erp heap-dag state).
(defun extract-heap-dag (state-dag ; hyps
                         state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (quick-simp-composed-term-and-dag '(jvm::heap s) 's state-dag
                                    :rules (append (get-local-rules)
                                                   '(jvm::myif-of-set-field-1-strong
                                                     jvm::myif-of-set-field-2-strong))))

;; Returns (mv erp invars state).
(defun maybe-array-ref-invar-for-local (local-num state-var loop-top-state-dag hyps state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((mv erp class-result-dag state)
        (extract-class-of-local local-num loop-top-state-dag hyps state))
       ((when erp) (mv erp nil state))
       (- (cw "(Class of local ~x0: ~x1.)~%" local-num class-result-dag))
       ((when (not (quotep class-result-dag)))
        (prog2$ (cw "(Not adding array-refp invariant for local ~x0 (could not resolve class))~%" local-num)
                (mv (erp-nil) nil state)))
       (class (unquote class-result-dag))
       ((when (not (jvm::array-typep class)))
        (prog2$ nil ;(cw "(Not adding array-refp invariant for local ~x0 (not an array))~%" local-num)
                (mv (erp-nil) nil state)))
       ((mv erp dimensions-result-dag state)
        (quick-simp-composed-term-and-dag `(get-array-dimensions-of-ref (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) replace-me))) (jvm::heap replace-me)) 'replace-me
                                          loop-top-state-dag
                                          :rule-alist *state-component-extraction-axe-rule-alist*
                                          :assumptions hyps
                                          :remove-duplicate-rulesp nil))
       ((when erp) (mv erp nil state))
       (- (cw "(Array dimensions of local ~x0: ~x1.)~%" local-num dimensions-result-dag))
       ((when (not (quotep dimensions-result-dag))) ;todo: relax this and perhaps the similar check for element type (but turn the dags into terms -- if they are not too big)
        (prog2$ (cw "(Not adding array-refp invariant for local ~x0 (non-constant dimensions -- could add support for that))~%" local-num)
                (mv (erp-nil) nil state)))
       ;; ((mv heap-dag state) (extract-heap loop-top-state-dag hyps state))
       ;; ;;TODO: What if the heap term is big?!
       ;; (heap-term (dag-to-term heap-dag))
       (invar `(ARRAY-REFP (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) ,state-var)))
                               ,dimensions-result-dag
                               ',(jvm::get-array-element-type class) ;,element-type-result-dag
                               (jvm::heap ,state-var)))
       (- (cw "(Adding array-refp invariant for local ~x0: ~x1)~%" local-num invar)))
      (mv (erp-nil) (list invar) state)))

;todo: add bit vector types, array-refp claims, etc.
;; Returns (mv erp type-invars-for-locals state).
(defun make-type-invars-for-local (local-num type state-var loop-top-state-dag hyps options print state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (jvm::reference-typep type)
      (b* ( ;;we always put in the address-or-nullp invar
           (address-or-nullp-invars (list `(address-or-nullp (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) ,state-var))))))
           ((mv erp non-null-invars state)
            ;; we put in the non-null invar, if we can show it holds initially:
            (maybe-non-null-invar-for-local local-num state-var loop-top-state-dag hyps state))
           ((when erp) (mv erp nil state))
           ;; If it's an array reference, we put in invars about the dimensions and element-type (in the form of a call to array-refp)
           ((mv erp array-ref-invars state)
            (maybe-array-ref-invar-for-local local-num state-var loop-top-state-dag hyps state))
           ((when erp) (mv erp nil state)))
        (mv (erp-nil)
            (append address-or-nullp-invars
                    non-null-invars
                    array-ref-invars)
            state))
    (if (eq :int type) ;TODO: handle other types!
        (let ((invars (list `(unsigned-byte-p '32 (jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) ,state-var)))))))
          (maybe-add-non-negative-invar-for-local local-num 32 state-var loop-top-state-dag hyps invars options print state))
      (mv (erp-nil) nil state))))

;; Returns (mv erp type-invars-for-locals state).
(defun make-type-invars-for-locals-aux (local-variable-table loop-pc state-var loop-top-state-dag hyps options print state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp local-variable-table)
      (mv (erp-nil) nil state)
    (let* ((entry (first local-variable-table))
           (index (nth 0 entry)) ;the local slot number
           (start-pc (nth 1 entry))
           (end-pc (nth 2 entry))
           ;;(name (nth 3 entry))
           (type (nth 4 entry)))
      (if (and (<= start-pc loop-pc)
               (<= loop-pc end-pc))
          (mv-let
            (erp invars1 state)
            (make-type-invars-for-local index type state-var loop-top-state-dag hyps options print state)
            (if erp
                (mv erp nil state)
              (mv-let
                (erp invars2 state)
                (make-type-invars-for-locals-aux (rest local-variable-table) loop-pc state-var loop-top-state-dag hyps options print state)
                (if erp
                    (mv erp nil state)
                  (mv (erp-nil) (append invars1 invars2) state)))))
        ;;this table entry doesn't cover the current PC:
        (make-type-invars-for-locals-aux (rest local-variable-table) loop-pc state-var loop-top-state-dag hyps options print state)))))

;; TODO: Analyze loop-top-state-dag and skip locals that are not initialized (they may sometimes be in scope according to the local variable table but not yet initialized).
;; Returns (mv erp type-invars-for-locals state).
;This uses state because it tries to prove that references are non-null
(defun make-type-invars-for-locals (local-variable-table loop-pc state-var loop-top-state-dag hyps options print state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (not local-variable-table)
      (prog2$ (cw "WARNING: local variable table is empty. Not generating type invars for locals.~%") ;only print this if there are some local vars
              (mv (erp-nil) nil state))
    (make-type-invars-for-locals-aux local-variable-table loop-pc state-var loop-top-state-dag hyps options print state)))

;TODO: does this have to preserve EQUAL or just IFF?
;TODO: Don't we have other versions of this?
(defun get-conjuncts-from-term (term)
  (if (call-of 'booland term)
      (append (get-conjuncts-from-term (farg1 term))
              (get-conjuncts-from-term (farg2 term)))
    (if (call-of 'not term)
        (let ((arg (farg1 term)))
          (if (call-of 'not arg)
              (get-conjuncts-from-term (farg1 arg)) ;remove double negation
            (if (call-of 'boolor arg) ;(not (boolor <X> <Y>)) = (and (not <X>) (not <Y>))
                (append (get-conjuncts-from-term `(not ,(farg1 arg)))
                        (get-conjuncts-from-term `(not ,(farg2 arg))))
              (list term))))
      ;;todo: look for (if x y nil) pattern that comes from macro expanding and?
      (list term))))

(assert-event (equal (get-conjuncts-from-term '(not (not x))) (list 'x)))
(assert-event (equal (get-conjuncts-from-term '(not (boolor x y))) '((not x) (not y))))
(assert-event (equal (get-conjuncts-from-term '(booland x y)) '(x y)))



(defun vars-in-term-include-onlyp (term vars)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp vars))))
  (subsetp-eq (GET-VARS-FROM-TERM term) vars))

(defun vars-in-terms-include-onlyp (terms vars)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (symbol-listp vars))))
  (if (endp terms)
      t
    (and (vars-in-term-include-onlyp (first terms) vars)
         (vars-in-terms-include-onlyp (rest terms) vars))))

(defun vars-in-term-lists-include-onlyp (term-lists vars)
  (declare (xargs :guard (and (pseudo-term-list-listp term-lists)
                              (symbol-listp vars))))
  (if (endp term-lists)
      t
    (and (vars-in-terms-include-onlyp (first term-lists) vars)
         (vars-in-term-lists-include-onlyp (rest term-lists) vars))))

;; (defun all-all-arities-okayp (term-lists state)
;;   (declare (xargs :guard (pseudo-term-list-listp term-lists)
;;                   :stobjs state))
;;   (if (endp term-lists)
;;       t
;;     (and (all-arities-okayp (first term-lists) state)
;;          (all-all-arities-okayp (rest term-lists) state))))


;; ;; The :invariant-alist should map loop-designators to lists of terms over the var 'state-var. TODO: can't we just use s1, etc.?
;; ;; TODO: what about something like \old ?
;; (defun invariant-alistp (alist state)
;;   (declare (xargs :stobjs state)
;;            (ignore state))
;;   (and (alistp alist)
;;        (all-loop-designatorp (strip-cars alist))
;;        (let ((invar-lists (strip-cdrs alist)))
;;          (and (all-untranslated-term-listp invar-lists)
;;               t
;;               ;; can't do this because translate-terms is in program mode:
;; ;;               (let ((translated-invars (map-translate-terms invars-lists 'invariant-alistp (w state)))
;; ;;                     )
;; ;; ;(vars-in-term-lists-include-onlyp (strip-cdrs alist) '(state-var)) ;; too strict: we need to talk about previous state-vars too
;; ;;                 (if (all-all-arities-okayp translated-invars state)
;; ;;                     t
;; ;;                   (prog2$ (cw "ERROR: Bad arity for term in invariant-alist!")
;; ;;                           nil)))
;;               ))))

;returns a measure or :skip or :auto (means use with-auto-termination tool) or :acl2 (means let ACL2 guess the measure) or nil
(defun measure-for-loop (loop-function-name loop-designator options)
  (let ((measures-option (g :measures-option options)))
    (if (eq :skip measures-option)
        :skip
      (if (eq :auto measures-option)
          :auto
        (if (eq :acl2 measures-option)
            :acl2
          (lookup-loop-function loop-function-name loop-designator measures-option :acl2) ;this might be :skip or :auto or :acl2
          )))))

(mutual-recursion
 (defun extract-rule-names-from-event (event)
   (if (call-of 'defthm event)
       (list (farg1 event))
     (if (call-of 'defthmd event)
         (prog2$ (cw "(Note: Not adding a rule for ~x0, because it is a defthmd.)~%" (farg1 event))
                 nil)
       (if (call-of 'defun event)
           (list (farg1 event))
         (if (call-of 'defund event)
             (prog2$ (cw "(Note: Not adding a rule for ~x0, because it is a defund.)~%" (farg1 event))
                     nil)
           (if (call-of 'skip-proofs event)
               (extract-rule-names-from-event (farg1 event))
             (if (call-of 'progn event)
                 (extract-rule-names-from-events (fargs event))
               (if (call-of 'encapsulate event)
                   (extract-rule-names-from-events (rest (fargs event))) ;skip the signatures
                 ;; TODO: Error or warning here!
                 nil))))))))
 (defun extract-rule-names-from-events (events)
   (if (endp events)
       nil
     (append (extract-rule-names-from-event (first events))
             (extract-rule-names-from-events (rest events))))))

(defun PRINT-LIST-with-indent-aux (LST indent-string)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      nil
    (progn$ (cw "~s0" indent-string)
            ;TODO: Is there a way to pretty print a form, with no newline before or after?
            (cw "~y0" (first lst))
            ;; ;; Print a new line for all but the last element:
            ;; (if (endp (cdr lst))
            ;;     nil
            ;;   (cw "~%"))
            (PRINT-LIST-with-indent-aux (rest LST) indent-string))))

(DEFUN PRINT-LIST-with-indent (LST indent-string)
  (declare (xargs :guard (and (true-listp lst)
                              (stringp indent-string))))
  (IF (CONSP LST)
      (PROGn$ (cw "~s0" indent-string)
              (CW "(~y0" (CAR LST))
              (PRINT-LIST-with-indent-aux (CDR LST) (concatenate 'string " " indent-string))
              (CW ")"))
      (CW "nil")))

(defund make-axe-rules-from-theorem-safe (theorem-body rule-symbol print wrld)
  (declare (xargs :guard (symbolp rule-symbol)
                  :mode :program))
  (let ((theorem-body (translate-term theorem-body 'make-axe-rules-from-theorem-safe wrld)))
    (if (symbolp rule-symbol) ;why check this here?
        (make-axe-rules-from-theorem! theorem-body rule-symbol
                                 nil ;rule-classes
                                 (known-booleans wrld)
                                 print
                                 wrld)
      (er hard? 'make-axe-rules-from-theorem-safe "Bad input: ~x0 is not a symbol." rule-symbol))))

;returns a list of nodenums
(defun dag-nodes-that-call (fns dag-lst)
  (if (endp dag-lst)
      nil
    (let* ((entry (first dag-lst))
           (expr (cdr entry)))
      (if (and (consp expr)
               (member-eq (ffn-symb expr) fns))
          (cons (car entry) ;the nodenum
                (dag-nodes-that-call fns (rest dag-lst)))
        (dag-nodes-that-call fns (rest dag-lst))))))

(defun terms-mentioned-in-possibly-negated-nodenums (context dag-lst)
  (if (endp context)
      nil
    (let* ((item (first context))
           (nodenum (if (consp item) (farg1 item) item))
           (term (dag-to-term-aux nodenum dag-lst)) ;todo: watch out for blowup
           )
      (cons (if (consp item) `(not ,term) term)
            (terms-mentioned-in-possibly-negated-nodenums (rest context) dag-lst)))))

(defun terms-mentioned-in-context (context dag-lst)
  (if (false-contextp context)
      (list :false) ;might as well include this
    (terms-mentioned-in-possibly-negated-nodenums context dag-lst)))

(defun get-terms-from-node-contexts-aux (nodenums context-array-name context-array dag-lst)
  (if (endp nodenums)
      nil
    (let* ((nodenum (first nodenums))
           (context (aref1 context-array-name context-array nodenum))
           )
      (union-equal (terms-mentioned-in-context context dag-lst)
                   (get-terms-from-node-contexts-aux (rest nodenums) context-array-name context-array dag-lst)))))

(defun get-terms-from-node-contexts (nodenums dag-lst)
  (let* ((dag-len (len dag-lst))
         (dag-array (make-into-array 'dag-array dag-lst))
         (context-array (make-full-context-array 'dag-array dag-array dag-len))
         (terms (get-terms-from-node-contexts-aux nodenums 'context-array context-array dag-lst))
         )
    terms))

(defun strip-nots-from-terms (terms)
  (declare (xargs :guard (true-listp terms)))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (cons (if (and (call-of 'not term)
                     (consp (cdr term)))
                (farg1 term)
              term)
            (strip-nots-from-terms (rest terms))))))

(defun maybe-print-info-on-exception-branches (dag-lst)
  (let* ((exception-nodenums (dag-nodes-that-call (list 'jvm::obtain-and-throw-exception) dag-lst)))
    (and exception-nodenums
         (let* ((governors (get-terms-from-node-contexts exception-nodenums dag-lst))
                (governors (strip-nots-from-terms governors))
                (governors (remove-duplicates-equal governors)))
           (cw "~%NOTE: Exception branches are present, governed by these conditions (possibly negated).  Consider trying to rewrite these tests, possibly by adding some assumptions: ~x0~%"
               governors)))))

;; Returns (mv erp initialized-state-dag state)
(defun initialize-classes-in-s0 (class-names
                                 initialized-class-names ;classes already initialized
                                 class-table-map
                                 extra-rules
                                 monitored-rules
                                 state)
  (declare (xargs :guard (and (string-listp class-names)
                              (string-listp initialized-class-names)
                              (symbol-listp extra-rules))
                  :mode :program ;todo
                  :stobjs (state)))
  (b* (((mv erp state-dag) ;; (dagify-term 's0) ;this was bad when no classes were to be initialized because the hyp about (jvm::initialized-classes s0) never fired..
        (dagify-term2 `(JVM::MAKE-STATE (JVM::THREAD-TABLE s0) ;fixme do we need a dummy frame below the current one?
                                        (JVM::HEAP s0)
                                        (JVM::CLASS-TABLE s0)
                                        (JVM::HEAPREF-TABLE s0)
                                        (JVM::monitor-TABLE s0)
                                        (JVM::STATIC-FIELD-MAP s0)
                                        ',initialized-class-names ;TODO Without the quote the decompiler crashed.
                                        (JVM::intern-table s0))))
       ((when erp) (mv erp nil state)))
    (initialize-classes class-names
                        '(th)
                        state-dag
                        ;; TODO: Instead pass in hyps?:
                        (append (standard-hyps-basic 's0)
                                (list '(jvm::jvm-statep s0))
                                (class-table-hyps 's0 class-table-map))
                        extra-rules
                        monitored-rules
                        ;;class-table-map
                        state)))

;call it loop-info-alist ?
(defun make-loop-infos (loops class-name method-name method-descriptor)
  (if (endp loops)
      nil
    (let* ((loop (car loops))
           (header-pc (g-safe :header loop))
           (pcs (g-safe :pcs loop))
           (loop-designator (make-pc-designator class-name method-name method-descriptor header-pc)))
      (acons loop-designator pcs (make-loop-infos (cdr loops) class-name method-name method-descriptor)))))

(defun get-loops-for-method (method-entry class-name)
  (let* ((name-and-descriptor (car method-entry))
         (name (car name-and-descriptor))
         (descriptor (cdr name-and-descriptor))
         (method-info (cdr method-entry))
         (native-flag (jvm::method-nativep method-info))
         (abstract-flag (jvm::method-abstractp method-info)))
    (if (or native-flag abstract-flag)
        nil ;native and abstract methods don't have any code
      (b* (;;(- (cw " (Getting loops for method ~x0~x1: " name descriptor))
           (program (lookup-eq-safe :program method-info))
           (loops (decompose-into-loops program))
           (loop-infos (make-loop-infos loops class-name name descriptor))
           ;;(- (cw " Found ~x0 loops.)~%" (len loop-infos)))
           )
        loop-infos))))

(defun get-loops-for-methods (methods class-name)
  (if (endp methods)
      nil
    (append (get-loops-for-method (car methods) class-name)
            (get-loops-for-methods (cdr methods) class-name))))

(defun get-loops-from-class (class-name class-info)
  (progn$ ; (cw "(Getting loops for class ~x0:~%" class-name)
          (let* ((methods (jvm::class-decl-methods class-info))
                 (loops (get-loops-for-methods methods class-name)))
            (progn$ ;; (cw ")~%")
                    loops))))

(defun get-loops-from-classes-aux (class-alist)
  (if (endp class-alist)
      nil
    (let* ((entry (first class-alist))
           (class-name (car entry))
           (class-info (cdr entry)))
      (append (get-loops-from-class class-name class-info)
              (get-loops-from-classes-aux (rest class-alist))))))

;; Returns an alist from loop headers (which are loop-designators) to lists of PCs in the corresponding loops.
(defun get-loops-from-classes (class-alist)
  (prog2$ (cw "(Analyzing classes for loops:~%")
          (let ((loop-alist (get-loops-from-classes-aux class-alist)))
            (prog2$ (cw "Done analyzing classes for loops.)~%")
                    loop-alist))))

;; (defun make-opener-theorems-for-n (tag n)
;;   (let* ((tag (mypackn (list tag '- (nat-to-string n))))
;;          (unroll-name (mypackn (list tag '-unroll)))
;;          (base-case-name (mypackn (list tag '-base-case)))
;;          (exit-test-name (mypackn (list tag '-exit-test)))
;;          ;(base-name (mypackn (list tag '-base)))
;;          (update-name (mypackn (list tag '-update)))
;;          )
;;     `()))

;; ;loop numbers start at 1
;; (defun make-opener-theorems (tag n)
;;   (declare (xargs :measure (nfix (+ 1 n))))
;;   (if (zp n)
;;       nil
;;     (append (make-opener-theorems-for-n tag n)
;;             (make-opener-theorems tag (+ -1 n)))))

;; (defun make-opener-theorem-names-for-n (tag n)
;;   (let* ((tag (mypackn (list tag '- (nat-to-string n))))
;;          (unroll-name (mypackn (list tag '-unroll)))
;;          (base-case-name (mypackn (list tag '-base-case)))

;;          )
;;     `(,unroll-name
;;       ,base-case-name)))

;; ;loop numbers start at 1
;; ;fixme the tag should not have to include -loop?
;; (defun make-opener-theorem-names (tag n)
;;   (declare (xargs :measure (nfix (+ 1 n))))
;;   (if (zp n)
;;       nil
;;     (append (make-opener-theorem-names-for-n tag n)
;;             (make-opener-theorem-names tag (+ -1 n)))))

;; (defun defun-runes-for-function (tag n)
;;   (let* ((tag (mypackn (list tag '- (nat-to-string n)))))
;;     `(,(mypackn (list tag '-exit-test))
;;       ,(mypackn (list tag '-base))
;;       ,(mypackn (list tag '-update)))))

;; ;loop numbers start at 1
;; (defun defun-runes-for-functions (tag n)
;;   (declare (xargs :measure (nfix (+ 1 n))))
;;   (if (zp n)
;;       nil
;;     (append (defun-runes-for-function tag n)
;;             (defun-runes-for-functions tag (+ -1 n)))))

;; (DEFUN REPS-FUNCTION-when-exit-runes (TAG COUNT)
;;   (IF (ZP COUNT)
;;       NIL
;;       (CONS (CONS ':REWRITE
;;                   (CONS (MYPACKN (LIST TAG (NAT-TO-STRING COUNT)
;;                                        '-reps-when-exit))
;;                         'NIL))
;;             (REPS-FUNCTION-when-exit-runes TAG (+ -1 COUNT)))))

;; (DEFUN generated-function-exit-test-runes (TAG COUNT)
;;   (IF (ZP COUNT)
;;       NIL
;;       (CONS (pack$ tag (nat-to-string count) '-exit-test)
;;             ;; (CONS ':definition
;;             ;;       (cons (pack$ tag (nat-to-string count) '-exit-test)
;;             ;;             'nil))
;;             (generated-function-exit-test-runes tag (+ -1 count)))))

;; (defun generated-function-update-fn-runes (tag count)
;;   (if (zp count)
;;       nil
;;       (cons (pack$ tag (nat-to-string count) '-update)
;;             ;; (cons ':definition
;;             ;;       (cons (pack$ tag (nat-to-string count) '-update)
;;             ;;             'nil))
;;             (generated-function-update-fn-runes tag (+ -1 count)))))

;; (DEFUN base-case-runes (TAG COUNT)
;;   (IF (ZP COUNT)
;;       NIL
;;       (CONS (pack$ TAG (NAT-TO-STRING COUNT) '-base-case)
;;             ;; (CONS ':REWRITE
;;             ;;       (CONS (pack$ TAG (NAT-TO-STRING COUNT)
;;             ;;                            '-base-case)
;;             ;;             'NIL))
;;             (base-case-runes TAG (+ -1 COUNT)))))

; Check whether X indicates a state component that the lifter can treat as an input.
;; In general, this is a chain of field acceses starting from a local
(defun input-indicatorp (x)
  (declare (xargs :guard t))
  (or (and (call-of :local x) ;(:local n)
           (true-listp (fargs x))
           (eql 1 (len (fargs x)))
           (natp (farg1 x)))
      (and (call-of :array-local x) ;(:array-local localnum type [optional-length])) -- currently we require this to be a 1-D array
           (true-listp (fargs x))
           (or (eql 2 (len (fargs x)))
               (eql 3 (len (fargs x))))
           (natp (farg1 x))
           (jvm::primitive-typep (farg2 x)) ;fixme add support for other types (not sure how objects or nested array would work...)
           ;; the length, if present, is a nat:
           (implies (equal 3 (len (fargs x)))
                    (natp (farg3 x))))
      ;; (and (true-listp x) ;;(:field <pair> <indicator-for-object>)
      ;;      (eql 2 (len (fargs x)))
      ;;      (eq :field (ffn-symb x))
      ;;      (class-name-field-id-pairp (farg1 x))
      ;;      (input-indicatorp (farg2 x)))
      ))

; Check whether ALIST associates names to input-indicatorps
(defun input-source-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (eq nil alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (let* ((input-var (car entry))
                  (source (cdr entry)))
             (and (symbolp input-var)
                  (input-indicatorp source)))
           (input-source-alistp (rest alist))))))

;; TODO; Compare to parameter-assumptions-aux.  only used in lift-java-code-segment-fn?
(defun make-input-assumptions (input-source-alist state-term)
  (declare (xargs :guard (input-source-alistp input-source-alist)))
  (if (endp input-source-alist)
      nil
    (let* ((entry (first input-source-alist))
           (input-var (car entry))
           (source (cdr entry))
           (assumptions (if (call-of :local source)
                            ;;TODO: Add some type assumptions:
                            (let ((localnum (second source)))
                              `((equal (jvm::nth-local ',localnum (jvm::locals (jvm::thread-top-frame (th) ,state-term)))
                                       ,input-var)))
                          ;; (:array-local localnum type length)
                          (if (call-of :array-local source)
                              ;;the input is in the contents of the array pointed to by the local:
                              (let* ((localnum (farg1 source))
                                     (element-type (farg2 source))
                                     (len-term (if (equal 3 (len (fargs source))) `',(farg3 source)  `(len ,input-var)))
                                     (dims-term (if (quotep len-term)
                                                    `',(cons (unquote len-term) nil) ;if we don't do this, dims like (cons '8 'nil) won't match '(8) in Axe.
                                                  `(cons ,len-term 'nil))))
                                `((array-refp (jvm::nth-local ',localnum (jvm::locals (jvm::thread-top-frame (th) ,state-term)))
                                              ,dims-term
                                              ',element-type (jvm::heap ,state-term))
                                  ;; This puts in the given var when the contents of the array are accessed:
                                  (equal (get-field (jvm::nth-local ',localnum (jvm::locals (jvm::thread-top-frame (th) ,state-term)))
                                                    ',(array-contents-pair)
                                                    (jvm::heap ,state-term))
                                         ,input-var)
                                  (true-listp ,input-var)
                                  ;; If the array is given a length, put in an assumption about the corresponding var
                                  ,@(if (eql 3 (len (fargs source)))
                                        `((equal (len ,input-var) ',(farg3 source)))
                                      nil)))
                            (hard-error 'make-input-assumptions "Bad input-source-alist" nil)))))
      (append assumptions (make-input-assumptions (rest input-source-alist) state-term)))))

(mutual-recursion
 ;;Return a term to wrap around a dag to extract the output.  The special symbol 'replace-me will be replaced with the DAG.
;todo: compare to wrap-term-with-output-extractor in unroll-java-code
 (defund output-extraction-term-core (output-indicator initial-locals-term class-table-alist)
   (declare (xargs :guard (and (output-indicatorp-aux output-indicator) ;:auto is handled in the wrapper
                               (pseudo-termp initial-locals-term)
                               (class-table-alistp class-table-alist))))
   (if (eq :all output-indicator)
       'replace-me
   (if (eq :return-value output-indicator)
       '(jvm::top-operand (jvm::stack (jvm::thread-top-frame (th) replace-me)))
     (if (eq :return-value-long output-indicator)
         ;; Recall that a long takes 2 stack slots and is stored entirely in the lower slot
         '(jvm::top-long (jvm::stack (jvm::thread-top-frame (th) replace-me)))
       (if (eq :array-return-value output-indicator)
           `(get-field (jvm::top-operand (jvm::stack (jvm::thread-top-frame (th) replace-me)))
                       ',(array-contents-pair)
                       (jvm::heap replace-me))
         (if (eq (car output-indicator) :array-local) ;;this means "get the final value of the array that was initially pointed to by array local N.  TODO: This could be an abbreviation for a :field of a :local...
             (let ((local-num (cadr output-indicator)))
               `(GET-FIELD (jvm::nth-local ',local-num ,initial-locals-term) ;;NOTE: The local is in the initial state (s0), not the final state!
                           ',(array-contents-pair)
                           (jvm::heap replace-me)))
           (if (eq (car output-indicator) :field)
               (let ((pair (farg1 output-indicator)))
                 (if (not (field-pair-okayp pair class-table-alist))
                     (er hard? 'wrap-term-with-output-extractor "Bad field: ~x0." pair)
                   `(GET-FIELD ,(output-extraction-term-core (farg2 output-indicator) initial-locals-term class-table-alist)
                               ',pair
                               (jvm::heap replace-me))))
             (if (eq (car output-indicator) :param-field)
                 (let ((pair (farg1 output-indicator))
                       (local-num (farg2 output-indicator)))
                   (if (not (field-pair-okayp pair class-table-alist))
                       (er hard? 'wrap-term-with-output-extractor "Bad field: ~x0." pair)
                     `(GET-FIELD (jvm::nth-local ',local-num ,initial-locals-term) ;;NOTE: The local is in the initial state (s0), not the final state!
                                 ',pair
                                 (jvm::heap replace-me))))
               (if (eq (car output-indicator) :tuple)
                   (output-extraction-terms-core (fargs output-indicator)
                                                 initial-locals-term class-table-alist)
                 (er hard 'output-extraction-term-core "Unrecognized output-indicator"))))))))))

 (defund output-extraction-terms-core (output-indicators initial-locals-term class-table-alist)
   (declare (xargs :guard (and (output-indicatorp-aux-lst output-indicators) ;:auto is handled in the wrapper
                               (pseudo-termp initial-locals-term)
                               (class-table-alistp class-table-alist))))
   (if (endp output-indicators)
       *nil*
     `(cons ,(output-extraction-term-core (first output-indicators) initial-locals-term class-table-alist)
            ,(output-extraction-terms-core (rest output-indicators) initial-locals-term class-table-alist)))))


;;Return a term to wrap around a dag to extract the output.  The special symbol 'replace-me will be replaced with the DAG.
;todo: compare to wrap-term-with-output-extractor in unroll-java-code
(defun output-extraction-term (output-indicator
                               initial-locals-term
                               return-type ;used for :auto
                               class-table-alist
                               )
  (declare (xargs ;:mode :program
            :guard (and (output-indicatorp output-indicator)
                        (pseudo-termp initial-locals-term)
                        (or (eq :void return-type)
                            (jvm::typep return-type))
                        (class-table-alistp class-table-alist))))
  (let ((output-indicator (if (eq :auto output-indicator)
                              (resolve-auto-output-indicator return-type)
                            output-indicator)))
    (if (not output-indicator)
        (er hard? 'output-extraction-term "Failed to resove output indicator.")
      (output-extraction-term-core output-indicator initial-locals-term class-table-alist))))

; returns (mv erp result state)
(defun extract-output-dag (output-indicator
                           dag ;; a DAG giving the final state, in terms of s0
                           assumptions ;can be needed to show lack of aliasing (e.g., array inputs are already allocated, so they can't alias new-ads).  these also replace components of s0 with input vars?
                           initial-locals-term
                           return-type
                           class-table-alist
                           state)
  (declare (xargs :mode :program
                  :guard (and (output-indicatorp output-indicator)
                              (class-table-alistp class-table-alist))
                  :stobjs (state)))
  (b* ((term (output-extraction-term output-indicator initial-locals-term return-type class-table-alist))
       ((mv erp dag2) (compose-term-and-dag term 'replace-me dag))
       ((when erp) (mv erp nil state)))
    (simp-dag dag2
              :rules (state-component-extraction-rules)
              ;; (append (amazing-rules-spec-and-dag)(map-rules)
              ;;         (map-rules) ;needed to push IFs, or we could open up JVM::thread-top-frame, JVM::CALL-STACK, etc.
              ;;         (jvm-semantics-rules)
              ;;         (jvm-simplification-rules))
              ;;:monitor '(IN-OF-RKEYS-WHEN-ARRAY-REFP not-equal-nth-new-ad-when-bound)
              :assumptions assumptions
              :check-inputs nil)))

;; (defun get-lifter-table (state)
;;   (declare (xargs :stobjs state))
;;   (table-alist 'lifter-table (w state)))

;; LOCALS-TERM is a term that represents the locals in the appropriate state
;; HEAP-TERM is a term that represents the heap in the appropriate state
;; TODO: Compare to make-input-assumptions and parameter-assumptions-aux
;; Returns (mv assumptions input-vars)
(defun param-assumptions-and-vars-aux (parameter-types
                                       param-slot-to-name-alist
                                       current-slot ; longs and doubles take 2 slots
                                       array-length-alist locals-term heap-term
                                       assumptions-acc
                                       input-vars-acc)
  (if (endp parameter-types)
      (mv (reverse assumptions-acc)
          (reverse input-vars-acc))
    (b* ((type (first parameter-types))
         (parameter-name (lookup-safe current-slot param-slot-to-name-alist))
         (local-term `(jvm::nth-local ',current-slot ,locals-term))
         ;; Generate an assumption to replace a param with a symbolic variable (or an array of such):
         ((mv assumptions input-vars)
          (cond ((member-eq type jvm::*primitive-types*)
                 ;; If it's a primitive type, we generate
                 ;; an equality assumption to cause the
                 ;; local to be replaced with the
                 ;; corresponding variable, and a type
                 ;; hypothesis about that variable.
                 (mv `((equal ,local-term ,parameter-name)
                       ,@(type-assumptions-for-param type parameter-name)) ;todo: may want to expand things like java-shortp TODO: things shorter than ints should just assume usb32 since there's no guarantee they don't use the high bits
                     (list parameter-name)))
                ((and (jvm::is-one-dim-array-typep type)
                      (member-eq (farg1 type) jvm::*bv-types*))
                 ;; todo: handle other types
                 ;; but first add support for more types
                 ;; in array-refp If it's an 1-d array
                 ;; type of a handled type (and we
                 ;; know the length), we generate an
                 ;; array-refp hyp for the local and a
                 ;; hyp to replace a lookup of the
                 ;; contents with a symbolic array term
                 (let* ((len (lookup-eq parameter-name array-length-alist)) ;this should be a natp or nil
                        (component-type (farg1 type))
;                        (len-term (if len `',len `(len ,parameter-name))) ;if no constant length, the length is just (len name)
                        (dimensions-term (if len
                                             `',(list len) ;need to compute this ground term so we get something like '(16) not (cons '16 'nil)
                                           `(cons (len ,parameter-name) 'nil)))
                        ;; If the len is a known constant, we could make a symbolic array with that many numbered vars
                        (contents-term (if len
                                           parameter-name ;(symbolic-array parameter-name len (jvm::size-of-array-element ;bit-width-from-type
                                         ;; (farg1 type)))
                                         parameter-name))
                        (input-vars (if len
                                        (list parameter-name) ;(make-var-names len parameter-name) ;TODO: what about clashes
                                      (list parameter-name)))
                        (len-claims (if len
                                        `((equal (len ,contents-term) ',len))
                                      nil))
                        (element-width (jvm::size-of-array-element component-type)) ;todo: what about floats and doubles?
                        (element-width-claim `(all-unsigned-byte-p ',element-width ,contents-term))
                        (assumptions `((equal (get-field ,local-term ',(array-contents-pair) ,heap-term)
                                              ,contents-term)
                                       ;; these are not needed because we have the array-refp <-- but these are about the new var that represents the contents
                                       (true-listp ,contents-term)
                                       ,@len-claims
                                       ,element-width-claim
                                       (array-refp ,local-term
                                                   ,dimensions-term
                                                   ',component-type
                                                   ,heap-term))))
                   (mv assumptions input-vars)))
                ;; TODO: If it's a reference, add an assumption that either it's an address or null
                (t (mv nil nil)
;(mv nil (er hard? 'lift-java-code "Unsupported parameter type: ~x0." type))
                   )))
         (slot-count (jvm::type-slot-count type)))
      (param-assumptions-and-vars-aux (rest parameter-types)
                                      param-slot-to-name-alist
                                      (+ current-slot slot-count)
                                      array-length-alist locals-term heap-term
                                      (revappend assumptions assumptions-acc)
                                      (revappend input-vars input-vars-acc)))))

;; Returns (mv assumptions input-vars)
;; Make assumptions for the parameters of the given method.  These will be
;; terms over LOCALS-TERM and HEAP-TERM. ARRAY-LENGTH-ALIST is an alist from
;; parameter names to naturals representing the lengths of the
;; corresponding arrays.
; ;TODO: Add assumptions about 'this' if non-static
(defun param-assumptions-and-vars (method-info array-length-alist locals-term heap-term param-slot-to-name-alist)
  (b* ((parameter-types (lookup-eq :parameter-types method-info)) ;does not include "this"
       (staticp (jvm::method-staticp method-info))
       (first-param-slot (if staticp 0 1)) ;skip a slot for "this" if it's an instance method
       )
    (param-assumptions-and-vars-aux parameter-types param-slot-to-name-alist first-param-slot
                                    array-length-alist locals-term heap-term nil nil)))

;; Returns (mv erp success state)
(defun show-term-unchanged (term ; term over the single variable state-var
                            one-rep-dag ;a DAG over state-var and perhaps previous state-vars and inputs
                            state-var
                            state
                            )
  (declare (xargs :stobjs (state)
                  :mode :program))
  (b* ((before-term term)
       ((mv erp before-dag) (dagify-term2 before-term))
       ((when erp) (mv erp nil state))
       ((mv erp after-dag) (compose-term-and-dag term state-var one-rep-dag))
       ((when erp) (mv erp nil state))
       ((mv erp equality-dag) (make-equality-dag before-dag after-dag))
       ((when erp) (mv erp nil state))
       (- (cw "(Attempting to prove that ~x0 is unchanged.~%" term))
       ((mv erp res state)
        (simp-dag equality-dag
                  :rules (state-component-extraction-rules)
                  :check-inputs nil))
       ((when erp) (mv erp nil state)))
    (if (equal res *t*)
        (prog2$ (cw "Success.)~%")
                (mv (erp-nil) t state))
      (progn$ (er hard 'show-term-unchanged "Failed to show that a term (see above) is unchanged.  Result: ~X01" res nil)
              (cw "Failed.)~%")
              (mv (erp-t) nil state)))))


;; Returns (mv erp success state)
(defun show-terms-unchanged (terms ; terms over the single variable :state
                             one-rep-dag
                             state-var
                             state
                             )
  (declare (xargs :stobjs (state)
                  :mode :program))
  (if (endp terms)
      (mv (erp-nil) t state)
    (mv-let (erp res state)
      (show-term-unchanged (first terms) one-rep-dag state-var state)
      (if erp
          (mv erp nil state)
        (if res
            (show-terms-unchanged (rest terms)
                                  one-rep-dag
                                  state-var
                                  state)
          (mv (erp-nil) nil state))))))

;; Returns (mv new-state-dag generated-events generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state).

;; Returns state TODO: Perhaps the generated-events stored upon failure should
;; include any postlude events that worked so far (but the postlude may not
;; always be a progn...).
(defun submit-postlude (postlude-event this-loop-number
                                       generated-events-acc ;to store in the state upon failure
                                       state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (b* ((- (cw "(Submitting :postlude event for loop number ~x0:~%" this-loop-number))
       ((mv erp state) (submit-event-helper postlude-event
                                   :brief ;todo: use an overarching print argument
                                   nil
                                   state))
       ((when erp)
        (let ((state (store-partial-lift generated-events-acc state)))
          (prog2$ (er hard? 'submit-postlude "Failed to submit postlude for loop ~x0." this-loop-number)
                  state)))
       (- (cw "Done submitting :postlude event for loop number ~x0.)~%" this-loop-number)))
    state))

;; Returns (mv erp new-state-dag generated-events generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state).
;; Throws a hard error if something goes wrong
;; todo: call something from the unroller instead of this?
(defun decompile-loop-by-unrolling (loop-pcs loop-top-state-dag hyps this-loop-number next-loop-number generated-rules-acc interpreted-function-alist-alist interpreted-function-alist print options generated-events-acc state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (b* ((- (cw "(Unrolling loop number ~x0:...~%" this-loop-number))
       ((mv erp dag-to-run)
        (compose-term-and-dag
         `(run-until-exit-segment (stack-height replace-me) ',loop-pcs replace-me)
         'replace-me
         loop-top-state-dag))
       ((when erp) (mv erp nil nil nil nil nil nil state))
       (- (cw "Assumptions: ~x0" hyps))
       ((mv erp state-dag state)
        ;;fixme what if this doesn't terminate?
        (simp-dag
         dag-to-run
         :rule-alists
         (list
          ;;TODO: There is something very much like this below
          ;;no trim rules first:
          (extend-rule-alist2
           (append (and (g :ignore-exceptions options) *ignore-exception-axe-rule-set*)
                   (and (g :ignore-errors options) *ignore-error-state-axe-rule-set*))
           (make-rule-alist! (set-difference-eq
                             (append
                              (g :extra-rules options)
                              (set-difference-eq
                               (append  ;we wait before applying trim rules (so that the rotate idioms can be turned into real rotates)
                                       (lifter-rules)
                                       (run-until-exit-segment-rules))
                               (append ;;(core-rules-bv) ;bad idea..
                                '(LEFTROTATE32-OPEN-WHEN-CONSTANT-SHIFT-AMOUNT
                                  BVOR-WITH-SMALL-ARG2
                                  GETBIT-OF-BVXOR
                                  BVSHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT
                                  BVSHL-REWRITE-WITH-BVCHOP-FOR-CONSTANT-SHIFT-AMOUNT
                                  )
                                (trim-rules) ;we wait before applying trim rules (so that the rotate idioms can be turned into real rotates)
                                )))
                             (g :remove-rules options))
                            (w state))
           (w state))
          (extend-rule-alist2
           (append (and (g :ignore-exceptions options) *ignore-exception-axe-rule-set*)
                   (and (g :ignore-errors options) *ignore-error-state-axe-rule-set*))
           (make-rule-alist! (set-difference-eq
                             (append  ;would like to wait before applying trim rules (so that the rotate patterns can be seen)
                                     (lifter-rules)
                                     (run-until-exit-segment-rules)
                                     (g :extra-rules options))
                             (g :remove-rules options))
                            (w state))
           (w state)))
         :monitor (append '(jvm::invoke-static-initializer-for-next-class-base) ;drop?
                          (g :monitor options))
         :assumptions hyps
         :simplify-xorsp nil
         :print nil ;:brief
         :check-inputs nil
         ))
       ((when erp) (mv erp nil nil nil nil nil nil state))
       (- (and print (progn$ (cw "(state dag after unrolling:~%")
                             (print-list state-dag)
                             (cw ")~%"))))
       ;; (- (cw ")~%")) ;matches the open paren printed at the top of this routine?
       )
    (if (member-eq 'run-until-exit-segment (dag-fns state-dag)) ;;todo: check whether we really did exit the segment?
        (prog2$ (cw "(Error dag (still contains calls of run-until-exit-segment):~X01)~%"
                    state-dag nil)
                (mv t
                    (hard-error 'decompile-loop
                                "didn't finish the run. See the state just above." nil)
                    nil nil nil nil nil state))
      (progn$ (- (cw "Done unrolling.)"))
              (mv nil state-dag generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state)))))

;;
;; The main mutual recursion of the lifter
;;

;todo: add debug printing option
;todo: maybe use arrays for the dags?
(mutual-recursion

 ;; Repeatedly attempt to decompile the loop body with respect to the
 ;; candidate-invars, discarding any candidate-invars that fail to be inductive
 ;; and trying again.  The process continues until we find a set of invariants
 ;; that works.  In the worst, case all invariants get dropped, and we get a
 ;; decompilation of the body that may not be very good.
 ;; Returns (mv erp proved-candidate-invars
 ;;            one-rep-dag ;stuff that happens when the loop does not exit - what vars might be in this?  can assumptions introduce vars other than state-var?
 ;;            termination-test-dag  ; the condition under which the loop exits
 ;;            exit-dag ; stuff that happens when the loop exits
 ;;            generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
;fffixme adapt some HYPS about previous-state-var (e.g., the ones about the classes of heap objects) into invars about state-var?
 (defun decompile-loop-body-with-invars (candidate-invars ;initial set of invariants to try (may be none)
                                         state-var
                                         hyps
                                         code-hyps
                                         initialized-classes ;when lifting a loop body, we assume the initialized-classes are exactly these?
                                         class-table-map
                                         loop-pc
                                         loop-pcs-no-header
                                         tag
                                         loop-depth
                                         loop-alist
                                         this-loop-number
                                         next-loop-number
                                         generated-rules-acc
                                         other-input-vars
                                         interpreted-function-alist-alist
                                         interpreted-function-alist
                                         unroll-nested-loopsp
                                         extra-invarsp
                                         print
                                         options
                                         generated-events-acc ;; Accumulator for all events generated by this lift so far.
                                         state)
   (declare (xargs :mode :program
                   :stobjs (state)
                   :guard (<= 1 loop-depth)))
   (b* ( ;; Decompile the loop body completely, including any nested loops and subroutine calls, assuming the candidate invars:
        ((mv erp state-var-dag) (dagify-term2 state-var))
        ((when erp) (mv erp nil nil nil nil nil nil nil nil nil state))
        ((mv erp body-dag ;what vars might be in this?  can assumptions introduce vars other than state-var?
             generated-events-acc new-generated-rules-acc new-next-loop-number new-interpreted-function-alist-alist new-interpreted-function-alist
             state)
         ;; Note that the state here is simply a variable, which has much less
         ;; information than loop-top-state-dag.  any information that we need
         ;; must be guessed and then proved as an invariant:
         (decompile-code-segment state-var-dag
                                 ;; we could safely add in here some invariants that we know will hold (e.g., about the classes of objects in the heap, which can never change, when the addresses can be expressed in terms of the inputs (perhaps using calls to new-ad, etc.)
                                 (append hyps ; new as of Sun Sep 15 16:32:42 2013 (includes hyps about previous state vars, e.g., s0, which seem needed if we push back values..)
                                         code-hyps ;fixme check that these other invars hold too?
                                         (assumptions-that-classes-are-initialized initialized-classes state-var) ;`((equal (jvm::initialized-classes ,state-var) ',initialized-classes))
                                         (standard-hyps-basic state-var)
                                         (class-table-hyps state-var class-table-map)
                                         candidate-invars)
                                 loop-pcs-no-header
                                 tag
                                 loop-depth
                                 t ;step-once-to-startp
                                 loop-alist
                                 next-loop-number
                                 generated-rules-acc
                                 initialized-classes
                                 other-input-vars
                                 interpreted-function-alist-alist interpreted-function-alist
                                 class-table-map unroll-nested-loopsp extra-invarsp print options generated-events-acc state))
        ((when erp) (mv erp nil nil nil nil nil nil nil nil nil state))
        ;;The result is a MYIF nest with states at the leaves.  Some of the leaf-states have exited the loop body; others are again at the loop top.
        ((mv erp one-rep-dag state) ;fixme what if no branches return to the top of the loop?
         (get-one-rep-dag body-dag loop-pc state-var state)) ;this drops the branches that exit the loop
        ((when erp) (mv erp nil nil nil nil nil nil nil nil nil state))
        ((mv erp termination-test-dag state)
         (get-termination-test-dag body-dag loop-pc state-var state))
        ((when erp) (mv erp nil nil nil nil nil nil nil nil nil state))
        ((mv erp exit-dag state)
         (get-exit-dag body-dag loop-pc state-var state))
        ((when erp) (mv erp nil nil nil nil nil nil nil nil nil state))
        (- (and print (cw "(One rep DAG for loop ~x0:~%~x1)~%" this-loop-number one-rep-dag)))
        (- (and print (cw "(Exit DAG for loop ~x0:~%~x1)~%" this-loop-number exit-dag)))
        (- (and print (cw "(Exit test DAG for loop ~x0:~%~x1)~%" this-loop-number termination-test-dag)))
        ;; (- (and print (cw "(Options: ~x0)~%" options)))
        (termination-test (dag-to-term termination-test-dag))
        (continuation-test (negate-term termination-test))
        ;; Here we must establish that the candidate-invars really are invariants:
        ;; fixme can we assume the negation of the exit test when proving the invars? that would be captured in the myif tests right?
        ;; fixme pass in the hyps?
        (- (cw "(Proving ~x0 loop invariants for loop ~x1:~%" (len candidate-invars) this-loop-number))
        (- (cw " (Loop continuation test: ~x0.)~%" continuation-test))
        ((mv erp failed-candidates state)
         (prove-candidate-invars candidate-invars
                                 (append (get-conjuncts-from-term continuation-test) ;we get to assume that the loop does not terminate (we are only concerned about the branches that come back to the loop top)
                                         (append candidate-invars hyps)) ;we get to assume all of the candidate invars hold before the loop rep; if any fail to be preserved, we'll have to throw them out and start all over.
                                 one-rep-dag
                                 (make-rule-alist-simple
                                  (append new-generated-rules-acc ;new!
                                          ;; (and (g :ignore-exceptions options) *ignore-exception-axe-rule-set*) ;drop?
                                          ;; (and (g :ignore-errors options) *ignore-error-state-axe-rule-set*) ;drop?
                                          (make-axe-rules! (set-difference-eq
                                                           (append (rule-list-1001)
                                                                   (type-rules2)
                                                                   (sbvlt-rules)
                                                                   (and (g :extra-rules options)
                                                                        (prog2$ (cw "(Adding extra rules: ~x0)~%" (g :extra-rules options))
                                                                                (g :extra-rules options)))
                                                                   '(equal-of-maxint-when-sbvlt
                                                                     sbvlt-of-bvplus-of-1-and-0
                                                                     INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE ;Mon Jul  6 21:02:14 2015
                                                                     ))
                                                           (g :remove-rules options))
                                                          (w state)))
                                  t
                                  (table-alist 'axe-rule-priorities-table (w state)))
                                 state-var interpreted-function-alist
                                 print
                                 (g :monitor options)
                                 (g :use-prover-for-invars options)
                                 this-loop-number
                                 nil ;accumulator for failed candidates

                                 state))
        ((when erp) (mv erp nil nil nil nil nil nil nil nil nil state)))
     (if (endp failed-candidates)
         ;; Good; none of the candidate invars failed.
         (prog2$ (cw "Proved all ~x0 loop invariants.)~%" (len candidate-invars))
                 (mv nil
                     candidate-invars
                     one-rep-dag termination-test-dag exit-dag
                     generated-events-acc new-generated-rules-acc new-next-loop-number new-interpreted-function-alist-alist new-interpreted-function-alist
                     state))
       (progn$ (cw "(These loop invariants for loop ~x0 failed to prove, so we'll remove them and try again:~%" this-loop-number)
               (print-list failed-candidates)
               (cw ".))~%")
               (decompile-loop-body-with-invars (set-difference-equal candidate-invars failed-candidates)
                                                state-var
                                                hyps
                                                code-hyps
                                                initialized-classes
                                                class-table-map
                                                loop-pc
                                                loop-pcs-no-header
                                                tag
                                                loop-depth
                                                loop-alist
                                                this-loop-number
                                                next-loop-number
                                                generated-rules-acc ;revert back to the old rule set (excludes anything generated on this attempt)
                                                other-input-vars
                                                interpreted-function-alist-alist
                                                interpreted-function-alist
                                                unroll-nested-loopsp
                                                extra-invarsp
                                                print options generated-events-acc state)))))

 ;; loop-top-state-dag is standing at a loop header and is over previous-state-var (the variable for the enclosing code segment) and maybe other enclosing state-vars
 ;; returns (mv erp new-state-dag generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
 ;;   where new-state-dag has a recursive function in for one loop and is over the same variable(s) as state-dag
 ;; all classes should already be initialized
;fixme handle cases when the loop doesn't execute..
 (defun decompile-loop (loop-pc
                        loop-top-state-dag ;a dag over previous-state-var and any enclosing state-vars (ones with lower numbers)
                        hyps ;these are terms over previous-state-var and maybe other state vars? think about how to use these more..
                        loop-alist tag
                        loop-depth ;the depth of the loop to be decompiled
                        next-loop-number ;a counter used to generate names for the functions that model the loops (fixme could use the class and methods names and the pcs to name these?
                        generated-rules-acc
                        initialized-classes ;fixme does this have to be an exhaustive list?  and what if more classes get initialized during the loop?
                        other-input-vars interpreted-function-alist-alist interpreted-function-alist class-table-map unroll-nested-loopsp extra-invarsp print
                        options
                        generated-events-acc
                        state)
   (declare (xargs :mode :program :stobjs (state) :guard (<= 1 loop-depth)))
;fffixme - what if we can resolve the loop test? might save a whole lot of work? (maybe only if the loop does not execute)
;did this check on the old decompiler - best way to tell is to just try running through the loop.
   (b* ( ;; Extract the method-info:
        ((mv erp method-info state)
         (quick-simp-composed-term-and-dag `(jvm::method-info (jvm::thread-top-frame (th) replace-me)) 'replace-me loop-top-state-dag
                                           :rule-alist *state-component-extraction-axe-rule-alist*
                                           :assumptions hyps ;;do we need the hyps (here and twice below)?
                                           ))
        ((when erp) (mv erp nil nil nil nil nil nil state))
        (method-info (safe-unquote method-info))
        ;; Extract the method-designator:
        ((mv erp method-designator state)
         (quick-simp-composed-term-and-dag `(jvm::method-designator (jvm::thread-top-frame (th) replace-me))
                                               'replace-me
                                               loop-top-state-dag
                                               :rule-alist *state-component-extraction-axe-rule-alist*
                                               :assumptions hyps))
        ((when erp) (mv erp nil nil nil nil nil nil state))
        (method-designator (safe-unquote method-designator))
        (class-name (first method-designator))
        (method-name (second method-designator))
        (method-descriptor (third method-designator))
        (loop-designator (make-loop-designator class-name method-name method-descriptor loop-pc))
        (this-loop-number next-loop-number)
        (next-loop-number (+ 1 next-loop-number)) ;;we number the state-vars according to loop depth - should we use the loop number?
        (loop-pcs (lookup-equal-safe loop-designator loop-alist))
        ;; Decide whether to unroll the loop:
        (unroll-loop-p (or (if (and (< 1 loop-depth) ;i suppose we could unroll non-nested loops too but then why use this lifter?
                                    unroll-nested-loopsp)
                               (progn$ (cw "(NOTE: Unrolling loop number ~x0 because we are unrolling all nested loops.)~%" this-loop-number)
                                       t)
                             nil)
                           (if (member-equal loop-designator (g :loops-to-unroll options))
                               (progn$ (cw "(NOTE: Unrolling loop number ~x0 due to the :loops-to-unroll option.)~%" this-loop-number)
                                       t)
                             nil))))
     (if unroll-loop-p
         ;; Unroll the loop instead of lifting it:
         (decompile-loop-by-unrolling loop-pcs loop-top-state-dag hyps this-loop-number next-loop-number generated-rules-acc interpreted-function-alist-alist interpreted-function-alist print options generated-events-acc state)
       ;;Try to decompile the loop:
       (mv-let
         (erp successp maybe-state-dag maybe-generated-events-acc maybe-generated-rules maybe-next-loop-number
                   maybe-interpreted-function-alist-alist maybe-interpreted-function-alist state)
         ;; This can bail out and return nil for successp for various reasons (some of which are not hard errors):
         ;; TODO: Maybe fewer things here hard errors?  Or should we require explicitly unrolling the loop in order to attempt that?
         (b* ((locals-count (lookup-eq-safe :max-locals method-info)) ;fixme what if there are locals that haven't been initialized yet?
              (line-number-table (lookup-eq :line-number-table method-info)) ;may not exist ;;TTODO: Use named accessors for things like this.
              (local-variable-table (lookup-eq :local-variable-table method-info)) ;may not exist
              ((when (not (jvm::local-variable-tablep local-variable-table)))
               (prog2$ (er hard 'decompile-loop "Ill-formed local variable table: ~x0." local-variable-table)
                       (mv t
                           nil ;successp
                           nil nil nil nil nil nil state)))
              (static-flag (jvm::method-staticp method-info))
              (line-number (lookup-in-line-number-table loop-pc line-number-table))
              (state-var (pack$ 's loop-depth))
              (previous-state-nums (ints-in-range 0 (+ -1 loop-depth)))
              (previous-state-vars (my-pack-list 's previous-state-nums)) ;could pass these in
;        (previous-state-var (car (last previous-state-vars))) ;todo: drop?
              (- (cw "(Decompiling loop number ~x0 (depth ~x1, state ~x2).~%" this-loop-number loop-depth state-var))
              ;;        (- (cw "Options: ~x0.~%" options))
              (- (cw " (Loop ~x5 is at PC ~x0 (line ~x4) in method: ~s1.~s2~s3.)~%"
                     loop-pc class-name method-name method-descriptor line-number this-loop-number))

              (- (cw " (Loop-designator: ~x0)~%" loop-designator))
              (- (cw " (Local variable table: ~x0)~%" local-variable-table))
              ;; There may also be temp vars inside the loop:
              (local-vars-at-loop-top (merge-sort-local-vars-for-pc (local-vars-for-pc loop-pc local-variable-table))) ;may be nil if there is no local-variable-table
              (- (cw " (Local vars in scope at this pc: ~x0)~%" local-vars-at-loop-top))
              (- (cw " (Static flag: ~x0)~%" static-flag))
              (- (check-dag-vars (append previous-state-vars other-input-vars) loop-top-state-dag)) ;what is the point of this check?
              (- (and print (progn$ (cw " (Loop top state dag:~%")
                                    (PRINT-LIST-with-indent loop-top-state-dag "  ")
                                    (cw ")~%"))))
              (- (and print (cw " (ifns: ~x0)~%" (strip-cars interpreted-function-alist))))
              (code-hyps (code-hyps loop-pc method-info class-name method-name method-descriptor state-var))
              (loop-pcs-no-header (remove loop-pc loop-pcs))
              (locals-stored-into (locals-stored-into loop-pcs (lookup-eq :program method-info) nil))
              (- (cw " (Locals stored into: ~x0.)~%" locals-stored-into)) ;TODO: Print the names if available, TODO: print the locals *not* stored into.


              (- (cw " (We will try to decompile the loop body.)~%"))
              (- (and print (progn$ (cw " (hyps passed in:~%")
                                    (print-list hyps)
                                    (cw ")~%"))))
              (loop-function-name (pack$ tag '-loop- this-loop-number)) ;move up?
              (invariant-alist (g :invariant-alist options))
              ;;(- (cw "(User-supplied invariant-alist: ~x0)~%" invariant-alist))
              (user-invariants (lookup-loop-function loop-function-name loop-designator invariant-alist nil)) ;fixme can these introduce vars? ;these are proved below
              (- (and user-invariants (cw "(User-supplied invariants (as provided): ~X01.)~%" user-invariants nil)))
              (user-invariants (translate-terms user-invariants 'decompile-loop (w state)))
              (- (and user-invariants (cw "(User-supplied invariants (after translation):~%~X01.)~%" user-invariants nil)))
              (user-invariants (desugar-invars user-invariants state-var local-vars-at-loop-top))
              (user-invariants (desugar-calls-of-contents-in-terms user-invariants `(jvm::heap ,state-var)))
              (- (and user-invariants (cw "(User-supplied invariants (after desugaring):~%~X01.)~%" user-invariants nil)))
              ;;the invariants are about the special variable 'state-var, which we replace with s1 (or whatever) here:
              (user-invariants (sublis-var-simple-lst (acons 'state-var state-var nil) user-invariants))
              ;; (legal-vars (append other-input-vars ;new!
              ;;                     (list 'state-var ;for now, until we decide how to handle this
              ;;                   state-var previous-state-var))) ;;TTODO: Allow *all* previous state vars!
;TODO: Add check back after adding all prev vars to the list above:
              ;; ((when (not (vars-in-terms-include-onlyp user-invariants legal-vars)))
              ;;  (progn$ (hard-error 'decompile-loop "Invalid invariant-alist entry (vars mentioned can only be ~x0)." (acons #\0 legal-vars nil))
              ;;          (mv nil nil nil nil nil nil nil nil state)))
              (- (and user-invariants (cw "(Using user-supplied invariants:~%~X01.)~%" user-invariants nil)))
              ;;ffixme put in other invars (types and lengths of arrays in the heap don't change, what else?)
              ;;generate annotations based on the types of locals in the local variable table?
              ;;for 2-d arrays, put in that they are well-formed?
              ;;put in annotations about whether things are null?

              ;;The tricky part about decompiling Java bytecode is that the code that gets run when a method is called depends on the type of the object on which the method is called (it can be the declared class or some subclass that overrides that method).  So we need to know the types of objects.  We generate assertions about the types of the objects at certain addresses (e.g., "new address 12 is the address of an object of class C") but we also need assertions about pointers to those objects not changing during the program (e.g., "local4.foo.bar points to new address 12").  I see two options for generating these: greedy (for every pointer-valued local, static field, and method field, generate an assertion saying that it is unchanged during the loop -- otherwise we can't decompile) or lazy (start decompiling and have the failure report the object whose class was unknown - may be tricky to propagate this information out of nested loops).  so i am going to try the greedy approach:
              ;;for every local that contains an address, we get the address in the loop-top state (something like "new address 12" or "input 3") and assert a loop invariant that the local contains that value.
              ;;same for every static field
              ;;same for every field of every object in the heap which contains an address? (scan the heap for setfields - can other stuff be in the heap, e.g., stuff passed in in the driver?)
              ((mv erp heap-invars state) (invariants-about-heap loop-top-state-dag state-var class-table-map extra-invarsp interpreted-function-alist state))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (- (progn$ (cw "(heap invars:~%") (print-list heap-invars) (cw ")~%")))
              (address-invars  nil ;(adapt-address-hyps hyps previous-state-var state-var)
                               )   ;todo: use all previous-state-vars here?
              (- (progn$ (cw "(adapted address invars:~%") (print-list address-invars) (cw ")~%")))
              ((mv erp type-invars-for-locals state) (make-type-invars-for-locals local-variable-table loop-pc state-var loop-top-state-dag hyps options print state))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (- (progn$ (cw "(type invars for locals:~%") (print-list type-invars-for-locals) (cw ")~%")))
              ;;build an invar about "this": ffixme what about other unchanged locals?  other unchanged state components?
              ((mv erp invars-about-this state)
               (if static-flag ;if it's a static method, there is no "this" parameter:
                   (mv (erp-nil) nil state)
                 (mv-let (erp local-0-dag state)
                   (get-local-dag 0 loop-top-state-dag state)
                   (if erp
                       (mv erp nil state)
                     (mv (erp-nil)
                         (list `(equal (jvm::NTH-local '0 (JVM::LOCALS (JVM::thread-top-frame (th) ,state-var)))
                                       ,(dag-to-term local-0-dag)))
                         state)))))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (- (progn$ (cw "(invars about this:~%") (print-list invars-about-this) (cw ")~%")))
              ((mv erp unchanged-local-invars state)
               ;;fffixme pass in ifns for embedded dags?
               (if extra-invarsp ; is this ever false?
                   (make-unchanged-local-invars (+ -1 locals-count) locals-stored-into state-var loop-top-state-dag interpreted-function-alist nil state)
                 (mv (erp-nil) nil state)))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
;ffixme if we have a hyp like this about previous-state-var (here s1):
              ;; (EQUAL (GET-FIELD (NEW-AD (RKEYS (JVM::HEAP S0)))
              ;;                    '("org.bouncycastle.crypto.digests.SHA1Digest" . "X")
              ;;                    (JVM::HEAP S1))
              ;;         (NTH-NEW-AD '3 (RKEYS (JVM::HEAP S0))))
;we may need to adapt it to be about state-var (here s2)
              (- (and print (cw "(unchanged-local-invars: ~x0.)~%" unchanged-local-invars)))
              (candidate-invars (append address-invars ;new!
                                        invars-about-this
                                        user-invariants heap-invars
                                        unchanged-local-invars
                                        type-invars-for-locals))
              ;; Discard candidate invars that don't hold initially:
              ((mv erp candidate-invars state)
               (if (g :assume-invariants-initially options)
                   (prog2$ (cw "WARNING: Assuming all invariants hold at the start of the loop.  This is unsound!  See the :assume-invariants-initially lifter option.~%")
                           (mv (erp-nil) candidate-invars state))
                 ;; I wonder if sometimes failure to hold here should be an error...
                 (filter-candidate-invars-that-hold-initially ;some things are filtered out earlier (TODO: so don't check them again?), but this catches user invars that fail to hold initially
                  candidate-invars
                  hyps ; these are over state-var?
                  loop-top-state-dag
                  ;;fixme: clean this up (I copied it from elsewhere):
                  (make-rule-alist-simple
                   (append generated-rules-acc
                           ;; (and (g :ignore-exceptions options) *ignore-exception-axe-rule-set*) ;drop?
                           ;; (and (g :ignore-errors options) *ignore-error-state-axe-rule-set*) ;drop?
                           (make-axe-rules! (set-difference-eq
                                            (append (map-rules)
                                                    (jvm-simplification-rules)
                                                    (jvm-rules-list)
                                                    (jvm-rules-alist)
                                                    (bv-array-rules)
                                                    (jvm-rules-unfiled-misc)
                                                    (boolean-rules)
                                                    '(IF-BECOMES-MYIF
                                                      MYIF-BECOMES-BOOLIF-AXE
                                                      UBP-LONGER-BETTER
                                                      SBVLT-TRIM-CONSTANT-RIGHT
                                                      sbvlt-of-bvplus-of-minus-1-and-minus-1
                                                      sbvlt-of-bvminus-of-1-and-minus-1
                                                      sbvlt-of-bvplus-of-minus-1-and-1
                                                      sbvlt-of-bvminus-of-1
                                                      NOT-EQUAL-MIN-INT-WHEN-NOT-SBVLT
                                                      LOOKUP-EQ-BECOMES-LOOKUP-EQUAL LOOKUP-EQUAL-OF-ACONS-SAME ;why are these needed for aes-128-encrypt-regular-cbc-pkcs5-loop-32.lisp?
                                                      equal-of-maxint-when-sbvlt
                                                      sbvlt-of-bvplus-of-1-and-0
                                                      INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE ;Mon Jul  6 21:02:14 2015
                                                      )
                                                    (unsigned-byte-p-rules)
                                                    (type-rules)
                                                    (core-rules-bv)
                                                    (base-rules)
                                                    ;;(rule-list-1001)
                                                    ;;(type-rules2)
                                                    ;;(sbvlt-rules)
                                                    (g :extra-rules options))
                                            (g :remove-rules options))
                                           (w state)))
                   t
                   (table-alist 'axe-rule-priorities-table (w state)))
                  state-var
                  interpreted-function-alist
                  print
                  (g :monitor options)
                  nil
                  generated-events-acc
                  state)))
              ((when erp)
               (mv erp nil ;successp
                   nil nil nil nil nil nil state))
              ;; Now decompile the loop body while guessing and checking invariants:
              ((mv erp proved-candidate-invars
                   one-rep-dag ;what vars might be in this?  state-var, previous state-vars, and inputs?  can assumptions introduce vars other than state-var?
                   termination-test-dag
                   exit-dag
                   generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist
                   interpreted-function-alist state)
               (decompile-loop-body-with-invars candidate-invars state-var hyps code-hyps initialized-classes class-table-map loop-pc loop-pcs-no-header
                                                tag loop-depth loop-alist this-loop-number next-loop-number generated-rules-acc other-input-vars
                                                interpreted-function-alist-alist interpreted-function-alist unroll-nested-loopsp extra-invarsp print options
                                                generated-events-acc
                                                state))
              ((when erp)
               (mv erp nil ;successp
                   nil nil nil nil nil nil state))
              ;;ffixme see if error-state remains in the body-dag or one-rep-dag?
              (- (cw "(Decompiling using ~x0 loop invariants.)~%" (len proved-candidate-invars)))
              ;;fixme move this invariant stuff up?  or just check whether the invariant proved above contains all the info that we need here?
              ;;now we build and prove an invariant (fixme combine this with the trusted invariant stuff?) fixme use type info from the local variable table?
              ;;for now, the invariant just says that any term used as an address in the loop body does not change during the loop body
;ffixme what about accesing a 2-d array?!  the address of the row may change during the loop... this happens in AESEngine?
;ffixme do we also show that the addresses aren't aliases?
              (addresses (get-addresses-from-dag one-rep-dag))
              ;;each address is a term over state-var
              (- (cw "(Addresses read or written by loop ~x2: ~X01)~%" addresses nil this-loop-number))

              ;;these are over state-var and the previous state-var(s)?
              ;;these conjuncts must be true, or we can't decompile since we can't bound the number of addresses
              ;;touched by the function
              ;;so for example, we can't decompile a function that walks down a linked list
              ((mv erp unchanged-pointer-invars state)
               (make-unchangedness-invariants-for-exprs addresses state-var loop-top-state-dag nil previous-state-vars state))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;;we need to prove these in sorted order? really? this may be a relic from when we took each subterm and tried to prove it was unchanged..
              (unchanged-pointer-invars (merge-sort-term-order unchanged-pointer-invars))
              ;; TODO: Suppress this printing (all the way to the close paren) if there are 0.
              (- (progn$ (cw "(Proving ~x0 unchanged pointer invariant(s):~%" (len unchanged-pointer-invars))
                         (print-list unchanged-pointer-invars)
                         (and print (cw "~%(Hyps:~x0)~%" hyps))))
              ((mv erp unchanged-pointer-invars state)
               (push-back-facts unchanged-pointer-invars hyps print state))
              ((when erp)
               (mv erp nil ;successp
                   nil nil nil nil nil nil state))
              (- (and print (cw "(Pushed back facts: ~X01)~%" unchanged-pointer-invars nil)))
              ;; we rewrite the later invars once we've proved the earlier invars
              ((mv erp provedp
                   unchanged-pointer-invars ;do we need to return the simplified conjuncts?
                   state)
               ;;fixme can we assume the negation of the exit test when proving the invars?
               ;;fixme can we assume the proved-candidate-invars here?
               (prove-invariant-conjuncts unchanged-pointer-invars
                                          hyps
                                          one-rep-dag
                                          unchanged-pointer-invars ;;FFIXME  think about this ;;initial-state-hyps ;hope this is okay
                                          (extend-rule-alist2
                                           (append ;; (and (g :ignore-exceptions options) *ignore-exception-axe-rule-set*) ;drop?
                                            ;; (and (g :ignore-errors options) *ignore-error-state-axe-rule-set*) ;drop?
                                            )
                                           (make-rule-alist! (rule-list-1001) (w state))
                                           (w state))
                                          state-var
                                          interpreted-function-alist
                                          print
                                          state))
              ((when erp)
               (mv erp nil ;successp
                   nil nil nil nil nil nil state))
              (- (if provedp
                     (cw "Good!  The unchanged pointer invariants all hold.)~%")
                   (cw "failed to prove unchanged pointer invariants)")))

              ((when (not provedp))
               (prog2$ (cw "Failed to decompile loop ~x0.)~%" this-loop-number) ; matches the open paren in "(Decompiling..."
                       (mv nil
                           nil ;successp
                           nil nil nil nil nil nil state)))
              (- (cw "Using unchanged pointer invariants to simplify things...~%")) ;when does this end?
              (all-invars (append proved-candidate-invars unchanged-pointer-invars))
              ;;now one-rep-dag is in terms of state-var and previous-state-vars (and other inputs?)
              ;;and all addresses are in terms of previous-state-vars (and other inputs?)
              ((mv erp one-rep-dag state)
               (quick-simp-dag
                one-rep-dag
                ;;new (todo: overkill?)
                :rule-alist
                (make-rule-alist! (first-loop-top-rules) ;reduce?
                                 (w state))
                :assumptions (append all-invars hyps))) ;hyps are new here
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;;(- (cw "Loop dag after invars: ~X01.~%" one-rep-dag nil))
              ;;we also use the invariant to simplify the termination/continuation test
              ((mv erp termination-test-dag state)
               (quick-simp-dag termination-test-dag
                               :rules nil ;include some rules?
                               :assumptions all-invars))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;; TODO: It is sound/useful to simplify the exit-dag here, assuming the invars?

              ;;Now we build the recursive function that corresponds to the
              ;;loop.  Each state component read of written by the loop
              ;;becomes a parameter to the function.  Our goal is to build
              ;;a term that captures the effect of the loop and has the
              ;;following structure: extract the state components used by
              ;;the loop, run the loop function on them, and then write the
              ;;results back into the state. (Then apply the exit-dag to that.)

;fixme some comments may be in the wrong places now.. see old versions

              ;; Make sure that the class-table, heapref-table,
              ;; monitor-table, initialized-class-names, and intern-table
              ;; are all unchanged by the loop body!
              ((mv erp success state)
               (show-terms-unchanged `((jvm::class-table ,state-var)
                                       (jvm::heapref-table ,state-var)
                                       (jvm::monitor-table ,state-var)
                                       (jvm::initialized-classes ,state-var)
                                       (jvm::intern-table ,state-var))
                                     one-rep-dag
                                     state-var
                                     state
                                     ))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ((when (not success))
               (prog2$ (cw "Failed to decompile loop ~x0.)~%" this-loop-number) ; matches the open paren in "(Decompiling..."
                       ;; an error will have been thrown in show-terms-unchanged
                       (mv nil
                           nil ;successp
                           nil nil nil nil nil nil state)))


              ;; Initialize accumulator vars for gathering info about loop params:
              ;; Number the params start at 0:
              (next-param-number 0)
              ;; UPDATED-STATE-TERM represents writing the return values of
              ;; the loop function back into the state after the loop. It
              ;; is a nest of updates to STATE-VAR where the values written
              ;; are components of the variable :loop-function-result,
              ;; which will be replaced below by the call of the loop
              ;; function.
              (updated-state-term state-var)
              ;;  The paramnum-update-alist maps each paramnum to a DAG
              ;;  representing the updated value of that param after the
              ;;  loop body (in terms of what? params?)
              (paramnum-update-alist nil)
              ;; The paramnum-extractor-alist maps each paramnum to a DAG
              ;; representing how to extract it from STATE-VAR. May also
              ;; mention previous state-vars (and inputs?) since heap
              ;; addresses may mention those.
              (paramnum-extractor-alist nil)
              ;;maps paramnums to their "names" for debugging (from the class file).  These can be entire get-field terms...
              (paramnum-name-alist nil)

              ;; Gather info for params that represent locals:
              (- (cw "(Making parameters for locals for loop ~x0:~%" this-loop-number))
              ;; (local-slots-in-scope (strip-cadrs local-vars-at-loop-top)) ;will be nil if there is no local-variable table
              (excluded-locals-alist (g :excluded-locals-alist options))
              ;; The user-supplied :excluded-locals are always used, if given:
              (excluded-locals (lookup-loop-function loop-function-name loop-designator excluded-locals-alist :auto))
              ((mv erp next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist state)
               (make-loop-parameters-for-locals (+ -1 locals-count) ;todo: what if the last local is a long or double?!
                                                loop-pc local-variable-table state-var
                                                excluded-locals
                                                one-rep-dag next-param-number updated-state-term
                                                paramnum-update-alist paramnum-extractor-alist paramnum-name-alist
                                                state))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (- (cw "Done handling locals.)~%"))

              ;; Gather info for params that represent fields of objects:
              (- (cw "(Making loop parameters for instance fields changed by the loop:~%"))
              ;;do we have to make this, or can we pass the main dag and a nodenum?
              ;;fffixme - what do we do if this has a myif for a heap subterm?

              ;;this checks that the addresses only depend on si (not s):
              ;; fixme think more about what to do if the heap doesn't change in the loop (we'll detect an invariant for the heap in terms of si)
              ;; maybe things work now
              ((mv erp heap-dag state) (extract-heap-dag one-rep-dag state))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (heap-update-triples
               (get-heap-update-triples heap-dag state-var previous-state-vars))
              (- (cw "(Found ~x0 heap updates: ~x1)~%" (len heap-update-triples) (if print heap-update-triples :elided)))
              (- (cw "(Attempting to show lack of aliasing:~%"))
              (heap-update-pairs (get-heap-update-pairs-from-triples heap-update-triples))
              ((mv erp no-aliasesp state) (no-aliasesp heap-update-pairs (append all-invars hyps) ;hope it's okay to assume all this
                                                       state))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ((when (not no-aliasesp))
               (mv t
                   (er hard? 'decompile-loop "Couldn't show lack of heap aliasing (pairs: ~X01)." heap-update-pairs nil)
                   nil nil nil nil nil nil state))
              (- (cw "Good! There is no aliasing among the fields changed by the loop.)~%"))
              ((mv erp updated-state-term paramnum-update-alist paramnum-extractor-alist next-param-number paramnum-name-alist)
               (make-loop-parameters-for-fields heap-update-triples updated-state-term next-param-number paramnum-update-alist
                                                paramnum-extractor-alist paramnum-name-alist state-var))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (- (cw "Done processing instance fields.)~%"))
              (- (cw "(Making loop parameters for static fields changed by the loop:~%"))
              ;; Extract the new static-field-map:
              ;;this is over state-var and previous-state-vars?
              ((mv erp static-field-map-dag state)
                ;;fixme what about ifs?
               (quick-simp-composed-term-and-dag '(jvm::static-field-map s) 's one-rep-dag
                                                 :rule-alist *get-local-axe-rule-alist*
                                                 :remove-duplicate-rulesp nil))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (static-field-update-pairs
               (get-static-field-update-pairs static-field-map-dag state-var previous-state-vars))
              ((when (not (no-duplicatesp (strip-cars static-field-update-pairs))))
               (prog2$ (er hard 'decompile-loop "Duplicates detected in static field updates: ~x0" static-field-update-pairs)
                       (mv t
                           nil ;successp
                           nil nil nil nil nil nil state)))
              ((mv erp updated-state-term paramnum-update-alist paramnum-extractor-alist next-param-number paramnum-name-alist)
               (make-loop-parameters-for-static-fields static-field-update-pairs
                                                       updated-state-term next-param-number paramnum-update-alist paramnum-extractor-alist paramnum-name-alist state-var))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (- (cw "Done processing static fields.)~%"))

              ;; fixme -think about the case where an address is itself a call to get-field - we might need to rewrite multiple times?? - not an issue since ads can't be functions of s?  what if an ad is a function of a get-field of si? - old comment?

              ;;can some param-exprs include others?  no, because ads for the heap reads and writes must not depend on state-var
              ;;fffixme check the stack height at the loop top somehow?
              ;; at this point, parameters have been made for all state components that change in the loop
              ;; but the cdrs of paramnum-update-alist (along with the termination-test-dag)
              ;; still need to have these parameters substituted in
              ;; also, state components that are read but not written still need to be made into parameters

              ;;we put in the appropriate param expressions:

              (replacement-alist (make-replacement-alist paramnum-extractor-alist)) ;; maps dags to nth terms over 'params
              ((mv erp paramnum-update-alist) ;; all state components that are changed have been replaced by their exprs in terms of 'params
               (perform-replacements-on-cdrs paramnum-update-alist replacement-alist))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ((mv erp termination-test-dag) ;fixme what about the exit-dag???
               (perform-replacements termination-test-dag replacement-alist))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;;(changed-param-count next-param-number)
              (paramnum-update-alist (lookup-params 0 (+ -1 next-param-number) paramnum-update-alist)) ;sorts and remove dups
              (param-new-val-dags (strip-cdrs paramnum-update-alist))
              (param-new-val-dags-and-termination-test-dag (cons termination-test-dag param-new-val-dags))
              (- (cw "(Finding read-only params.~%"))
              ;;we've handled all state componenents that get written in the loop body, but the updates of those components may depend on other
              ;;components which are read in the loop but not written to.  we must make params in the loop function for these as well.
              ;;now we find any other expressions that need to be made into params:
;fffixme use dags instead of terms throughout?
              ((mv erp
                   param-new-val-dags-and-termination-test-dag
                   read-only-param-dag-alist ;fixme: this is a paramnum-extractor-alist too?
                   next-param-number
                   & ;; paramnum-name-alist ;; use this?
                   state)
               (find-read-only-params-lst param-new-val-dags-and-termination-test-dag
                                          nil
                                          next-param-number
                                          nil
                                          paramnum-name-alist
                                          state))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (- (cw "  Done finding read-only params.)~%"))
              (param-count next-param-number)
              (max-param-number (+ -1 param-count))
              (termination-test-dag (car param-new-val-dags-and-termination-test-dag))
              (termination-test-term (dag-to-term termination-test-dag))
              ;;these are in order:
              ;;check that these only depend on params and input vars..ffixme
              (param-new-val-dags (cdr param-new-val-dags-and-termination-test-dag))
              ;;the above may have added params (but only for state components that didn't change?)
              ;;so we need to add dags for their new values
              ((mv erp new-val-dags-read-only) (make-new-val-dags-read-only (reverse read-only-param-dag-alist)))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              (param-new-val-dags (append param-new-val-dags new-val-dags-read-only))
              (paramnum-extractor-alist (append read-only-param-dag-alist paramnum-extractor-alist))
              (paramnum-extractor-alist (lookup-params 0 max-param-number paramnum-extractor-alist)) ;sorts and remove dups

;can we just compose on the defining exprs and let simplification apply later?
              ;;                                  (initial-value-dags (make-initial-value-dags (prog2$ (cw "making initial value dags.~%")
              ;;                                                                                       paramnum-extractor-alist)
              ;;                                                                               loop-top-state-dag state-var state))

              (initial-value-dags (strip-cdrs paramnum-extractor-alist)) ;these are over state-var and perhaps earlier state vars (and inputs??)
              (- (cw "(There are ~x0 params.)~%" param-count))
              ;; (- (progn$ (cw "(Initial values of params:~%")
              ;;            (print-list initial-value-dags)
              ;;            (cw ")~%")))
              ((mv erp initial-params-dag) (make-cons-nest-dag initial-value-dags))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))

              ;;updated-state-term will be in terms of :loop-function-result and state-var
              ;; (- (cw "(updated state term: ~X01)~%" updated-state-term nil))
              ;;this represents the execution of all the loop iterations,
              ;;with the PC again at the top of the loop

              ;; Build the term that represents the loop:

              ;; Apply the loop function to the intial values of the params:
              ((mv erp loop-function-call-dag) (compose-term-and-dag `(,loop-function-name :inital-params)
                                                                 :inital-params
                                                                 initial-params-dag))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;; Write the values computed by the loop back into the state:
              ((mv erp new-state-dag) (compose-term-and-dag updated-state-term :loop-function-result loop-function-call-dag))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;; Apply the effect of the exit branches around it:
              ((mv erp new-state-dag) (compose-dags exit-dag state-var new-state-dag t)) ;can this be a constant?
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;; now we apply the effect of the loop to the initial
              ;; loop-top-state-dag by replacing state-var with
              ;; loop-top-state-dag.
              ((mv erp new-state-dag) (compose-dags new-state-dag state-var loop-top-state-dag t))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;; simplify:
              ((mv erp new-state-dag state)
               (quick-simp-dag (check-dag-vars (append previous-state-vars other-input-vars)
                                               new-state-dag)
                               :rule-alist *get-local-axe-rule-alist*
                               :remove-duplicate-rulesp nil
                               :simplify-xorsp nil))
              ((when erp) (mv erp nil nil nil nil nil nil nil state))
              ;; (- (cw "New state dag: ~X01" new-state-dag nil))
              (exit-test-function-name (pack$ loop-function-name '-exit-test))
              (loop-guard-alist (g :loop-guard-alist options))
              (user-guard-untranslated (lookup-loop-function loop-function-name loop-designator loop-guard-alist nil))
              (- (and user-guard-untranslated (cw "(Using user-supplied guard for this loop function: ~x0)~%" user-guard-untranslated)))
              ;; Make sure we can translate the user guard:
              (- (and user-guard-untranslated (translate-term user-guard-untranslated 'decompile-loop (w state))))

              ;;TODO: Option to do nothing if the guards are violated
              (guard-untranslated (or user-guard-untranslated
                                      `(and (equal (len params) ,param-count)
                                            (true-listp params))))
              ;; (guard-translated (or user-guard-translated
              ;;                       `(if (equal (len params) ',param-count)
              ;;                            (true-listp params)
              ;;                          'nil)))
              (check-guards-in-functions (g :check-guards-in-functions options))
              (inlinep (g :inline options))
              (exit-test-function-body termination-test-term)
              ;; Make the exit-test for the loop function:
              (exit-test-expr-core (if inlinep
                                       exit-test-function-body
                                     `(,exit-test-function-name params)))
              ;; Maybe add a check of the guard (and terminate if it fails):
              (exit-test-expr-untranslated (if check-guards-in-functions
                                               `(or (not ,guard-untranslated)
                                                    ,exit-test-expr-core)
                                             exit-test-expr-core))
              ;; (exit-test-expr-translated (if check-guards-in-functions
              ;;                                `(if (not ,guard-translated)
              ;;                                     (not ,guard-translated)
              ;;                                   ,exit-test-expr-core)
              ;;                              exit-test-expr-core))
              (- (cw "(Exit test is: ~X01)~%" exit-test-function-body nil))

              (update-function-name (pack$ loop-function-name '-update))
              ((mv erp update-dag) (make-cons-nest-dag param-new-val-dags))
              ((when erp) (mv erp nil nil generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state))
              (update-dag-fns (dag-fns update-dag))
              (- (cw "(fns in update dag: ~X01.)~%" update-dag-fns nil))
              (- (cw "(Updated values of params: ~X01.)~%" param-new-val-dags nil)) ;todo: only print if there is a problem
              (update-dag-fns-not-built-in (set-difference-eq update-dag-fns (append *axe-evaluator-functions*
                                                                                     ;;TTODO: add more:
                                                                                     '(JVM::MAKE-DOUBLE JVM::DOUBLE-SUB JVM::DCMPL JVM::DCMPG))))
              (update-dag-interpreted-function-alist
               (lookup-and-union update-dag-fns-not-built-in ;todo: what about functions called transitively?
                                 interpreted-function-alist-alist
                                 nil))
              (use-lets-in-terms (g :use-lets-in-terms options))
              (max-term-size (g :max-term-size options))
              (update-function-body (dag-to-term-limited update-dag max-term-size use-lets-in-terms update-dag-interpreted-function-alist))
              (update-expr (if inlinep
                               update-function-body
                             `(,update-function-name params)))
              (- (and print (cw "(~x0 is ~X12)~%" update-function-name update-function-body nil)))

              ;; Build the body of the loop function:
              (loop-function-body-untranslated `(if ,exit-test-expr-untranslated
                                                    params
                                                  (,loop-function-name ,update-expr)))


              ;; (loop-function-body-translated `(if ,exit-test-expr-translated
              ;;                                     params
              ;;                                   (,loop-function-name ,update-expr)))
              (constant-opener-theorem-body
               `(implies (syntaxp (quotep params))
                         (equal (,loop-function-name params)
                                ,loop-function-body-untranslated)))
              (constant-opener-theorem-name (pack$ loop-function-name '-constant-opener))

              (unroll-name (pack$ loop-function-name '-unroll))
              (base-case-name (pack$ loop-function-name '-base-case))
              (measure (measure-for-loop loop-function-name loop-designator options))
;                                 (skip-terminationp (eq :skip measure-or-skip))
              (- (if (eq :skip measure)
                     (cw "(WARNING: Skipping termination proof for loop ~x0.)~%" this-loop-number)
                   (if (eq :auto measure)
                       (cw "(Using with-auto-termination tool for loop ~x0.)~%" this-loop-number)
                     (if (eq :acl2 measure)
                         (cw "(Letting ACL2 guess the measure for loop ~x0.)~%" this-loop-number)
                       (cw "(Using user-supplied measure, ~x0, for loop number ~x1.)~%" measure this-loop-number)))))
              (measure-hints (lookup-loop-function loop-function-name loop-designator (g :measure-hints-alist options) nil))
              ;; Create the opener rules for the loop function:
              (disable-loop-openersp (g :disable-loop-openers options))
              (defthm-variant-for-openers (if disable-loop-openersp 'defthmd 'defthm))
              (defuns-and-theorems
                `((defun ,update-function-name (params)
                    (declare (xargs :normalize nil
                                    :guard ,guard-untranslated
                                    :verify-guards nil))
                    ,update-function-body)

                  (defun ,exit-test-function-name (params)
                    (declare (xargs :normalize nil
                                    :guard ,guard-untranslated
                                    :verify-guards nil))
                    ,exit-test-function-body)

                  ;; TODO: Add support for guessing measures.
                  ;; TODO: Add support for verifying the guards
                  ,(if (eq :skip measure)
                       ;; :skip was indicated (for this loop or all loops), so we put in a skip-proofs:
                       `(skip-proofs
                         (defund ,loop-function-name (params)
                           (declare (xargs :guard ,guard-untranslated
                                           :normalize nil
                                           :verify-guards nil)) ;;TODO: add an option to drop this (but delay the guard proof so it doesn't get skip-proofed)
                           ,loop-function-body-untranslated))
                     (if (eq :auto measure)
                         `(with-auto-termination
                           (defund ,loop-function-name (params)
                             (declare (xargs :guard ,guard-untranslated ;no :measure, no :hints
                                             :normalize nil
                                             :verify-guards nil)) ;;TODO: add an option to drop this
                             ,loop-function-body-untranslated))
                       (if (eq :acl2 measure)
                           `(defund ,loop-function-name (params)
                              (declare (xargs ;; no measure
                                        ,@(if measure-hints (list :hints measure-hints) nil)
                                        :guard ,guard-untranslated
                                        :normalize nil
                                        :verify-guards nil)) ;;TODO: add an option to drop this
                              ,loop-function-body-untranslated)
                         ;; the user gave a measure, so use it:
                         `(defund ,loop-function-name (params)
                            (declare (xargs :measure ,measure
                                            ,@(if measure-hints (list :hints measure-hints) nil)
                                            :guard ,guard-untranslated
                                            :normalize nil
                                            :verify-guards nil)) ;;TODO: add an option to drop this
                            ,loop-function-body-untranslated))))
                  ;; The two opener rules:
                  (,defthm-variant-for-openers ,unroll-name
                    (implies (not ,exit-test-expr-untranslated)
                             (equal (,loop-function-name params)
                                    (,loop-function-name ,update-expr)))
                    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                               '(,loop-function-name)))))
                  (,defthm-variant-for-openers ,base-case-name
                    (implies ,exit-test-expr-untranslated
                             (equal (,loop-function-name params)
                                    params))
                    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                               '(,loop-function-name)))))

                  ;;opener theorem for the loop for constant args:
                  (defthmd ,constant-opener-theorem-name
                    ,constant-opener-theorem-body
                    :hints (("Goal" :expand (,loop-function-name params)
                             :in-theory nil)))))
              ;; (dummy99 (cw "defuns and theorems:~X01~%" defuns-and-theorems nil))
              (new-type-rules nil) ;(make-type-rules param-new-val-dags 0 loop-function-name) ;Sun Jul  4 18:05:51 2010
              ;;(cw "Generated type rules: ~x0" new-type-rules)
              ;;ffixme abuse of the name map - make an append for records?
              ;; (- (cw "(paramnum-name-alist: ~x0)~%" (reverse paramnum-name-alist))) ;todo: drop?

              ;; Submit the events right now, so we can reason about the new functions (e.g., to prove that array lengths are unchanged)
              (state (submit-events defuns-and-theorems state))
              (generated-events-acc (append generated-events-acc defuns-and-theorems)) ;; new stuff comes at the end
              (postlude-alist (g :postlude-alist options))
              (postlude-event (lookup-loop-function loop-function-name loop-designator postlude-alist nil)) ;often a progn, or nil if there is none
              (state (if postlude-event
                         (submit-postlude postlude-event this-loop-number generated-events-acc state)
                       state))
              ;; Add the postlude events to the set of rules:
              (postlude-rule-names (extract-rule-names-from-event postlude-event))
              (postlude-rules (and postlude-rule-names
                                   (prog2$ (cw "(Adding postlude rules ~x0.)~%" postlude-rule-names)
                                           (make-axe-rules! postlude-rule-names (w state)))))
              (generated-events-acc (if postlude-event
                                        (append generated-events-acc (list postlude-event))
                                      generated-events-acc))
              (rules
               (append
                ;; openers for the exit test and update-function
                ;;fixme is this sort of thing used?
                (make-axe-rules! (list exit-test-function-name update-function-name) (w state))
                ;;constant opener (TODO: Just call make-axe-rules, as above?):
                (make-axe-rules-from-theorem-safe constant-opener-theorem-body
                                              constant-opener-theorem-name
                                              nil
                                              (w state))))
              (loop-function-body-translated (translate-term loop-function-body-untranslated 'decompile-loop (w state)))
              (interpreted-function-alist-for-this-function
               (acons exit-test-function-name
                      (list (list 'params) exit-test-function-body)
                      (acons update-function-name
                             (list (list 'params) update-function-body)
                             (acons loop-function-name
                                    (list (list 'params) loop-function-body-translated)
                                    ;;these get added below:
                                    (add-fns-to-interpreted-function-alist
                                     ;;Sat Mar  6 04:49:00 2010:
                                     nil ;;'(eval-dag-with-axe-evaluator dag-val-with-axe-evaluator)
                                     update-dag-interpreted-function-alist
                                     (w state))))))
              (interpreted-function-alist-alist
               (acons loop-function-name
                      interpreted-function-alist-for-this-function
                      interpreted-function-alist-alist))
              (- (cw "Done decompiling loop number ~x0.)~%" this-loop-number)))
           (mv nil
               t ;success
               new-state-dag
               generated-events-acc
               (append postlude-rules (append new-type-rules (append rules generated-rules-acc))) ;fixme some of these are not type rules!
               next-loop-number
               interpreted-function-alist-alist
               ;;fffixme check for consistency??
               (append interpreted-function-alist-for-this-function
                       interpreted-function-alist)
               state))
         (if erp
             (mv erp nil nil nil nil nil nil state)
           (if successp ;; We decompiled the loop:
               (mv nil
                   maybe-state-dag maybe-generated-events-acc maybe-generated-rules maybe-next-loop-number
                   maybe-interpreted-function-alist-alist maybe-interpreted-function-alist state)
             ;; TODO: Perhaps avoid this case (require explicit instructions to unroll the loop?):
             (progn$ (cw "(NOTE: Decompiling loop ~x0 failed, so we will try to unroll it.)~%" this-loop-number)
                     (decompile-loop-by-unrolling loop-pcs loop-top-state-dag hyps this-loop-number next-loop-number generated-rules-acc interpreted-function-alist-alist interpreted-function-alist print options
                                                  generated-events-acc ;not including events from the failed lift of the loop
                                                  state))))))))

 ;; STATE-DAG represents a MYIF nest with states at the branches (or possibly
 ;; just a single state).  For any branch that is at a loop header, this lifts
 ;; the loop corresponding loop and splices in the result.
 ;;TODO: If we use internal contexts when doing symbolic simulation, we can get ':irrelevant as a branch... (why doesn't the rewriter replace the whole if with the non-irrelevant branch?
 ;;Returns (mv erp state-dag generated-events-acc generated-rules-acc change-flg next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
 ;;where the new state-dag is equivalent to state-dag but with the loops at the leaves of the myif nest decompiled
 (defun decompile-loop-branches (state-dag
                                 hyps
                                 segment-call-stack-height ;what vars might be in this?
                                 segment-pcs
                                 tag
                                 loop-alist ;all loops in the program
                                 loop-depth
                                 next-loop-number
                                 generated-rules-acc
                                 initialized-classes
                                 other-input-vars
                                 indentation
                                 interpreted-function-alist-alist interpreted-function-alist
                                 class-table-map unroll-nested-loopsp extra-invarsp print
                                 options
                                 generated-events-acc
                                 state)
   (declare (xargs :mode :program :stobjs (state)))
   (let* ((expr (lookup (top-nodenum state-dag) state-dag)))
     (if (call-of 'jvm::make-state expr)
         ;; it's a make-state, so determine whether it has exited the segment (if not, it's at a loop header of a nested loop)
         (mv-let (erp call-stack-less-than-flg state)
            ;;ffixme see function stack-height-comparison
           (quick-simp-composed-term-and-dag `(comparison (jvm::call-stack-size (jvm::call-stack (th) replace-me))
                                                          ,segment-call-stack-height)
                                             'replace-me ;;state-var (this was bad?  what is state-var at this point?)
                                             state-dag
                                             :rule-alist *stack-height-axe-rule-alist*
                                             ;;fixme where else might we need these assumptions?
                                             :assumptions (prog2$ nil ;(if print (cw "hyps: ~x0" hyps) (cw "(hyps elided)~%"))
                                                                  hyps))
           (if erp
               (mv erp nil nil nil nil nil nil nil state)
             (let* ((call-stack-less-than-flg
                     (safe-unquote call-stack-less-than-flg)))
               (if (eq '< call-stack-less-than-flg)
                   ;;we've exited from the stack-height
                   (prog2$ (cw "(Branch has exited from the stack height (whoa).)~%")
                           (mv nil state-dag generated-events-acc generated-rules-acc nil next-loop-number interpreted-function-alist-alist interpreted-function-alist state))
                 (mv-let (erp pc state)
                   (get-dag-pc state-dag hyps state)
                   (if erp
                       (mv erp state-dag generated-events-acc generated-rules-acc nil next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
                     (let ((pc (safe-unquote2 'decompile-loop-branches
;fffixme this needs to take hyps. if the loop starts at pc 0, state-dag won't have an explicit PC subterm? or maybe the state-dag could just be s0, not even a make-state?
                                              pc
                                              ))) ;move into the if test?
                       (if (and (eq 'equal call-stack-less-than-flg)
                                (not (member pc segment-pcs)))
                           ;;we are at the same stack height and outside of the segment
                           (prog2$ (cw "(Branch has exited the loop body.)~%") ;deceptive message?
                                   (mv nil state-dag generated-events-acc generated-rules-acc nil next-loop-number interpreted-function-alist-alist interpreted-function-alist state))
                         ;;otherwise, we are at the header of a nested loop (TODO: why 'nested'?):
                         (let ((loop-number next-loop-number))
                           (mv-let (erp state-dag generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
                             (prog2$
                              (cw "(This branch is standing at a loop header:~%")
                              (decompile-loop pc
                                              state-dag
                                              hyps ;new - make sure this is okay
                                              loop-alist tag
                                              (+ 1 loop-depth)
                                              next-loop-number
                                              generated-rules-acc
                                              initialized-classes
                                              other-input-vars
                                              interpreted-function-alist-alist interpreted-function-alist
                                              class-table-map unroll-nested-loopsp extra-invarsp print options generated-events-acc state))
                             (if erp
                                 (mv erp nil nil nil nil nil nil nil state)
                               (mv nil
                                   (prog2$ (cw (concatenate 'string indentation "decompiled a loop (number ~x0, plus maybe some nested loops) on this branch.)~%") loop-number) state-dag)
                                   generated-events-acc
                                   generated-rules-acc
                                   t
                                   next-loop-number
                                   interpreted-function-alist-alist interpreted-function-alist state))))))))))))
       (if (call-of 'myif expr)
           (b* ((- (cw (concatenate 'string indentation "(handling a myif in decompile-loop-branches (depth ~x0).~%") loop-depth))
                (test (first (fargs expr)))
                (then-part (second (fargs expr)))
                (else-part (third (fargs expr)))
                (test-dag (get-subdag test state-dag)) ;todo: more direct way to get the size of one node in a dag? call size-of-node?
                (test-term (if (dag-or-quotep-size-less-thanp test-dag 1000)
                               (dag-to-term test-dag)
                             nil)) ;nil means it's too big (TODO: find a way to pass in this assumption as a dag node)
                (- (cw "(Test: ~x0)~%" test-term)))
             (mv-let (erp then-state-dag generated-events-acc generated-rules-acc then-flg next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
               (decompile-loop-branches (get-subdag then-part state-dag)
                                        ;; Assume the test of the ITE when decompiling the then part:
                                        (if test-term (cons test-term hyps) hyps)
                                        segment-call-stack-height
                                        segment-pcs tag loop-alist loop-depth next-loop-number generated-rules-acc
                                        initialized-classes other-input-vars
                                        (concatenate 'string " " indentation)
                                        interpreted-function-alist-alist interpreted-function-alist
                                        class-table-map unroll-nested-loopsp extra-invarsp print options generated-events-acc state)
               (if erp
                   (mv erp nil nil nil nil nil nil nil state)
                 (mv-let (erp else-state-dag generated-events-acc generated-rules-acc else-flg next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
                   (decompile-loop-branches (get-subdag else-part state-dag)
                                            ;; Assume the negation of the test of the ITE when decompiling the else part:
                                            (if test-term (cons (negate-term test-term) hyps) hyps)
                                            segment-call-stack-height
                                            segment-pcs tag loop-alist loop-depth next-loop-number generated-rules-acc
                                            initialized-classes other-input-vars
                                            (concatenate 'string " " indentation)
                                            interpreted-function-alist-alist interpreted-function-alist
                                            class-table-map unroll-nested-loopsp extra-invarsp print options generated-events-acc state)
                   (if erp
                       (mv erp nil nil nil nil nil nil nil state)
                     (if (or then-flg else-flg) ;use a general version of compose-term-and-dag here (need a version that allows multiple dags)
                         (b* (((mv erp then-nodenum state-dag)
                               (merge-dag-into-dag-quick ;merge-dags-allows-constants2
                                then-state-dag
                                state-dag))
                              ((when erp) (mv erp nil nil nil nil nil nil nil state))
                              ((mv erp else-nodenum state-dag)
                               (merge-dag-into-dag-quick ;merge-dags-allows-constants2
                                else-state-dag
                                state-dag))
                              ((when erp) (mv erp nil nil nil nil nil nil nil state))
                              ((mv nodenum dag)
                               (add-to-dag (prog2$ (cw "adding ITE node to dag~%")
                                                   `(myif ,test ,then-nodenum ,else-nodenum))
                                           state-dag)))
                           (mv nil
                               (prog2$ (cw (concatenate 'string indentation "done handling myif.)~%"))
                                       (get-subdag nodenum dag))
                               generated-events-acc
                               generated-rules-acc
                               t
                               next-loop-number
                               interpreted-function-alist-alist interpreted-function-alist state))
                       (mv nil
                           (prog2$ (cw (concatenate 'string indentation "done handling myif -- nothing changed.)~%")) state-dag)
                           generated-events-acc
                           generated-rules-acc
                           nil
                           next-loop-number
                           interpreted-function-alist-alist interpreted-function-alist state)))))))
               ;;it's neither a make-state nor a myif (TODO: What if it's just a variable?):
               (mv t
                   (er hard? 'decompile-loop-branches "Unexpected expression (expected a myif-nest of make-states): ~x0" expr)
                   generated-events-acc
                   nil
                   nil
                   next-loop-number
                   interpreted-function-alist-alist interpreted-function-alist state)))))

 ;; Decompile the given code segment, including any loops, by repeatedly 1) Running all branches forward until they exit the segment or hit a loop, and 2) Decompiling any branches that are at loops.
 ;;returns (mv erp state-dag generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
 (defun decompile-code-segment-aux (state-dag ;; either a variable s0, s1, etc. or such a var with static initializers run on it?
                                    hyps
                                    segment-call-stack-height ;a term representing the stack-height of the segment of code we are decompiling (fffixme what vars can this mention?)
                                    segment-pcs ;;the pcs of the code we are decompiling (should not include the loop header if we are decompiling its body)
                                    tag
                                    loop-depth
                                    step-once-to-startp ;todo: instead, have the caller step the state once and then remove this param...
                                    loop-alist ;all loops in the program
                                    next-loop-number
                                    generated-rules-acc
                                    initialized-classes ;a list of strings
                                    other-input-vars
                                    interpreted-function-alist-alist interpreted-function-alist
                                    class-table-map unroll-nested-loopsp extra-invarsp print options generated-events-acc state)
   (declare (xargs :mode :program :stobjs (state)))
   ;;First we run until we exit the segment or hit a loop header:
   ;; fixme - could check first whether we even need to run..
   (b* ((- (cw "(Attempting to run until all branches hit a loop or exit the segment.~%(stack height: ~x0)~%(ifns ~x1)~%(hyps: ~x2)~%"
               segment-call-stack-height
               (if (and print (not (eq :brief print))) (strip-cars interpreted-function-alist) :elided)
               (if print hyps :elided)))
        ;; (- (cw "(Rules: ~x0)" generated-rules-acc))
        (loop-headers (strip-cars loop-alist))
        ;; (- (cw "(Loop headers: ~x0)" loop-headers)) ;we could print these just for this class
        ((mv erp dag-to-run) (compose-term-and-dag
                     `(run-until-exit-segment-or-hit-loop-header
                       ,segment-call-stack-height
                       ',segment-pcs ;does not include the header of the current loop
                       ',loop-headers
                       ;; if we are at a loop header, we'll need to step the state once to get past it:
                       ,(if step-once-to-startp `(jvm::step-always-open (th) replace-me) 'replace-me))
                     'replace-me
                     state-dag))
        ((when erp) (mv erp nil nil nil nil nil nil state))
        (symbolic-execution-rules (g :symbolic-execution-rules options))
        (rule-alists (list
                      ;;no trim rules, etc., in hopes that rotates will be introduced:
                      (extend-rule-alist2
                       (append (and (g :ignore-exceptions options) *ignore-exception-axe-rule-set*)
                               (and (g :ignore-errors options) *ignore-error-state-axe-rule-set*)
                               generated-rules-acc)
                       (make-rule-alist! (set-difference-eq
                                         (append
                                          (g :extra-rules options)
                                          (set-difference-equal
                                           (append ;we wait before applying trim rules (so that the rotate idioms can be turned into real rotates)
                                            (lifter-rules)
                                            symbolic-execution-rules
                                            )
                                           (append ;;(core-rules-bv) ;bad idea..
                                            '(LEFTROTATE32-OPEN-WHEN-CONSTANT-SHIFT-AMOUNT
                                              BVOR-WITH-SMALL-ARG2
                                              GETBIT-OF-BVXOR
                                              BVSHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT
                                              BVSHL-REWRITE-WITH-BVCHOP-FOR-CONSTANT-SHIFT-AMOUNT
                                              BVASHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT ;Sun Dec 26 01:15:28 2010
                                              )
                                            (trim-rules))))
                                         (g :remove-rules options))
                                        (w state))
                       (w state))
                      ;;now includes the trim rules, etc.:
                      (extend-rule-alist2
                       (append (and (g :ignore-exceptions options) *ignore-exception-axe-rule-set*)
                               (and (g :ignore-errors options) *ignore-error-state-axe-rule-set*)
                               generated-rules-acc)
                       (make-rule-alist! (set-difference-equal
                                         (append
                                          (g :extra-rules options)
                                          (append ;would like to wait before applying trim rules (so that the rotate patterns can be seen)
                                           (lifter-rules)
                                           symbolic-execution-rules))
                                         (g :remove-rules options))
                                        (w state))
                       (w state))))
        ;; Symbolically execute the DAG to push it forward:
        ((mv erp state-dag state)
         (simp-dag
          dag-to-run
          :rule-alists rule-alists
          :interpreted-function-alist interpreted-function-alist ;Thu Jul 29 02:45:04 2010
          :monitor (append '( ;; get-class-of-inner-array-2d
                             ;;RUN-UNTIL-EXIT-SEGMENT-OR-HIT-LOOP-HEADER-OPENER-2;;
                             ;;RUN-UNTIL-EXIT-SEGMENT-OR-HIT-LOOP-HEADER-OPENER-1;;
                             ;;JVM::INVOKE-STATIC-INITIALIZER-FOR-NEXT-CLASS-BASE
                             )
                           (g :monitor options))
          :assumptions hyps
          :simplify-xorsp nil
          :print-interval 10000
          :print print ;;:print t
          :use-internal-contextsp t ;trying this... Wed Apr 29 16:32:19 2015 ;;this leads to occurrences of ':irrelevant
          :check-inputs nil
          ))
        ((when erp) (mv erp nil nil nil nil nil nil state))
        ;; Prune unreachable branches:
        ;; TODO: May need to repeatedly prune branches and rewrite?
        ((mv erp state-dag state)
         (maybe-prune-dag (g :prune-branches options)
                          state-dag
                          hyps
                          (set-difference-eq
                           ;;todo: improve?:
                           (append (amazing-rules-spec-and-dag)
                                   (map-rules)
                                   ;; (jvm-semantics-rules)
                                   (jvm-simplification-rules)
                                   (g :extra-rules options))
                           (g :remove-rules options))
                          (g :monitor options)
                          (g :call-stp options)
                          state))
        ((when erp) (mv erp nil nil nil nil nil nil state))
        (- (cw " Done attempting to run all branches.)~%")))
     (if (member-eq 'run-until-exit-segment-or-hit-loop-header (dag-fns state-dag))
         (progn$ (cw "~%DAG:~X01~%" state-dag nil)
                 (cw "hyps: ~x0" hyps)
                 (cw "~%ERROR: DAG still contains calls of run-until-exit-segment-or-hit-loop-header~%")
                 (maybe-print-info-on-exception-branches state-dag)
                 (mv t
                     (hard-error 'decompile-code-segment-aux "didn't finish the run. See the state DAG, hyps, and notes printed above." nil)
                     nil nil nil nil nil state))
       ;;the run ended because each branch either exited from the stack height, left the code segment, or hit a loop header.
       ;;For each branch that hit a loop header, we need to decompile the loop and splice the result back into the state-dag.
       ;;Then we have to continue running all the branches on which loops were decompiled
       ;;fixme print the number of branches?
       (progn$ ;fixme what if there are none of these?
        (cw "(All branches seemed to run without error.)~%")
        (cw "(State DAG after running all branches:~%")
        (if print (print-list state-dag) (cw ":ELIDED"))
        (cw ")~%")
        (cw "(Decompiling loop branches~% (segment-call-stack-height: ~x0)~%" segment-call-stack-height)
        (and print (cw "(state-dag:~%"))
        (and print (print-list state-dag))
        (and print (cw "~%)"))
        (mv-let (erp state-dag2 ;details of this?
                 generated-events-acc generated-rules-acc change-flg next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
          (decompile-loop-branches state-dag
                                   hyps
                                   segment-call-stack-height
                                   segment-pcs ;;the pcs of the code we are decompiling (should not include the loop header if we are decompiling its body)
                                   tag
                                   loop-alist ;all loops in the program
                                   loop-depth
                                   next-loop-number
                                   generated-rules-acc
                                   initialized-classes
                                   other-input-vars
                                   "" ;indentation
                                   interpreted-function-alist-alist interpreted-function-alist
                                   class-table-map unroll-nested-loopsp extra-invarsp print options generated-events-acc state)
          (if erp
              (mv erp nil nil nil nil nil nil state)
            (prog2$
             (cw "Done decompiling loop branches.)~%")
             (if (not change-flg) ;no loops were decompiled
                 (if (member-eq 'run-until-exit-segment-or-hit-loop-header (dag-fns state-dag2)) ;TODO: impossible?
                     (mv t
                         (hard-error 'decompile-code-segment-aux "Could not finish executing.  DAG:~X01"
                                     (acons #\0 state-dag2 (acons #\1 nil nil)))
                         nil nil nil nil nil state)
                   (progn$ (cw "No nested loops were decompiled (print is ~x0.)~%" print) ;todo: print loop-depth
                           (cw "(state dag:~%")
                           (if print (print-list state-dag) (cw "elided~%"))
                           (cw ")~%")
                           (mv nil
                               state-dag
                               generated-events-acc generated-rules-acc next-loop-number
                               interpreted-function-alist-alist interpreted-function-alist state)))
               ;;otherwise, we decompiled a loop at some leaf, so keep running:
               (decompile-code-segment-aux
                (prog2$ (cw "(continuing since we decompiled at least one nested loop.)~%") ;;TODO: Why does this say "nested"?
                        state-dag2)
                hyps
                segment-call-stack-height
                segment-pcs
                tag
                loop-depth
                nil ;step-once-to-startp
                loop-alist
                next-loop-number
                generated-rules-acc
                initialized-classes
                other-input-vars
                interpreted-function-alist-alist interpreted-function-alist
                class-table-map unroll-nested-loopsp extra-invarsp print
                options
                generated-events-acc
                state)))))))))

 ;; Completely decompile a segment of code, including all subroutine calls (TODO: relax this to be compositional) and nested loops.
 ;;returns (mv erp state-dag generated-events-acc generated-rules next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
 ;;... where state-dag is, in general, a myif nest with make-states at the leaves
 ;;each leaf has been executed until it left the segment (exited the PC range or exited from the stack height)
 ;;todo: for a loop with multiple exits, should we try to recombine the branches?
 ;;This is the entry point for the clique of functions.
 (defun decompile-code-segment (state-dag ;; either a variable s0, s1, etc. or such a var with static initializers run on it?
                                hyps ;;hyps over state-var (previous state vars?) that tell us what code is running, etc. (may also mention other inputs to the program?)
                                segment-pcs ;;the pcs of the code we are decompiling (should not include the loop header if we are decompiling its body)
                                tag
                                loop-depth
                                step-once-to-startp
                                loop-alist ;all loops in the program (or, at least, all loops that we are not unrolling)
                                next-loop-number
                                generated-rules-acc ;do we use this?
                                initialized-classes
                                other-input-vars ;how are these used?
                                interpreted-function-alist-alist ; maps each generated function to the interpreted-function-alist for the fns it calls?
                                interpreted-function-alist
                                class-table-map unroll-nested-loopsp extra-invarsp print
                                options
                                generated-events-acc
                                state)
   (declare (xargs :mode :program
                   :stobjs (state)
                   :guard (and (pseudo-term-listp hyps) ;TODO add more to the guard
                               ;(invariant-alistp (g :invariant-alist options) state) ;TODO: Make a decompiler-optionsp?
                               )))
   (b* ( ;; Get the stack-height (we do this once, outside of decompile-code-segment-aux):
        ((mv erp stack-height-dag state)
         (quick-simp-composed-term-and-dag `(stack-height state-var) 'state-var state-dag
                                           ;;pass in ifns?
                                           ;; do we need assumptions here (what if state-dag is a var?)?
                                           :rule-alist *stack-height-axe-rule-alist*))
        ((when erp) (mv erp nil nil nil nil nil nil state))
        (- (cw "(Decompiling code segment (~x0 hyps) (print is ~x1) (pcs: ~x2)~%" (len hyps) print segment-pcs))
        ;; Repeatedly push all branches forward and decompile any nested loop encountered:
        ((mv erp state-dag generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist state)
         (decompile-code-segment-aux state-dag
                                     hyps
                                     (dag-to-term stack-height-dag)
                                     segment-pcs
                                     tag
                                     loop-depth
                                     step-once-to-startp
                                     loop-alist
                                     next-loop-number
                                     generated-rules-acc
                                     initialized-classes
                                     other-input-vars
                                     interpreted-function-alist-alist interpreted-function-alist
                                     class-table-map unroll-nested-loopsp extra-invarsp
                                     print options
                                     generated-events-acc
                                     state))
        ((when erp) (mv erp nil nil nil nil nil nil state))
        (- (cw "Done decompiling code segment.)~%")))
     (mv (erp-nil)
         state-dag generated-events-acc generated-rules-acc next-loop-number interpreted-function-alist-alist interpreted-function-alist
         state)))

 ) ;end mutual-recursion

;STATE-DAG should be in terms of the input variables and should be poised to execute a loop
;to find invariants for a loop (starting from a loop-top state, s0, where we know some stuff)
;make set of predicates, each saying that some expression over s is whatever that expression evaluates to over s0
;repeatedly:
; decompile the loop body to get a term and try to show that each predicate holds on the term (assuming all the preds still under consideration)
;  throw out the predicates that fail to hold
;conjoin the predicates that remain to make the invariant

;how exactly do we get the predicates?!?!
;maybe we precompute them for each program point

;; Returns (mv erp state-dag ;;expressed as a modification of the initial state, s0? and other inputs?
;;            generated-events
;;           generated-rules interpreted-function-alist-alist interpreted-function-alist state)
;; Loops are numbered starting at 1 (but some may be skipped, if a loop is unrolled?)
;; OPTIONS may contain:
;; :invariant-alist ;the keys are of the form (list <loop-pc> <class-name> <method-name> <method-descriptor>) and the invars are about the special var 'state-var
;; :measures
;; :measure-hints-alist
;; ...?
;; This is really initialize-classes-and-decompile-code-segment
(defun decompile-program (hyps ;;hyps over s0 that tell us what code is running, etc. can also mention the input variables!
                          segment-pcs ;;the pcs of the code we are decompiling (should not include the loop header if we are decompiling its body)
                          tag ;the "name" of the program being decompiled (gets prepended to all loop function names)
                          other-input-vars
                          unroll-nested-loopsp extra-invarsp
                          print
                          classes-to-assume-initialized
                          options
                          state)
  (declare (xargs :mode :program
                  :stobjs (state)
                  :guard (and (symbolp tag)
                              ;(invariant-alistp (g :invariant-alist options) state)
                              (subsetp-eq (get-vars-from-terms hyps) (cons 's0 other-input-vars))
                              (or (string-listp classes-to-assume-initialized)
                                  (eq :all classes-to-assume-initialized)))))
  ;;FFIXME is it cheating to run all class initializers first?
  (b* ((- (cw "(Decompiling program ~x0~%" tag))
       (class-alist (global-class-alist state))
       (class-table-map (alist-to-map class-alist))
       (all-class-names (strip-cars class-alist)) ; What if not all classes in the class table will actually be used?
       ((when (and (not (eq :all classes-to-assume-initialized))
                   (not (subsetp-equal classes-to-assume-initialized all-class-names))))
        (prog2$ (er hard 'decompile-program "The following classes are not included in the ACL2 session (add include-books for them): ~x0." (set-difference-equal classes-to-assume-initialized all-class-names))
                (mv t nil nil nil nil nil state)))
       (classes-to-assume-initialized (if (eq :all classes-to-assume-initialized)
                                          all-class-names
                                        classes-to-assume-initialized))
       (class-names-to-initialize (set-difference-equal all-class-names classes-to-assume-initialized))
       (- (cw "(Initializing ~x0 classes:~%" (len class-names-to-initialize)))
       (initialized-class-names (union-equal classes-to-assume-initialized
                                             '("java.lang.Object" "java.lang.System") ;;FIXME we assume that these classes are already initialized
                                             ))
       (- (cw "Assuming these classes are already initialized: ~x0~%" initialized-class-names))
       (extra-rules (g :extra-rules options))
       (monitored-rules (g :monitor options))
       ((mv erp initialized-state-dag state)
        (initialize-classes-in-s0 class-names-to-initialize
                                  initialized-class-names ;classes already initialized
                                  class-table-map
                                  extra-rules
                                  monitored-rules
                                  state))
       ((when erp) (mv erp nil nil nil nil nil state))
       ;; Extract the list of initialized classes, after class initialization:
       ((mv erp ic-dag)
        (compose-term-and-dag `(jvm::initialized-classes replace-me) 'replace-me initialized-state-dag))
       ((when erp) (mv erp nil nil nil nil nil state))
       ((mv erp initialized-class-names state) ;fixme don't we know what these should be, since we just ran the initializers?  (maybe some more have gotten sucked in?)
        (simp-dag ic-dag
                  :rules (append '(bool-fix$inline)
                                 (rule-list-1001))
                  :simplify-xorsp nil
                  :check-inputs nil))
       ((when erp) (mv erp nil nil nil nil nil state))
       (initialized-class-names (safe-unquote initialized-class-names))
       ;; Extract the heap after class initialization:
       ((mv erp h-dag)
        (compose-term-and-dag `(jvm::heap replace-me) 'replace-me initialized-state-dag))
       ((when erp) (mv erp nil nil nil nil nil state))
       ((mv erp heap-dag state)
        (simp-dag h-dag
                  :rules (append '(bool-fix$inline)
                                 (rule-list-1001))
                  :simplify-xorsp nil
                  :check-inputs nil))
       ((when erp) (mv erp nil nil nil nil nil state))
       ;;fixme i hope this is not too big:
       (heap (dag-to-term heap-dag))
       ;; Extract the static-field-map after class initialization: (can we do this better somehow?)
       ((mv erp sfm-dag)
        (compose-term-and-dag `(jvm::static-field-map replace-me)
                              'replace-me
                              initialized-state-dag))
       ((when erp) (mv erp nil nil nil nil nil state))
       ((mv erp static-field-map state)
        (simp-dag sfm-dag
         :rules (append '(bool-fix$inline)
                        (rule-list-1001))
         :simplify-xorsp nil
         :check-inputs nil))
       ((when erp) (mv erp nil nil nil nil nil state))
       ;;fixme i hope this is not too big:
       (static-field-map (dag-to-term static-field-map))
       (- (cw "The following classes were initialized: ~x0~%Done Initializing classes.)~%" initialized-class-names))
       (loop-alist (get-loops-from-classes class-alist))
       ((mv erp make-state-dag)
        ;;this state is like s0 but reflects the initialization:
        ;;fixme can't we make this more directly from initialized-state-dag?
        (dagify-term2 `(jvm::make-state (jvm::thread-table s0)
                                        ,heap ;todo: improve
                                        (jvm::class-table s0)
                                        (jvm::heapref-table s0)
                                        (jvm::monitor-table s0)
                                        ,static-field-map ;todo: improve
                                        (jvm::initialized-classes s0)
                                        (jvm::intern-table s0))))
       ((when erp) (mv erp nil nil nil nil nil state))
       ((mv erp
            state-dag generated-events generated-rules
            & ;next-loop-number
            interpreted-function-alist-alist interpreted-function-alist state)
        (decompile-code-segment
         make-state-dag
         (remove-duplicates-equal ;drop?
          (append (assumptions-that-classes-are-initialized initialized-class-names 's0) ;;  `((equal (jvm::initialized-classes s0) ',initialized-class-names)) ;we also pass around the list of initialized classes in the main mut rec...i guess we now also pass in the heap and thread table above..
                  (standard-hyps 's0)
                  (class-table-hyps 's0 class-table-map)
                  hyps))
         segment-pcs
         tag
         0           ;loop depth
         t           ;nil            ;step-once-to-startp
         loop-alist  ;all loops in the program
         1           ;next-loop-number
         nil ;generated-rules-acc
         initialized-class-names
         other-input-vars
;fffixme what other fns might appear in the dag for a loop update function?
;initial interpreted-function-alist-alist:
         nil ;;(acons 'dag-val-with-axe-evaluator (make-interpreted-function-alist '(dag-val-with-axe-evaluator eval-dag-with-axe-evaluator) (w state)) nil)
         nil ;initial interpreted-function-alist
         class-table-map unroll-nested-loopsp extra-invarsp
         print options
         nil ;;generated-events-acc
         state))
       ((when erp)
        (mv erp nil nil nil nil nil state))
       (- (cw "Done decompiling program ~x0.)~%" tag)))
    (mv nil
        state-dag generated-events generated-rules
        interpreted-function-alist-alist interpreted-function-alist state)))

;; The core function of the lifter
;Returns (mv erp event state)
(defun lift-java-code-fn (method-designator-string
                          program-name ; the name of the program to generate, a symbol which will be added onto the front of generated function names.
                          param-names ; usually not used
                          array-length-alist
                          output-indicator
                          user-assumptions
                          classes-to-assume-initialized
                          print
                          ignore-exceptions
                          ignore-errors
                          invariants
                          guard ;guard to use for the top-level function
                          loop-guards ;a list of non-dotted pais that associate loop-ids to guards for the corresponding loop functions
                          measures ;a list of non-dotted pairs of loop-designators and expressions (special case: if a key is a natural number, it is taken to be a PC in the main method being lifted)
                          measure-hints ;a list of non-dotted pairs
                          max-term-size
                          assume-invariants-initially
                          check-guards-in-functions
                          excluded-locals
                          inline
                          extra-rules
                          remove-rules
                          monitor
                          postludes
                          extra-invars
                          other-input-vars ;todo: just harvest these from the assumptions?
                          prune-branches
                          loops-to-unroll
                          use-prover-for-invars
                          branches
                          call-stp
                          use-lets-in-terms
                          disable-loop-openers
                          whole-form
                          state)
  (declare (xargs :stobjs (state)
                  :guard (and ;;(pseudo-term-listp user-assumptions) ;now these can be untranslated terms, so we translate them below
                          (booleanp ignore-exceptions)
                          (booleanp ignore-errors)
                          (booleanp inline)
                          (booleanp extra-invars)
                          (or (string-listp classes-to-assume-initialized)
                              (eq :all classes-to-assume-initialized))
                          (symbol-listp other-input-vars)
                          (all-loop-designatorp loops-to-unroll)
                          (or (member-eq call-stp '(t nil))
                              (natp call-stp))
                          (booleanp use-prover-for-invars)
                          (or (eq branches :smart)
                              (eq branches :split))
                          (symbol-listp param-names) ;; todo: what else to check here?
                          (booleanp disable-loop-openers)
                          )
                  :mode :program))
  (b* ( ;; Check whether an identical call to the lifter has already been done:
       ((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ;; Check inputs (TODO: What other checks should we do here?):
       ;; ((when (not (input-source-alistp input-source-alist)))
       ;;  (mv t (er hard 'lift-java-code "ERROR: Ill-formed input-source-alist!") state))
       ((when (not (output-indicatorp output-indicator)))
        (mv t (er hard 'lift-java-code "ERROR: Ill-formed output-indicator!") state))
       ((when (not (invariantsp invariants)))
        (mv t (er hard 'lift-java-code "ERROR: Ill-formed invariants!") state))
       ((when (not (excluded-localsp excluded-locals)))
        (mv t (er hard 'lift-java-code "ERROR: Ill-formed excluded-locals!") state))
       ((when (not (measuresp measures state)))
        (mv t (er hard 'lift-java-code "ERROR: Ill-formed measures!") state))
       ((when (not (measure-hintsp measure-hints)))
        (mv t (er hard 'lift-java-code "ERROR: Ill-formed measure-hints!") state))
       ((when (not (loop-guardsp loop-guards)))
        (mv t (er hard 'lift-java-code "ERROR: Ill-formed guards!") state))
       ((when (not (postludesp postludes)))
        (mv t (er hard 'lift-java-code "ERROR: Ill-formed postludes!") state))
       ;; Gather info about the main method to be lifted:
       (method-class (extract-method-class method-designator-string))
       (method-name (extract-method-name method-designator-string))
       (method-descriptor (extract-method-descriptor method-designator-string))
       (class-alist (global-class-alist state)) ;todo: redone in decompile-program
;TODO: Combine with similar code in unroll-java-code
       (class-info (lookup-equal method-class class-alist))
       ((when (not class-info))
        (prog2$ (cw "ERROR: Error getting the class info for ~x0" method-class)
                (mv t nil state)))
       (method-info (lookup-equal (cons method-name method-descriptor) (jvm::class-decl-methods class-info)))
       ((when (not method-info))
        (prog2$ (cw "ERROR: Couldn't find info for method ~x0 with descriptor ~x1 in class ~x2.  Existing methods are ~x3."
                    method-name method-descriptor method-class (strip-cars (jvm::class-decl-methods class-info)))
                (mv t nil state)))
       (code (lookup-eq :program method-info))
       ((when (not code))
        (prog2$ (cw "ERROR: Couldn't find code for method ~x0 with descriptor ~x1 in class ~x2" method-name method-descriptor method-class)
                (mv t nil state)))
       (local-variable-table (lookup-eq :local-variable-table method-info)) ;may be nil
       ((when (not (jvm::local-variable-tablep local-variable-table)))
        (prog2$ (er hard 'lift-java-code-fn "Ill-formed local variable table: ~x0." local-variable-table)
                (mv t nil state)))
       (static-flag (jvm::method-staticp method-info))
       (param-slot-to-name-alist (make-param-slot-to-name-alist method-info param-names))
       (param-name-to-slot-alist (reflect-alist param-slot-to-name-alist))
       ;; ((when (and (not input-source-alist)
       ;;             (not local-variable-tablep)))
       ;;  (prog2$ (hard-error 'lift-java-code-fn "We don't know the names of the inputs because no input-source-alist was supplied and no local-variable-table is present (consider recompiling the code with the -g flag to create the local variable table)." nil)
       ;;          (mv t nil state)))
;       (parameter-types (lookup-eq :parameter-types method-info))
       ;; (input-source-alist (or input-source-alist
       ;;                         ;(make-input-source-alist parameter-types local-variable-table static-flag)
       ;;                         ))
       (locals-term `(jvm::locals (jvm::thread-top-frame (th) s0)))
       (heap-term `(jvm::heap s0))
       ((mv param-assumptions param-input-vars)
        (param-assumptions-and-vars method-info array-length-alist locals-term heap-term param-slot-to-name-alist))
       ;; Translate and desugar user-supplied assumptions:
       (user-assumptions (translate-terms user-assumptions 'lift-java-code-fn (w state))) ;throws an error on bad input
;       (local-vars-at-pc-0 (merge-sort-local-vars-for-pc (local-vars-for-pc 0 local-variable-table))) ;may be nil if there is no local-variable-table
;       (- (cw " (Locals at PC 0: ~x0)~%" local-vars-at-pc-0)) ;todo: might there be locals that are not params?
       (user-assumptions (desugar-params-in-assumption-terms user-assumptions 's0 param-name-to-slot-alist))
       (user-assumptions (desugar-calls-of-contents-in-terms user-assumptions heap-term))
       ;; Check that the :assumptions don't call var (a common mistake).  ;TODO: or should we allow this?
       ((when (intersection-eq (all-ffn-symbs-lst user-assumptions nil)
                               '(var)))
        (mv t
            (er hard 'lift-java-code "Assumptions should not call VAR (just mention the var as a symbol)")
            state))
       (assumptions-about-this (if static-flag
                                   nil ;no assumptions about "this" for a static method
                                 `((addressp (jvm::nth-local '0 (jvm::locals (jvm::thread-top-frame (th) s0))))
                                   (not (null-refp (jvm::nth-local '0 (jvm::locals (jvm::thread-top-frame (th) s0))))) ;might be implied by addressp?
                                   ;;todo: add assumption about the class of "this" (what can we say)?
                                   )))
       (assumptions (append (list `(jvm::jvm-statep s0))
                            param-assumptions user-assumptions assumptions-about-this)) ;these can be about the input-vars.  If we want an assumption about the state itself, should use s0 for the state?? a pseudo-term-listp
       (- (cw "Will lift with these assumptions: ~x0." assumptions))
       (measures-option       (elaborate-measures-option               measures        method-class method-name method-descriptor)) ;special treatment to support a single keyword
       (measure-hints-alist   (elaborate-loop-function-ids-in-doublets measure-hints   method-class method-name method-descriptor :measure-hints))
       (invariant-alist       (elaborate-loop-function-ids-in-doublets invariants      method-class method-name method-descriptor :invariants))
       (excluded-locals-alist (elaborate-loop-function-ids-in-doublets excluded-locals method-class method-name method-descriptor :excluded-locals))
       (loop-guard-alist      (elaborate-loop-function-ids-in-doublets loop-guards     method-class method-name method-descriptor :loop-guards))
       (postlude-alist        (elaborate-loop-function-ids-in-doublets postludes       method-class method-name method-descriptor :postludes))
       (symbolic-execution-rules (if (eq branches :split)
                                     (run-until-exit-segment-or-hit-loop-header-rules-split)
                                   (run-until-exit-segment-or-hit-loop-header-rules-smart)))
       ;;a map (TODO: why not an alist?) including options other than the ones passed here explicitly:
       (options (s :measures-option measures-option
                   (s :measure-hints-alist measure-hints-alist
                      (s :invariant-alist invariant-alist
                         (s :excluded-locals-alist excluded-locals-alist
                            (s :loop-guard-alist loop-guard-alist
                               (s :postlude-alist postlude-alist
                                  (s :max-term-size max-term-size
                                     (s :ignore-exceptions ignore-exceptions
                                        (s :ignore-errors ignore-errors
                                           (s :call-stp call-stp
                                              (s :loops-to-unroll loops-to-unroll
                                                 (s :prune-branches prune-branches
                                                    (s :extra-rules extra-rules
                                                       (s :remove-rules remove-rules
                                                          (s :check-guards-in-functions check-guards-in-functions
                                                             (s :assume-invariants-initially assume-invariants-initially
                                                                (s :inline inline
                                                                   (s :monitor monitor
                                                                      (s :use-prover-for-invars use-prover-for-invars
                                                                         (s :symbolic-execution-rules symbolic-execution-rules
                                                                            (s :use-lets-in-terms use-lets-in-terms
                                                                               (s :disable-loop-openers disable-loop-openers
                                                                                  nil)))))))))))))))))))))))
       (input-vars (append param-input-vars other-input-vars)) ;input variables (assumptions can be about these, and they become params of the generated function) , a symbol-listp
       ;;((mv erp event state)
;todo: clean up here:
       (extra-invarsp extra-invars) ;add to options?
       ;; Do the decompilation:
       ((mv erp final-state-dag generated-events generated-rules
            & ;interpreted-function-alist-alist  ;fixme think about this.
            interpreted-function-alist state)
        (decompile-program
         (append (code-hyps 0 method-info method-class method-name method-descriptor 's0)
                 assumptions)
         (jvm::get-pcs-from-program code)
         program-name
         input-vars
         nil ;don't unroll nested loops
         extra-invarsp
         print ;t   ;:brief
         classes-to-assume-initialized
         options
         state))
       ((when erp) (mv erp nil state))
       (- (and print (progn$ (cw "(Dag before extracting outputs:~%")
                             (print-list final-state-dag)
                             (cw ")~%"))))
       ;; Extract the term representing the output:
       (return-type (lookup-eq :return-type method-info))
       ((mv erp output-dag state)
        (extract-output-dag output-indicator final-state-dag
                            (append assumptions)
                            '(jvm::locals (JVM::thread-top-frame (th) s0))
                            return-type
                            class-alist
                            state))
       ((when erp) (mv erp nil state))
       ;; TODO: This seemed necessary, but why?!:  maybe because for :array-return-value, we have multiple occs of the IF nest in the output term and then the getfield-of-myif rules fire
       ;; handle better since the two if nests are in sync...
       ((mv erp output-dag state)
        (maybe-prune-dag (g :prune-branches options)
                         output-dag
                         assumptions ;todo think about this
                         (set-difference-eq
                           ;todo: improve?:
                          (append (amazing-rules-spec-and-dag)
                                  (map-rules)
                                  ;; (jvm-semantics-rules)
                                  (jvm-simplification-rules)
                                  (g :extra-rules options))
                          (g :remove-rules options))
                         (g :monitor options)
                         (g :call-stp options)
                         state))
       ((when erp) (mv erp nil state))
       (- (and print (progn$ (cw "(Output DAG:~%")
                             (print-list output-dag)
                             (cw ")~%"))))
       (dag-vars (dag-vars output-dag)) ; these get sorted below
       ;; TODO: Shouldn't we just add inputs automatically for this new stuff?
       (- (and (not (subsetp-eq dag-vars input-vars))
               (cw "WARNING: Unexpected variables, ~x0, appear in the DAG.  At this point only input vars should remain.  If state vars such as S0 remain, consider identifying additional state components that should be considered inputs (using input-vars plus assumptions that equate the state components with the new input vars).~%"  (set-difference-eq dag-vars input-vars))))
       (dag-vars (sort-vars-with-guidance dag-vars input-vars))
       ;; Maybe sure s0, etc do not appear (does this happen when locals need to be excluded?):
       ;;(- (check-dag-vars input-vars output-dag)) ;;check that the vars of this DAG only include the vars in INPUT-VARS ! TODO: better error message here
       (top-fn-body (dag-to-term-limited output-dag max-term-size use-lets-in-terms interpreted-function-alist))
       (event
        `(progn
           (cw-event "(Processing ~x0 generated events...~%" ,(len generated-events)) ;todo: print the names?
           ,@generated-events
           (cw-event "Done Processing generated events.)~%")
           (defun ,(pack$ program-name '-generated-rules) ()
             (declare (xargs :normalize nil))
             ',generated-rules)
           (defun ,program-name ,dag-vars
             (declare (xargs :normalize nil
                             ,@(if guard `(:guard ,guard) nil)
                             :verify-guards nil))
             ,top-fn-body))))
    (mv nil ; no error
        (extend-progn (extend-progn event `(table lift-java-code-table ',whole-form ',event))
                      `(value-triple ',program-name))
        state)))

;; The main way to call the lifter.
;; The actual code should have been already stored in the GLOBAL-CLASS-TABLE (in the books generated by build-book-for-class).
;; NOTE: Keep this in sync with SHOW-LIFT-JAVA-CODE below.
;; TODO: Consider re-playing with :print t if the lift attempt fails.
;; TODO: Suppress more printing if :print is nil.
(defmacro lift-java-code (&whole whole-form
                                 method-designator-string
                                 program-name ; the name of the program to generate, a symbol which will be added onto the front of generated function names.
                                 &key
                                 (param-names 'nil)
                                 (output ':auto) ;an output-indicatorp
                                 (array-length-alist 'nil)
                                 (assumptions 'nil)
                                 (classes-to-assume-initialized 'nil)
                                 (print 'nil)
                                 (ignore-exceptions 'nil)
                                 (ignore-errors 'nil)
                                 (invariants 'nil)
                                 (guard 'nil)
                                 (loop-guards 'nil)
                                 (max-term-size '*max-term-size*)
                                 (measures ':acl2) ;; (measures ':auto)  ;FFIXME put this back once it works (either need to flatten params in the lifter or have with-auto-termination handle params that are tuples better)
                                 (measure-hints 'nil)
                                 (assume-invariants-initially 'nil) ;;Assume invariants hold at the top of each loop; dangerous!
                                 (check-guards-in-functions 'nil)
                                 (excluded-locals 'nil)
                                 (inline 't) ;whether to inline the loop termination test and exit test
                                 (extra-rules 'nil)
                                 (remove-rules 'nil)
                                 (monitor 'nil)
                                 (postludes 'nil)
                                 (extra-invars 'nil)
                                 (other-input-vars 'nil) ;TODO: Document!
                                 (show-only 'nil)
                                 (prune-branches 'nil) ;TODO: Document!  TODO: Change the defaut to something like 10000?
                                 (loops-to-unroll 'nil) ;todo: document
                                 (call-stp 'nil)
                                 (use-lets-in-terms 'nil)
                                 (use-prover-for-invars 'nil) ;todo: consider T
                                 (branches ':split) ;; either :smart (try to merge at join points) or :split (split the execution and don't re-merge) -- TODO: Switch the default to :smart
                                 (disable-loop-openers 'nil) ;todo: consider T
                                 )
  (let ((form `(lift-java-code-fn ,method-designator-string
                                  ,program-name
                                  ',param-names
                                  ,array-length-alist
                                  ,output
                                  ,assumptions
                                  ,classes-to-assume-initialized
                                  ,print
                                  ,ignore-exceptions
                                  ,ignore-errors
                                  ,invariants
                                  ,guard
                                  ,loop-guards
                                  ,measures
                                  ,measure-hints
                                  ,max-term-size
                                  ,assume-invariants-initially
                                  ,check-guards-in-functions
                                  ,excluded-locals
                                  ',inline
                                  ,extra-rules
                                  ,remove-rules
                                  ,monitor
                                  ,postludes
                                  ',extra-invars
                                  ',other-input-vars
                                  ',prune-branches
                                  ',loops-to-unroll
                                  ,use-prover-for-invars
                                  ,branches
                                  ',call-stp
                                  ',use-lets-in-terms
                                  ',disable-loop-openers
                                  ',whole-form
                                  state)))
    (if show-only
        `(mv-let (erp res state)
           ,form
           (declare (ignore erp)) ;todo
           (progn$ (cw "~x0" res)
                   (mv state)))
      (if print
          `(make-event ,form)
        `(with-output
           :off :all
           :on error
           :gag-mode nil
           (make-event ,form))))))

;; Show but do not submit the lifted code.
;; NOTE: Keep this in sync with LIFT-JAVA-CODE above.
(defmacro show-lift-java-code (&rest args)
  `(lift-java-code ,@args :show-only t))

;;
;; lift-java-code-segment
;;

;; TODO: Add xdoc for lift-java-code-segment

;TODO: Make sure this is in sync with lift-java-code-fn!

;; Lift a segment of code (not an entire method) into logic.
;Returns (mv erp event state)
(defun lift-java-code-segment-fn (program-name ; the name of the program to generate, a symbol which will be added onto the front of generated function names.
                                  method-designator-string
                                  start-pc
                                  segment-pcs ;is there a nicer way to specify the segment? ;this should contain start-pc
                                  input-source-alist ;todo: can we do away with this now (lift-java-code-fn doesn't have it)?
                                  output-indicator
                                  assumptions
                                  classes-to-assume-initialized
                                  print
                                  ignore-exceptions
                                  ignore-errors
                                  invariants
                                  guard ;guard to use for the top-level function
                                  loop-guards ;associates loop-ids with guards for the corresponding loop functions
                                  measures
                                  measure-hints
                                  max-term-size
                                  assume-invariants-initially
                                  excluded-locals
                                  monitor
                                  postludes
                                  extra-rules
                                  remove-rules
                                  call-stp
                                  use-lets-in-terms
                                  whole-form
                                  state)
  (declare (xargs :stobjs (state)
                  :guard (and (invariantsp invariants)
                              (measuresp measures state)
                              (measure-hintsp measure-hints)
                              (loop-guardsp loop-guards)
                              ;;(pseudo-term-listp assumptions)  ;now these can be untranslated terms, so we translate them below
                              (output-indicatorp output-indicator)
                              (booleanp ignore-exceptions)
                              (booleanp ignore-errors)
                              (input-source-alistp input-source-alist)
                              (or (string-listp classes-to-assume-initialized)
                                  (eq :all classes-to-assume-initialized))
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp))) ;todo: what else?
                  :mode :program))
  (b* (;; Check whether this call to the lifter has already been made:
       ((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ((when (not input-source-alist))
        (prog2$ (hard-error 'lift-java-code-segment-fn "No input-source-alist supplied." nil) ;TODO: Remove this check and instead auto-generate it.
                (mv t nil state)))
       (assumptions (translate-terms assumptions 'lift-java-code-segment-fn (w state))) ;throws an error on bad input
       (method-class (extract-method-class method-designator-string))
       (method-name (extract-method-name method-designator-string))
       (method-descriptor (extract-method-descriptor method-designator-string))
       (class-alist (global-class-alist state))
       (class-info (lookup-equal method-class class-alist))
       ((when (not class-info))
        (prog2$ (cw "ERROR: Error getting the class info for ~x0" method-class)
                (mv t nil state)))
       (method-info (lookup-equal (cons method-name method-descriptor) (jvm::class-decl-methods class-info)))
       (code (lookup-eq :program method-info))
       (return-type (lookup-eq :return-type method-info))
       ((when (not code))
        (prog2$ (cw "ERROR: Couldn't find code for method ~x0 with descriptor ~x1 in class ~x2" method-name method-descriptor method-class)
                (mv t nil state)))
       ;; todo: check that the segment PCs are in fact PCs of bytecode in the method
       (input-assumptions (make-input-assumptions input-source-alist 's0))
       (inputs (strip-cars input-source-alist))

       (measures-option       (elaborate-measures-option               measures        method-class method-name method-descriptor)) ;special treatment to support a single keyword
       (measure-hints-alist   (elaborate-loop-function-ids-in-doublets measure-hints   method-class method-name method-descriptor :measure-hints))
       (invariant-alist       (elaborate-loop-function-ids-in-doublets invariants      method-class method-name method-descriptor :invariants))
       (excluded-locals-alist (elaborate-loop-function-ids-in-doublets excluded-locals method-class method-name method-descriptor :excluded-locals))
       (loop-guard-alist      (elaborate-loop-function-ids-in-doublets loop-guards     method-class method-name method-descriptor :loop-guards))
       (postlude-alist        (elaborate-loop-function-ids-in-doublets postludes       method-class method-name method-descriptor :postludes))
       (symbolic-execution-rules (if nil ;(eq branches :split)
                                     (run-until-exit-segment-or-hit-loop-header-rules-split)
                                   (run-until-exit-segment-or-hit-loop-header-rules-smart)))
       ;;the options (todo: aren't there more options than these?):
       (options (s :measures-option measures-option
                   (s :measure-hints-alist measure-hints-alist
                      (s :invariant-alist invariant-alist
                         (s :excluded-locals-alist excluded-locals-alist
                            (s :loop-guard-alist loop-guard-alist
                               (s :postlude-alist postlude-alist
                                  (s :max-term-size max-term-size
                                     (s :ignore-exceptions ignore-exceptions
                                        (s :ignore-errors ignore-errors
                                           (s :call-stp call-stp
                                              ;;todo: :loops to unroll, :prune-branches
                                              (s :extra-rules extra-rules
                                                 (s :remove-rules remove-rules
                                                    ;;todo: :check-guards-in-functions
                                                    (s :assume-invariants-initially assume-invariants-initially
                                                       ;; todo: :inline
                                                       (s :monitor monitor
                                                          ;; todo: :use-prover-for-invars, :use-lets-in-terms, :disable-loop-openers, ...
                                                          (s :symbolic-execution-rules symbolic-execution-rules
                                                             nil))))))))))))))))
       ((mv erp final-state-dag generated-events generated-rules   ;;fixme think about these ignores
            & ;interpreted-function-alist-alist
            interpreted-function-alist state)
        (decompile-program
         (append (code-hyps start-pc method-info method-class method-name method-descriptor 's0)
                 assumptions
                 input-assumptions)
         segment-pcs
         program-name
         inputs
         nil          ;don't unroll nested loops
         nil          ;no extra invars
         print        ;t   ;:brief
         classes-to-assume-initialized
         options
         state))
       ((when erp) (mv erp nil state))
       ((mv erp output-dag state)
        (extract-output-dag output-indicator
                            final-state-dag
                            assumptions
                            '(jvm::locals (JVM::thread-top-frame (th) s0))
                            return-type
                            class-alist
                            state))
       ((when erp) (mv erp nil state))
       ;; Check that the vars of this DAG only include the vars in INPUTS:
       (- (check-dag-vars inputs output-dag))
       (top-fn-body (dag-to-term-limited output-dag max-term-size use-lets-in-terms
                                         interpreted-function-alist ;fixme think about this..
                                         ))
       (event
        `(progn
           ,@generated-events
           (defun ,(pack$ program-name '-generated-rules) ()
             (declare (xargs :normalize nil))
             ',generated-rules)
           ;; This is the top-level function created by the decompiler:
           (defun ,program-name ,inputs
             (declare (xargs :normalize nil
                             ,@(if guard `(:guard ,guard) nil)
                             :verify-guards nil))
             ,top-fn-body))))
    (mv nil
        (extend-progn event `(table lift-java-code-segment-table ',whole-form ',event))
        state)))

;; Keep this in sync with show-lift-java-code-segment below.
(defmacro lift-java-code-segment (&whole whole-form
                                         program-name ; the name of the program to generate, a symbol which will be added onto the front of generated function names.
                                         method-designator-string
                                         start-pc
                                         segment-pcs ;is there a nicer way to specify the segment (line numbers in the source)?
                                         output-indicator ;an output-indicatorp (TODO: make this a keyword arg defaulting to :auto)
                                         &key
                                         (input-source-alist 'nil) ;an input-source-alistp
                                         (assumptions 'nil)
                                         (classes-to-assume-initialized 'nil)
                                         (print 'nil)
                                         (ignore-exceptions 'nil)
                                         (ignore-errors 'nil)
                                         (invariants 'nil)
                                         (guard 'nil)
                                         (loop-guards 'nil)
                                         (max-term-size '*max-term-size*)
                                         (measures ':acl2)
                                         (measure-hints 'nil)
                                         (assume-invariants-initially 'nil)
                                         (excluded-locals 'nil)
                                         ;TODO: Add check-guards-in-functions, excluded-locals, inline,
                                         (monitor 'nil) ;rules to monitor
                                         (postludes 'nil)
                                         (extra-rules 'nil)
                                         (remove-rules 'nil)
                                         (call-stp 'nil)
                                         (use-lets-in-terms 'nil)
                                         ;TODO: Add postludes, extra-invars
                                         )
  `(make-event (lift-java-code-segment-fn ',program-name
                                          ,method-designator-string
                                          ,start-pc
                                          ,segment-pcs ;is there a nicer way to specify the segment?
                                          ,input-source-alist
                                          ,output-indicator
                                          ,assumptions
                                          ,classes-to-assume-initialized
                                          ,print
                                          ,ignore-exceptions
                                          ,ignore-errors
                                          ,invariants
                                          ,guard
                                          ,loop-guards
                                          ,measures
                                          ,measure-hints
                                          ,max-term-size
                                          ,assume-invariants-initially
                                          ,excluded-locals
                                          ,monitor
                                          ,postludes
                                          ,extra-rules
                                          ,remove-rules
                                          ',call-stp
                                          ',use-lets-in-terms
                                          ',whole-form
                                          state)))

;; Keep this in sync with lift-java-code-segment above.
(defmacro show-lift-java-code-segment (&whole whole-form
                                              program-name
                                              method-designator-string
                                              start-pc
                                              segment-pcs
                                              output-indicator ;an output-indicatorp
                                              &key
                                              (input-source-alist 'nil) ;an input-source-alistp
                                              (assumptions 'nil)
                                              (classes-to-assume-initialized 'nil)
                                              (print 'nil)
                                              (ignore-exceptions 'nil)
                                              (ignore-errors 'nil)
                                              (invariants 'nil)
                                              (guard 'nil)
                                              (loop-guards 'nil)
                                              (max-term-size '*max-term-size*)
                                              (measures ':acl2)
                                              (measure-hints 'nil)
                                              (assume-invariants-initially 'nil)
                                              (excluded-locals 'nil)
                                              (monitor 'nil)
                                              (postludes 'nil)
                                              (extra-rules 'nil)
                                              (remove-rules 'nil)
                                              (call-stp 'nil)
                                              (use-lets-in-terms 'nil)
                                              )
  `(lift-java-code-segment-fn ',program-name
                              ,method-designator-string
                              ,start-pc
                              ,segment-pcs ;is there a nicer way to specify the segment?
                              ,input-source-alist
                              ,output-indicator
                              ,assumptions
                              ,classes-to-assume-initialized
                              ,print
                              ,ignore-exceptions
                              ,ignore-errors
                              ,invariants
                              ,guard
                              ,loop-guards
                              ,measures
                              ,measure-hints
                              ,max-term-size
                              ,assume-invariants-initially
                              ,excluded-locals
                              ,monitor
                              ,postludes
                              ,extra-rules
                              ,remove-rules
                              ',call-stp
                              ',use-lets-in-terms
                              '(lift-java-code-segment ,@(fargs whole-form))
                              state))
