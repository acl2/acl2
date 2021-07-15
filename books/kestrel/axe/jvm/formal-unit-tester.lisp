; The formal unit testing tool
;
; Copyright (C) 2016-2020 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/jvm/load-class-from-hierarchy" :dir :system)
;(include-book "../jvm/gather-relevant-classes2")
(include-book "kestrel/utilities/unify" :dir :system)
(include-book "unroll-java-code")
(include-book "../tactic-prover")
(include-book "kestrel/bv/bvdiv-rules" :dir :system)
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

(local (in-theory (disable jvm::method-descriptorp jvm::method-idp jvm::method-namep))) ;todo: push back

;; TODO: Support API calls -- load in the libraries
;; TODO: Support classes that must be initialized.

;; TODO: Clarify which Java versions we support

;; TODO: Current restrictions of the tool:
;; Problem must be simple enough for unrolling and solving to work (bounded
;; computation, given the assumptions).
;; No API calls (coming soon).
;; Program must be in a single, self-contained file (more general support
;; coming soon).
;; No use of assertions (may be coming soon).
;; The tester will test any method whose name starts with "test".

;; The tool supports two methods of specifying correct behavior: having the
;; test method return a boolean or using asserts. In either case, encode
;; assumptions for testing as explicit tests (either return true or refrain
;; from testing any asserts if they are violated).

;; Setup

;; 1. Ensure that a recent verson of STP is installed and findable on your
;; path.

;; 2. Ensure that the ACL2_ROOT environment variable points to your ACL2
;; directory (which should contain a books/ subdirectory).  The directory name
;; given should not end in a slash.

;; 3. Set the JAVA_BOOTSTRAP_CLASSES_ROOT environment variable to point to a
;; hierarchy of .class files for the built-in Java bootstrap classes.  Such a
;; directory can be usually created by unzipping the rt.jar file that comes
;; with Java.  The directory name given should not end in a slash.

;; NOTE: To run the Formal Unit Tester from an IDE such as IntelliJ IDEA,
;; relevant environment variables may need to be set in your .profile file,
;; rather than a shell-specific file such as .bashrc.

;; Installation into IntelliJ IDEA:
;; 1. Under Preferences, choose Tools and then External Tools.
;; 2. Press '+' to add a tool.
;; 3. Set the options as follows:
;; Name: Formal Unit Tester
;; Description: Formal Unit Tester
;; Program: <insert the path to kestrel-acl2/axe/formal-unit-tester.sh>
;; Arguments: $FilePath$

;; To run the tool in IntelliJ IDEA:
;; 1. Open the .java file to be tested.
;; 2. Select Tools / External Tools / Formal Unit Tester.
;; 3. Results should appear in the "Run" window (often positioned at the bottom
;;    of the screen).

;; Interestingly, too many assumptions when lifting can cause overarching
;; "assumptions" that we need during the proof to be rewritten away.  We expect
;; the DAG to be proved to be of the form (bvif 1 <assumptions> <test-expr> 1)
;; and then we try to prove that is equals 1.

;;;
;;;
;;;

;; (thm
;;  (equal (equal (bvchop 8 x) (bvsx 32 16 (bvchop 16 x)))
;;         (equal 0 (slice 15 8 x)))
;;  :hints (("Goal"
;;           :cases ((equal 0 (GETBIT 15 X)))
;;           :use (:instance SPLIT-BV (y (slice 15 8 x)) (n 16) (m 8))
;;           :in-theory (e/d (bvsx) (BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE
;;                                   )))))

;;;
;;;
;;;

(defund method-id-to-string (method-id)
  (declare (xargs :guard (jvm::method-idp method-id)))
  (let ((name (jvm::method-id-name method-id))
        (descriptor (jvm::method-id-descriptor method-id)))
    (concatenate 'string name descriptor)))

(defun method-ids-to-strings (method-ids)
  (declare (xargs :guard (and (true-listp method-ids)
                              (jvm::all-method-idp method-ids))))
  (if (endp method-ids)
      nil
    (cons (method-id-to-string (first method-ids))
          (method-ids-to-strings (rest method-ids)))))

(defun print-strings-on-lines (strings)
  (if (endp strings)
      nil
    (prog2$ (cw "~x0~%" (first strings))
            (print-strings-on-lines (rest strings)))))

(defun print-string-left-aligned-in-field (str field-width)
  (declare (xargs :guard (and (stringp str)
                              (natp field-width)
                              (<= 3 field-width) ;must have enough room for 3 dots
                              )))
  (let ((str-length (length str)))
    (if (> str-length field-width)
        (prog2$ (cw "~s0" (implode (take (- field-width 3) (explode str))))
                (cw "..."))
      (prog2$ (cw "~s0" str)
              (cw "~_0" (- field-width str-length))))))

;; TODO: Add more cases?
;; TODO: Can this blow-up?
;; This could be more generally usefull, especially when trying to get STP to
;; prove a claim of the form (equal (get-field ..) ..).
(defun type-assumptions-for-get-field-nodes (dag current-nodenum acc)
  (declare (xargs :guard (and (integerp current-nodenum)
                              (<= -1 CURRENT-NODENUM)
                              (pseudo-dagp-aux dag current-nodenum))
                  :measure (len dag)
                  :guard-hints (("Goal" :in-theory (enable PSEUDO-DAGP-AUX)))
                  ))
  (if (endp dag)
      acc
    (let* ((entry (first dag))
           (expr (cdr entry)))
      (type-assumptions-for-get-field-nodes (rest dag)
                                            (+ -1 current-nodenum)
                                            (if (and (call-of 'GET-FIELD expr) ;; ex: (GET-FIELD <node> '("Packing" "C3" . :INT) <node>)
                                                     (= 3 (len (dargs expr)))
                                                     ;; arg1 should be a local?
                                                     (myquotep (darg2 expr)) ;ex: '("Packing" "C3" . :INT)
                                                     (= 2 (len (unquote (darg2 expr))))
                                                     (eq ':int (cddr (unquote (darg2 expr))))
                                                     ;;arg3 should be (the nodenum of) INITIAL-HEAP?
                                                     )
                                                (cons `(unsigned-byte-p '32 ,(dag-to-term-aux current-nodenum dag))
                                                      acc)
                                              acc)))))
;; ;move
;; (defund defconst-value (name wrld)
;;   (declare (xargs :guard (and (symbolp name)
;;                               (plist-worldp wrld))))
;;   (let ((quoted-value (getprop name 'const nil 'current-acl2-world wrld)))
;;     (if (not quoted-value)
;;         (er hard? 'defconst-value "No value found for constant ~x0 !" name)
;;       (if (not (myquotep quoted-value))
;;           (er hard? 'defconst-value "Value found for constant ~x0 is not quoted !" name)
;;         (unquote quoted-value)))))

(defun param-var-assumptions-aux (slot parameter-types param-slot-to-name-alist
                                       ;; array-length-alist ;the array lengths may be assumed by tests in the code, so we may not have this
                                       )
  (declare (xargs :guard (and (natp slot)
                              (true-listp parameter-types)
                              (jvm::all-typep parameter-types)
                              (param-slot-to-name-alistp param-slot-to-name-alist))
                  :verify-guards nil ;todo
                  ))
  (if (endp parameter-types)
      nil
    (let* ((type (first parameter-types))
           (parameter-name (lookup slot param-slot-to-name-alist))
           (assumptions (if (jvm::primitive-typep type)
                            (type-assumptions-for-param type parameter-name)
                          nil ;todo: what about arrays?
                          ))
           (slot-count (jvm::type-slot-count type)))
      (append assumptions
              (param-var-assumptions-aux (+ slot slot-count)
                                         (rest parameter-types)
                                         param-slot-to-name-alist)))))

;; todo: compare to parameter-assumptions-aux
(defun parameter-var-assumptions (method-info ; array-length-alist
                                  param-slot-to-name-alist)
  (declare (xargs :guard (and (jvm::method-infop method-info)
                              ;;(array-length-alistp array-length-alist)
                              (param-slot-to-name-alistp param-slot-to-name-alist)
                              ;;(member-eq vars-for-array-elements '(t nil :bits))
                              )
                  :verify-guards nil ;todo
                  ))
  (let* ((parameter-types (lookup-eq :parameter-types method-info)) ;does not include "this"
         (staticp (jvm::method-staticp method-info))
         (first-param-slot (if staticp 0 1)) ;skip a slot for "this" if it's an instance method
         )
    (param-var-assumptions-aux first-param-slot parameter-types param-slot-to-name-alist ; array-length-alist
                               )))

;; Used during lifting and after
(defun formal-unit-testing-extra-simplification-rules ()
  (declare (xargs :guard t))
  (append '(bv-array-read-of-bv-array-write
            ;;todo: when prove-with-tactics sees a not applied to a boolor, it should try to prove both cases
            ;;boolor  ;might have a loop
            sbvlt-of-bvif-when-sbvlt-arg3
            sbvlt-of-bvif-when-sbvlt-arg4
            sbvlt-of-bvif-when-not-sbvlt-arg3
            sbvlt-of-bvif-when-not-sbvlt-arg4
            sbvlt-of-bvif-when-sbvlt-arg3-alt
            sbvlt-of-bvif-when-sbvlt-arg4-alt
            sbvlt-of-bvif-when-not-sbvlt-arg3-alt
            sbvlt-of-bvif-when-not-sbvlt-arg4-alt
            equal-of-bvif
            equal-of-bvif-alt
            bvplus-of-bvif-arg2 ;perhaps restrict to the case when the duplicated term is a constant
            bvplus-of-bvif-arg3 ;perhaps restrict to the case when the duplicated term is a constant
            sbvlt-of-myif-arg2-safe
            sbvlt-of-myif-arg3-safe
            integerp-when-unsigned-byte-p-free ;needed for update-nth reasoning for object arrays (but we may change that)
            <-of-constant-when-usb ;needed for update-nth reasoning for object arrays (but we may change that)a
            max                    ;used in object array reasoning
            SBVLT-OF-+-ARG2        ;used in object array reasoning
            ;;SBVLT-OF-+-ARG3
            <-OF-+-COMBINE-CONSTANTS-1 ;used in object array reasoning
            not-<-when-sbvlt-alt       ;used in object array reasoning
            <-OF-BVCHOP-ARG1 ; since BV-ARRAY-READ-OF-BV-ARRAY-WRITE introduces <
            bvlt-of-bvif-arg2
            bvlt-of-bvif-arg3
            equal-of-myif-arg1-safe
            equal-of-myif-arg2-safe
            bv-array-read-of-bvif-arg2
            bvmult-of-bvif-arg3
            bvshl-of-bvif-arg3
            bv-array-read-of-bv-array-write-diff ;can help when the indices are not constant but are provably unequal (might be ITEs)

            ;;todo: move these next few to core-rules-bv:
            equal-of-bvchop-and-bvplus-of-same
            equal-of-bvchop-and-bvplus-of-same-alt
            sbvlt-of-bvplus-of-constant-and-constant-2
            signed-addition-overflowsp
            signed-addition-underflowsp
            <-of-bvplus-becomes-bvlt-arg1 ;the < may come from array rules (todo: avoid even introducing it?)

            ;; move these?:
            sbvlt-when-sbvlt-of-bvplus-of-constant
            sbvlt-when-sbvlt-of-bvminus-of-constant
            sbvlt-of-bvplus-of-constant-and-constant-2
            sbvlt-of-bvplus-of-constant-and-constant-2b
            bvlt-of-bvdiv-constants
            sbvlt-of-0-and-sbvdiv
            sbvlt-false-when-sbvlt-gen ; move to more basic rule set (but this is in a big expensive file that we may not want to depend on)
            )
          (amazing-rules-spec-and-dag)))

(defun formal-unit-testing-extra-simplification-rules-no-boolif ()
  (declare (xargs :guard t))
  (set-difference-eq
   (formal-unit-testing-extra-simplification-rules)
   ;; since pruning doesn't know about booland/boolor/etc:
   '(MYIF-BECOMES-BOOLIF-T-ARG1 ;rename
     ;;MYIF-BECOMES-BOOLIF-T-ARG2
     ;;MYIF-BECOMES-BOOLIF-NIL-ARG1
     MYIF-BECOMES-BOOLIF-NIL-ARG2 ;rename
     ;;MYIF-BECOMES-BOOLIF-AXE
     )))

(defun formal-unit-tester-extra-lifting-rules ()
  (append '(;addressp-when-address-or-nullp-and-not-null-refp ;loops with address-or-nullp
            equal-of-addressfix-same
            jvm::execute-model-static-boolean-method
            boolif booland ; why?
            )
          (formal-unit-testing-extra-simplification-rules-no-boolif)))

;;;
;;; Testing a given method (to be called from the ACL2 REPL)
;;;

;; ;; Returns an event.
;; ;; todo: deprecate?
;; (defun test-method-event (method-id method-info-alist class-name assumptions root-of-class-hierarchy)
;;   (b* ((method-name (car method-id))
;;        (method-signature (cdr method-id))
;;        (method-designator-string (concatenate 'string class-name "." method-name method-signature))
;;        ((when (not (assoc-equal method-id method-info-alist)))
;;         (er hard? 'test-method-event "Method ~x0 not found in class ~x1." method-designator-string class-name))
;;        (method-info (lookup-equal method-id method-info-alist))
;;        (param-slot-to-name-alist (make-param-slot-to-name-alist method-info nil ;param-names
;;                                                                 ))
;;        (param-var-assumptions (parameter-var-assumptions method-info param-slot-to-name-alist))
;;        (defconst-name (pack$ '*lifted-program- method-name '-*))
;;        )
;;     `(progn
;;        (load-class ,class-name :root ,root-of-class-hierarchy) ;; done so that unroll-java-code can find it
;;        (unroll-java-code ,defconst-name ,method-designator-string
;;                          :chunkedp t)
;;        (prove-with-tactics ,defconst-name
;;                            :rules (formal-unit-testing-extra-simplification-rules)
;;                            :assumptions (append ',param-var-assumptions
;;                                                 ,assumptions)
;;                            :type :bit
;;                            :tactics '(:rewrite :stp) ;todo: maybe prune?
;;                            :timeout nil
;;                            :print t
;;                            :rule-classes nil ;todo: will always be needed if we use :type :bit?
;;                            )
;;        (cw-event "Test passed for method ~x0." ,method-designator-string))))

;; ;; todo: deprecate?
;; ;;Returns (mv erp event state).
;; (defun prove-test-fn (method-designator-string assumptions root-of-class-hierarchy state)
;;   (declare (xargs :guard (and (method-designator-stringp method-designator-string)
;;                               (stringp root-of-class-hierarchy))
;;                   :verify-guards nil ;todo
;;                   :stobjs state))
;;   (b* ((fully-qualified-class-name (extract-method-class method-designator-string))
;;        (method-name (extract-method-name method-designator-string))
;;        (method-descriptor (extract-method-descriptor method-designator-string))
;;        (class-file (concatenate 'string root-of-class-hierarchy "/" (turn-dots-into-slashes fully-qualified-class-name) ".class"))
;;        ((mv erp class-info state) (read-and-parse-class-file class-file t state))
;;        ((when erp) (mv erp nil state))
;;        (method-info-alist (jvm::class-decl-methods class-info))
;;        (method-id (cons method-name method-descriptor)))
;;     (mv (erp-nil)
;;         (test-method-event method-id method-info-alist fully-qualified-class-name assumptions ".")
;;         state)))

;; ;; todo: deprecate?
;; ;; todo: rename to something like test-method?
;; (defmacro prove-test (method-designator-string &key
;;                                                (root-of-class-hierarchy '".")
;;                                                (assumptions 'nil))
;;   `(make-event (prove-test-fn ,method-designator-string ',assumptions ,root-of-class-hierarchy state)))

;;;
;;; Testing an entire file
;;;

;; Decide which methods to test (default: all whose names start with "test").  TODO: What if not boolean?
(defun select-method-ids-to-test (method-info-alist methods-to-test)
  (declare (xargs :guard (and (jvm::method-info-alistp method-info-alist)
                              (or (eq :auto methods-to-test)
                                  (string-listp methods-to-test)))
                  :guard-hints (("Goal" :in-theory (enable JVM::METHOD-INFO-ALISTP)))
                  ))
  (if (endp method-info-alist)
      nil
    (let* ((entry (first method-info-alist))
           (method-id (first entry))
           (name (jvm::method-id-name method-id))
           ;;(signature (cdr method-id))
           (testp (if (eq :auto methods-to-test)
                      ;; todo: abstract this pattern as string-starts-with:
                      (prefixp (explode-atom "test" 10)
                               (explode-atom name 10))
                    (member-equal name methods-to-test))))
      (if testp
          (cons method-id (select-method-ids-to-test (rest method-info-alist) methods-to-test))
        (select-method-ids-to-test (rest method-info-alist) methods-to-test)))))

(defun strip-steps-from-term (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (if (and (call-of 'step-state-with-pc-and-call-stack-height expr)
           (= 3 (len (fargs expr))))
      (strip-steps-from-term (farg3 expr))
    (if (and (call-of 'step-state-with-pc-designator-stack expr)
             (= 2 (len (fargs expr))))
        (strip-steps-from-term (farg2 expr))
      expr)))

;; Convert branches that are throwing asserts to 0 and regular make-states to 1:
;; TODO: Consider skipping over enclosing calls of STEP-STATE-WITH-PC-AND-CALL-STACK-HEIGHT.
(defun convert-assert-branches-in-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (call-of 'jvm::make-state term)
      ''1 ;; this branch is not throwing an assert
    (if (and (call-of 'myif term)
             (= 3 (len (fargs term))))
        ;;Process both branches of the myif:
        `(myif ,(farg1 term)
               ,(convert-assert-branches-in-term (farg2 term))
               ,(convert-assert-branches-in-term (farg3 term)))
      ;; Look for run-until-return-from-stack-height applied to some number of
      ;; steps (maybe 0), applied to a call of jvm::execute-new to make the
      ;; AssertionError:
      (mv-let (matchp alist)
        (unify-term term '(run-until-return-from-stack-height
                           (binary-+ '2 (jvm::call-stack-size :call-stack))
                           :s))
        (if (not matchp)
            (er hard? 'convert-assert-branches-in-term "Unrecognized term: ~X01." term nil)
          (b* ((s (lookup-eq :s alist))
               ((when (not (pseudo-termp s))) (er hard? 'convert-assert-branches-in-term "Bad term: ~X01." s nil)) ;todo: drop this (prove it can't happen)
               (stripped-s (strip-steps-from-term s))
               ((when (not (pseudo-termp stripped-s))) (er hard? 'convert-assert-branches-in-term "Bad term: ~X01." s nil)))
            (mv-let (matchp alist)
              (unify-term stripped-s '(jvm::execute-new
                                       '(:new "java.lang.AssertionError")
                                       :th
                                       (jvm::make-state :tt :heap :ct :hrt :mt :sfm :icn :it)))
              (declare (ignore alist))
              (if (not matchp)
                  (er hard? 'convert-assert-branches-in-term "Unrecognized term after stripping steps: ~X01." stripped-s nil)
                ''0 ;; this branch is throwing an assert
                ))))))))

(defthm pseudo-termp-of-convert-assert-branches-in-term
  (implies (pseudo-termp term)
           (pseudo-termp (convert-assert-branches-in-term term)))
  :hints (("Goal" :in-theory (enable convert-assert-branches-in-term))))

;; Returns (mv erp dag-or-quotep).
;;todo: Avoid going to a term
(defun convert-assert-branches (dag)
  (declare (xargs :guard (pseudo-dagp dag)))
  (let* ((term (dag-to-term dag))
         (term (convert-assert-branches-in-term term))
         )
    (dagify-term term)))

;; Returns (mv erp dag-or-quotep).
;; This version avoids imposing invariant-risk on callers, because it has a guard of t.
(defun convert-assert-branches-unguarded (dag)
  (declare (xargs :guard t))
  (if (not (pseudo-dagp dag))
      (mv :bad-dag
          (er hard? 'convert-assert-branches-unguarded "Bad dag: ~x0." dag))
    (convert-assert-branches dag)))

(defun assert-assumptions (class-name)
  (declare (xargs :guard (jvm::class-namep class-name)))
  `( ;; assertion checking is on:
    (equal 0
           (jvm::get-static-field ',class-name
                                  '("$assertionsDisabled" . :boolean)
                                  initial-static-field-map))
    (lookup-equal ',class-name initial-heapref-table)
    (not (null-refp (lookup-equal ',class-name initial-heapref-table)))
    (equal (get-field (lookup-equal ',class-name
                                    initial-heapref-table)
                      '(:special-data . :class)
                      initial-heap)
           "java.lang.Class")))

;; Returns (mv erp failedp state)
(defun run-formal-test-on-method (method-id methods-expected-to-fail method-info-alist class-name assumptions root-of-class-hierarchy print extra-rules remove-rules monitor state)
  (declare (xargs :stobjs (state)
                  :guard (and (jvm::method-idp method-id)
                              (jvm::method-info-alistp method-info-alist)
                              (jvm::class-namep class-name)
                              ;; TODO: translate the assumptions!
                              (stringp root-of-class-hierarchy) ;a directory name
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp monitor))
                  :mode :program ;; for several reasons
                  ))
  (b* ((method-name (car method-id))
       (method-descriptor (cdr method-id))
       (method-info (lookup-equal method-id method-info-alist))
       (method-designator-string (concatenate 'string class-name "." method-name method-descriptor)) ;todo: use fully qualified name?
       (method-return-type (jvm::return-type-from-method-descriptor method-descriptor))
       (variant (if (eq method-return-type :void)
                    :assert ;; void method means the proof is that it triggers no asserts (todo: what about exceptions?)
                  (if (eq method-return-type :boolean)
                      :boolean ;; boolean method means the proof is that it returns true
                    (er hard? 'run-formal-test-on-method "Method ~x0 is neither boolean nor void." method-name))))
       (- (cw "~%(Testing ~x0:~%" method-designator-string))
       (- (if (eq variant :assert)
              (cw "(Will try to show that no asserts are triggered.)~%")
            (cw "(Will try to show that it returns true.)~%")))
       (param-slot-to-name-alist (make-param-slot-to-name-alist method-info nil ;param-names
                                                                ))
       (param-var-assumptions (parameter-var-assumptions method-info param-slot-to-name-alist))
       ;; Populate the global-class-alist (so that unroll-java-code can find the code):
       ;; TODO: Pull this out
       ;; TODO: Don't bother to submit this event, just add the class to an alist?
       (state ;(mv state constant-pool)
        (submit-event-quiet `(load-class-from-hierarchy ,class-name :root ,root-of-class-hierarchy)
                            state))
       (output-indicator (if (eq variant :assert)
                             :all
                           :return-value))
       (error-on-incomplete-runsp (if (eq variant :assert)
                                      nil ; stop before throwing an assert (will try to show such branches unreachable)
                                    nil ;; exception branches may be pruned below
                                    ))
       (assert-assumptions (assert-assumptions class-name))
       (- (cw "(Unrolling code:~%"))
       ((mv erp dag & & & & state)
        ;; TODO: Use assumptions here:
        (unroll-java-code-fn-aux method-designator-string
                                 output-indicator
                                 nil   ;;array-length-alist
                                 ;; extra-rules, to add to default set:
                                 (append (formal-unit-tester-extra-lifting-rules)
                                         extra-rules)
                                 ;; remove-rules, to remove from default set (since boolif isn't handled right by pruning):
                                 (append '(MYIF-BECOMES-BOOLIF-T-ARG1
                                           MYIF-BECOMES-BOOLIF-T-ARG2
                                           MYIF-BECOMES-BOOLIF-NIL-ARG1
                                           MYIF-BECOMES-BOOLIF-NIL-ARG2
                                           MYIF-BECOMES-BOOLIF-AXE)
                                         remove-rules)
                                 nil ;rule-alists
                                 monitor
                                 ;todo: think about these:
                                 assert-assumptions ;; nil ;user-assumptions
                                 t ;simplify-xorsp
                                 :all ;'("java.lang.Object" "java.lang.System") ;classes-to-assume-initialized
                                 nil ;ignore-exceptions
                                 nil ;ignore-errors
                                 print
                                 nil    ;print-interval
                                 t ;memoizep
                                 t      ;vars-for-array-elements
                                 t      ;prune-branches
                                 nil    ;call-stp ;t, nil, or a timeout
                                 :auto  ;steps
                                 :smart ;; (if (eq variant :assert) :split :smart)
                                 nil    ;param-names
                                 t ;chunkedp ;whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code?)
                                 error-on-incomplete-runsp
                                 state))
       ((when erp) (mv erp t state))
       ;; ;;prune again: todo: shouldn't be needed!:
       ;; (- (cw "(Pruning again:~%"))
       ;; ((mv erp dag state)
       ;;  (prune-dag dag nil (formal-unit-testing-extra-simplification-rules-no-boolif) nil nil state))
       ;; ((when erp) (mv erp t state))
       ;; (- (cw "Result of pruning again: ~X01)~%"
       ;;        (dag-to-term dag) ;todo: limit
       ;;        nil))
       ;; put boolifs back:
       ((mv erp dag state)
        (simp-dag dag :rules (formal-unit-testing-extra-simplification-rules)
                  :check-inputs nil))
       ((when erp) (mv erp t state))
       (- (cw "Done unrolling code)~%"))
       ;; Handle the :assert case, if applicable:
       ((mv erp dag state)
        (if (eq variant :assert)
            (b* (((mv erp dag) (convert-assert-branches-unguarded dag))
                 ((when erp) (mv erp dag state))
                 ;; Simplify the DAG in case putting in the 0s and 1s allows it:
                 (- (cw "(Simplifying the dag to prove:~%"))
                 ((mv erp dag state)
                  (simp-dag dag
                            :rules (append (set-difference-equal (amazing-rules-bv)
                                                                 remove-rules)
                                           extra-rules)
                            :use-internal-contextsp t
                            :monitor monitor
                            :check-inputs nil))
                 ((when erp) (mv erp dag state))
                 (- (cw "Done Simplifying)~%")))
              (mv (erp-nil) dag state))
          ;; Do nothing since the dag should already be simplified
          (mv (erp-nil) dag state)))
       ((when erp) (mv erp t state))
       ;; Handle a DAG that is a quotep:
       ((when (quotep dag))
        (cw "The DAG to prove for ~s0 is the constant ~x1.)~%" method-designator-string dag)
        (mv (erp-nil)
            (let ((expected-result 1))
              (if (equal (unquote dag) expected-result)
                  nil ;did not fail
                t     ;failed
                ))
            state))
       (- (and print (cw "(DAG to prove: ~x0)~%" dag)))
       ;; (dag-len (len dag))
       (dag-size (dag-size dag))
       (- (cw "(DAG to prove for ~s0 has size ~x1.)~%" method-designator-string dag-size))
       (- (and (< dag-size 1000)
               (progn$ (cw "(DAG is:~%")
                       (cw "~X01" (dag-to-term-unguarded dag) nil)
                       (cw ")~%"))))
       (- (cw "(Applying tactic prover:~%"))
       (type-assumptions-for-fields (type-assumptions-for-get-field-nodes dag (top-nodenum dag) nil))
       ((mv result
            & ;info-acc
            & ;actual-dag
            & ;assumptions-given
            state)
        (apply-tactic-prover dag
                             '(:rewrite :stp) ;todo: maybe prune? ;; tactics
                             (append param-var-assumptions
                                     type-assumptions-for-fields
                                     assumptions)
                             nil ;simplify-assumptions
                             print
                             nil ;*default-stp-timeout* ;timeout ;a number of seconds, or nil for no timeout
                             t   ;call-stp-when-pruning
                             (append extra-rules
                                     (set-difference-eq (formal-unit-testing-extra-simplification-rules)
                                                        remove-rules))
                             nil  ;monitor
                             t ;simplify-xors (todo: try nil? or make an option?)
                             :bit ;type
                             state
                            ))
       (- (cw ")~%"))
       ((when (eq *error* result)) (prog2$ (cw "An error occured when testing method ~x0.)~%" method-designator-string)
                                           (mv (erp-t) t state))))
    (if (eq *valid* result)
        (progn$ (cw "PASSED test for method ~x0.)~%" method-designator-string)
                (and (not (eq :any methods-expected-to-fail))
                     (member-equal method-name methods-expected-to-fail)
                     (er hard? 'run-formal-test-on-method "Method ~x0 was expected to fail but actually passed." method-name))
                (mv (erp-nil)
                    nil ;no failure
                    state))
      (progn$ (cw "FAILED test for method ~x0.)~%" method-designator-string)
              (and (not (eq :any methods-expected-to-fail))
                   (not (member-equal method-name methods-expected-to-fail))
                   (er hard? 'run-formal-test-on-method "Method ~x0 was expected to pass but actually failed." method-name))
              (mv (erp-nil)
                  t ;failed
                  state)))))

;; The result of a FUT call
(defun fut-resultp (res)
  (declare (xargs :guard t))
  (and (consp res)
       (jvm::method-idp (car res))
       (member-equal (cdr res) '("FAILED" "PASSED"))))

(defun fut-result-listp (results)
  (declare (xargs :guard t))
  (if (atom results)
      (null results)
    (and (fut-resultp (first results))
         (fut-result-listp (rest results)))))

;; Returns (mv erp results state).
(defun run-formal-tests-on-methods (method-ids methods-expected-to-fail method-info-alist class-name root-of-class-hierarchy print extra-rules remove-rules monitor results-acc state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (if (endp method-ids)
      (mv (erp-nil) (reverse results-acc) state)
    (let ((method-id (first method-ids)))
      (mv-let (erp failedp state)
        (run-formal-test-on-method method-id methods-expected-to-fail method-info-alist class-name nil root-of-class-hierarchy print extra-rules remove-rules monitor state)
        (if erp
            (mv erp nil state)
          (run-formal-tests-on-methods (rest method-ids)
                                       methods-expected-to-fail method-info-alist class-name root-of-class-hierarchy print extra-rules remove-rules monitor
                                       (cons (cons method-id (if failedp "FAILED" "PASSED")) results-acc)
                                       state))))))

(defun print-test-results (results methods-expected-to-fail)
  (declare (xargs :guard (and (fut-result-listp results)
                              (or (eq :any methods-expected-to-fail)
                                  (string-listp methods-expected-to-fail) ;these are just bare names, for now
                                  ))
                  :guard-hints (("Goal" :in-theory (enable jvm::stringp-when-method-namep)))
                  ))
  (if (endp results)
      nil
    (let* ((result (first results))
           (method-id (car result))
           (method-name (jvm::method-id-name method-id))
           ;; (method-descriptor (cdr method-id))
           (res (cdr result)))
      (progn$ (cw "The test for method ")
              (print-string-left-aligned-in-field method-name ;todo: include the descriptor if needed to disambiguate: (concatenate 'string method-name method-descriptor)
                                                  20)
              (if (eq :any methods-expected-to-fail)
                  ;; We don't know if the failure was expected, so just print the result:
                  (cw " ~s0.~%" res)
                ;; Print the result and whether it is as expected:
                (if (equal res (if (member-equal method-name methods-expected-to-fail) "FAILED" "PASSED"))
                    (cw " ~s0, as expected.~%" res)
                  (cw " ~s0 -- UNEXPECTED!~%" res)))
              (print-test-results (rest results) methods-expected-to-fail)))))

;; Returns (mv erp event state constant-pool), but the event is always an
;; empty progn.  This may need to be called inside a make-event.
(defun test-file-fn (path-to-java-file ;; we prepend the cbd if this is not an absolute path (TODO: Perhaps instead just take the name of the class and use the classpath to find it?)
                     methods-to-test
                     methods-expected-to-fail ;todo: check that these are all methods in the class
                     ;;assumptions
                     print
                     extra-rules
                     remove-rules
                     monitor
                     state
                     constant-pool)
  (declare (xargs :mode :program
                  :stobjs (state constant-pool)
                  :guard (and (or (eq :auto methods-to-test)
                                  (string-listp methods-to-test) ;these are just bare names, for now
                                  )
                              (or (eq :any methods-expected-to-fail)
                                  (string-listp methods-expected-to-fail) ;these are just bare names, for now
                                  ))))
  (b* (((mv & java-bootstrap-classes-root state) (getenv$ "JAVA_BOOTSTRAP_CLASSES_ROOT" state)) ; must contain a hierarchy of class files.  cannot be a jar.  should not end in slash.
       ((when (not java-bootstrap-classes-root))
        (er hard? 'test-file-fn "Please set your JAVA_BOOTSTRAP_CLASSES_ROOT environment var to a directory that contains a hierarchy of class files.")
        (mv :JAVA_BOOTSTRAP_CLASSES_ROOT-unset nil state constant-pool))
       ;; TODO: Don't bother to submit these events:
       ;; TODO: Build in many more classes?
       ;; TODO: Should we save these when we build the FUT executable?
       ;; TODO: Any way to track these dependencies?
       (state
        (submit-event-quiet `(load-class-from-hierarchy "java.lang.Object" :root ,java-bootstrap-classes-root)
                            state))
       (state
        (submit-event-quiet `(load-class-from-hierarchy "java.lang.Class" :root ,java-bootstrap-classes-root)
                            state))
       (state
        (submit-event-quiet `(load-class-from-hierarchy "java.lang.Math" :root ,java-bootstrap-classes-root)
                            state))
       (absolute-path-to-java-file
        (if (equal #\/ (char path-to-java-file 0))
            path-to-java-file ;; already starts with slash
          (concatenate 'string (cbd) path-to-java-file)))
       (- (cw "Running tester on:~% ~s0.~%~%" absolute-path-to-java-file)) ;ex: "/home/emily/foo/bar/baz/Search.java"
       (base-name (substring-before-last-occurrence absolute-path-to-java-file #\.)) ;strip the dot and extension, ex: "/home/emily/foo/bar/baz/Search"
       ;; (- (cw "Base name: ~s0~%" base-name))
       (root-of-user-class-hierarchy (substring-before-last-occurrence base-name #\/)) ;; for now, we assume the given class is at the top level of the hierarchy (todo: deduce the root using the fully qualified name stored in the class file)
       ;; (- (cw "Directory: ~s0~%" root-of-user-class-hierarchy))
       (class-name (substring-after-last-occurrence base-name #\/)) ;todo: add support for fully-qualified names
       ;; (- (cw "Class name: ~s0~%" class-name))
       (class-file-name (concatenate 'string base-name ".class"))
       ;; (- (cw "Class file name: ~s0~%" class-file-name))
       ;; Read the class file:
       ((mv erp class-name-from-class-file class-info
            & ; field-defconsts
            state constant-pool) (read-and-parse-class-file class-file-name t state constant-pool))
       ((when erp) (mv erp nil state constant-pool))
       ((when (not (equal class-name-from-class-file
                          class-name)))
        (er hard? 'test-file-fn "Class-name mismatch: ~x0 vs ~x1." class-name class-name-from-class-file)
        (mv :class-name-mismatch nil state constant-pool))
       ;; We'll test any method whose name starts with "test":
       (method-info-alist (jvm::class-decl-methods class-info))
       (test-method-ids (select-method-ids-to-test method-info-alist methods-to-test))
       ((when (endp test-method-ids))
        (er hard? 'test-file-fn "There are no methods to test.")
        (mv (erp-t) nil state constant-pool))
       ;; Print the methods to be tested:
       (- (if (endp (rest test-method-ids))
              (cw "Will test the single method ~s0.~%" (method-id-to-string (first test-method-ids)))
            (prog2$ (cw "Will test these ~x0 methods:.~%" (len test-method-ids))
                    (print-strings-on-lines (method-ids-to-strings test-method-ids)))))
       ;; Load the relevant classes (TODO: Consider speeding things up by doing this lazily):
       ;; ((mv erp kestrel-acl2 state) (getenv$ "KESTREL_ACL2" state))
       ;; ((when erp)
       ;;  (er hard? 'test-file-fn "KESTREL_ACL2 environment variable is unset.")
       ;;  (mv (erp-t) nil state))
       ;; (java-library-dir (concatenate 'string kestrel-acl2 "/examples/java7-libraries/rt.jar.unzipped"))
       ;; (- (cw "(Loading relevant classes:~%"))
       ;; (state (load-relevant-classes class-name root-of-user-class-hierarchy java-library-dir :skip state))
       ;; (- (cw ")~%"))
       ;; Run the tests:
       ((mv erp results state)
        (run-formal-tests-on-methods test-method-ids methods-expected-to-fail method-info-alist class-name root-of-user-class-hierarchy print extra-rules remove-rules monitor
                      nil ;empty accumulator
                      state))
       ((when erp) (mv erp nil state constant-pool))
       (state (maybe-remove-temp-dir state))
       (- (cw "~%~%~%"))
       (- (cw "==============================================================================~%"))
       (- (cw "Summary of results for class ~x0:~%" class-name))
       (- (print-test-results results methods-expected-to-fail))
       (- (cw "==============================================================================~%"))
       ;;(- (cw "~%"))
       )
    (mv (erp-nil) '(progn) state constant-pool)))

;; Test all methods in the given file whose names start with "test".  This
;; variant of the tool should be called from within the ACL2 loop.
(defmacro test-file (path-to-java-file &key
                                       ;;(assumptions 'nil)
                                       (methods ':auto) ;;which methods to test (default is ones whose names start with "test")
                                       (expected-failures 'nil)
                                       (extra-rules 'nil)
                                       (remove-rules 'nil)
                                       (monitor 'nil)
                                       (print 'nil))
  `(make-event-quiet (test-file-fn ,path-to-java-file
                                   ;;',assumptions
                                   ,methods
                                   ,expected-failures
                                   ,print
                                   ,extra-rules
                                   ,remove-rules
                                   ,monitor
                                   state
                                   constant-pool)))

;; Test all methods in the given file whose names start with "test".  This
;; variant of the tool should be called from the shell or from an IDE.  This
;; does not check whether the tests get the right answers (it allows any of the
;; tests to fail). By contrast, test-file lets you indicate which tests should
;; fail (and thus which tests must not fail).
(defmacro test-file-and-exit (path-to-java-file &key
                                                ;;(assumptions 'nil)
                                                (methods ':auto) ;;which methods to test (default is ones whose names start with "test")
                                                (extra-rules 'nil)
                                                (remove-rules 'nil)
                                                (monitor 'nil)
                                                (print ':brief) ;(print 'nil)
                                                )
  `(mv-let (erp event state constant-pool)
     (test-file-fn ,path-to-java-file
                   ;;',assumptions
                   ,methods
                   :any
                   ,print
                   ,extra-rules
                   ,remove-rules
                   ,monitor
                   state
                   constant-pool)
     (declare (ignore erp event))
     (prog2$ (exit 0) ;; Prevent printing of stuff (NIL, a prompt, and "Bye.") before exiting
             (mv state
                 constant-pool))))
