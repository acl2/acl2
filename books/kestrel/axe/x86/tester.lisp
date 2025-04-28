; Formal Unit Tester for x86
;
; Copyright (C) 2021-2022 Kestrel Technology, LLC
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; See also the Formal Unit Tester for Java.

(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(include-book "kestrel/axe/tactic-prover" :dir :system)
(include-book "kestrel/utilities/strip-stars-from-name" :dir :system)
(include-book "kestrel/utilities/merge-sort-string-less-than" :dir :system)
(include-book "kestrel/utilities/if-rules" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)
(include-book "kestrel/utilities/real-time-since" :dir :system)
(include-book "kestrel/booleans/booleans" :dir :system)
(include-book "kestrel/strings-light/add-prefix-to-strings" :dir :system)
(include-book "kestrel/strings-light/strings-starting-with" :dir :system)
(include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system) ; for +-OF-+-OF---SAME
(include-book "kestrel/arithmetic-light/types" :dir :system) ; for rationalp-when-integerp
(include-book "kestrel/arithmetic-light/floor" :dir :system)
(include-book "unroll-x86-code")
(include-book "tester-rules-bv")
(include-book "tester-rules")
(include-book "kestrel/bv/convert-to-bv-rules" :dir :system) ; todo: combine with bv/intro?
(include-book "kestrel/bv/intro" :dir :system) ; for BVCHOP-OF-LOGXOR-BECOMES-BVXOR
(include-book "rule-lists")
(include-book "../bv-array-rules")
;(include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system) ; for minus-cancellation-on-right
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/utilities/get-real-time" :dir :system))

(acl2::ensure-rules-known (extra-tester-rules))
(acl2::ensure-rules-known (extra-tester-lifting-rules))
(acl2::ensure-rules-known (tester-proof-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Parens in output may not be balanced?

(acl2::def-constant-opener alistp) ; why?

;; ;todo: not really an assumption generator
;; todo: redo this like elf64-section-loadedp.
(defun section-assumptions-mach-o-64 (segment-name section-name parsed-mach-o
                                      text-offset stack-slots-needed x86)
  (declare (xargs :guard (and (stringp segment-name)
                              (stringp section-name)
                              ;; parsed-mach-o
                              (natp text-offset)
                              (natp stack-slots-needed))
                  :stobjs x86
                  :verify-guards nil ;todo
                  ))
  (if (acl2::mach-o-section-presentp segment-name section-name parsed-mach-o)
      (let* ((segment (acl2::get-mach-o-segment segment-name (acl2::lookup-eq-safe :cmds parsed-mach-o)))
             (section (acl2::get-mach-o-section section-name (acl2::lookup-eq-safe :SECTIONS segment)))
             (section-bytes (acl2::lookup-eq-safe :contents section))
             (section-address (acl2::lookup-eq-safe :addr section))
             (text-section-address (acl2::get-mach-o-code-address parsed-mach-o))
             ;; todo: can this be negative?:
             (section-offset-from-text (- section-address text-section-address))
             (section-start (+ text-offset section-offset-from-text)))
        (and (bytes-loaded-at-address-64 section-bytes section-start x86)
             ;; (canonical-address-p$inline const-section-start)
             ;; (canonical-address-p$inline (+ -1 (len const-section-bytes) const-section-start))
             ;; The constant data is disjoint from the part of the stack that is written:
             (separate :r (len section-bytes) section-start
                       ;; Only a single stack slot is written
                       ;;old: (create-canonical-address-list 8 (+ -8 (rgfi *rsp* x86)))
                       :r (* 8 stack-slots-needed) (+ (* -8 stack-slots-needed) (rsp x86)))))
    ;; no assumptions if section not present:
    t))

(defun elf64-section-loadedp (section-bytes
                              section-address
                              text-offset
                              position-independentp ; whether to assume position independence
                              stack-slots-needed
                              text-section-address
                              x86)
  (declare (xargs :guard (and (acl2::unsigned-byte-listp 8 section-bytes)
                              (consp section-bytes)
                              (natp section-address)
                              (natp text-offset)
                              (booleanp position-independentp)
                              (natp stack-slots-needed)
                              (natp text-section-address))
                  :stobjs x86))
  (let* ((section-start (if position-independentp
                            ;; position-independent, so assume the section is loaded at the appropriate offset wrt TEXT-OFFSET, which is where we assume the text section starts.
                            ;; todo: can this be negative?:
                            (let* (;; todo: can this be negative?:
                                   (section-offset-from-text (- section-address text-section-address)))
                              (+ text-offset section-offset-from-text))
                          ;; not position-independent, so use the numeric address (may be necessary):
                          section-address)))
    (and (bytes-loaded-at-address-64 section-bytes section-start x86)
         ;; (canonical-address-p$inline const-section-start)
         ;; (canonical-address-p$inline (+ -1 (len const-section-bytes) const-section-start))
         ;; The section is disjoint from the part of the stack that we expect to be written:
         (if (posp stack-slots-needed) ; should be resolved, because separate requires but numbers to be positive
             (separate :r (len section-bytes) section-start
                       :r (* 8 stack-slots-needed) (+ (* -8 stack-slots-needed)
                                                      (rsp x86)))
           t))))

;; Returns a list of terms over the variables X86 and (perhaps TEXT-OFFSET).
;; TODO: Consider making this non-meta.  That is, make it a predicate on the x86 state.
(defund assumptions-for-elf64-sections (section-names position-independentp stack-slots text-section-address parsed-elf)
  ;; (declare (xargs :guard (and (string-listp section-names) (booleanp position-independentp) (natp stack-slots)
  ;;                             (parsed-elfp parsed-elf)
  ;;                             )))
  (if (endp section-names)
      nil
    (let* ((section-name (first section-names)))
      (if (acl2::elf-section-presentp section-name parsed-elf)
          (prog2$ (cw "(~s0 section detected.)~%" section-name)
                  ;; todo: do better?
                  (cons `(elf64-section-loadedp ;; ',section-name
                                                ',(acl2::get-elf-section-bytes section-name parsed-elf)
                                                ',(acl2::get-elf-section-address section-name parsed-elf)
                                                text-offset
                                                ',position-independentp
                                                ',stack-slots
                                                ',text-section-address
                                                x86)
                        (assumptions-for-elf64-sections (rest section-names) position-independentp stack-slots text-section-address parsed-elf)))
        (assumptions-for-elf64-sections (rest section-names) position-independentp stack-slots text-section-address parsed-elf)))))

;; Returns a list of terms.
;; TODO: Consider making this non-meta.  That is, make it a predicate on the x86 state.
(defun architecture-specific-assumptions (executable-type position-independentp stack-slots parsed-executable)
  (declare (xargs :guard (and (member-eq executable-type '(:mach-o-64 :elf-64))
                              (booleanp position-independentp)
                              (natp stack-slots)
                              ;; parsed-executable
                              )
                  :verify-guards nil))
  (if (eq :mach-o-64 executable-type)
      (b* ((- (and (acl2::mach-o-section-presentp "__TEXT" "__const" parsed-executable) (cw "(__TEXT,__const section detected.)~%")))
           (- (and (acl2::mach-o-section-presentp "__DATA" "__data" parsed-executable) (cw "(__DATA,__data section detected.)~%")))
           (- (and (acl2::mach-o-section-presentp "__DATA_CONST" "__got" parsed-executable) (cw "(__DATA_CONST,__got section detected.)~%"))))
        `((section-assumptions-mach-o-64 "__TEXT" "__const" ',parsed-executable text-offset ',stack-slots x86)
          (section-assumptions-mach-o-64 "__DATA" "__data" ',parsed-executable text-offset ',stack-slots x86)
          (section-assumptions-mach-o-64 "__DATA_CONST" "__got" ',parsed-executable text-offset ',stack-slots x86)
          ;; ,@(and const-section-presentp ; suppress when there is no __const section
          ;;        `((acl2::const-assumptions-mach-o-64 ',parsed-executable text-offset ,stack-slots x86)))
          ;; ,@(and data-section-presentp ; suppress when there is no __data section
          ;;        `((acl2::data-assumptions-mach-o-64 ',parsed-executable text-offset ,stack-slots x86)))
          ))
    (if (eq :elf-64 executable-type) ; todo: handle elf32
        ;; todo: handle more sections here:
        (assumptions-for-elf64-sections '(".data" ".rodata"
                                          ;;  ".got" ; todo: consider putting this back (at least assume it disjoint from the stack)
                                          )
                                        position-independentp stack-slots (acl2::get-elf-code-address parsed-executable) parsed-executable)
      (if (eq :elf-32 executable-type)
          (cw "WARNING: Architecture-specific assumptions are not yet supported for ELF32.~%")
        nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes assumptions that replace calls of the REGISTER-FUNCTIONS, such as (RDI X86),
;; with the given VARS.
;; We make the register variables be usb64s, and we assert that the registers
;; contain their signed forms.  (Note that the registers are signed; see rule X86ISA::I64P-XR-RGF.)
;; Returns (mv replacement-assumptions type-assumptions).
;; TODO: How do these interact with the input-assumptions?
(defund make-register-replacement-assumptions64 (register-functions vars replacement-assumptions-acc type-assumptions-acc)
  (declare (xargs :guard (and (symbol-listp vars)
                              (symbol-listp register-functions))))
  (if (or (endp register-functions) ; additional params will be on the stack
          (endp vars))
      (mv replacement-assumptions-acc type-assumptions-acc)
    (let ((register-name (first register-functions))
          (var (first vars)))
      (make-register-replacement-assumptions64 (rest register-functions)
                                               (rest vars)
                                               (cons `(equal (,register-name x86) (logext '64 ,var)) replacement-assumptions-acc)
                                               (cons `(unsigned-byte-p '64 ,var) type-assumptions-acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Print OK if expected, otherwise ERROR
(defund print-test-summary-aux (result-alist)
  (declare (xargs :guard (alistp result-alist)))
  (if (endp result-alist)
      nil
    (prog2$
     (let* ((entry (first result-alist))
            (name (car entry)) ; a string
            (val (cdr entry)))
       (if (not (and (stringp name)
                     (= 3 (len val))))
           (er hard? 'print-test-summary-aux "Bad entry in result-alist: ~x0." entry)
         (let* ((result (first val)) ; either :pass or :fail
                (expected-result (second val)) ; :pass or :fail or :any
                (elapsed (third val))
                (elapsed (if (and (rationalp elapsed)
                                  (<= 0 elapsed))
                             elapsed
                           (prog2$ (er hard? 'print-test-summary-aux "Bad elapsed time: ~x0." elapsed)
                                   0)))
                (result-string (if (eq :pass result) "pass" "fail"))
                (numspaces (nfix (- 40 (len (coerce name 'list)))))
                )
           (if (equal result expected-result)
               (progn$ (cw "Test ~s0:~_1 OK (~s2)   " name numspaces result-string)
                       (acl2::print-to-hundredths elapsed)
                       (cw "s.~%"))
             (if (eq :any expected-result)
                 ;; In this case, we don't know whether the test is supposed to pass:
                 (progn$ (cw "Test ~s0:~_1 ?? (~s2)   " name numspaces result-string)
                         (acl2::print-to-hundredths elapsed)
                         (cw "s.~%"))
               (progn$ (cw "Test ~s0:~_1 ERROR (~s2, but we expected ~s3).  " name numspaces result-string (if (eq :pass expected-result) "pass" "fail"))
                       (acl2::print-to-hundredths elapsed)
                       (cw "s~%")))))))
     (print-test-summary-aux (rest result-alist)))))

(defund print-test-summary (result-alist executable-path)
  (declare (xargs :guard (and (alistp result-alist)
                              (stringp executable-path))))
  (progn$ (cw"~%========================================~%")
          (cw "SUMMARY OF RESULTS for ~x0:~%" executable-path)
          (print-test-summary-aux result-alist)
          (cw"========================================~%")))

(defun any-result-unexpectedp (result-alist)
  (declare (xargs :guard (alistp result-alist)))
  (if (endp result-alist)
      nil
    (let* ((entry (first result-alist))
           ;; (name (car entry)) ; a string
           (val (cdr entry)))
      (if (not (and ;; (stringp name)
                (= 3 (len val))))
          (er hard? 'any-result-unexpectedp "Bad entry in result-alist: ~x0." entry)
        (let* ((result (first val))           ; either :pass or :fail
               (expected-result (second val))  ; :pass or :fail or :any
               (expectedp (or (eq :any expected-result)
                              (equal result expected-result))))
          (or (not expectedp)
              (any-result-unexpectedp (rest result-alist))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an (mv erp passedp time state).
;; TODO: Add redundancy checking -- where?
;; Parsing of the executable is done outside this function (so we don't do it more than once).
(defun test-function-core (function-name-string
                           parsed-executable
                           param-names ; todo: can we somehow get these from the executable?
                           assumptions ; untranslated terms
                           extra-rules extra-lift-rules extra-proof-rules
                           remove-rules remove-lift-rules remove-proof-rules
                           normalize-xors count-hits print monitor
                           step-limit step-increment
                           prune-precise prune-approx tactics
                           max-conflicts  ;a number of conflicts, or nil for no max
                           inputs-disjoint-from
                           stack-slots
                           position-independentp
                           state)
  (declare (xargs :guard (and (stringp function-name-string)
                              (symbol-listp extra-rules)
                              (symbol-listp extra-lift-rules)
                              (symbol-listp extra-proof-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp remove-lift-rules)
                              (symbol-listp remove-proof-rules)
                              (or (eq :debug monitor)
                                  (symbol-listp monitor))
                              (natp step-limit)
                              (natp step-increment)
                              (acl2::normalize-xors-optionp normalize-xors)
                              (acl2::count-hits-argp count-hits)
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (acl2::tacticsp tactics)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (or (natp stack-slots)
                                  (eq :auto stack-slots))
                              (booleanp position-independentp))
                  :mode :program ; because of apply-tactic-prover and unroll-x86-code-core
                  :stobjs state))
  (b* ((- (acl2::ensure-x86 parsed-executable))
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (32-bitp (member-eq executable-type *executable-types32*))

       (stack-slots (if (eq :auto stack-slots) 100 stack-slots))
       ;; Translate the assumptions supplied by the user:
       (user-assumptions (translate-terms assumptions 'test-function-core (w state)))

       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (- (cw "(Testing ~x0.~%" function-name-string))
       ;; Check the param names, if any:
       ((when (not (or (eq :none param-names)
                       (and (symbol-listp param-names)
                            (no-duplicatesp param-names)
                            (not (member-eq 'x86 param-names))))))
        (cw "ERROR: Bad param names: ~x0." param-names)
        (mv (erp-t) nil nil state))
       ;; todo: consider also the microsoft calling convention:
       (register-names64 '(rdi rsi rdx rcx r8 r9)) ; see the x86-64 calling convention ; todo: what about xmm0-xmm7? param-names should be a map, or separate for float and non-float.
       (param-names (if (eq :none param-names)
                        register-names64 ; todo: how to tell how many will be needed?
                      param-names))
       ;; These serve to introduce vars for the 6 registers that may contain params (todo: confirm this)
       ;; TODO: Consider the implications if the replacement may be incomplete.
       ;; TODO: Add more of these?  What about registers that hold floats, etc.?
       ((mv register-replacement-assumptions register-type-assumptions)
        (if 32-bitp ;todo: add support for this in 32-bit mode, or is the calling convention too different?
            (mv nil nil)
          (make-register-replacement-assumptions64 register-names64 param-names nil nil)))
       (assumptions `(,@user-assumptions
                      ;; (equal (x86isa::mxcsrbits->de$inline (mxcsr x86)) 0) ; no denormal result created yet
                      ;; (equal (x86isa::mxcsrbits->ie$inline (mxcsr x86)) 0) ; invalid operation
                      ;; todo: build this stuff into def-unrolled:
                      ,@register-replacement-assumptions
                      ,@register-type-assumptions
                      ;; todo: build this into def-unrolled:
                      ,@(architecture-specific-assumptions executable-type position-independentp stack-slots parsed-executable)
                      ))
       (target function-name-string)

       (debug-rules (if 32-bitp (debug-rules32) (debug-rules64)))
       (rules-to-monitor (maybe-add-debug-rules debug-rules monitor))
       ;; Unroll the computation:
       ;; TODO: Need this to return assumptions that may be needed in the proof (e.g., about separateness of memory regions)
       ((mv erp result-dag-or-quotep & & & & state)
        (unroll-x86-code-core
          target
          parsed-executable
          assumptions
          nil ;suppress-assumptions
          inputs-disjoint-from
          stack-slots
          position-independentp
          :skip ; no input assumptions -- todo
          '(:register-bool 0) ; output, rax (output should always be boolean), this chops it down to 1 byte (why not one bit?)
          t                   ; use-internal-contextsp
          prune-precise
          prune-approx
          ;; extra-rules:
          (append extra-rules
                  extra-lift-rules
                  (extra-tester-lifting-rules))
          ;; remove-rules:
          (append remove-rules
                  remove-lift-rules)
          ;; extra-assumption-rules:
          (append ;; (new-normal-form-rules64)
                  ;; todo: build these in deeper
                  '(section-assumptions-mach-o-64
                    acl2::mach-o-section-presentp-constant-opener
                    acl2::maybe-get-mach-o-segment-constant-opener
                    acl2::maybe-get-mach-o-segment-from-load-commands-constant-opener
                    acl2::maybe-get-mach-o-section-constant-opener
                    acl2::alistp-constant-opener
                    ;;acl2::const-assumptions-mach-o-64
                    ;;acl2::data-assumptions-mach-o-64
                    ;;acl2::get-mach-o-constants-address-constant-opener
                    ;;acl2::get-mach-o-constants-constant-opener
                    ;;acl2::get-mach-o-data-address-constant-opener
                    ;;acl2::get-mach-o-data-constant-opener
                    elf64-section-loadedp ; todo:package
                    acl2::elf-section-presentp
                    fix-of-rsp
                    integerp-of-rsp))
          ;; remove-asumption-rules:
          nil ; todo: use the remove-lift-rules?
          step-limit
          step-increment
          nil ; stop-pcs
          t ; memoizep (nil allows internal contexts)
          rules-to-monitor
          normalize-xors
          count-hits
          print
          10 ; print-base (todo: consider 16)
          t ; untranslatep (todo: make this an option)
          state))
       ((when erp) (mv erp nil nil state))
       ((when (quotep result-dag-or-quotep))
        (mv-let (elapsed state)
          (acl2::real-time-since start-real-time state)
          (if (equal result-dag-or-quotep ''1)
              (progn$ (cw "Test ~s0 passed in " function-name-string)
                      (acl2::print-to-hundredths elapsed)
                      (cw "s.)~%")
                      (mv (erp-nil)
                          t ; passed ;; `(table test-function-table ',whole-form '(value-triple :invisible))
                          elapsed
                          state))
            (progn$ (cw "Test ~x0 failed (lifting returned the constant dag ~x1 where '1 would mean success).)~%" function-name-string result-dag-or-quotep)
                    (mv (erp-nil)
                        nil ; failed ;; `(table test-function-table ',whole-form '(value-triple :invisible))
                        elapsed
                        state)))))
       (result-dag result-dag-or-quotep)
       ;; Always print the DAG, so we can see the nodenums (e.g., if one is non-pure):
       (- (progn$ (cw "(DAG after lifting:~%")
                  (acl2::print-list result-dag)
                  (cw ")~%")))
       ;; Print the term if small:
       (- (and (acl2::dag-or-quotep-size-less-thanp result-dag 1000)
               (cw "(Term after lifting: ~X01)~%" (acl2::dag-to-term result-dag) nil)))
       (result-dag-fns (dag-fns result-dag))
       ((when (member-eq 'run-until-stack-shorter-than result-dag-fns)) ; TODO: try pruning first
        (cw "ERROR in test ~x0: Did not finish the run.  See DAG above.)~%" function-name-string)
        (mv-let (elapsed state)
          (acl2::real-time-since start-real-time state)
          (mv :did-not-finish-the-run nil elapsed state)))
       (- (and (not (acl2::dag-is-purep result-dag)) ; TODO: This was saying an IF is not pure (why?).  Does it still?
               (cw "WARNING: Result of lifting is not pure (see above).~%")))
       ;; Prove the test routine always returns 1 (we pass :bit for the type):
       (proof-rules (set-difference-eq (append (tester-proof-rules) extra-rules extra-proof-rules)
                                       (append remove-rules
                                               remove-proof-rules
                                               ;; these can introduce boolor: todo: remove from tester-proof-rules?
                                               ;; todo: why is boolor bad?
                                               '(acl2::boolif-x-x-y-becomes-boolor ;drop?
                                                 acl2::boolif-when-quotep-arg2
                                                 acl2::boolif-when-quotep-arg3))))
       ((mv result info-acc state)
        (acl2::apply-tactic-prover result-dag
                                   ;; These are needed because their presence during rewriting can cause BVCHOPs to be dropped:
                                   register-type-assumptions ;TODO: We may need separateness assumptions!
                                   nil ; interpreted-fns
                                   :bit ; type (means try to prove that the DAG is 1)
                                   ;; tests ;a natp indicating how many tests to run
                                   tactics
                                   t   ; simplify-assumptions
                                   ;; types ;does soundness depend on these or are they just for testing? these seem to be used when calling stp..
                                   print
                                   ;; debug ; todo: use this?
                                   max-conflicts
                                   t       ; call-stp-when-pruning
                                   t ; counterexamplep
                                   nil ; print-cex-as-signedp
                                   proof-rules
                                   ;; monitor:
                                   (append '(;ACL2::EQUAL-OF-BVPLUS-MOVE-BVMINUS-BETTER ;drop?
                                             ;;bvlt-reduce-when-not-equal-one-less
                                             ;;boolif-of-bvlt-strengthen-to-equal
                                             )
                                           rules-to-monitor)
                                   t ;normalize-xors
                                   state))
       ((mv elapsed state) (acl2::real-time-since start-real-time state)))
    (if (eq result acl2::*error*)
        (mv :error-in-tactic-proof nil nil state)
      (if (eq result acl2::*valid*)
          (progn$ (cw "Test ~s0 passed in " function-name-string)
                  (acl2::print-to-hundredths elapsed)
                  (cw "s.)~%")
                  (mv (erp-nil)
                      t ; passed ;; `(table test-function-table ',whole-form '(value-triple :invisible))
                      elapsed
                      state))
        ;; result is :invalid, :no-change, or some remaining problems:
        (progn$ (cw "Failure info: ~x0.~%" info-acc) ; todo: sort the counterexample to be in the same order as the param names...
                (cw "Test ~s0 failed.)~%" function-name-string)
                (mv (erp-nil)
                    nil ; failed
                    elapsed
                    state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp event state).
;;If the test passes, EVENT is just (value-triple :invisible).  throws an error if the test failed.
(defun test-function-fn (function-name-string
                         executable ; a parsed-executable or a string (meaning read from that file)
                         param-names ; todo: can we somehoe get these from the executable?
                         assumptions
                         extra-rules extra-lift-rules extra-proof-rules
                         remove-rules remove-lift-rules remove-proof-rules
                         normalize-xors count-hits print monitor
                         step-limit step-increment
                         prune-precise prune-approx tactics
                         max-conflicts inputs-disjoint-from stack-slots
                         position-independent
                         expected-result
                         state)
  (declare (xargs :guard (and (stringp function-name-string)
                              (symbol-listp extra-rules)
                              (symbol-listp extra-lift-rules)
                              (symbol-listp extra-proof-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp remove-lift-rules)
                              (symbol-listp remove-proof-rules)
                              (acl2::normalize-xors-optionp normalize-xors)
                              (acl2::count-hits-argp count-hits)
                              (or (eq :debug monitor)
                                  (symbol-listp monitor))
                              (natp step-limit)
                              (natp step-increment)
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (acl2::tacticsp tactics)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (or (natp stack-slots)
                                  (eq :auto stack-slots))
                              (member-eq position-independent '(t nil :auto))
                              (member-eq expected-result '(:pass :fail :any)))
                  :mode :program
                  :stobjs state))
  (b* (((mv erp parsed-executable state)
        (if (stringp executable)
            (acl2::parse-executable executable state)
          (mv nil executable state)))
       ((when erp) (mv erp nil state))
       (executable-type (acl2::parsed-executable-type parsed-executable))
       ;; Handle a :position-independent of :auto: ; todo: eventually drop this
       (position-independentp (if (eq :auto position-independent)
                                  (if (eq executable-type :mach-o-64)
                                      t ; since clang seems to produce position-independent code by default
                                    (if (eq executable-type :elf-64)
                                        nil ; since gcc seems to not produce position-independent code by default
                                      ;; TODO: Think about this case:
                                      t))
                                position-independent))
       (function-name-string
        (if (eq executable-type :mach-o-64)
            (concatenate 'string "_" function-name-string) ; todo: why do we always have to add the underscore?
          function-name-string))
       ((mv erp passedp elapsed state)
        (test-function-core function-name-string parsed-executable param-names assumptions
                            extra-rules extra-lift-rules extra-proof-rules
                            remove-rules remove-lift-rules remove-proof-rules
                            normalize-xors count-hits print monitor step-limit step-increment prune-precise prune-approx tactics max-conflicts inputs-disjoint-from stack-slots position-independentp state))
       ((when erp) (mv erp nil state))
       (- (cw "Time: ")
          (acl2::print-to-hundredths elapsed)
          (cw "s.~%"))
       (result-ok (if (eq :any expected-result)
                      t
                    (if (eq :pass expected-result)
                        passedp
                      ;; expected-result is :fail
                      (not passedp)))))
    (if result-ok
        (progn$ ;; (cw "Test ~s0: ~s1.~%" function-name-string (if passedp "PASSED" "FAILED"))
         (mv (erp-nil) '(value-triple :invisible) state))
      (prog2$ (er hard? 'test-function-fn "For test ~x0, expected ~x1 but got ~x2." function-name-string expected-result (if passedp :pass :fail))
              (mv :unexpected-result nil state)))))

;; Test a single function:
(defmacro test-function (function-name-string
                         executable ; a parsed-executable or a string (meaning read from that file) ; TODO: Disallow a parsed-executable here?
                         &key
                         (param-names ':none)
                         (assumptions 'nil)
                         (extra-rules 'nil)
                         (extra-lift-rules 'nil)
                         (extra-proof-rules 'nil)
                         (remove-rules 'nil)
                         (remove-lift-rules 'nil)
                         (remove-proof-rules 'nil)
                         (normalize-xors 't) ; todo: try :compact?  maybe not worth it when not equivalence checking
                         (count-hits 'nil)
                         (print 'nil)
                         (monitor 'nil)
                         (step-limit '1000000)
                         (step-increment '100)
                         (prune-precise '10000) ; t, nil, or a max size
                         (prune-approx 't)      ; t, nil, or a max size
                         (tactics '(:rewrite :stp)) ; todo: try something with :prune
                         (expected-result ':pass)
                         (inputs-disjoint-from ':code)
                         (stack-slots ':auto)
                         (position-independent ':auto)
                         (max-conflicts '1000000))
  `(acl2::make-event-quiet (test-function-fn ',function-name-string
                                             ,executable   ; gets evaluated
                                             ,param-names  ; gets evaluated
                                             ,assumptions  ; gets evaluated
                                             ,extra-rules  ; gets evaluated
                                             ,extra-lift-rules ; gets evaluated
                                             ,extra-proof-rules ; gets evaluated
                                             ,remove-rules ; gets evaluated
                                             ,remove-lift-rules ; gets evaluated
                                             ,remove-proof-rules ; gets evaluated
                                             ',normalize-xors
                                             ',count-hits
                                             ',print
                                             ,monitor ; gets evaluated
                                             ',step-limit ',step-increment ',prune-precise ',prune-approx ',tactics ',max-conflicts ',inputs-disjoint-from ',stack-slots ',position-independent ',expected-result state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an (mv erp result-alist state).
(defun test-functions-fn-aux (function-name-strings
                              parsed-executable
                              assumptions-alist
                              extra-rules extra-lift-rules extra-proof-rules
                              remove-rules remove-lift-rules remove-proof-rules
                              normalize-xors count-hits
                              print monitor step-limit step-increment prune-precise prune-approx
                              tactics max-conflicts
                              inputs-disjoint-from
                              stack-slots
                              position-independentp
                              expected-failures
                              result-alist
                              state)
  (declare (xargs :guard (and (string-listp function-name-strings)
                              (and (alistp assumptions-alist)
                                   (string-listp (strip-cars assumptions-alist))
                                   (true-list-listp (strip-cdrs assumptions-alist)))
                              (symbol-listp extra-rules)
                              (symbol-listp extra-lift-rules)
                              (symbol-listp extra-proof-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp remove-lift-rules)
                              (symbol-listp remove-proof-rules)
                              (acl2::normalize-xors-optionp normalize-xors)
                              (acl2::count-hits-argp count-hits)
                              (or (eq :debug monitor)
                                  (symbol-listp monitor))
                              (natp step-limit)
                              (natp step-increment)
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (acl2::tacticsp tactics)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (or (natp stack-slots)
                                  (eq :auto stack-slots))
                              (booleanp position-independentp)
                              (string-listp expected-failures)
                              (alistp result-alist))
                  :mode :program
                  :stobjs state))
  (if (endp function-name-strings)
      (mv (erp-nil) (acl2::reverse-list result-alist) state)
    (b* ((function-name (first function-name-strings))
         ((mv erp passedp elapsed state)
          (test-function-core function-name parsed-executable
                              :none ; todo: some way to pass in param-names?
                              (acl2::lookup-equal function-name assumptions-alist)
                              extra-rules extra-lift-rules extra-proof-rules
                              remove-rules remove-lift-rules remove-proof-rules
                              normalize-xors count-hits print monitor step-limit step-increment prune-precise prune-approx tactics max-conflicts inputs-disjoint-from stack-slots position-independentp state))
         ((when erp) (mv erp nil state))
         (result (if passedp :pass :fail))
         (expected-result (if (member-equal function-name expected-failures)
                              :fail
                            :pass))
         (- (cw "~%")) ; blank line as separator
         )
      (test-functions-fn-aux (rest function-name-strings) parsed-executable assumptions-alist
                             extra-rules extra-lift-rules extra-proof-rules
                             remove-rules remove-lift-rules remove-proof-rules
                             normalize-xors count-hits print monitor step-limit step-increment prune-precise prune-approx
                             tactics max-conflicts inputs-disjoint-from stack-slots position-independentp
                             expected-failures
                             (acons function-name (list result expected-result elapsed) result-alist)
                             state))))

;; Returns (mv erp event state) an event (a progn containing an event for each test).
;; TODO: Return an error if any test is not as expected, but not until the end.
(defun test-functions-fn (executable ; a path to an executable
                          include-fns ; a list of strings (names of functions), or :all
                          exclude-fns ; a list of strings (names of functions)
                          assumptions
                          extra-rules extra-lift-rules extra-proof-rules
                          remove-rules remove-lift-rules remove-proof-rules
                          normalize-xors count-hits print monitor step-limit step-increment prune-precise prune-approx
                          tactics max-conflicts inputs-disjoint-from stack-slots position-independent
                          expected-failures
                          state)
  (declare (xargs :guard (and (stringp executable)
                          (or (string-listp include-fns)
                              (eq :all include-fns))
                          (string-listp exclude-fns)
                              ;; assumptions
                          (symbol-listp extra-rules)
                          (symbol-listp extra-lift-rules)
                          (symbol-listp extra-proof-rules)
                          (symbol-listp remove-rules)
                          (symbol-listp remove-lift-rules)
                          (symbol-listp remove-proof-rules)
                          (acl2::normalize-xors-optionp normalize-xors)
                          (acl2::count-hits-argp count-hits)
                          (or (eq :debug monitor)
                              (symbol-listp monitor))
                          (natp step-limit)
                          (natp step-increment)
                          (or (eq nil prune-precise)
                              (eq t prune-precise)
                              (natp prune-precise))
                          (or (eq nil prune-approx)
                              (eq t prune-approx)
                              (natp prune-approx))
                          (acl2::tacticsp tactics)
                          (or (null max-conflicts)
                              (natp max-conflicts))
                          (member-eq inputs-disjoint-from '(nil :code :all))
                          (or (natp stack-slots)
                              (eq :auto stack-slots))
                          (member-eq position-independent '(t nil :auto))
                          (or (eq :auto expected-failures)
                              (string-listp expected-failures)))
                  :mode :program
                  :stobjs state))
  (b* (((mv overall-start-real-time state) (get-real-time state))
       ;; Parse the executable (TODO: Can we parse less than the whole thing?):
       ((mv erp parsed-executable state)
        (acl2::parse-executable executable state))
       ((when erp) (mv erp nil state))
       ;; Analyze the executable:
       (executable-type (acl2::parsed-executable-type parsed-executable))
       ;; Handle a :position-independent of :auto:
       (position-independentp (if (eq :auto position-independent)
                                  (if (eq executable-type :mach-o-64)
                                      t ; since clang seems to produce position-independent code by default
                                    (if (eq executable-type :elf-64)
                                        nil ; since gcc seems to not produce position-independent code by default
                                      ;; TODO: Think about this case:
                                      t))
                                position-independent))
       ;; We will test all functions whose names begin with test_ or fail_test_
       (function-name-strings (if (eq :all include-fns)
                                  (if (eq :elf-64 executable-type)
                                      (let ((all-functions (acl2::parsed-elf-symbols parsed-executable)))
                                        (append (acl2::strings-starting-with "test_" all-functions)
                                                (acl2::strings-starting-with "fail_test_" all-functions)))
                                    (if (eq :mach-o-64 executable-type)
                                        (let ((all-functions (acl2::get-all-mach-o-symbols parsed-executable)))
                                          (append (acl2::strings-starting-with "_test_" all-functions)
                                                  (acl2::strings-starting-with "_fail_test_" all-functions)))
                                      (er hard? 'test-functions-fn "Unsupported executable type: ~x0" executable-type)))
                                ;; The functions to test were given explicitly:
                                (if (eq executable-type :mach-o-64)
                                    ;; todo: why do we always have to add the underscore?
                                    (acl2::add-prefix-to-strings "_" include-fns)
                                  include-fns)))
       (assumption-alist (if (null assumptions)
                             nil
                           (let ((first-assumption-item (first assumptions)))
                             (if (and (consp first-assumption-item)
                                      (stringp (car first-assumption-item)))
                                 ;; it's an alist, not a list of terms: ; todo: make this a doublet list?
                                 (if (and (alistp assumptions)
                                          (string-listp (strip-cars assumptions))
                                          (true-list-listp (strip-cdrs assumptions)))
                                     assumptions
                                   (er hard? 'test-functions-fn "Ill-formed assumptions: ~X01." assumptions nil))
                               ;; it's a list of (untranslated) terms to be used as assumptions for every function:
                               (pairlis$ function-name-strings (acl2::repeat (len function-name-strings) assumptions))))))
       (expected-failures (if (eq expected-failures :auto)
                              (if (eq :elf-64 executable-type)
                                  (acl2::strings-starting-with "fail_test_" function-name-strings)
                                (if (eq :mach-o-64 executable-type)
                                    (acl2::strings-starting-with "_fail_test_" function-name-strings)
                                  (er hard? 'test-functions-fn "Unsupported executable type: ~x0" executable-type)))
                            ;; The expected failures were given explicitly:
                            expected-failures))
       ;; Handle any excludes:
       (exclude-fns (if (eq executable-type :mach-o-64)
                        (acl2::add-prefix-to-strings "_" exclude-fns)
                      exclude-fns))
       (function-name-strings (set-difference-equal function-name-strings exclude-fns))
       (expected-failures (set-difference-equal expected-failures exclude-fns))
       ;; Sort the functions (TODO: What determines the order in the executable?)
       (function-name-strings (acl2::merge-sort-string< function-name-strings))
       ;; Test the functions:
       ((mv erp result-alist state)
        (test-functions-fn-aux function-name-strings parsed-executable
                               assumption-alist
                               extra-rules extra-lift-rules extra-proof-rules
                               remove-rules remove-lift-rules remove-proof-rules
                               normalize-xors count-hits print monitor step-limit step-increment prune-precise prune-approx
                               tactics max-conflicts inputs-disjoint-from stack-slots position-independentp
                               expected-failures
                               nil ; empty result-alist
                               state))
       ((mv overall-time state) (acl2::real-time-since overall-start-real-time state))
       ((when erp) (mv erp nil state))
       (- (print-test-summary result-alist executable))
       (- (cw "TOTAL TIME: ")
          (acl2::print-to-hundredths overall-time)
          (cw "s (~x0 tests).~%"  (len function-name-strings))))
    (if (any-result-unexpectedp result-alist)
        (prog2$ (er hard? 'test-functions-fn "Unexpected result (see above).")
                (mv t nil state))
      (mv (erp-nil)
          `(value-triple :invisible)
          state))))

;; Test a list of functions:
;; TODO: deprecate this?
(defmacro test-functions (function-name-strings ; or can be :all
                          executable ; a string
                          &key
                          (extra-rules 'nil)
                          (extra-lift-rules 'nil)
                          (extra-proof-rules 'nil)
                          (remove-rules 'nil)
                          (remove-lift-rules 'nil)
                          (remove-proof-rules 'nil)
                          (normalize-xors 't)
                          (count-hits 'nil)
                          (print 'nil)
                          (monitor 'nil)
                          (step-limit '1000000)
                          (step-increment '100)
                          (prune-precise '10000) ; t, nil, or a max size
                          (prune-approx 't)      ; t, nil, or a max size
                          (tactics '(:rewrite :stp)) ; todo: try something with :prune
                          (max-conflicts '1000000)
                          (inputs-disjoint-from ':code)
                          (stack-slots ':auto)
                          (position-independent ':auto)
                          (expected-failures ':auto)
                          (assumptions 'nil) ; an alist pairing function names (strings) with lists of terms, or just a list of terms
                          )
  `(acl2::make-event-quiet (test-functions-fn ,executable ; gets evaluated
                                              ',function-name-strings
                                              nil ; no need for excludes (just don't list the functions you don't want to test)
                                              ,assumptions  ; gets evaluated
                                              ,extra-rules  ; gets evaluated
                                              ,extra-lift-rules ; gets evaluated
                                              ,extra-proof-rules ; gets evaluated
                                              ,remove-rules ; gets evaluated
                                              ,remove-lift-rules ; gets evaluated
                                              ,remove-proof-rules ; gets evaluated
                                              ',normalize-xors
                                              ',count-hits
                                              ',print
                                              ,monitor ; gets evaluated
                                              ',step-limit ',step-increment ',prune-precise ',prune-approx
                                              ',tactics ',max-conflicts ',inputs-disjoint-from ',stack-slots ',position-independent
                                              ',expected-failures
                                              state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests all the functions in the file.
;; Use :include to test only a given set of functions.
;; Use :exclude to test all but a given set of functions.
(defmacro test-file (executable ; a string
                     &key
                     (include ':all) ; names of functions (strings) to test, or can be :all
                     (exclude 'nil) ; names of functions (strings) to exclude from testing
                     (extra-rules 'nil)
                     (extra-lift-rules 'nil)
                     (extra-proof-rules 'nil)
                     (remove-rules 'nil)
                     (remove-lift-rules 'nil)
                     (remove-proof-rules 'nil)
                     (normalize-xors 't)
                     (count-hits 'nil)
                     (print 'nil)
                     (monitor 'nil)
                     (step-limit '1000000)
                     (step-increment '100)
                     (prune-precise '10000) ; t, nil, or a max size
                     (prune-approx 't)      ; t, nil, or a max size
                     (tactics '(:rewrite :stp)) ; todo: try something with :prune
                     (max-conflicts '1000000)
                     (inputs-disjoint-from ':code)
                     (stack-slots ':auto)
                     (position-independent ':auto)
                     (expected-failures ':auto)
                     (assumptions 'nil) ; an alist pairing function names (strings) with lists of terms, or just a list of terms
                     )
  `(acl2::make-event-quiet (test-functions-fn ,executable ; gets evaluated
                                              ',include ; todo: evaluate?
                                              ',exclude ; todo: evaluate?
                                              ,assumptions  ; gets evaluated
                                              ,extra-rules  ; gets evaluated
                                              ,extra-lift-rules ; gets evaluated
                                              ,extra-proof-rules ; gets evaluated
                                              ,remove-rules ; gets evaluated
                                              ,remove-lift-rules ; gets evaluated
                                              ,remove-proof-rules ; gets evaluated
                                              ',normalize-xors
                                              ',count-hits ',print
                                              ,monitor ; gets evaluated
                                              ',step-limit ',step-increment ',prune-precise ',prune-approx
                                              ',tactics ',max-conflicts ',inputs-disjoint-from ',stack-slots ',position-independent
                                              ',expected-failures
                                              state)))
