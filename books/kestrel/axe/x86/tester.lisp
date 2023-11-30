; Formal Unit Tester for x86
;
; Copyright (C) 2021-2022 Kestrel Technology, LLC
; Copyright (C) 2023 Kestrel Institute
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
(include-book "kestrel/booleans/booleans" :dir :system)
(include-book "kestrel/strings-light/string-starts-withp" :dir :system)
(include-book "kestrel/strings-light/add-prefix-to-strings" :dir :system)
(include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system) ; for +-OF-+-OF---SAME
(include-book "unroll-x86-code")
(include-book "tester-rules")
(include-book "kestrel/bv/convert-to-bv-rules" :dir :system) ; todo: combine with bv/intro?
(include-book "kestrel/bv/intro" :dir :system) ; for BVCHOP-OF-LOGXOR-BECOMES-BVXOR
(include-book "rule-lists")
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/utilities/get-real-time" :dir :system))

(acl2::ensure-rules-known (extra-tester-rules))
(acl2::ensure-rules-known (extra-tester-lifting-rules))
(acl2::ensure-rules-known (tester-proof-rules))

;; Returns (mv time-difference state) where time-difference is in seconds and
;; may not be an integer.
(defun real-time-since (start-real-time state)
  (declare (xargs :guard (rationalp start-real-time)
                  :stobjs state))
  (mv-let (now state)
    (get-real-time state)
    (mv (- now start-real-time)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Parens in output may not be balanced?

(acl2::def-constant-opener acl2::maybe-get-mach-o-segment-from-load-commands)
(acl2::def-constant-opener acl2::maybe-get-mach-o-segment)
(acl2::def-constant-opener acl2::maybe-get-mach-o-section)
(acl2::def-constant-opener acl2::mach-o-section-presentp)
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
                       :r (* 8 stack-slots-needed) (+ (* -8 stack-slots-needed) (rgfi *rsp* x86)))))
    ;; no assumptions if section not present:
    t))

;; TODO: Can ELF sections be relocated?
(defun elf64-section-loadedp (section-bytes
                              section-address
                              text-offset
                              position-independentp ; whether to assume position independence, todo: is this ever true?
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
                                                      (rgfi *rsp* x86) ; rephrase?
                                                      ))
           t))))

;; Returns a list of terms over the variables X86 and (perhaps TEXT-OFFSET).
;; TODO: Consider making this non-meta.  That is, make it a predicate on the x86 state.
(defund assumptions-for-elf64-sections (section-names position-independentp stack-slots text-section-address parsed-elf)
  ;; (declare (xargs :guard (and (string-listp section-names) (booleanp position-independentp) (natp stack-slots)
  ;;                             (alistp parsed-elf) ; strengthen
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
        (assumptions-for-elf64-sections '(".data" ".rodata") position-independentp stack-slots (acl2::get-elf-code-address parsed-executable) parsed-executable)
      (if (eq :elf-32 executable-type)
          (cw "WARNING: Architecture-specific assumptions are not yet supported for ELF32.~%")
        nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-register-replacement-assumptions (param-names register-names)
  (declare (xargs :guard (and (symbol-listp param-names)
                              (symbol-listp register-names))))
  (if (or (endp param-names)
          (endp register-names) ; additional params will be on the stack
          )
      nil
    (let ((register-name (first register-names))
          (param-name (first param-names)))
      (cons `(equal (,register-name x86) ,param-name)
            (make-register-replacement-assumptions (rest param-names) (rest register-names))))))

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

;; Filter the STRINGS, keeping only those that start with PREFIX
(defun acl2::strings-starting-with (prefix strings)
  (declare (xargs :guard (and (string-listp strings)
                              (stringp prefix))))
  (if (endp strings)
      nil
    (let ((string (first strings)))
      (if (acl2::string-starts-withp string prefix)
          (cons string
                (acl2::strings-starting-with prefix (rest strings)))
        (acl2::strings-starting-with prefix (rest strings))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an (mv erp passedp time state).
;; TODO: Add redundancy checking
(defun test-function-core (function-name-string
                           parsed-executable
                           param-names ; todo: can we somehow get these from the executable?
                           assumptions ; untranslated terms
                           extra-rules extra-lift-rules extra-proof-rules
                           remove-rules remove-lift-rules remove-proof-rules
                           print monitor
                           step-limit step-increment
                           prune tactics
                           max-conflicts  ;a number of conflicts, or nil for no max
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
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (acl2::tacticsp tactics)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (or (natp stack-slots)
                                  (eq :auto stack-slots))
                              (booleanp position-independentp))
                  :mode :program ; because of apply-tactic-prover and def-unrolled-fn-core
                  :stobjs state))
  (b* ((stack-slots (if (eq :auto stack-slots) 100 stack-slots))
       ;; Translate the assumptions supplied by the user:
       (user-assumptions (translate-terms assumptions 'test-function-core (w state)))
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (- (acl2::ensure-x86 parsed-executable))
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (- (cw "(Now testing ~x0.~%" function-name-string))
       ;; Check the param names:
       ((when (not (or (eq :none param-names)
                       (and (symbol-listp param-names)
                            (no-duplicatesp param-names)
                            (not (member-eq 'x86 param-names))))))
        (cw "ERROR: Bad param names: ~x0." param-names)
        (mv (erp-t) nil nil state))
       ;; These serve to introduce vars for the 6 registers that may contain params (todo: confirm this)
       ;; TODO: Consider the implications if the replacement may be incomplete.
       (register-assumptions (if (eq param-names :none)
                                 ;; We make the register variables be usb64s (todo: add those assumptions), and we assert that the registers
                                 ;; contain their signed forms:
                                 `((equal (rdi x86) (logext 64 rdi))
                                   (equal (rsi x86) (logext 64 rsi))
                                   (equal (rdx x86) (logext 64 rdx))
                                   (equal (rcx x86) (logext 64 rcx))
                                   (equal (r8 x86) (logext 64 r8))
                                   (equal (r9 x86) (logext 64 r9)))
                               (make-register-replacement-assumptions param-names '(rdi rsi rdx rcx r8 r9))))
       (assumptions `(,@user-assumptions
                      ;; these help with floating point code:
                      (equal (x86isa::cr0bits->ts (x86isa::ctri 0 x86)) 0)
                      (equal (x86isa::cr0bits->em (x86isa::ctri 0 x86)) 0)
                      (equal (x86isa::cr4bits->osfxsr (x86isa::ctri 4 x86)) 1)
                      (equal (x86isa::feature-flag ':sse) 1) ; build in?
                      (equal (x86isa::feature-flag ':sse2) 1)
                      (equal (x86isa::mxcsrbits->daz$inline (xr ':mxcsr 'nil x86)) 0) ; denormals are not 0 (true at reset)
                      (equal (x86isa::mxcsrbits->de$inline (xr ':mxcsr 'nil x86)) 0) ; no denormal result created yet
                      (equal (x86isa::mxcsrbits->im$inline (xr ':mxcsr 'nil x86)) 1) ; invalid operations are being masked (true at reset)
                      (equal (x86isa::mxcsrbits->dm$inline (xr ':mxcsr 'nil x86)) 1) ; denormal operations are being masked (true at reset)
                      (equal (x86isa::mxcsrbits->ie$inline (xr ':mxcsr 'nil x86)) 0) ;
                      ;; todo: build this into def-unrolled:
                      ,@register-assumptions
                      ;; todo: build this into def-unrolled:
                      ,@(architecture-specific-assumptions executable-type position-independentp stack-slots parsed-executable)
                      ))
       (target function-name-string)
       (32-bitp (member-eq executable-type *executable-types32*))
       (debug-rules (if 32-bitp (debug-rules32) (debug-rules64)))
       (rules-to-monitor (maybe-add-debug-rules debug-rules monitor))
       ;; Unroll the computation:
       ((mv erp result-dag-or-quotep & & state)
        (def-unrolled-fn-core
          target
          parsed-executable
          assumptions
          nil ;suppress-assumptions
          stack-slots
          position-independentp
          '(:register-bool 0) ; output, rax (output should always be boolean), this chops it down to 1 byte
          t                   ; use-internal-contextsp
          prune
          ;; extra-rules:
          (append '(x86isa::SAL/SHL-SPEC-8-redef
                    x86isa::SAL/SHL-SPEC-16-redef
                    x86isa::SAL/SHL-SPEC-32-redef
                    x86isa::SAL/SHL-SPEC-64-redef
                    x86isa::SHR-SPEC-8-redef
                    x86isa::SHR-SPEC-16-redef
                    x86isa::SHR-SPEC-32-redef
                    x86isa::SHR-SPEC-64-redef
                    x86isa::SAR-SPEC-8-redef
                    x86isa::SAR-SPEC-16-redef
                    x86isa::SAR-SPEC-32-redef
                    x86isa::SAR-SPEC-64-redef
                    x86isa::GPR-OR-SPEC-1-redef
                    x86isa::GPR-OR-SPEC-2-redef
                    x86isa::GPR-OR-SPEC-4-redef
                    x86isa::GPR-OR-SPEC-8-redef
                    ) ; push back to def-unrolled
                  extra-rules
                  extra-lift-rules
                  (extra-tester-lifting-rules))
          ;; remove-rules:
          (append
           '(;; x86isa::gpr-sub-spec-1
             ;; x86isa::gpr-sub-spec-2
             ;; x86isa::gpr-sub-spec-4
             ;; x86isa::gpr-sub-spec-8
             x86isa::x86-cwd/cdq/cqo ; todo: push back to def-unrolled..
             x86isa::GPR-OR-SPEC-1$inline
             x86isa::GPR-OR-SPEC-2$inline
             x86isa::GPR-OR-SPEC-4$inline
             x86isa::GPR-OR-SPEC-8$inline
             x86isa::SAL/SHL-SPEC-8
             x86isa::SAL/SHL-SPEC-16
             x86isa::SAL/SHL-SPEC-32
             x86isa::SAL/SHL-SPEC-64
             x86isa::SHR-SPEC-8
             x86isa::SHR-SPEC-16
             x86isa::SHR-SPEC-32
             x86isa::SHR-SPEC-64
             ;;x86isa::SAR-SPEC-8 ; why are these not present?
             ;;x86isa::SAR-SPEC-16
             ;;x86isa::SAR-SPEC-32
             ;;x86isa::SAR-SPEC-64
             acl2::bvchop-of-bvshr
             acl2::bvchop-of-bvashr)
           remove-rules
           remove-lift-rules)
          ;; extra-assumption-rules:
          (append (lifter-rules64-new)
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
                    acl2::get-elf-section-address
                    acl2::get-elf-section-bytes
                    elf64-section-loadedp
                    acl2::elf-section-presentp
                    fix-of-rsp
                    integerp-of-rsp))
          step-limit
          step-increment
          t ; memoizep
          rules-to-monitor
          print
          10 ; print-base (todo: consider 16)
          state))
       ((when erp) (mv erp nil nil state))
       ((when (quotep result-dag-or-quotep))
        (mv-let (elapsed state)
          (real-time-since start-real-time state)
          (if (equal result-dag-or-quotep ''1)
              (progn$ (cw "Test ~x0 passed (lifting returned the constant dag ~x1).)~%" function-name-string result-dag-or-quotep)
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
        (cw "Test ~x0 failed: Did not finish the run.  See DAG above.)~%" function-name-string)
        (mv-let (elapsed state)
          (real-time-since start-real-time state)
          (mv (erp-nil) nil elapsed state)))
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
                                                 acl2::boolif-when-quotep-arg3
                                                 acl2::bvchop-of-bvshr
                                                 acl2::bvchop-of-bvashr))))
       ((mv result info-acc
            & ; actual-dag
            & ; assumptions-given
            state)
        (acl2::apply-tactic-prover result-dag
                                   ;; tests ;a natp indicating how many tests to run
                                   tactics
                                   nil ; assumptions
                                   t   ; simplify-assumptions
                                   ;; types ;does soundness depend on these or are they just for testing? these seem to be used when calling stp..
                                   print
                                   ;; debug ; todo: use this?
                                   max-conflicts
                                   t       ; call-stp-when-pruning
                                   t ; counterexamplep
                                   nil ; print-cex-as-signedp
                                   proof-rules
                                   nil ; interpreted-fns
                                   ;; monitor:
                                   (append '(;ACL2::EQUAL-OF-BVPLUS-MOVE-BVMINUS-BETTER ;drop?
                                             ;;bvlt-reduce-when-not-equal-one-less
                                             ;;boolif-of-bvlt-strengthen-to-equal
                                             )
                                           rules-to-monitor)
                                   t ;normalize-xors
                                   :bit ; type (means try to prove that the DAG is 1)
                                   state
                                   ;;rand
                                   ))
       ((mv elapsed state) (real-time-since start-real-time state)))
    (if (eq result acl2::*error*)
        (mv :error-in-tactic-proof nil nil state)
      (if (eq result acl2::*valid*)
          (progn$ (cw "Test ~x0 passed.)~%" function-name-string)
                  (mv (erp-nil)
                      t ; passed ;; `(table test-function-table ',whole-form '(value-triple :invisible))
                      elapsed
                      state))
        ;; result is :invalid, :no-change, or some remaining problems:
        (progn$ (cw "Failure info: ~x0.~%" info-acc) ; todo: sort the counterexample to be in the same order as the param names...
                (cw "Test ~x0 failed.)~%" function-name-string)
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
                         print monitor
                         step-limit step-increment
                         prune tactics
                         max-conflicts stack-slots
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
                              (or (eq :debug monitor)
                                  (symbol-listp monitor))
                              (natp step-limit)
                              (natp step-increment)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (acl2::tacticsp tactics)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
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
       ;; Handle a :position-independent of :auto:
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
                            print monitor step-limit step-increment prune tactics max-conflicts stack-slots position-independentp state))
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
                         executable ; a parsed-executable or a string (meaning read from that file)
                         &key
                         (param-names ':none)
                         (assumptions 'nil)
                         (extra-rules 'nil)
                         (extra-lift-rules 'nil)
                         (extra-proof-rules 'nil)
                         (remove-rules 'nil)
                         (remove-lift-rules 'nil)
                         (remove-proof-rules 'nil)
                         (print 'nil)
                         (monitor 'nil)
                         (step-limit '1000000)
                         (step-increment '100)
                         (prune '10000)             ; t, nil, or a max size
                         (tactics '(:rewrite :stp)) ; todo: try something with :prune
                         (expected-result ':pass)
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
                                             ',print
                                             ,monitor ; gets evaluated
                                             ',step-limit ',step-increment ',prune ',tactics ',max-conflicts ',stack-slots ',position-independent ',expected-result state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an (mv erp result-alist state).
(defun test-functions-fn-aux (function-name-strings
                              parsed-executable
                              assumptions-alist
                              extra-rules extra-lift-rules extra-proof-rules
                              remove-rules remove-lift-rules remove-proof-rules
                              print monitor step-limit step-increment prune
                              tactics max-conflicts
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
                              (or (eq :debug monitor)
                                  (symbol-listp monitor))
                              (natp step-limit)
                              (natp step-increment)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (acl2::tacticsp tactics)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
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
                              print monitor step-limit step-increment prune tactics max-conflicts stack-slots position-independentp state))
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
                             print monitor step-limit step-increment prune
                             tactics max-conflicts stack-slots position-independentp
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
                          print monitor step-limit step-increment prune
                          tactics max-conflicts stack-slots position-independent
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
                          (or (eq :debug monitor)
                              (symbol-listp monitor))
                          (natp step-limit)
                          (natp step-increment)
                          (or (eq nil prune)
                              (eq t prune)
                              (natp prune))
                          (acl2::tacticsp tactics)
                          (or (null max-conflicts)
                              (natp max-conflicts))
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
                                      (let ((all-functions (acl2::get-all-elf-symbols parsed-executable)))
                                        (append (acl2::strings-starting-with "test_" all-functions)
                                                (acl2::strings-starting-with "fail_test_" (acl2::get-all-elf-symbols parsed-executable))))
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
                               print monitor step-limit step-increment prune
                               tactics max-conflicts stack-slots position-independentp
                               expected-failures
                               nil ; empty result-alist
                               state))
       ((mv overall-time state) (real-time-since overall-start-real-time state))
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
;; deprecate this?
(defmacro test-functions (function-name-strings ; or can be :all
                          executable ; a string
                          &key
                          (extra-rules 'nil)
                          (extra-lift-rules 'nil)
                          (extra-proof-rules 'nil)
                          (remove-rules 'nil)
                          (remove-lift-rules 'nil)
                          (remove-proof-rules 'nil)
                          (print 'nil)
                          (monitor 'nil)
                          (step-limit '1000000)
                          (step-increment '100)
                          (prune '10000)             ; t, nil, or a max size
                          (tactics '(:rewrite :stp)) ; todo: try something with :prune
                          (max-conflicts '1000000)
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
                                              ',print
                                              ,monitor ; gets evaluated
                                              ',step-limit ',step-increment ',prune
                                              ',tactics ',max-conflicts ',stack-slots ',position-independent
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
                     (print 'nil)
                     (monitor 'nil)
                     (step-limit '1000000)
                     (step-increment '100)
                     (prune '10000)             ; t, nil, or a max size
                     (tactics '(:rewrite :stp)) ; todo: try something with :prune
                     (max-conflicts '1000000)
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
                                              ',print
                                              ,monitor ; gets evaluated
                                              ',step-limit ',step-increment ',prune
                                              ',tactics ',max-conflicts ',stack-slots ',position-independent
                                              ',expected-failures
                                              state)))
