; An unrolling lifter xfor x86 code (based on Axe)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Two approaches: 1. Use X86 as the only variable and get back a term
;; over the single variable X86 that captures the effect of the code.
;; 2. Introduce variables such as X and Y for the inputs and get back
;; a term over x86 and those variables.  This may make it easier to
;; state assumptions (since they can mention X and Y).  We use the
;; second approach here for now.

(include-book "support-axe")
(include-book "../bitops-rules")
(include-book "../logops-rules-axe")
(include-book "kestrel/x86/if-lowering" :dir :system)
(include-book "kestrel/x86/read-over-write-rules" :dir :system)
(include-book "kestrel/x86/read-over-write-rules32" :dir :system)
(include-book "kestrel/x86/read-over-write-rules64" :dir :system)
(include-book "kestrel/x86/write-over-write-rules" :dir :system)
(include-book "kestrel/x86/write-over-write-rules32" :dir :system)
(include-book "kestrel/x86/write-over-write-rules64" :dir :system)
(include-book "kestrel/x86/x86-changes" :dir :system)
(include-book "kestrel/x86/tools/lifter-support" :dir :system)
(include-book "kestrel/x86/conditions" :dir :system)
(include-book "kestrel/x86/support" :dir :system)
(include-book "kestrel/x86/assumptions32" :dir :system)
(include-book "kestrel/x86/assumptions64" :dir :system)
(include-book "kestrel/x86/floats" :dir :system)
(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(include-book "kestrel/x86/separate" :dir :system)
(include-book "kestrel/x86/support-bv" :dir :system)
(include-book "rule-lists")
(include-book "kestrel/x86/run-until-return" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "../rules-in-rule-lists")
;(include-book "../rules2") ;for BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P-NON-CONST
;(include-book "../rules1") ;for ACL2::FORCE-OF-NON-NIL, etc.
(include-book "../rewriter") ; for the :legacy rewriter option ; todo: brings in skip-proofs, TODO: Consider using rewriter-basic (but it needs versions of simp-dag and simplify-terms-repeatedly)
;(include-book "../basic-rules")
(include-book "../step-increments")
(include-book "../dag-size")
(include-book "../dag-info")
(include-book "../prune-dag-precisely")
(include-book "../prune-dag-approximately")
(include-book "../arithmetic-rules-axe")
(include-book "rewriter-x86")
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/if" :dir :system)
(include-book "kestrel/utilities/if-rules" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system) ; for print-to-hundredths
(include-book "kestrel/utilities/map-symbol-name" :dir :system)
(include-book "kestrel/utilities/defmacrodoc" :dir :system)
(include-book "kestrel/booleans/booleans" :dir :system)
(include-book "kestrel/lists-light/take" :dir :system)
(include-book "kestrel/lists-light/nthcdr" :dir :system)
(include-book "kestrel/lists-light/append" :dir :system)
(include-book "kestrel/arithmetic-light/less-than" :dir :system)
(include-book "kestrel/bv/arith" :dir :system) ;reduce?
(include-book "kestrel/bv/intro" :dir :system)
(include-book "kestrel/bv/rtl" :dir :system)
(include-book "kestrel/bv/convert-to-bv-rules" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system) ;reduce? for logext-identity
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/arithmetic-light/ash" :dir :system) ; for ash-of-0, mentioned in a rule-list
(include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system) ; for +-OF-+-OF---SAME
(include-book "kestrel/bv/bvif2" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/arithmetic-light/truncate" :dir :system)
(include-book "kestrel/utilities/real-time-since" :dir :system)
(include-book "kestrel/strings-light/string-ends-withp" :dir :system)
(include-book "kestrel/strings-light/strip-suffix-from-string" :dir :system)
(include-book "kestrel/strings-light/split-string" :dir :system)
(local (include-book "kestrel/utilities/get-real-time" :dir :system))
(local (include-book "kestrel/utilities/doublet-listp" :dir :system))
(local (include-book "kestrel/utilities/greater-than-or-equal-len" :dir :system))

(in-theory (disable str::coerce-to-list-removal)) ;todo

(acl2::ensure-rules-known (lifter-rules32-all))
(acl2::ensure-rules-known (lifter-rules64-all))
(acl2::ensure-rules-known (assumption-simplification-rules))
(acl2::ensure-rules-known (step-opener-rules))

;move
;; We often want these for ACL2 proofs, but not for 64-bit examples
(deftheory 32-bit-reg-rules
  '(xw-becomes-set-eip
    xw-becomes-set-eax
    xw-becomes-set-ebx
    xw-becomes-set-ecx
    xw-becomes-set-edx
    xw-becomes-set-esp
    xw-becomes-set-ebp
    ;; introduce eip too?
    xr-becomes-eax
    xr-becomes-ebx
    xr-becomes-ecx
    xr-becomes-edx
    xr-becomes-ebp
    xr-becomes-esp)
  :redundant-okp t)

;; For safety:
(in-theory (disable (:executable-counterpart sys-call)))
(theory-invariant (not (active-runep '(:executable-counterpart sys-call))))

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move this util

(defun print-term-elided (item firstp fns-to-elide)
  (declare (xargs :guard (symbol-listp fns-to-elide)))
  (if (and (consp item)
           (member-eq (ffn-symb item) fns-to-elide))
      ;; eliding:
      ;; todo: allow eliding some args but not others?
      (if firstp ; leading paren but not leading space
          (cw "((~x0 ...)~%" (ffn-symb item))
        (cw " (~x0 ...)~%" (ffn-symb item)))
    ;; not eliding:
    (if firstp ; no leading space
        (cw "(~y0" item)
      (cw " ~y0" item))))

;doesn't stack overflow when printing a large list
(defun print-terms-elided-aux (lst fns-to-elide)
  (declare (xargs :guard (and (true-listp lst)
                              (symbol-listp fns-to-elide))))
  (if (atom lst)
      nil
    (prog2$ (print-term-elided (first lst) nil fns-to-elide)
            (print-terms-elided-aux (rest lst) fns-to-elide))))

(defun print-terms-elided (lst fns-to-elide)
  (declare (xargs :guard (and (true-listp lst)
                              (symbol-listp fns-to-elide))))
  (if (consp lst)
      (prog2$ (print-term-elided (first lst) t fns-to-elide) ;print the first element separately to put in an open paren
              (prog2$ (print-terms-elided-aux (rest lst) fns-to-elide)
                      (cw ")")))
    (cw "nil") ; or could do ()
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: strengthen:   what are the allowed types?  todo: Allow float types?
(defun names-and-typesp (names-and-types)
  (declare (xargs :guard t))
  (and (doublet-listp names-and-types)
       (let ((names (strip-cars names-and-types))
             (types (acl2::strip-cadrs names-and-types)))
         (and (symbol-listp names)
              ;; Can't use the same name as a register (would make the output-indicator ambiguous):
              (not (intersection-equal (acl2::map-symbol-name names) '("RAX" "EAX" "ZMM0" "YMM0" "XMM0"))) ; todo: keep in sync with normal-output-indicatorp
              (acl2::symbol-listp types)))))

;; todo: think about signed (i) vs unsigned (u)
(defconst *scalar-type-to-bytes-alist*
  '(("U8" . 1)
    ("I8" . 1)
    ("U16" . 2)
    ("I16" . 2)
    ("U32" . 4)
    ("I32" . 4)
    ("U64" . 8)
    ("I64" . 8)
    ;; anything larger would not fit in register
    ))

(defund bytes-in-scalar-type (type)
  (declare (xargs :guard (stringp type)))
  (let ((res (acl2::lookup-equal type *scalar-type-to-bytes-alist*)))
    (if res
        res
      (prog2$ (er hard? 'bytes-in-scalar-type "Unsupported type: ~x0." type)
              ;; for guard proof:
              1))))

(defthm posp-of-bytes-in-scalar-type
  (posp (bytes-in-scalar-type type))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable bytes-in-scalar-type ACL2::LOOKUP-EQUAL))))

(defund var-intro-assumptions-for-array-input (index len element-size pointer-name var-name)
  (declare (xargs :guard (and (natp index)
                              (natp len)
                              (posp element-size)
                              (symbolp pointer-name)
                              (symbolp var-name))
                  :measure (nfix (+ 1 (- len index)))))
  (if (or (not (mbt (and (natp len)
                         (natp index))))
          (<= len index))
      nil
    (cons `(equal (read ,element-size
                        ,(if (posp index)
                            `(+ ,(* index element-size) ,pointer-name)
                          pointer-name)
                        x86)
                  ,(acl2::pack-in-package "X" var-name index))
          (var-intro-assumptions-for-array-input (+ 1 index) len element-size pointer-name var-name))))

;; (var-intro-assumptions-for-array-input '0 '6 '4 'foo-ptr 'foo)

;;Rreturns a parsed-type or :error.
;; Types are parsed right-to-left, with the rightmost thing being the top construct.
(defund parse-type-string (type-str)
  (declare (xargs :guard (stringp type-str)
                  :measure (length type-str)
                  :hints (("Goal" :in-theory (disable length)))))
  (if (acl2::string-ends-withp type-str "*")
      `(:pointer ,(parse-type-string (acl2::strip-suffix-from-string "*" type-str)))
    (if (acl2::string-ends-withp type-str "]")
        (b* (((mv foundp base-type rest) (acl2::split-string type-str #\[))
             ((when (not foundp)) :error)
             (element-count-string (acl2::strip-suffix-from-string "]" rest))
             (element-count (acl2::parse-string-as-decimal-number element-count-string))
             ((when (not (posp element-count))) :error))
          `(:array ,(parse-type-string base-type) ,element-count))
      ;; a scalar type:
      (if (assoc-equal type-str *scalar-type-to-bytes-alist*)
          type-str
        :error))))

(defund parse-type (sym)
  (declare (xargs :guard (symbolp sym)))
  (parse-type-string (symbol-name sym)))

(defund assumptions-for-input (var-name
                               type ;; examples: :u32 or :u32* or :u32[4]
                               state-component
                               stack-slots
                               text-offset
                               code-length)
  (declare (xargs :guard (and (symbolp var-name)
                              (symbolp type)
                              ;;state-component might be rdi or (rdi x86)
                              (natp stack-slots)
                              ;; text-offset is a term
                              (natp code-length))))
  (let ((type (parse-type type)))
    (if (eq :error type)
        (er hard? 'assumptions-for-input "Bad type: ~x0." type)
      (if (atom type) ; scalar
          ;; just put in the var name for the state component:
          ;; todo: what about signed/unsigned?
          `((equal ,state-component ,var-name))
        (let ((stack-byte-count (* 8 stack-slots))) ; each stack element is 64-bits
          (if (and (call-of :pointer type)
                   (stringp (farg1 type)) ; for guards
                   )
              (let* ((base-type (farg1 type))
                     (numbytes (bytes-in-scalar-type base-type))
                     (pointer-name (acl2::pack-in-package "X" var-name '_ptr)) ;todo: watch for clashes; todo: should this be the main name and the other the "contents"?
                     )
                `((equal ,state-component ,pointer-name)
                  ;; todo: what about reading individual bytes?:  don't trim down reads?
                  (equal (read ,numbytes ,pointer-name x86) ,var-name)
                  (canonical-address-p$inline ,pointer-name) ; first address
                  (canonical-address-p (+ ,(- numbytes 1) ,pointer-name)) ; last address
                  ;; The input is disjount from the space into which the stack will grow:
                  (separate :r ,numbytes ,pointer-name
                            :r ,stack-byte-count
                            (+ ,(- stack-byte-count) (rsp x86)))
                  ;; The input is disjoint from the code:
                  (separate :r ,numbytes ,pointer-name
                            :r ,code-length ,text-offset)
                  ;; The input is disjoint from the saved return address:
                  ;; todo: reorder args?
                  (separate :r 8 (rsp x86)
                            :r ,numbytes ,pointer-name)))
            (if (and (call-of :array type)
                     (stringp (farg1 type)) ; for guards
                     (natp (farg2 type)) ; for guards
                     )
                ;; must be an :array type:  ; TODO: What if the whole array fits in a register?
                (b* ((base-type (farg1 type))
                     (element-count (farg2 type))
                     (element-size (bytes-in-scalar-type base-type))
                     (numbytes (* element-count element-size))
                     (pointer-name (acl2::pack-in-package "X" var-name '_ptr)) ;todo: watch for clashes; todo: should this be the main name and the other the "contents"?
                     )
                  (append (var-intro-assumptions-for-array-input 0 element-count element-size pointer-name var-name)
                          `((equal ,state-component ,pointer-name)
                            (canonical-address-p$inline ,pointer-name) ; first address
                            (canonical-address-p (+ ,(- numbytes 1) ,pointer-name)) ; last address
                            ;; The input is disjount from the space into which the stack will grow:
                            (separate :r ,numbytes ,pointer-name
                                      :r ,stack-byte-count
                                      (+ ,(- stack-byte-count) (rsp x86)))
                            ;; The input is disjoint from the code:
                            (separate :r ,numbytes ,pointer-name
                                      :r ,code-length ,text-offset)
                            ;; The input is disjoint from the saved return address:
                            ;; todo: reorder args?
                            (separate :r 8 (rsp x86)
                                      :r ,numbytes ,pointer-name))))
              (er hard? 'assumptions-for-input "Bad type: ~x0." type))))))))

;; might have extra, unneeded items in state-components
(defun assumptions-for-inputs (names-and-types state-components stack-slots text-offset code-length)
  (declare (xargs :mode :program ; todo
                  :guard (and (names-and-typesp names-and-types)
                              (natp stack-slots)
                              ;; text-offset is a term
                              (natp code-length))))
  (if (endp names-and-types)
      nil
    (let* ((name-and-type (first names-and-types))
           (name (first name-and-type))
           (type (second name-and-type))
           (state-component (first state-components))
           )
      (append (assumptions-for-input name type state-component stack-slots text-offset code-length)
              (assumptions-for-inputs (rest names-and-types) (rest state-components) stack-slots text-offset code-length)))))

;; Example: (assumptions-for-inputs '((v1 :u32*) (v2 :u32*)) '((rdi x86) (rsi x86)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun remove-assumptions-about (fns-to-remove terms)
  (declare (xargs :guard (and (symbol-listp fns-to-remove)
                              (pseudo-term-listp terms))))
  (if (endp terms)
      nil
    (let* ((term (first terms))
           ;; strip a NOT if present:
           (term (if (and (consp term)
                          (eq 'not (ffn-symb term))
                          (= 1 (len (fargs term))))
                     (farg1 term)
                   term)))
      (if (and (consp term)
               (member-eq (ffn-symb term) fns-to-remove))
          (remove-assumptions-about fns-to-remove (rest terms))
        (cons term (remove-assumptions-about fns-to-remove (rest terms)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: more?
(defconst *non-stp-assumption-functions*
  '(canonical-address-p$inline
    program-at
    separate
    x86p
    cr0bits-p$inline
    cr4bits-p$inline
    alignment-checking-enabled-p
    ))

;; Repeatedly rewrite DAG to perform symbolic execution.  Perform
;; STEP-INCREMENT steps at a time, until the run finishes, STEPS-LEFT is
;; reduced to 0, or a loop or an unsupported instruction is detected.
;; Returns (mv erp result-dag-or-quotep state).
(defun repeatedly-run (steps-left step-increment dag rule-alist assumptions rules-to-monitor use-internal-contextsp prune print print-base untranslatep memoizep rewriter total-steps state)
  (declare (xargs :guard (and (natp steps-left)
                              (acl2::step-incrementp step-increment)
                              (acl2::pseudo-dagp dag)
                              (acl2::rule-alistp rule-alist)
                              (pseudo-term-listp assumptions)
                              (symbol-listp rules-to-monitor)
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (booleanp memoizep)
                              (natp total-steps)
                              (member-eq rewriter '(:x86 :legacy)))
                  :mode :program
                  :stobjs (state)))
  (if (zp steps-left)
      (mv (erp-nil) dag state)
    (b* ((this-step-increment (acl2::this-step-increment step-increment total-steps))
         (steps-for-this-iteration (min steps-left this-step-increment))
         (- (cw "(Running (up to ~x0 steps):~%" steps-for-this-iteration))
         ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
         (old-dag dag)
         ;; (- (and print (progn$ (cw "(DAG before stepping:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         (limits nil) ; todo: call this empty-rule-limits?
         (limits (acl2::add-limit-for-rules (step-opener-rules) steps-for-this-iteration limits)) ; don't recompute for each small run?
         ((mv erp dag-or-quote state)
          (if (eq :legacy rewriter)
              (acl2::simp-dag dag ; todo: call the basic rewriter, but it needs to support :use-internal-contextsp
                              :exhaustivep t
                              :rule-alist rule-alist
                              :assumptions assumptions
                              :monitor rules-to-monitor
                              ;; :fns-to-elide '(program-at) ; not supported
                              :use-internal-contextsp use-internal-contextsp
                              ;; pass print, so we can cause rule hits to be printed:
                              :print print ; :brief ;nil
                              ;; :print-interval 10000 ;todo: pass in
                              :limits limits
                              :memoizep memoizep
                              :check-inputs nil)
            (mv-let (erp result)
              (acl2::simplify-dag-x86 dag
                                        assumptions
                                        nil ; interpreted-function-alist
                                        limits
                                        rule-alist
                                        t ; count-hints ; todo: think about this
                                        print
                                        (acl2::known-booleans (w state))
                                        rules-to-monitor
                                        '(program-at) ; fns-to-elide
                                        t ; normalize-xors
                                        memoizep)
              (mv erp result state))))
         ((when erp) (mv erp nil state))
         ((mv elapsed state) (acl2::real-time-since start-real-time state))
         (- (cw " This limited run took ")
            (acl2::print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
            (cw "s.)~%")) ; matches "(Running"
         ((when (quotep dag-or-quote)) (mv (erp-nil) dag-or-quote state))
         (- (and print ;(acl2::print-level-at-least-tp print)
                 (progn$ (cw "(DAG after this limited run:~%")
                         (cw "~X01" dag-or-quote nil)
                         (cw ")~%"))))
         (dag dag-or-quote) ; it wasn't a quotep
         ;; Prune the DAG quickly but possibly imprecisely:
         ((mv erp dag-or-quotep state) (acl2::prune-dag-approximately dag
                                                                      (remove-assumptions-about *non-stp-assumption-functions* assumptions)
                                                                      t ; check-fnsp
                                                                      print state))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-quotep)) (mv (erp-nil) dag-or-quotep state))
         (dag dag-or-quotep) ; it wasn't a quotep
         ;; (- (and print (progn$ (cw "(DAG after first pruning:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; Prune precisely if feasible:
         ;; TODO: Maybe don't prune if the run has completed (but do simplify in that case)?
         ((mv erp dag-or-quotep state)
          (acl2::maybe-prune-dag-precisely prune ; if a natp, can help prevent explosion.
                                           dag
                                           ;; the assumptions used during lifting (program-at, MXCSR assumptions, etc) seem unlikely
                                           ;; to be helpful when pruning, and user assumptions seem like they should be applied by the
                                           ;; rewriter duing lifting (TODO: What about assumptions only usable by STP?)
                                           nil ; assumptions
                                           :none
                                           rule-alist
                                           nil ; interpreted-fns
                                           rules-to-monitor
                                           t ;call-stp
                                           print
                                           state))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-quotep)) (mv (erp-nil) dag-or-quotep state))
         (dag dag-or-quotep) ; it wasn't a quotep
         ;; (- (and print (progn$ (cw "(DAG after second pruning:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; TODO: If pruning did something, consider doing another rewrite here (pruning may have introduced bvchop or bool-fix$inline).  But perhaps now there are enough rules used in pruning to handle that?
         (dag-fns (acl2::dag-fns dag))
         ;; Stop if we hit an unimplemented instruction (what if it's on an unreachable branch?):
         ((when (member-eq 'x86isa::x86-step-unimplemented dag-fns))
          (prog2$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%")
                  (mv (erp-nil) dag state))) ; todo: return an error?
         (nothing-changedp (acl2::equivalent-dagsp dag old-dag)) ; todo: can we test equivalence up to xor nest normalization?
         ((when nothing-changedp)
          (cw "Note: Stopping the run because nothing changed.~%")
          (mv (erp-nil) dag state)) ; todo: return an error?
         (run-completedp (not (member-eq 'run-until-stack-shorter-than dag-fns))) ;; stop if the run is done
         (- (and run-completedp (cw "(The run has completed.)~%")))
         )
      (if run-completedp
          ;; Simplify one last time (since pruning may have done something -- todo: skip this if pruning did nothing):
          (b* ((- (cw "(Doing final simplification:~%"))
               ((mv erp dag-or-quote state)
                (if (eq :legacy rewriter)
                    (acl2::simp-dag dag ; todo: call the basic rewriter, but it needs to support :use-internal-contextsp
                                    :exhaustivep t
                                    :rule-alist rule-alist
                                    :assumptions assumptions
                                    :monitor rules-to-monitor
                                    :use-internal-contextsp use-internal-contextsp
                                    ;; pass print, so we can cause rule hits to be printed:
                                    :print print ; :brief ;nil
                                    ;; :print-interval 10000 ;todo: pass in
                                    :limits limits
                                    :memoizep memoizep
                                    :check-inputs nil)
                  (mv-let (erp result)
                    (acl2::simplify-dag-x86 dag
                                            assumptions
                                            nil ; interpreted-function-alist
                                            limits
                                            rule-alist
                                            t ; count-hints ; todo: think about this
                                            print
                                            (acl2::known-booleans (w state))
                                            rules-to-monitor
                                            '(program-at code-segment-assumptions32-for-code) ; fns-to-elide
                                            t ; normalize-xors
                                            memoizep)
                    (mv erp result state))))
               (- (cw " Done with final simplification.)~%")) ; balances "(Doing final simplification"
               ((when erp) (mv erp nil state)))
            (mv (erp-nil) dag-or-quote state))
        ;; Continue the symbolic execution:
        (let* ((total-steps (+ steps-for-this-iteration total-steps))
               (state ;; Print as a term unless it would be huge:
                 (if (acl2::print-level-at-least-tp print)
                     (if (< (acl2::dag-or-quotep-size dag) 1000)
                         (b* ((- (cw "(Term after ~x0 steps:~%" total-steps))
                              (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                                         (set-print-base-radix print-base state)
                                       state))
                              (- (cw "~X01" (let ((term (dag-to-term dag)))
                                              (if untranslatep
                                                  (untranslate term nil (w state))
                                                term))
                                     nil))
                              (state (set-print-base-radix 10 state)) ;make event sets it to 10
                              (- (cw ")~%")))
                           state)
                       (b* ((- (cw "(DAG after ~x0 steps:~%" total-steps))
                            (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                                       (set-print-base-radix print-base state)
                                     state))
                            (- (cw "~X01" dag nil))
                            (state (set-print-base-radix 10 state))
                            (- (cw "(DAG has ~x0 IF-branches.)~%" (acl2::count-top-level-if-branches-in-dag dag)))
                            (- (cw ")~%")))
                         state))
                   state)))
          (repeatedly-run (- steps-left steps-for-this-iteration)
                          step-increment
                          dag rule-alist assumptions rules-to-monitor use-internal-contextsp prune print print-base untranslatep memoizep rewriter
                          total-steps
                          state))))))

;; Returns (mv erp result-dag-or-quotep assumptions lifter-rules-used assumption-rules-used state).
;; This is also called by the formal unit tester.
(defun unroll-x86-code-core (target
                             parsed-executable
                             extra-assumptions ; todo: can these introduce vars for state components?  support that more directly?  could also replace register expressions with register names (vars)
                             suppress-assumptions
                             stack-slots
                             position-independentp
                             inputs
                             output
                             use-internal-contextsp
                             prune
                             extra-rules
                             remove-rules
                             extra-assumption-rules
                             step-limit
                             step-increment
                             memoizep
                             monitor
                             print
                             print-base
                             untranslatep
                             rewriter
                             state)
  (declare (xargs :guard (and (lifter-targetp target)
                              ;; parsed-executable
                              ;; extra-assumptions ; untranslated terms
                              (booleanp suppress-assumptions)
                              (natp stack-slots)
                              (booleanp position-independentp)
                              (or (eq :skip inputs) (names-and-typesp inputs))
                              (output-indicatorp output)
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp extra-assumption-rules)
                              (natp step-limit)
                              (acl2::step-incrementp step-increment)
                              (booleanp memoizep)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (member-eq rewriter '(:x86 :legacy)))
                  :stobjs (state)
                  :mode :program))
  (b* ((- (cw "(Lifting ~s0.~%" target)) ;todo: print the executable name
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (state (acl2::widen-margins state))
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (- (acl2::ensure-x86 parsed-executable))
       (- (and (acl2::print-level-at-least-tp print) (cw "(Executable type: ~x0.)~%" executable-type)))
       ;;todo: finish adding support for :entry-point!
       ((when (and (eq :entry-point target)
                   (not (eq :pe-32 executable-type))))
        (er hard? 'unroll-x86-code-core "Starting from the :entry-point is currently only supported for PE-32 files.")
        (mv :bad-entry-point nil nil nil nil state))
       ((when (and (natp target)
                   (not (eq :pe-32 executable-type))))
        (er hard? 'unroll-x86-code-core "Starting from a numeric offset is currently only supported for PE-32 files.")
        (mv :bad-entry-point nil nil nil nil state))
       (- (and (stringp target)
               ;; Throws an error if the target doesn't exist:
               (acl2::ensure-target-exists-in-executable target parsed-executable)))
       ((when (and (not position-independentp)
                   (not (member-eq executable-type '(:mach-o-64 :elf-64)))))
        (er hard? 'unroll-x86-code-core "Non-position-independent lifting is currently only supported for ELF64 and MACHO64 files.")
        (mv :bad-options nil nil nil nil state))
       ;; Generate assumptions (these get simplified below to put them into normal form):
       (64-bitp (member-equal executable-type '(:mach-o-64 :pe-64 :elf-64)))
       (text-offset
         (and 64-bitp ; todo
              (if (eq :mach-o-64 executable-type)
                  (if position-independentp 'text-offset `,(acl2::get-mach-o-code-address parsed-executable))
                (if (eq :pe-64 executable-type)
                    'text-offset ; todo: match what we do for other executable types
                  (if (eq :elf-64 executable-type)
                      (if position-independentp 'text-offset `,(acl2::get-elf-code-address parsed-executable))
                    (if (eq :mach-o-32 executable-type)
                        nil ; todo
                      (if (eq :pe-32 executable-type)
                          nil ; todo
                        ;; todo: add support for :elf-32
                        (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type))))))))
       (code-length
         (and 64-bitp ; todo
              (if (eq :mach-o-64 executable-type)
                  (len (acl2::get-mach-o-code parsed-executable))
                (if (eq :pe-64 executable-type)
                    10000 ; fixme
                  (if (eq :elf-64 executable-type)
                      (len (acl2::get-elf-code parsed-executable))
                    (if (eq :mach-o-32 executable-type)
                        nil ; todo
                      (if (eq :pe-32 executable-type)
                          nil ; todo
                        ;;todo: add support for :elf-32
                        (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type))))))))
       (automatic-assumptions
        (if suppress-assumptions
            ;; Suppress tool-generated assumptions; use only the explicitly provided ones:
            nil
          (if (eq :mach-o-64 executable-type)
              `((standard-assumptions-mach-o-64 ',target
                                                ',parsed-executable
                                                ',stack-slots
                                                ,text-offset
                                                x86))
            (if (eq :pe-64 executable-type)
                `((standard-assumptions-pe-64 ',target
                                              ',parsed-executable
                                              ',stack-slots
                                              text-offset
                                              x86))
              (if (eq :elf-64 executable-type)
                  `((standard-assumptions-elf-64 ',target
                                                 ',parsed-executable
                                                 ',stack-slots
                                                 ,text-offset
                                                 x86))
                (if (eq :mach-o-32 executable-type)
                    (gen-standard-assumptions-mach-o-32 target parsed-executable stack-slots)
                  (if (eq :pe-32 executable-type)
                      ;; todo: try without expanding this:
                      (gen-standard-assumptions-pe-32 target parsed-executable stack-slots)
                    ;;todo: add support for :elf-32
                    (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type))))))))
       (input-assumptions (if (and 64-bitp ; todo
                                   (not (equal inputs :skip)) ; really means generate no assumptions
                                   )
                              (assumptions-for-inputs inputs
                                                      ;; todo: handle zmm regs and values passed on the stack?!:
                                                      ;; handle structs that fit in 2 registers?
                                                      ;; See the System V AMD64 ABI
                                                      '((rdi x86) (rsi x86) (rdx x86) (rcx x86) (r8 x86) (r9 x86))
                                                      stack-slots
                                                      text-offset
                                                      code-length)
                            nil))
       (assumptions (append automatic-assumptions input-assumptions extra-assumptions))
       (assumptions-to-return assumptions)
       (assumptions (acl2::translate-terms assumptions 'unroll-x86-code-core (w state))) ; perhaps don't translate the automatic-assumptions?
       (- (and (acl2::print-level-at-least-tp print) (progn$ (cw "(Unsimplified assumptions:~%")
                                                             (print-terms-elided assumptions '(standard-assumptions-elf-64
                                                                                              standard-assumptions-mach-o-64
                                                                                              standard-assumptions-pe-64)) ; todo: more?
                                                             (cw ")~%"))))
       (- (cw "(Simplifying assumptions...~%"))
       ((mv assumption-simp-start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (32-bitp (member-eq executable-type *executable-types32*))
       (debug-rules (if 32-bitp (debug-rules32) (debug-rules64)))
       (rules-to-monitor (maybe-add-debug-rules debug-rules monitor))
       ;; Next, we simplify the assumptions.  This allows us to state the
       ;; theorem about a lifted routine concisely, using an assumption
       ;; function that opens to a large conjunction before lifting is
       ;; attempted.  We need to assume some assumptions when simplifying the
       ;; others, because opening things like read64 involves testing
       ;; canonical-addressp (which we know from other assumptions is true):
       (assumption-rules (append extra-assumption-rules
                                 (reader-and-writer-intro-rules)
                                 (assumption-simplification-rules)
                                 (if 32-bitp
                                     nil ; todo: why not use (lifter-rules32-new)?
                                   ;; needed to match the normal forms used during lifting:
                                   (lifter-rules64-new))))
       ((mv erp assumption-rule-alist)
        (acl2::make-rule-alist assumption-rules (w state)))
       ((when erp) (mv erp nil nil nil nil state))
       ;; TODO: Option to turn this off, or to do just one pass:
       ((mv erp
            assumptions
            state)
        (acl2::simplify-terms-repeatedly
         assumptions
         assumption-rule-alist
         rules-to-monitor ; do we want to monitor here?  What if some rules are not incldued?
         nil ; don't memoize (avoids time spent making empty-memoizations)
         t ; todo: warn just once
         state))
       ((when erp) (mv erp nil nil nil nil state))
       (assumptions (acl2::get-conjuncts-of-terms2 assumptions))
       ((mv assumption-simp-elapsed state) (acl2::real-time-since assumption-simp-start-real-time state))
       (- (cw " (Simplifying assumptions took ") ; usually <= .01 seconds
          (acl2::print-to-hundredths assumption-simp-elapsed)
          (cw "s.)~%"))
       (- (cw " Done simplifying assumptions)~%"))
       (- (and print (progn$ (cw "(Simplified assumptions:~%")
                             (if (acl2::print-level-at-least-tp print)
                                 (acl2::print-list assumptions)
                               (print-terms-elided assumptions '(program-at ; the program can be huge
                                                                )))
                             (cw ")~%"))))
       ;; Prepare for symbolic execution:
       (term-to-simulate '(run-until-return x86))
       (term-to-simulate (wrap-in-output-extractor output term-to-simulate)) ;TODO: delay this if lifting a loop?
       (- (cw "(Limiting the unrolling to ~x0 steps.)~%" step-limit))
       ;; Convert the term into a dag for passing to repeatedly-run:
       ;; TODO: Just call simplify-term here?
       ((mv erp dag-to-simulate) (dagify-term term-to-simulate))
       ((when erp) (mv erp nil nil nil nil state))
       ;; Choose the lifter rules to use:
       (lifter-rules (if 32-bitp (lifter-rules32-all) (lifter-rules64-all)))
       ;; Add any extra-rules:
       (lifter-rules (append extra-rules lifter-rules)) ; todo: use union?
       ;; Remove any remove-rules:
       (- (let ((non-existent-remove-rules (set-difference-eq remove-rules lifter-rules)))
            (and non-existent-remove-rules
                 (cw "WARNING: The following rules in :remove-rules were not present: ~X01.~%" non-existent-remove-rules nil))))
       (lifter-rules (set-difference-eq lifter-rules remove-rules))
       ((mv erp lifter-rule-alist)
        (acl2::make-rule-alist lifter-rules (w state))) ; todo: allow passing in the rule-alist (and don't recompute for each lifted function)
       ((when erp) (mv erp nil nil nil nil state))
       ;; Do the symbolic execution:
       ((mv erp result-dag-or-quotep state)
        (repeatedly-run step-limit step-increment dag-to-simulate lifter-rule-alist assumptions rules-to-monitor use-internal-contextsp prune print print-base untranslatep memoizep rewriter 0 state))
       ((when erp) (mv erp nil nil nil nil state))
       (state (acl2::unwiden-margins state))
       ((mv elapsed state) (acl2::real-time-since start-real-time state))
       (- (cw " (Lifting took ")
          (acl2::print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
          (cw "s.)~%"))
       (- (if (quotep result-dag-or-quotep)
              (cw " Lifting produced the constant ~x0.)~%" result-dag-or-quotep) ; matches (Lifting...
            (progn$ (cw " Lifting produced a dag:~%")
                    (acl2::print-dag-info result-dag-or-quotep 'result t)
                    (cw ")~%") ; matches (Lifting...
                    ))))
    (mv (erp-nil) result-dag-or-quotep assumptions-to-return lifter-rules assumption-rules state)))

;; Returns (mv erp event state)
(defun def-unrolled-fn (lifted-name
                        target
                        executable
                        extra-assumptions
                        suppress-assumptions
                        stack-slots
                        position-independent
                        inputs
                        output
                        use-internal-contextsp
                        prune
                        extra-rules
                        remove-rules
                        extra-assumption-rules
                        step-limit
                        step-increment
                        memoizep
                        monitor
                        print
                        print-base
                        untranslatep
                        rewriter
                        produce-function
                        non-executable
                        produce-theorem
                        prove-theorem ;whether to try to prove the theorem with ACL2 (rarely works)
                        restrict-theory
                        whole-form
                        state)
  (declare (xargs :guard (and (symbolp lifted-name)
                              (lifter-targetp target)
                              ;; executable
                              ;; extra-assumptions ; untranslated-terms
                              (booleanp suppress-assumptions)
                              (natp stack-slots)
                              (member-eq position-independent '(t nil :auto))
                              (or (eq :skip inputs) (names-and-typesp inputs))
                              (output-indicatorp output)
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune)
                                  (eq t prune)
                                  (natp prune))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp extra-assumption-rules)
                              (natp step-limit)
                              (acl2::step-incrementp step-increment)
                              (booleanp memoizep)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (member-eq rewriter '(:x86 :legacy))
                              (booleanp produce-function)
                              (member-eq non-executable '(t nil :auto))
                              (booleanp produce-theorem)
                              (booleanp prove-theorem)
                              (booleanp restrict-theory))
                  :stobjs (state)
                  :mode :program))
  (b* (;; Check whether this call to the lifter has already been made:
       (previous-result (previous-lifter-result whole-form state))
       ((when previous-result)
        (mv nil '(value-triple :redundant) state))
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       ((mv erp parsed-executable state)
        (if (stringp executable)
            ;; it's a filename, so parse the file:
            (acl2::parse-executable executable state)
          ;; it's already a parsed-executable:
          (mv nil executable state)))
       ((when erp)
        (er hard? 'def-unrolled-fn "Error parsing executable: ~s0." executable)
        (mv t nil state))
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
       ;; Lift the function to obtain the DAG:
       ((mv erp result-dag assumptions lifter-rules-used assumption-rules-used state)
        (unroll-x86-code-core target parsed-executable
          extra-assumptions suppress-assumptions stack-slots position-independentp
          inputs output use-internal-contextsp prune extra-rules remove-rules extra-assumption-rules
          step-limit step-increment memoizep monitor print print-base untranslatep rewriter state))
       ((when erp) (mv erp nil state))
       ;; TODO: Fully handle a quotep result here:
       (result-dag-size (acl2::dag-or-quotep-size result-dag))
       (result-dag-fns (acl2::dag-fns result-dag))
       ;; Sometimes the presence of text-offset may indicate that something
       ;; wasn't resolved, but other times it's just needed to express some
       ;; junk left on the stack
       (result-dag-vars (acl2::dag-vars result-dag))
       (defconst-name (pack-in-package-of-symbol lifted-name '* lifted-name '*))
       (defconst-form `(defconst ,defconst-name ',result-dag))
       (fn-formals result-dag-vars) ; we could include x86 here, even if the dag is a constant
       (64-bitp (member-equal executable-type '(:mach-o-64 :pe-64 :elf-64)))
       ;; Now sort the formals:
       (param-names (if (and 64-bitp
                             (not (equal :skip inputs)))
                        ;; The user gave names to the params, and those vars will be put in for the registers:
                        (strip-cars inputs) ; fixme: handle array and pointer values (just look at the dag vars?)
                      ;; The register names may be being introduced (todo: deprecate this?):
                      '(rdi rsi rdx rcx r8 r9))) ; todo: handle 32-bit calling convention
       (common-formals (append param-names '(x86))) ; todo: handle 32-bit calling convention
       ;; these will be ordered like common-formals:
       (expected-formals (intersection-eq common-formals fn-formals))
       (unexpected-formals (acl2::merge-sort-symbol< (set-difference-eq fn-formals common-formals))) ; todo: warn if inputs given?  maybe x86 will sometimes be needed?
       (fn-formals (append expected-formals unexpected-formals))
       ;; Do we want a check like this?
       ;; ((when (not (subsetp-eq result-vars '(x86 text-offset))))
       ;;  (mv t (er hard 'lifter "Unexpected vars, ~x0, in result DAG!" (set-difference-eq result-vars '(x86 text-offset))) state))
       ;; TODO: Maybe move some of this to the -core function:
       ((when (intersection-eq result-dag-fns '(run-until-stack-shorter-than run-until-return)))
        (if (< result-dag-size 100000) ; todo: make customizable
            (progn$ (cw "(Term:~%")
                    (cw "~X01" (let ((term (dag-to-term result-dag)))
                                 (if untranslatep
                                     (untranslate term nil (w state))
                                   term))
                        nil)
                    (cw ")~%"))
          (progn$ (cw "(DAG:~%")
                  (cw "~X01" result-dag nil)
                  (cw ")~%")))
        (mv t (er hard 'lifter "Lifter error: The run did not finish.") state))
       ;; Not valid if (not (< result-dag-size 10000)):
       (maybe-result-term (and (< result-dag-size 10000) ; avoids exploding
                               (acl2::dag-to-term result-dag)))
       ;; Print the result:
       (- (and print
               (if (< result-dag-size 10000)
                   (cw "(Result: ~x0)~%" maybe-result-term)
                 (progn$ (cw "(Result:~%")
                         (cw "~X01" result-dag nil)
                         (cw ")~%")))))
       ;; Possibly produce a defun:
       ((mv erp defuns) ; defuns is nil or a singleton list
        (if (not produce-function)
            (mv (erp-nil) nil)
          (b* (;;TODO: consider untranslating this, or otherwise cleaning it up:
               (function-body (if (< result-dag-size 1000)
                                  maybe-result-term
                                `(acl2::dag-val-with-axe-evaluator ',result-dag
                                                                   ,(acl2::make-acons-nest result-dag-vars)
                                                                   ',(acl2::make-interpreted-function-alist (acl2::get-non-built-in-supporting-fns-list result-dag-fns (w state)) (w state))
                                                                   '0 ;array depth (not very important)
                                                                   )))
               (function-body-untranslated (if untranslatep (untranslate function-body nil (w state)) function-body)) ;todo: is this unsound (e.g., because of user changes in how untranslate works)?
               (function-body-retranslated (acl2::translate-term function-body-untranslated 'def-unrolled-fn (w state)))
               ;; TODO: I've seen this check fail when (if x y t) got turned into (if (not x) (not x) y):
               ((when (not (equal function-body function-body-retranslated))) ;todo: make a safe-untranslate that does this check?
                (er hard? 'lifter "Problem with function body.  Untranslating and then re-translating did not give original body.  Body was ~X01" function-body nil)
                (mv :problem-with-function-body nil))
               ;;(- (cw "Runes used: ~x0" runes)) ;TODO: Have Axe return these?
               ;;use defun-nx by default because stobj updates are not all let-bound to x86
               (non-executable (if (eq :auto non-executable)
                                   (if (member-eq 'x86 fn-formals) ; there may be writes to the stobj (perhaps with unresolved reads around them), so we use defun-nx (todo: do a more precise check)
                                       ;; (eq :all output) ; we use defun-nx since there is almost certainly a stobj update (and updates are not properly let-bound)
                                       t
                                     nil)
                                 non-executable))
               (defun-variant (if non-executable 'defun-nx 'defun))
               (defun `(,defun-variant ,lifted-name (,@fn-formals)
                         (declare (xargs ,@(if (member-eq 'x86 fn-formals)
                                               `(:stobjs x86)
                                             nil)
                                         :verify-guards nil ;TODO
                                         )
                                  ,@(let ((ignored-vars (set-difference-eq fn-formals result-dag-vars)))
                                      (and ignored-vars
                                           `((ignore ,@ignored-vars)))))
                         ,function-body-untranslated)))
            (mv (erp-nil) (list defun)))))
       ((when erp) (mv erp nil state))
       (produce-theorem (and produce-theorem
                             (if (not produce-function)
                                 ;; todo: do something better in this case?
                                 (prog2$ (cw "NOTE: Suppressing theorem because :produce-function is nil.~%")
                                         nil)
                               t)))
       (defthms ; either nil or a singleton list
         (and produce-theorem
              (let* ((defthm `(defthm ,(acl2::pack$ lifted-name '-correct)
                                (implies (and ,@assumptions)
                                         (equal (run-until-return x86)
                                                (,lifted-name ,@fn-formals)))
                                :hints ,(if restrict-theory
                                            `(("Goal" :in-theory '(,lifted-name ;,@runes ;without the runes here, this won't work
                                                                   )))
                                          `(("Goal" :in-theory (enable ,@lifter-rules-used
                                                                       ,@assumption-rules-used))))
                                :otf-flg t))
                     (defthm (if prove-theorem
                                 defthm
                               `(skip-proofs ,defthm))))
                (list defthm))))
       (events (cons defconst-form (append defuns defthms)))
       (event-names (acl2::strip-cadrs events))
       (event `(progn ,@events))
       (event (acl2::extend-progn event `(table x86-lifter-table ',whole-form ',event)))
       (event (acl2::extend-progn event `(value-triple '(,@event-names))))
       ((mv elapsed state) (acl2::real-time-since start-real-time state))
       (- (cw " (Unrolling ~x0 took " lifted-name)
          (acl2::print-to-hundredths elapsed)
          (cw "s, not including event submission.)~%")))
    (mv nil event state)))

;TODO: Add show- variant
;bad name?
;; TODO: :print nil is not fully respected
;; Creates some events to represent the unrolled computation, including a defconst for the DAG and perhaps a defun and a theorem.
(acl2::defmacrodoc def-unrolled (&whole whole-form
                                  lifted-name
                                  executable
                                  &key
                                  (target ':entry-point)
                                  (extra-assumptions 'nil)
                                  (suppress-assumptions 'nil)
                                  (stack-slots '100)
                                  (position-independent ':auto)
                                  (inputs ':skip)
                                  (output ':all)
                                  (use-internal-contextsp 't)
                                  (prune '1000)
                                  (extra-rules 'nil)
                                  (remove-rules 'nil)
                                  (extra-assumption-rules 'nil)
                                  (step-limit '1000000)
                                  (step-increment '100)
                                  (memoizep 't)
                                  (monitor 'nil)
                                  (print ':brief)             ;how much to print
                                  (print-base '10)
                                  (untranslatep 't)
                                  (rewriter ':x86)
                                  (produce-function 't)
                                  (non-executable ':auto)
                                  (produce-theorem 'nil)
                                  (prove-theorem 'nil)
                                  (restrict-theory 't)       ;todo: deprecate
                                  )
  `(,(if (acl2::print-level-at-least-tp print) 'make-event 'acl2::make-event-quiet)
    (def-unrolled-fn
      ',lifted-name
      ,target
      ,executable ; gets evaluated
      ,extra-assumptions
      ',suppress-assumptions
      ',stack-slots
      ',position-independent
      ',inputs
      ',output
      ',use-internal-contextsp
      ',prune
      ,extra-rules ; gets evaluated since not quoted
      ,remove-rules ; gets evaluated since not quoted
      ,extra-assumption-rules ; gets evaluated since not quoted
      ',step-limit
      ',step-increment
      ',memoizep
      ,monitor ; gets evaluated since not quoted
      ',print
      ',print-base
      ',untranslatep
      ',rewriter
      ',produce-function
      ',non-executable
      ',produce-theorem
      ',prove-theorem
      ',restrict-theory
      ',whole-form
      state))
  :parents (lifters)
  :short "Lift an x86 binary function to create a DAG, unrolling loops as needed."
  :args ((lifted-name "The name to use for the generated function and constant (the latter surrounded by stars).")
         (executable "The x86 binary executable that contains the target function.  Usually a string (a filename), or this can be a parsed executable of the form created by defconst-x86.")
         (target "Where to start lifting (a numeric offset, the name of a subroutine (a string), or the symbol :entry-point)")
         (extra-assumptions "Extra assumptions for lifting, in addition to the standard-assumptions")
         (suppress-assumptions "Whether to suppress the standard assumptions.")
         (stack-slots "How much available stack space to assume exists.") ; 4 or 8 bytes each?
         (position-independent "Whether to attempt the lifting without assuming that the binary is loaded at a particular position.")
         (inputs "Either the special value :skip (meaning generate no additional assumptions on the input) or a doublet list pairing input names with types.  Types include things like u32, u32*, and u32[2].")
         (output "An indication of which state component(s) will hold the result of the computation being lifted.  See output-indicatorp.")
         (use-internal-contextsp "Whether to use contextual information from ovararching conditionals when simplifying DAG nodes.")
         ;; todo: better name?  only for precise pruning:
         (prune "Whether to prune DAGs using precise contexts.  Either t or nil or a natural number representing an (exclusive) limit on the maximum size of the DAG if represented as a term.  This kind of pruning can blow up if attempted for DAGs that represent huge terms.")
         ;; todo: how do these affect assumption simp:
         (extra-rules "Rules to use in addition to (lifter-rules32-all) or (lifter-rules64-all).")
         (remove-rules "Rules to turn off.")
         (extra-assumption-rules "Extra rules to be used when simplifying assumptions.")
         (step-limit "Limit on the total number of model steps (instruction executions) to allow.")
         (step-increment "Number of model steps to allow before pausing to simplify the DAG and remove unused nodes.")
         (memoizep "Whether to memoize during rewriting (when not using contextual information -- as doing both would be unsound).")
         (monitor "Rule names (symbols) to be monitored when rewriting.") ; during assumptions too?
         (print "Verbosity level.") ; todo: values
         (print-base "Base to use when printing during lifting.  Must be either 10 or 16.")
         (untranslatep "Whether to untranslate term when printing.")
         (rewriter "Which rewriter to use, either :x86 (preferred) or :legacy.")
         (produce-function "Whether to produce a function, not just a constant DAG, representing the result of the lifting.")
         (non-executable "Whether to make the generated function non-executable, e.g., because stobj updates are not properly let-bound.  Either t or nil or :auto.")
         (produce-theorem "Whether to try to produce a theorem (possibly skip-proofed) about the result of the lifting.")
         (prove-theorem "Whether to try to prove the theorem with ACL2 (rarely works, since Axe's Rewriter is different and more scalable than ACL2's rewriter).")
         (restrict-theory "To be deprecated..."))
  :description ("Given an ax86 binary function, extract an equivalent term in DAG form, by symbolic execution including inlining all functions and unrolling all loops."
                "This event creates a @(see defconst) whose name is derived from the @('lifted-name') argument."
                "To inspect the resulting DAG, you can simply enter its name at the prompt to print it."))
