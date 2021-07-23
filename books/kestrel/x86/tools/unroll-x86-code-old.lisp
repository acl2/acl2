; An unrolling lifter xfor x86 code (not based on Axe)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book includes a tool, def-lifted-x86, which can be used to unroll x86
;; programs using the ACL2 rewriter.  Note that this is much slower than using
;; Axe, as is done by the similar tool in unroll-x86-code.lisp, which we use
;; much more than the tool in this book.  But the tool in this book perhaps has
;; higher assurance.

;; Two approaches: 1. Use X86 as the only variable and get back a term
;; over the single variable X86 that captures the effect of the code.
;; 2. Introduce variables such as X and Y for the inputs and get back
;; a term over x86 and those variables.  This may make it easier to
;; state assumptions (since they can mention X and Y).  We use the
;; second approach here for now.

;; See also lifter-axe.lisp, for the Axe-based version of this lifter (which is
;; what we mostly use).

(include-book "support")
(include-book "lifter-support")
(include-book "assumptions")
(include-book "symsim")
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/utilities/runes" :dir :system)
(include-book "kestrel/axe/util2" :dir :system) ;for make-cons-nest
(include-book "kestrel/x86/parsers/parsed-executable-tools" :dir :system)

;todo: factor some of this stuff out into a lifter-common file

;; An attachable function that always returns nil.
(defun nil2 (x y) (declare (xargs :guard t) (ignore x y)) nil)

(defconst *standard-lifter-enables*
  '(run-until-return))

;; Returns (mv erp nil state)
(defun def-lifted-x86-fn (lifted-name
                          subroutine-name
                          parsed-executable
                          stack-slots-needed
                          enables
                          whole-form
                          prove-theorem
                          output
                          assumptions ;TODO: Translate these
                          non-executable
                          restrict-theory
                          state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp lifted-name)
                              (stringp subroutine-name)
                              (natp stack-slots-needed)
                              (output-indicatorp output)
                              (booleanp non-executable))
                  :mode :program))
  (b* ( ;; Check whether this call to the lifter has already been made:
       (previous-result (previous-lifter-result whole-form state))
       ((when previous-result)
        (mv nil '(value-triple :redundant) state))
       (executable-type (acl2::parsed-executable-type parsed-executable))
       ;; assumptions (these get simplified and so don't have to be in normal form):
       (assumptions (if (eq :mach-o-64 executable-type)
                        (cons `(standard-assumptions-mach-o-64 ',subroutine-name
                                                             ',parsed-executable
                                                             ',stack-slots-needed
                                                             text-offset
                                                             x86)
                              assumptions)
                      ;; TODO: Support :pe-32
                      (if (eq :pe-64 executable-type)
                          (cons `(standard-assumptions-pe-64 ',subroutine-name
                                                           ',parsed-executable
                                                           ',stack-slots-needed
                                                           text-offset
                                                           x86)
                                assumptions)
                        assumptions)))
       (- (cw "Assumptions: ~x0.~%" assumptions))
       ;; Force the expander not to give up prematurely:
       ((mv & & state)
        ;; can't actually call defattach here for common lisp reasons:
        (acl2::defattach-fn '((acl2::too-many-ifs-pre-rewrite nil2)
                              :system-ok t)
                            state
                            '(defattach (acl2::too-many-ifs-pre-rewrite nil2)
                               :system-ok t)))
       ((mv & & state)
        (acl2::defattach-fn '((acl2::too-many-ifs-post-rewrite nil2)
                              :system-ok t)
                            state
                            '(defattach (acl2::too-many-ifs-post-rewrite nil2)
                               :system-ok t)))
       ;; Do the symbolic simulation:
       (enables (append enables *standard-lifter-enables*))
       (term-to-simulate '(run-until-return x86))
       (term-to-simulate (wrap-in-output-extractor output term-to-simulate))
       ((mv result runes state)
        (symsim$-fn term-to-simulate
                    assumptions
                    enables
                    state))
       (- (cw "Result: ~x0" result))
       (- (cw "Runes used: ~x0" runes))
       (runes (acl2::drop-fake-runes runes))
       ((when (member-eq 'run-until-rsp-greater-than (acl2::all-ffn-symbs result nil)))
        (mv t (er hard 'lifter "Lifter error: The run did not finish.") state))
       (vars (acl2::all-vars result))
       ;;use defun-nx by default because stobj updates are not all let-bound to x86
       (defun-variant (if non-executable 'defun-nx 'defun))
       (event `(progn (,defun-variant ,lifted-name (,@vars)
                        (declare (xargs ,@(if (member-eq 'x86 vars)
                                              `(:stobjs x86)
                                            nil)
                                        :verify-guards nil ;TODO
                                        ))
                        ,result)
                      ,@(and prove-theorem
                             `((defthm ,(acl2::pack$ lifted-name '-correct)
                                 (implies (and ,@assumptions)
                                          (equal (run-until-return x86)
                                                 (,lifted-name x86)))
                                 :hints ,(if restrict-theory
                                             `(("Goal" :in-theory '(,lifted-name ,@runes)))
                                           `(("Goal" :in-theory (enable ,@enables))))
                                 :otf-flg t)))))
       (event (acl2::extend-progn event `(table x86-lifter-table ',whole-form ',event))))
    (mv nil event state)))

;TODO: Add show variant
(defmacro def-lifted-x86 (&whole whole-form
                                 lifted-name ;name to use for the generated function
                                 subroutine-name ;this assumes there is a symbol table!
                                 parsed-executable
                                 stack-slots-needed
                                 &key
                                 (enable 'nil)
                                 (prove-theorem 't)
                                 (output ':all)
                                 (assumptions 'nil) ;extra assumptions in addition to the standard assumptions
                                 (non-executable 't) ;allow :auto?
                                 (restrict-theory 't) ;try to prove the theorem using only the rules reported as being used by the expander tool
                                 )
  `(make-event (def-lifted-x86-fn
                 ',lifted-name
                 ,subroutine-name
                 ,parsed-executable
                 ',stack-slots-needed
                 ',enable
                 ',whole-form
                 ',prove-theorem
                 ',output
                 ,assumptions
                 ',non-executable
                 ',restrict-theory
                 state)))

;needed after some x86 model changes:
(in-theory (enable acl2::bvplus-recollapse))

(defthm bvchop-of-if
  (equal (bvchop n (if test tp ep))
         (if test
             (bvchop n tp)
           (bvchop n ep))))

(in-theory (enable x86isa::rflagsbits->ac$inline-constant-opener
                   x86isa::rflagsbits->af$inline-constant-opener
                   x86isa::rflagsbits->cf$inline-constant-opener
                   x86isa::rflagsbits->of$inline-constant-opener
                   x86isa::rflagsbits->pf$inline-constant-opener
                   x86isa::rflagsbits->sf$inline-constant-opener
                   x86isa::rflagsbits->zf$inline-constant-opener

                   !rflags-of-!rflagsbits->af
                   !rflags-of-!rflagsbits->cf
                   !rflags-of-!rflagsbits->of
                   !rflags-of-!rflagsbits->pf
                   !rflags-of-!rflagsbits->sf
                   !rflags-of-!rflagsbits->zf

                   rflagsbits->cf$inline-of-xr
                   rflagsbits->pf$inline-of-xr
                   rflagsbits->af$inline-of-xr
                   rflagsbits->zf$inline-of-xr
                   rflagsbits->sf$inline-of-xr
                   rflagsbits->tf$inline-of-xr
                   rflagsbits->intf$inline-of-xr
                   rflagsbits->df$inline-of-xr
                   rflagsbits->of$inline-of-xr
                   rflagsbits->iopl$inline-of-xr
                   rflagsbits->nt$inline-of-xr
                   rflagsbits->rf$inline-of-xr
                   rflagsbits->vm$inline-of-xr
                   rflagsbits->ac$inline-of-xr
                   rflagsbits->vif$inline-of-xr
                   rflagsbits->vip$inline-of-xr
                   rflagsbits->id$inline-of-xr
                   ))
;; (in-theory (enable X86ISA::RFLAGSBITS-FIX$INLINE))
;; (in-theory (enable X86ISA::RFLAGSBITS->CF$INLINE))
;; (in-theory (enable X86ISA::RFLAGSBITS->PF$INLINE))
;; (in-theory (enable X86ISA::RFLAGSBITS->AF$INLINE))
;; (in-theory (enable X86ISA::RFLAGSBITS->ZF$INLINE))
;; (in-theory (enable X86ISA::RFLAGSBITS->SF$INLINE))
;; (in-theory (enable X86ISA::RFLAGSBITS->OF$INLINE))
;; (in-theory (enable X86ISA::RFLAGSBITS->AC$INLINE))

;; (in-theory (enable X86ISA::!RFLAGSBITS->CF$INLINE))
;; (in-theory (enable X86ISA::!RFLAGSBITS->PF$INLINE))
;; (in-theory (enable X86ISA::!RFLAGSBITS->AF$INLINE))
;; (in-theory (enable X86ISA::!RFLAGSBITS->ZF$INLINE))
;; (in-theory (enable X86ISA::!RFLAGSBITS->SF$INLINE))
;; (in-theory (enable X86ISA::!RFLAGSBITS->OF$INLINE))
;; (in-theory (enable X86ISA::!RFLAGSBITS->AC$INLINE))

(in-theory (disable x86isa::write-user-rflags$inline))

(in-theory (enable
            ;; TODO: Add other sizes?:
            x86isa::rml32
            x86isa::rml64))
