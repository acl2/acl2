; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "input-processing")
(include-book "table")
(include-book "generation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 atc

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('targets') is the list @('(t1 ... tp)') of inputs to @(tsee atc),
   or a suffix of it."

  "@('target') is an element in @('targets')."

  "@('target-fns') is the sublist of @('targets')
   consisting of all the functions, in the same order;
   or it is a suffix of this list of target functions."

  "@('fn') is one of the function symbols in @('targets')."

  "@('inscope') is a list of alists from ACL2 variable symbols to C types.
   These are the variables in scope
   for the ACL2 term whose code is being generated,
   organized in nested scopes from innermost to outermost.
   This is like a symbol table for ACL2's representation of the C code."

  "@('prec-fns') is an alist from ACL2 function symbols to function information.
   The function symbols are the ones in @('targets') that precede,
   in the latter list,
   the target in @('targets') for which C code is being generated."

  "@('prec-tags') is an alist
   from ACL2 @(tsee defstruct) symbols to their associated information.
   The @(tsee defstruct) symbols are the ones in @('targets') that precede,
   in the latter list,
   the target in @('targets') for which C code is being generated.
   The @('prec-tags') alist is always a subset of the "
  (xdoc::seetopic "defstruct-table-definition" "@(tsee defstruct) table")
  " that is constructed by @(tsee defstruct) calls
   and that is part of the ACL2 world prior to calling ATC:
   the @('prec-tags') is initially empty,
   gets extended as targets that are @(tsee defstruct) names are processed,
   and eventually contains all the @(tsee defstruct) table information
   for the @(tsee defstruct) targets passed to ATC.
   The reason for using the @('prec-tags') alist this way,
   instead of using the @(tsee defstruct) table directly,
   is so that we can ensure that all the targets are supplied to ATC,
   and in the right order;
   furthermore, it makes it easier and more efficient
   to retrieve information about all the target @(tsee defstruct)s of interest."

  (xdoc::evmac-topic-implementation-item-input "output-file")

  (xdoc::evmac-topic-implementation-item-input "proofs")

  (xdoc::evmac-topic-implementation-item-input "const-name")

  (xdoc::evmac-topic-implementation-item-input "print")

  xdoc::*evmac-topic-implementation-item-call*

  "@('fn-appconds') is an alist
   from the recursive functions among @('t'), ..., @('tp')
   to the names (keywords) of the corresponding applicability conditions."

  "@('prog-const') is the symbol specified by @('const-name').
   This is @('nil') if @('proofs') is @('nil')."

  "@('wf-thm') is the name of the generated program well-formedness theorem.
   This is @('nil') if @('proofs') is @('nil')."

  "@('fn-thms') is an alist from @('t1'), ..., @('tp')
   to the names of the generated respective correctness theorems.
   This is @('nil') if @('proofs') is @('nil')."

  "@('typed-formals') is an alist
   from the formal parameters of one of the functions in @('t1'), ..., @('tp')
   to their C types.
   The keys are unique and in the same order as the formal parameters."

  "@('affect') is a list of symbols consisting of
   the variables of array or structure type affected by
   one of the functions in @('t1'), ..., @('tp')."

  xdoc::*evmac-topic-implementation-item-names-to-avoid*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-fn ((args true-listp) (call pseudo-event-formp) (ctx ctxp) state)
  :returns (mv erp (event "A @('pseudo-event-formp').") state)
  :mode :program
  :parents (atc-implementation)
  :short "Process the inputs and
          generate the events and code."
  (b* (((when (atc-table-lookup call (w state)))
        (acl2::value '(value-triple :redundant)))
       ((er (list t1...tp
                  output-file
                  pretty-printing
                  proofs
                  prog-const
                  wf-thm
                  fn-thms
                  print))
        (atc-process-inputs args ctx state)))
    (atc-gen-everything t1...tp
                        output-file
                        pretty-printing
                        proofs
                        prog-const
                        wf-thm
                        fn-thms
                        print
                        call
                        ctx
                        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-macro-definition
  :parents (atc-implementation)
  :short "Definition of the @(tsee atc) macro."
  (defmacro atc (&whole call &rest args)
    (b* ((print-etc (member-eq :print args))
         (print-nil-p (and (consp print-etc)
                           (consp (cdr print-etc))
                           (eq (cadr print-etc) nil))))
      `(make-event-terse (atc-fn ',args ',call 'atc state)
                         :suppress-errors ,print-nil-p))))
