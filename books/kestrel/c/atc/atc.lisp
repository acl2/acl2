; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "input-processing")
(include-book "table")
(include-book "generation")

(local (include-book "kestrel/std/system/w" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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
   from ACL2 @(tsee defstruct) names to their associated information.
   The @(tsee defstruct)s are the ones in @('targets') that precede,
   in the latter list,
   the target in @('targets') for which C code is being generated.
   The @('prec-tags') alist is always a subset of the @(tsee defstruct) table
   that is constructed by @(tsee defstruct) calls
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

  "@('prec-objs') is an alist
   from ACL2 @(tsee defobject) names to their associated information.
   The @(tsee defobject)s are the ones in @('targets') that precede,
   in the latter list,
   the target in @('targets') for which C code is being generated.
   The @('prec-objs') alist is always a subset of the @(tsee defobject) table
   that is constructed by @(tsee defobject) calls
   and that is part of the ACL2 world prior to calling ATC:
   the @('prec-objs') is initially empty,
   gets extended as targets that are @(tsee defobject) names are processed,
   and eventually contains all the @(tsee defobject) table information
   for the @(tsee defobject) targets passed to ATC.
   The reason for using the @('prec-objs') alist this way,
   instead of using the @(tsee defobject) table directly,
   is so that we can ensure that all the targets are supplied to ATC,
   and in the right order;
   furthermore, it makes it easier and more efficient
   to retrieve information about all the target @(tsee defobject)s of interest."

  (xdoc::evmac-topic-implementation-item-input "output-dir")

  (xdoc::evmac-topic-implementation-item-input "file-name")

  "@('path-wo-ext') is the path of the generated file(s),
   without the @('.c') or @('.h') extension.
   This @('path-wo-ext') is obtained from @('output-dir') and @('file-name')."

  (xdoc::evmac-topic-implementation-item-input "header")

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

  "@('fn-guard') is the name of a locally generated function
   for the guard of @('fn')."

  "@('typed-formals') is an alist
   from the formal parameters of one of the functions in @('t1'), ..., @('tp')
   to their C types.
   The keys are unique and in the same order as the formal parameters."

  "@('var-term-alist') is an alist from variables to terms
   that keeps track of the current substitution context
   as terms are recursively processed.
   This alist collects the @(tsee let) and @(tsee mv-let) bindings
   encountered along the way.
   These are used to properly instantiate terms
   limits associated to function calls,
   because those limits apply to the functions' formals,
   which must therefore be replaced not just with the actuals of the call,
   but with those actuals with variables replaced with terms
   according to the bindings that lead to the call."

  "@('affect') is a list of symbols consisting of
   the variables of array or structure type affected by
   one of the functions in @('t1'), ..., @('tp').
   This @('affect') is denoted as @('vars') in the user documentation."

  "@('context') is the context in which theorems are generated
   for each generated piece of C code."

  "@('thm-index') is a positive integer
   that is threaded through the code generation functions
   to generate unique and readable local theorem names."

  "@('compst-var') is a symbol used as a variable for
   the computation state in generated theorems."

  "@('fenv-var') is a symbol used as a variable for
   the function environment in generated theorems."

  "@('limit-var') is a symbol used as a variable for
   the execution recursion limit in generated theorems."

  xdoc::*evmac-topic-implementation-item-names-to-avoid*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-inputs-and-gen-everything ((args true-listp)
                                               (call pseudo-event-formp)
                                               state)
  :returns (mv erp
               (event pseudo-event-formp)
               state)
  :parents (atc-implementation)
  :short "Process the inputs and generate the events and code."
  (b* (((reterr) '(_) state)
       ((when (atc-table-lookup call (w state)))
        (retok '(value-triple :redundant) state))
       ((erp targets
             file-name
             path-wo-ext
             header
             pretty-printing
             proofs
             prog-const
             wf-thm
             fn-thms
             & ; fn-limits
             & ; fn-body-limits
             print
             state)
        (atc-process-inputs args state))
       ((erp event)
        (atc-gen-everything targets
                            file-name
                            path-wo-ext
                            header
                            pretty-printing
                            proofs
                            prog-const
                            wf-thm
                            fn-thms
                            print
                            call
                            state)))
    (retok event state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-fn ((args true-listp) (call pseudo-event-formp) (ctx ctxp) state)
  :returns (mv erp
               (event pseudo-event-formp)
               state)
  :parents (atc-implementation)
  :short "Event expansion of @(tsee atc)."
  (b* (((mv erp event state)
        (atc-process-inputs-and-gen-everything args call state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (acl2::value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-macro-definition
  :parents (atc-implementation)
  :short "Definition of the @(tsee atc) macro."
  (defmacro atc (&whole call &rest args)
    `(make-event-terse (atc-fn ',args ',call 'atc state))))
