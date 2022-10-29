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

(include-book "../language/types")
(include-book "../language/abstract-syntax")

(include-book "clause-processors/pseudo-term-fty" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-function-tables
  :parents (atc-event-and-code-generation)
  :short "Tables of ACL2 functions, and operations on these tables."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod atc-fn-info
  :short "Fixtype of information associated to
          an ACL2 function translated to a C function or loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of:
     an optional C type that is present,
     and represents the function's output type,
     when the function is not recursive;
     a list of C types representing the function's input types;
     an optional (loop) statement that is present,
     and is represented by the function,
     when the function is recursive;
     a list of variables affected by the function;
     the name of the locally generated theorem about the function result(s);
     the name of the locally generated theorem that asserts
     that the execution of the function is functionally correct;
     the name of the locally generated theorem that asserts
     that the measure of the function (when recursive) yields a natural number
     (@('nil') if the function is not recursive);
     the name of the locally generated theorem that asserts
     that looking up the function in the function environment
     yields the information for the function
     (@('nil') if the function is recursive);
     and a limit that suffices to execute the code generated from the function,
     as explained below.
     The limit is a term that may depend on the function's parameters.
     For a non-recursive function,
     the term expresses a limit that suffices to execute @(tsee exec-fun)
     on the C function generated from the ACL2 function
     when the arguments of the C functions have values
     symbolically expressed by the ACL2 function's formal parameters.
     For a recursive function,
     the term expressed a limit that suffices to execute @(tsee exec-stmt-while)
     on the C loop generated from the ACL2 function
     when the variables read by the C loop have values
     symbolically expressed by the ACL2 function's formal parameters.
     If none of the target ACL2 functions are recursive,
     all the limit terms are quoted constants;
     if there are recursive functions,
     then those, and all their direct and indirect callers,
     have limit terms that in general depend on each function's parameters.
     All these limit terms are calculated
     when the C code is generated from the ACL2 functions.")
   (xdoc::p
    "Note that exactly one of the first two fields is @('nil').
     This is an invariant."))
  ((out-type type-option)
   (in-types type-list)
   (loop? stmt-option)
   (affect symbol-list)
   (result-thm symbol)
   (correct-thm symbol)
   (measure-nat-thm symbol)
   (fun-env-thm symbol)
   (limit pseudo-term))
  :pred atc-fn-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist atc-symbol-fninfo-alist
  :short "Fixtype of alists from symbols to function information."
  :key-type symbolp
  :val-type atc-fn-info
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  :pred atc-symbol-fninfo-alistp
  ///

  (defrule atc-fn-infop-of-cdr-of-assoc-equal
    (implies (and (atc-symbol-fninfo-alistp x)
                  (assoc-equal k x))
             (atc-fn-infop (cdr (assoc-equal k x)))))

  (defruled symbol-listp-of-strip-cars-when-atc-symbol-fninfo-alistp
    (implies (atc-symbol-fninfo-alistp prec-fns)
             (symbol-listp (strip-cars prec-fns)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-result-thms
  ((prec-fns atc-symbol-fninfo-alistp) (among symbol-listp))
  :returns (thms symbol-listp)
  :short "Project the result theorems
          out of a function information alist,
          for the functions among a given list."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof of each of these theorems for a function @('fn')
     makes use of the same theorems for
     some of the preceding functions in @('prec-fns'),
     more precisely the ones called in the body of @('fn').
     This function serves to collect those theorem names from the alist.
     The list of symbols given as input consists of
     the functions called by @('fn'):
     it is fine if the list contains functions that are not keys of the alist,
     as it is merely used to filter.")
   (xdoc::p
    "The alist has no duplicate keys.
     So this function is correct."))
  (cond ((endp prec-fns) nil)
        ((member-eq (caar prec-fns) among)
         (cons (atc-fn-info->result-thm (cdr (car prec-fns)))
               (atc-symbol-fninfo-alist-to-result-thms (cdr prec-fns) among)))
        (t (atc-symbol-fninfo-alist-to-result-thms (cdr prec-fns) among))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-correct-thms
  ((prec-fns atc-symbol-fninfo-alistp) (among symbol-listp))
  :returns (thms symbol-listp)
  :short "Project the execution correctness theorems
          out of a function information alist,
          for the functions among a given list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-symbol-fninfo-alist-to-result-thms).
     See that function's documentation for more details."))
  (cond ((endp prec-fns) nil)
        ((member-eq (caar prec-fns) among)
         (cons (atc-fn-info->correct-thm (cdr (car prec-fns)))
               (atc-symbol-fninfo-alist-to-correct-thms (cdr prec-fns)
                                                        among)))
        (t (atc-symbol-fninfo-alist-to-correct-thms (cdr prec-fns)
                                                    among))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-measure-nat-thms
  ((prec-fns atc-symbol-fninfo-alistp) (among symbol-listp))
  :returns (thms symbol-listp)
  :short "Project the measure theorems
          out of a function information alist,
          for the functions among a given list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-symbol-fninfo-alist-to-result-thms).
     See that function's documentation for more details.")
   (xdoc::p
    "We skip over non-recursive functions,
     which have @('nil') as that entry."))
  (cond ((endp prec-fns) nil)
        ((member-eq (caar prec-fns) among)
         (b* ((thm (atc-fn-info->measure-nat-thm (cdr (car prec-fns)))))
           (if thm
               (cons thm
                     (atc-symbol-fninfo-alist-to-measure-nat-thms (cdr prec-fns)
                                                                  among))
             (atc-symbol-fninfo-alist-to-measure-nat-thms (cdr prec-fns)
                                                          among))))
        (t (atc-symbol-fninfo-alist-to-measure-nat-thms (cdr prec-fns)
                                                        among))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-fun-env-thms
  ((prec-fns atc-symbol-fninfo-alistp) (among symbol-listp))
  :returns (thms symbol-listp)
  :short "Project the function environment theorems
          out of a function information alist,
          for the functions among a given list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-symbol-fninfo-alist-to-result-thms).
     See that function's documentation for more details.")
   (xdoc::p
    "We skip over recursive functions,
     which have @('nil') as that entry."))
  (cond ((endp prec-fns) nil)
        ((member-eq (caar prec-fns) among)
         (b* ((thm (atc-fn-info->fun-env-thm (cdr (car prec-fns)))))
           (if thm
               (cons thm
                     (atc-symbol-fninfo-alist-to-fun-env-thms (cdr prec-fns)
                                                              among))
             (atc-symbol-fninfo-alist-to-fun-env-thms (cdr prec-fns)
                                                      among))))
        (t (atc-symbol-fninfo-alist-to-fun-env-thms (cdr prec-fns)
                                                    among))))
