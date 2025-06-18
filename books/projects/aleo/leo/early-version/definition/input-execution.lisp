; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "input-files")
(include-book "value-expressions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-execution
  :parents (dynamic-semantics)
  :short "Execution of input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executing an input file amounts to
     evaluating its items to obtain inputs for the main function.
     We formalize this defensively,
     as for other aspects of the Leo dynamic semantics,
     i.e. we also check that the values and sorts match
     the types and sorts of the main parameters."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod funarg
  :short "Fixtype of function arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function argument consists of
     a name, a sort, and a value.
     It is the dynamic counterpart of
     a function parameter (see @(tsee funparam)."))
  ((name identifier)
   (sort var/const-sort)
   (value value))
  :tag :funarg
  :pred funargp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist funarg-list
  :short "Fixtype of lists of function arguments."
  :elt-type funarg
  :true-listp t
  :elementp-of-nil nil
  :pred funarg-listp
  ///

  (defrule funarg-listp-of-remove1-equal
    (implies (funarg-listp args)
             (funarg-listp (remove1-equal arg args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption funarg-option
  funarg
  :short "Fixtype of optional function arguments."
  :pred funarg-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funarg-result
  :short "Fixtype of errors and function arguments."
  :ok funarg
  :pred funarg-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funarg-list-result
  :short "Fixtype of errors and listf of function arguments."
  :ok funarg-list
  :pred funarg-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-input-item ((initem input-itemp)
                         (intitle input-titlep)
                         (curve curvep))
  :returns (funarg funarg-resultp)
  :short "Evaluate an input item."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate the input item to a function argument,
     which has the same name as the input item,
     whose sort is determined by the input title under which the item appears,
     and whose value is obtained by evaluating the input expression."))
  (b* (((input-item initem) initem)
       (expr (input-expression->get initem.value))
       ((unless (expression-valuep expr))
        (reserrf (list :not-value-expression expr)))
       ((okf val) (value-expr-to-value expr curve)))
    (make-funarg :name initem.name
                 :sort (input-title->sort intitle)
                 :value val))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-input-item-list ((initems input-item-listp)
                              (intitle input-titlep)
                              (curve curvep))
  :returns (funargs funarg-list-resultp)
  :short "Evaluate a list of input items."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate them one after the other,
     returning a corresponding list of function arguments.
     We stop as soon as there is an error."))
  (b* (((when (endp initems)) nil)
       ((okf funarg) (eval-input-item (car initems) intitle curve))
       ((okf funargs) (eval-input-item-list (cdr initems) intitle curve)))
    (cons funarg funargs))
  :prepwork
  ((local
    (in-theory
     (enable funargp-when-funarg-resultp-and-not-reserrp
             funarg-listp-when-funarg-list-resultp-and-not-reserrp))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-input-section ((insec input-sectionp) (curve curvep))
  :returns (funargs funarg-list-resultp)
  :short "Evaluate an input section."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate its items,
     using the input title as the sort."))
  (eval-input-item-list (input-section->items insec)
                        (input-section->title insec)
                        curve)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-input-section-list ((insecs input-section-listp) (curve curvep))
  :returns (funargs funarg-list-resultp)
  :short "Evaluate a list of input sections."
  :long
  (xdoc::topstring
   (xdoc::p
    "We evaluate them one after the other,
     concatenating the resulting function arguments."))
  (b* (((when (endp insecs)) nil)
       ((okf funargs) (eval-input-section (car insecs) curve))
       ((okf more-funargs) (eval-input-section-list (cdr insecs) curve)))
    (append funargs more-funargs))
  :prepwork
  ((local
    (in-theory
     (enable funargp-when-funarg-resultp-and-not-reserrp
             funarg-listp-when-funarg-list-resultp-and-not-reserrp))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-input-file ((infile input-filep) (curve curvep))
  :returns (funargs funarg-list-resultp)
  :short "Evaluate an input file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This reduces to evaluating the input sections."))
  (eval-input-section-list (input-file->sections infile) curve)
  :hooks (:fix))
