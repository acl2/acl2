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
(include-book "type-checking")
(include-book "value-expressions")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input-checking
  :parents (static-semantics)
  :short "Static checks on input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "These check static semantic requirements on Leo input files.
     The checks also calculate information from the input file
     that is used to check
     the combination of a Leo program and its input file.")
   (xdoc::p
    "The checking of an input file happens in the context of
     a static environment that is derived from the program."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-input-type ((intype input-typep) (env senvp))
  :returns (ok reserr-optionp)
  :short "Check an input type."
  (typecheck-type (input-type->get intype) env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-input-expression ((inexpr input-expressionp) (env senvp))
  :returns (type type-resultp)
  :short "Check an input expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression must be a value expression."))
  (b* ((expr (input-expression->get inexpr))
       ((unless (expression-valuep expr))
        (reserrf (list :not-value-expression expr)))
       ((okf etype) (typecheck-expression expr env)))
    (expr-type->type etype))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-input-item ((initem input-itemp)
                          (intitle input-titlep)
                          (params funparam-listp)
                          (env senvp))
  :returns (new-params funparam-list-resultp)
  :short "Check an input item."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that the type of the input expression
     matches the input type.")
   (xdoc::p
    "The @('params') input to this ACL2 function
     consists of (the information in) all the input items
     that precede this input item in the input file.
     We use them to check that the name of this item
     is different from all the previous ones,
     and we extend the list of function parameters
     with the information from this input item;
     we use the current input title to determine the variable or constant sort.
     This way, as we go through all the items of the input file,
     we ensure that they have distinct names
     and we create a list of function parameters corresponding to them.
     The reason for this list of function parameters is that
     the items in an input file correspond to
     the inputs of the main function of the Leo program,
     and so in this way we can check the consistency of
     the input file with the main function."))
  (b* (((input-item initem) initem)
       ((okf &) (check-input-type initem.type env))
       ((okf type) (check-input-expression initem.value env))
       (intype (input-type->get initem.type))
       ((unless (equal type intype))
        (reserrf (list :input-item-mistype
                   :type initem.type
                   :expression type)))
       ((when (member-equal initem.name
                            (funparam-list->name-list params)))
        (reserrf (list :duplicate-input-name initem.name))))
    (cons (make-funparam :name initem.name
                         :type intype
                         :sort (input-title->sort intitle))
          (funparam-list-fix params)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-input-items ((initems input-item-listp)
                           (intitle input-titlep)
                           (params funparam-listp)
                           (env senvp))
  :returns (new-params funparam-list-resultp)
  :short "Check a list of input items."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check each one of them, one after the other.
     These are all under the same input title."))
  (b* (((when (endp initems)) (funparam-list-fix params))
       ((okf params) (check-input-item (car initems) intitle params env)))
    (check-input-items (cdr initems) intitle params env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-input-section ((insec input-sectionp)
                             (params funparam-listp)
                             (env senvp))
  :returns (new-params funparam-list-resultp)
  :short "Check an input section."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check all the items, using the title of the section."))
  (check-input-items (input-section->items insec)
                     (input-section->title insec)
                     params
                     env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-input-section-list ((insecs input-section-listp)
                                  (params funparam-listp)
                                  (env senvp))
  :returns (new-params funparam-list-resultp)
  :short "Check a list of input sections."
  (b* (((when (endp insecs)) (funparam-list-fix params))
       ((okf params) (check-input-section (car insecs) params env)))
    (check-input-section-list (cdr insecs) params env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-input-file ((infile input-filep) (env senvp))
  :returns (params funparam-list-resultp)
  :short "Check an input file."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting with the empty list of function parameters,
     we go through the file and collect all the function parameters
     corresponding to the input items.
     We also ensure that the sections have all distinct titles,
     i.e. that there are no repeated section titles.
     It is not required for all possible section titles to be present."))
  (b* ((insecs (input-file->sections infile))
       ((okf params) (check-input-section-list insecs nil env))
       ((unless (no-duplicatesp-equal (input-section-list->title-list insecs)))
        (reserrf (list :duplicate-sections))))
    params)
  :hooks (:fix))
