; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macros for building defprod and deftagsum types.

;; These can generate function definitions for the invariant.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/alists/top" :dir :system)

(include-book "types")
(include-book "expressions") ; for translate-term
(include-book "functions") ; for s-fun-main

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We need to add invariants to product types.
;; This includes top-level product type definitions as well as product type
;; definitions within deftagsum.

;; See also xdoc fty::defprod, "Experimental Dependent Type Option".

;; If an invariant is specified in make-product-type,
;; there are two or three requirements.
;; 1. fty::defprod gets called with :require <expression>
;; 2. at least one of the fields needs :reqfix
;; 3? there must be a theorem that applying the regular fixing
;;    functions for the types of the fields, followed by the
;;    reqfix for all fields that have it specified,
;;    yields fields that satisfy the :require <expression>
;;    However, the doc is not clear on whether defprod generates
;;    that theorem automatically or not.

;; One of the purposes of the reqfix seems to be to make fields
;; that have the reqfix be dependent on required fields that do not,
;; so you can have a partial product value and
;; let the fixing function assign the missing fields to be
;; consistent with the required fields.

;; If this is not our use case, then we might just want to
;; have a specific tuple of values for all the fields that
;; satisfies the invariant, and then make :reqfix for each field
;; just return its value in that tuple.  This arrangement
;; would be analogous to how we use the base-value parameter
;; in make-subtype.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parsing the arguments to make-product-type

;; We allow mixed fields and keys/vals.

;; As well as the field+type doublets, and the optional :short and :long
;; keywords, this macro takes either none or all of the following keyword
;; arguments:
;;   :invariant <expr>
;;   :fixvals <list-of-values>
;; The invariant expression must mention all the field names as free variables.
;; The invariant expression must hold if the params are bound to the
;; <list-of-values>.


(define parse-mixed-lists-and-keyvals-aux ((list-items-so-far true-listp)
                                           (keys-and-vals-so-far alistp)
                                           (rest-of-list true-listp))
  :returns (mv (list-args true-listp) (keys-and-vals alistp))
  (let ((rest-of-list (list-fix rest-of-list))
        (list-items-so-far (list-fix list-items-so-far))
        (keys-and-vals-so-far (acl2::alist-fix keys-and-vals-so-far)))
  (if (endp rest-of-list)
      (mv (reverse list-items-so-far)
          (reverse keys-and-vals-so-far))
    (if (listp (car rest-of-list))
        (parse-mixed-lists-and-keyvals-aux (cons (car rest-of-list)
                                                 list-items-so-far)
                                           keys-and-vals-so-far
                                           (cdr rest-of-list))
      (if (or (not (symbolp (car rest-of-list)))
              (not (equal "KEYWORD" (symbol-package-name (car rest-of-list))))
              (endp (cdr rest-of-list)))
        (mv (er hard? 'top-level "keywords and values must come in pairs") nil)
        (parse-mixed-lists-and-keyvals-aux list-items-so-far
                                           (cons (cons (car rest-of-list)
                                                       (cadr rest-of-list))
                                                 keys-and-vals-so-far)
                                           (cddr rest-of-list)))))))

;; The arguments to make-product-type are either lists (field type)
;; or sequential pairs of keyword arg and value.
;; The canonical order could be:
;; (defxxx
;;   :short "something"
;;   :long "some thing"
;;   (field1 type1)
;;   (field2 type2)
;;   :invariant (related-p type1 type2)
;;   :fixvals (list val1 val2))

(define parse-mixed-lists-and-keyvals ((arglist true-listp))
  :returns (mv (list-args true-listp) (keys-and-vals alistp))
  (parse-mixed-lists-and-keyvals-aux nil nil arglist))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Construct reqfix functions

;; Construct the definitions that define the functions that are called after
;; the :reqfix field keyword.
;;
;; Note that currently we require that all the fields have fixing functions
;; and, if there is a defprod :require, all the fields will have reqfix functions.

;; Notes:
;; A product type field spec is
;;   ("fieldname" (s-type-constructor-form ..))
;; Let's say there N fields.
;; We turn those into N functions, each of which mentions all the fields
;; in its params (:inputs).
;;   (s-fun "reqfix-funname1" :inputs (("fieldname1" (s-type-form1 ..)) ..)
;;          :outputs (("return-name1" (s-type-boolean)))
;;          :body invariant)

;; We need a reqfix function for every field
;; (or none at all, but then this section of code is not used).
;; To construct a reqfix function, we need:
;; - the name of the product type
;; - the names and types of all the fields, to use as params
;;   Note that the format ("fieldname" (s-field-type-constructor ..))
;;   is the same for a product field spec and for a :input param.
;; - the invariant expression
;; - the name of the current field for which we are constructing a reqfix function
;; - the fixing value of the current field


;;; TODO: do we have any syntactic convention for auto-generated function
;;; and param names, like starting with some character not normally allowed?
;;; For now I prepend "$".
(defun reqfix-function-name (product-type-name field-name)
  (concatenate 'string "$" product-type-name "-FIX-" field-name))

(defun construct-reqfix-function (product-type-name fieldspecs invariant
                                                    this-fieldspec this-fixval)
  ;; Copied logic here from defmacro s-fun
  ;; Added "?" on input-types and output-types since those were used for
  ;; adding type definitions but these reqfix functions don't need any new type defs.
  ;; Also took out refine-types-given-assumes.
  (b* (((mv erp param-list let-fixing-list ?input-types &)
        (process-s-fun-inputs fieldspecs nil))
       ((when erp) (er hard? 'top-level "Bad :inputs to s-fun"))
;;       ((mv param-list let-fixing-list)
;;        (refine-types-given-assumes nil param-list let-fixing-list))
       ((mv erp returns-list ?output-fixer ?output-types &)
        (process-s-fun-outputs `((,(concatenate 'string "$RETURN-" (car this-fieldspec))
                                  ,(cadr this-fieldspec)))
                               nil))
       ((when erp) (er hard? 'top-level "Bad :outputs to s-fun")))
    ;; EM: I'm not fully convinced this make-event is needed.
    ;; It might be OK to retry the (s-fun ..) macro sometime.
    `(make-event (s-fun-main
                  ,(reqfix-function-name product-type-name (car this-fieldspec))
                  ',param-list
                  '(s-conditional
                    ,invariant
                    (s-var-ref ,(car this-fieldspec))
                    ,this-fixval)
                  ',let-fixing-list
                  ',returns-list
                  nil nil nil nil state))))

(defun construct-reqfix-functions-recur (;; params that stay the same
                                         product-type-name
                                         all-fieldspecs
                                         invariant
                                         ;; params that iterate
                                         remaining-fieldspecs
                                         remaining-fixvals)
  (if (or (endp remaining-fieldspecs) (endp remaining-fixvals))
      nil
    (cons (construct-reqfix-function product-type-name
                                     all-fieldspecs
                                     invariant
                                     (car remaining-fieldspecs)
                                     (car remaining-fixvals))
          (construct-reqfix-functions-recur product-type-name
                                            all-fieldspecs
                                            invariant
                                            (cdr remaining-fieldspecs)
                                            (cdr remaining-fixvals)))))

(defun construct-reqfix-functions (product-type-name ;  stringp
                                   fieldspecs ; string-listp
                                   invariant ; expression
                                   fixvals) ; listp

  (if (not (and (listp fieldspecs) (listp fixvals)
                (equal (len fieldspecs) (len fixvals))))
      (er hard? 'top-level? "number of fields does not match number of base values")
    (list*
;;;;;; NOTE: probably should just take out this comment.  I think it is wrong,
;;;;;; but I don't know why. - EM
;; I think this prevents the resulting form from being an embedded event form.
;; We maybe need to set these at the top level for processing Syntheto.
;;     ;; These will go inside an encapsulate.
;;     ;; Since we don't require all the parameters are used, we need to
;;     ;; tell ACL2 that.
     '(set-ignore-ok t)
     '(set-irrelevant-formals-ok t)
     (construct-reqfix-functions-recur
      product-type-name fieldspecs invariant fieldspecs fixvals))))

;; Similar to above, but just the names, for example for use with (local (enable..))
(defun construct-reqfix-function-names (product-type-name fieldspecs)
  (if (endp fieldspecs) nil
    (cons (intern-syndef (reqfix-function-name product-type-name (car (car fieldspecs))))
          (construct-reqfix-function-names product-type-name (cdr fieldspecs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Construct the reqfix-enhanced fieldlist for use in fty::defprod.

;; A product type field spec is
;;   ("fieldname" (s-type-constructor-form ..))

;; However, when an invariant is specified, this is added:
;;   :reqfix (reqfix-fun ..all fieldnames..)

;; Each field in the defprod fieldlist has a
;; - field name (symbol in SYNDEF package)
;; - type symbol (as computed by s-type-to-fty-name-symbol)
;; - optional :reqfix (<prodname>-FIX-<fieldname> <fieldnames..>)
;;   The reqfix function name is returned by
;;     (reqfix-function-name product-type-name field-name)

;; Previously we did
;;   (field+type-to-field+type-list f+t-list)
;; which simply replaced, for each field+type in the list,
;;   (1) a field name string by its symbol in the syndef package
;;   (2) a (s- ..) type constructor by a type symbol using (s-type-to-fty-name-symbol ..)
;; Now we replace this by construct-defprod-fieldlist, which
;; adds the reqfix when needed.

(defun gather-field-symbols (field+type-list)
  (if (endp field+type-list) nil
    (cons (intern-syndef (car (car field+type-list)))
          (gather-field-symbols (cdr field+type-list)))))

(defun construct-defprod-fieldspec (product-type-name  ; pre-translated
                                    field+type  ; pre-translated
                                    reqfix?
                                    field-symbols) ; boolean
  (list* (intern-syndef (first field+type))
        ;; NOTE: converting the type name to pred is not needed here.
        ;; The examples in the xdoc for defprod and other fty defining forms
        ;; use the recognizer pred to specify the component types,
        ;; but it works fine to specify them as the type names.
        ;; We suspect that the xdoc examples are a holdover from defaggregate.
        (let ((type-indicator (second field+type)))
          (s-type-to-fty-name-symbol type-indicator))
        (and reqfix?
             `(:reqfix (,(intern-syndef (reqfix-function-name product-type-name (car field+type)))
                        ,@field-symbols)))))

(defun construct-defprod-fieldspec-list-recur
    (product-type-name ; pre-translated string
     field+type-list ; pre-translated (string s-type-constructor)
     reqfix?  ; boolean
     field-symbols) ; already translated to syndef symbols
  (if (endp field+type-list)
      nil
    (cons (construct-defprod-fieldspec product-type-name
                                       (car field+type-list)
                                       reqfix?
                                       field-symbols)
          (construct-defprod-fieldspec-list-recur product-type-name
                                                  (cdr field+type-list)
                                                  reqfix?
                                                  field-symbols))))

(defun construct-defprod-fieldspec-list
    (product-type-name ; pre-translated string
     field+type-list ; pre-translated (string s-type-constructor)
     reqfix?) ; boolean
  (construct-defprod-fieldspec-list-recur product-type-name
                                          field+type-list
                                          reqfix?
                                          ;; precompute the field symbols since
                                          ;; they are the same for each reqfix call
                                          (gather-field-symbols field+type-list)))

(set-state-ok t)

(defun fixvals-for-types (types state)
  (declare (xargs :mode :program))
  (if (endp types)
      (value nil)
    (b* ((type-name (s-type-to-fty-name-symbol (car types)))
         (fixing-fn (type-name-to-fix type-name))
         ((er fixval1)
          (trans-eval `(with-guard-checking :none (,fixing-fn  'bad-value)) t state nil))
         ((er rec-fixvals)
          (fixvals-for-types (cdr types) state)))
      (value (cons (cdr fixval1) rec-fixvals)))))

(defun find-fixvals-for-product (field+type-list invariant state)
  (declare (xargs :mode :program))
  (b* (((er fixvals)
        (fixvals-for-types (strip-cadrs field+type-list) state))
       ((when (null fixvals))
          (value nil))
       (invariant-term (translate-term invariant))
       (varlist (translate-names (strip-cars field+type-list)))
       (constraint-lambda-term `((lambda ,varlist
                                   (declare (ignorable ,@varlist))
                                   ,invariant-term)
                                 ,@fixvals))
       ((er fixvals-satisfy-constraint)
        (trans-eval constraint-lambda-term t state nil)))
  (value (and (cdr fixvals-satisfy-constraint)
              fixvals))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (make-product-type NAME
;;   :shortdoc "d"
;;   :longdoc "doc"
;;   ("field1" (s-type..))
;;   ("field2" (s-type..))
;;   :invariant <expr>
;;   :fixvals <list-of-values> )
;; The invariant expression must mention all the field names as free variables.
;; The invariant expression must hold if the params are bound to the
;; <list-of-values>.
;;
;; The keyword args pairs and the fieldspecs may occur in any order,
;; although, of course, the relative order of the fieldspecs is significant.

(defun make-product-type-main (name field+type-list keys-and-vals state)
  (declare (xargs :mode :program))
  (b* ((short-doc-string (cdr (assoc :short keys-and-vals)))
       (long-doc-string (cdr (assoc :long keys-and-vals)))
       (invariant (cdr (assoc :invariant keys-and-vals)))
       (fixvals0 (cdr (assoc :fixvals keys-and-vals)))
       ((er fixvals)
        (if (and invariant (not fixvals0))
            (find-fixvals-for-product field+type-list invariant
                                        ;(fty::get-fixtypes-alist (w state))
                                      state)
          (value fixvals0)))
       ((when (or (and invariant (not fixvals))
                  (and (not invariant) fixvals)))
        (value (er hard 'top-level "make-product-type: either both or neither \
                                 of :invariant and :fixvals must be provided")))
       (short-doc-list (and short-doc-string
                            (list :short short-doc-string)))
       (long-doc-list (and long-doc-string
                           (list :long long-doc-string)))

       ;; This must have both or neither of invariant and fixvals.
       ;; If they are provided, we have to generate the reqfix functions
       ;; and to add the :reqfix calls into the field defs.
       ;; The invariant must be translated since fty::defprod doesn't
       ;; do that.
       (require-list (and invariant
                          (list :require (translate-term invariant))))
       (reqfix-functions (and fixvals
                              (construct-reqfix-functions name
                                                          field+type-list
                                                          invariant
                                                          fixvals)))
       (reqfix-function-names           ; just the names
        (and fixvals
             (construct-reqfix-function-names name
                                              field+type-list)))
       (fieldlist (construct-defprod-fieldspec-list name
                                                    field+type-list
                                                    (and fixvals T))))
    (value `(encapsulate nil
              ,@reqfix-functions
              (local (in-theory (enable ,@reqfix-function-names)))
              (fty::defprod ,(intern-syndef name)
                            ,@short-doc-list
                            ,@long-doc-list
                            ,fieldlist
                            ;; Prepend a tag so we can check types at runtime. ;
                            ;; This should not be necessary once we have static type ;
                            ;; checking, but it could be helpful for debugging. ;
                            :tag ,(intern name "KEYWORD")
                            ,@require-list )))))



(defmacro make-product-type (name &rest field+type-list+keys)
  (mv-let (field+type-list keys-and-vals)
      (parse-mixed-lists-and-keyvals field+type-list+keys)

    ;; field+type-list has string varnames and (s-...) S-expression type constructors
    ;; like ( ("idint" (S-TYPE-INTEGER)) ("idref" (S-TYPE-REF "acid")) ...)

    (let ((type-defs (defining-forms-for-unnamed-types-in-s-exp field+type-list)))
      ;; note, it would be nice to give a reasonable error if someone
      ;; misspelled a keyword arg, instead of silently ignoring it.
      `(with-output :off :all :on error :gag-mode t
         (progn ,@type-defs
                (make-event (make-product-type-main ',name ',field+type-list ',keys-and-vals state)))))))

#||

;; Here is an example of :reqfix that works:

;(include-book "centaur/bitops/top" :dir :system)

;; Here is the example from the xdoc.
(fty::defprod sizednum
  ((size natp)
   (bits natp :reqfix (loghead size bits)))
  :require (unsigned-byte-p size bits))


;; Here's an example of something we could generate automatically.

(defun sizednum-fix-size (size bits)
  (if (unsigned-byte-p size bits)
      size
  0))

(defun sizednum-fix-bits (size bits)
  (if (unsigned-byte-p size bits)
      bits
  0))

(fty::defprod sizednum0
  ((size natp :reqfix (sizednum-fix-size size bits))
   (bits natp :reqfix (sizednum-fix-bits size bits)))
  :require (unsigned-byte-p size bits))

So the steps here are:
1. make sure we have all the needed info
2. define N functions, one for each field.
(defun prodname-fix-fieldN (field1 field2 ..)
  (if <require-expr>
      fieldN
    valN))

||#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Support for sum types

;; reference: see name+prodspecs-to-sum-alternatives-list

;; find and return separately the :invariant and :fixvals arguments
;; without translating them
(defun parse-syn-fieldspecs (syn-fieldspecs)
  (b* (((unless (true-listp syn-fieldspecs))
        (mv (er hard? 'top-level "bad fieldspecs") nil nil))
       (variant-key-position (position ':invariant syn-fieldspecs))
       ((when (null variant-key-position))
        (mv syn-fieldspecs nil nil))
       ;; now we expect to see the tail (:variant vv :fixvals (fv..))
       ((unless (and (= variant-key-position (- (len syn-fieldspecs) 4))
                     (= (position ':fixvals syn-fieldspecs) (- (len syn-fieldspecs) 2))))
        (mv (er hard? 'top-level ":variant or :fixvals in wrong position") nil nil))
       (variant (nth (+ variant-key-position 1) syn-fieldspecs))
       (fixvals (nth (+ variant-key-position 3) syn-fieldspecs))
       ((unless (and (consp variant) (consp fixvals)))
        (mv (er hard? 'top-level "bad variant or fixvals format") nil nil)))
    (mv (butlast syn-fieldspecs 4)
        variant
        fixvals)))

(defun fty-sum-prod-require-function-name (sum-name tag-string)
  (concatenate 'string
               "$" sum-name "$" tag-string "-INVARIANT"))

;; require-fn-name is a pre-translated string
(defun construct-require-function (require-fn-name syn-fieldspecs invariant)
  ;; see construct-reqfix-function for similar code
  (b* (((mv erp param-list let-fixing-list ?input-types &)
        (process-s-fun-inputs syn-fieldspecs nil))
       ((when erp) (er hard? 'top-level "Bad :inputs to s-fun"))
       ((mv erp returns-list ?output-fixer ?output-types &)
        (process-s-fun-outputs `((,(concatenate 'string "$RETURN-" require-fn-name)
                                  (s-type-boolean)))
                               nil))
       ((when erp) (er hard? 'top-level "Bad :outputs to s-fun")))
    `(make-event (s-fun-main
                  ,require-fn-name
                  ',param-list
                  ',invariant
                  ',let-fixing-list
                  ',returns-list
                  nil nil nil nil state))))

;; It would be good if this operated on strings.  See below.
(defun fty-fieldnames-to-s-var-refs (fty-fieldnames)
  (if (endp fty-fieldnames) nil
    (cons `(s-var-ref ,(symbol-name (car fty-fieldnames)))
          (fty-fieldnames-to-s-var-refs (cdr fty-fieldnames)))))

;; like reqfix-function-name, but for prod in a sum
(defun reqfix-function-name-v2 (sum-name tag-string field-name)
  (concatenate 'string "$" sum-name "$" tag-string "-FIX-" field-name))

;; like construct-reqfix-function, but for prod in a sum
(defun construct-reqfix-function-v2 (reqfix-fn-name sum-name tag-string
                                                    all-syn-fieldspecs all-fty-fieldnames require-fn-name
                                                    this-syn-fieldspec this-fixval)
  ;; Copied logic here from defmacro s-fun
  ;; Added "?" on input-types and output-types since those were used for
  ;; adding type definitions but these reqfix functions don't need any new type defs.
  ;; Also took out refine-types-given-assumes.
  (b* (((mv erp param-list let-fixing-list ?input-types &)
        (process-s-fun-inputs all-syn-fieldspecs nil))
       ((when erp) (er hard? 'top-level "Bad :inputs to s-fun"))
;;       ((mv param-list let-fixing-list)
;;        (refine-types-given-assumes nil param-list let-fixing-list))
       ((mv erp returns-list ?output-fixer ?output-types &)
        (process-s-fun-outputs `((,(concatenate 'string sum-name "$" tag-string "$RETURN-" (car this-syn-fieldspec))
                                  ,(cadr this-syn-fieldspec)))
                               nil))
       ((when erp) (er hard? 'top-level "Bad :outputs to s-fun")))
    ;; EM: I'm not fully convinced this make-event is needed.
    ;; It might be OK to retry the (s-fun ..) macro sometime.
    `(make-event (s-fun-main
                  ,reqfix-fn-name
                  ',param-list
                  ;; Note: it would be better if the fieldnames could be passed down as strings.  TODO: try it.
                  '(s-conditional
                    (s-call ,require-fn-name ,@(fty-fieldnames-to-s-var-refs all-fty-fieldnames))
                    (s-var-ref ,(car this-syn-fieldspec))
                    ,this-fixval)
                  ',let-fixing-list
                  ',returns-list
                  nil nil nil nil state))))

;; like construct-defprod-fieldspec, but we know we have a reqfix here, and we pass in the reqfix-fn-name
(defun construct-defsum-prod-fieldspec (this-syn-fieldspec reqfix-fn-name field-symbols)
  (list* (intern-syndef (first this-syn-fieldspec))
         ;; NOTE: converting the type name to pred is not needed here.
         ;; The examples in the xdoc for defprod and other fty defining forms
         ;; use the recognizer pred to specify the component types,
         ;; but it works fine to specify them as the type names.
         ;; We suspect that the xdoc examples are a holdover from defaggregate.
         (let ((type-indicator (second this-syn-fieldspec)))
           (s-type-to-fty-name-symbol type-indicator))
         `(:reqfix (,(intern-syndef reqfix-fn-name)
                    ,@field-symbols))))

;; returns: (mv reqfix-fn enable-fn fty-fieldspec)
(defun syn-fieldspec-to-fty-fieldspec (sum-name
                                       tag-string
                                       tag-keyword-symbol
                                       all-syn-fieldspecs
                                       all-fty-fieldnames
                                       require-fn-name
                                       all-fixvals
                                       this-syn-fieldspec
                                       this-fixval)
  (declare (ignore tag-keyword-symbol all-fixvals))
  (let* ((reqfix-fn-name (reqfix-function-name-v2 sum-name tag-string (car this-syn-fieldspec)))
         (reqfix-fn (construct-reqfix-function-v2 reqfix-fn-name sum-name tag-string
                                                  all-syn-fieldspecs all-fty-fieldnames require-fn-name
                                                  this-syn-fieldspec this-fixval))
         (fty-fieldspec (construct-defsum-prod-fieldspec this-syn-fieldspec reqfix-fn-name all-fty-fieldnames)))
    ;; translate reqfix-fn-name to return as a function that needs to be locally enabled
    (mv reqfix-fn (intern-syndef reqfix-fn-name) fty-fieldspec)))

;; returns: (mv reqfix-fns enable-fns fty-fieldspecs)
(defun syn-fieldspecs-to-fty-fieldspecs-recur (;; params that stay the same
                                               sum-name
                                               tag-string
                                               tag-keyword-symbol
                                               all-syn-fieldspecs
                                               all-fty-fieldnames
                                               require-fn-name
                                               all-fixvals
                                               ;; params that iterate
                                               remaining-syn-fieldspecs
                                               remaining-fixvals)
  (b* (((when (or (endp remaining-syn-fieldspecs)
                  (endp remaining-fixvals))) ; defensive; they should be the same length
        (mv nil nil nil))
       ((mv reqfix-fn-f enable-fn-f fty-fieldspec-f)
        (syn-fieldspec-to-fty-fieldspec sum-name
                                        tag-string
                                        tag-keyword-symbol
                                        all-syn-fieldspecs
                                        all-fty-fieldnames
                                        require-fn-name
                                        all-fixvals
                                        (car remaining-syn-fieldspecs)
                                        (car remaining-fixvals)))
       ((mv reqfix-fns-r enable-fns-r fty-fieldspecs-r)
        (syn-fieldspecs-to-fty-fieldspecs-recur sum-name
                                        tag-string
                                        tag-keyword-symbol
                                        all-syn-fieldspecs
                                        all-fty-fieldnames
                                        require-fn-name
                                        all-fixvals
                                        (cdr remaining-syn-fieldspecs)
                                        (cdr remaining-fixvals))))
    (mv (cons reqfix-fn-f reqfix-fns-r)
        (cons enable-fn-f enable-fns-r)
        (cons fty-fieldspec-f fty-fieldspecs-r))))

;; similar in concept to construct-reqfix-functions, but returns more stuff
;; returns: (mv reqfix-fns enable-fns fty-fieldnames fty-fieldspecs)
(defun syn-fieldspecs-to-fty-fieldspecs (sum-name
                                         tag-string
                                         tag-keyword-symbol
                                         syn-fieldspecs
                                         require-fn-name
                                         fixvals
                                         )
  (let ((fty-fieldnames (gather-field-symbols syn-fieldspecs)))
    ;; fty-fieldnames is a list of symbols (altready translated, unlike the other params here
    (mv-let (reqfix-fns enable-fns fty-fieldspecs)
        (syn-fieldspecs-to-fty-fieldspecs-recur
         sum-name tag-string tag-keyword-symbol syn-fieldspecs fty-fieldnames require-fn-name fixvals
         ;; again, to iterate:
         syn-fieldspecs fixvals)
      ;; include fty-fieldnames among the values returned.
      (mv reqfix-fns enable-fns fty-fieldnames fty-fieldspecs))))


;; Returns
;;   (mv require-preds reqfix-fns enable-fns fty-prodspec)
;; Although we return a list of require-preds (so it is easier to append later),
;; there can only be one.
(defun syn-prodspec-w-invariant-to-fty-prodspec (sum-name
                                                 tag-string
                                                 tag-keyword-symbol
                                                 syn-fieldspecs
                                                 invariant
                                                 fixvals)

;    ;; TODO: take this out
;    (declare (ignorable sum-name
;                   tag-string
;                   tag-keyword-symbol
;                   syn-fieldspecs
;                   invariant
;                   fixvals))

  (b* ;; fixvals must be a list with one val for each field
      (((when (and (consp fixvals)
                   (not (equal (len fixvals) (len syn-fieldspecs)))))
        (mv (er hard? 'top-level ":fixvals (val1 .. ) must have one value for each field") nil nil nil))

       ;; We build our own invariant predicate out of the expression
       ;; (for make-product-type, we originally just translated the expression and then
       ;; let fty::defprod do the defining part, but now we want more control)
       ;; require-fn-name is a string
       ;; require-call is what goes after the :require in the fty form
       (require-fn-name (fty-sum-prod-require-function-name sum-name tag-string))
       (invariant-pred (construct-require-function require-fn-name syn-fieldspecs invariant))

       ;; Iterate through the syn-fieldspecs gathering all the fieldspec-specific things
       ;; and generating the new fty-fieldspec.
       ;; This is a better-organized version of defmacro make-product-type's
       ;; original method of calculating require-list, reqfix-functions, and fieldlist separately.
       ((mv reqfix-fns enable-fns fty-fieldnames fty-fieldspecs)
        (syn-fieldspecs-to-fty-fieldspecs sum-name
                                          tag-string
                                          tag-keyword-symbol
                                          syn-fieldspecs
                                          require-fn-name
                                          fixvals))

       (require-call `(,(intern-syndef require-fn-name) ,@fty-fieldnames))
       (fty-prodspec `(,tag-keyword-symbol ,fty-fieldspecs :require ,require-call)))

    (mv (list invariant-pred) reqfix-fns enable-fns fty-prodspec)))


;; sum-name is the pre-translated string.  (syn-ps is obviously also pre-translated)
(defun syntheto-prodspec-to-deftagsum-prodspec (sum-name syn-ps)
  ;; The input syn-ps is ( tag-string ( fieldspec1 fieldspec2 .. &key invariant fixvals ) )
  ;; (syn-ps abbreviates "Syntheto product type specifier")
  ;; A syn-fieldspec is  ( fieldname-string (s-type-descriptor..) )
  ;;
  ;; The output is  (mv require-preds reqfix-fns enable-fns fty-prodspec)
  ;; where fty-prodspec is ( tag-symbol-in-keyword-package ( fty-fieldspec1 .. ) &key require )
  ;; Note the change in shape.
  ;; An fty-fieldspec is ( field-name-symbol-in-syndef-package type-symbol &key reqfix )
  (b* (((unless (and (listp syn-ps)
                     (= (length syn-ps) 2)
                     (stringp (first syn-ps))
                     (listp (second syn-ps))))
        (mv (er hard? 'top-level "incorrect format for Syntheto product type specifier") nil nil nil))
       ((list tag-string syn-fieldspecs-maybe-invariant) syn-ps)
       ;; translate the tag
       (tag-keyword-symbol (intern tag-string "KEYWORD"))
       ;; parse out :invariant and :fixvals
       ((mv syn-fieldspecs invariant fixvals)
        (parse-syn-fieldspecs syn-fieldspecs-maybe-invariant))
       ;; some error checks
       ((when (or (and invariant (not fixvals))
                  (and (not invariant) fixvals)))
        (mv (er hard? 'top-level "Syntheto product type specifier must have either \
                                  both or neither of :invariant and :fixvals")
            nil nil nil)))
    (if invariant
        (syn-prodspec-w-invariant-to-fty-prodspec sum-name
                                                  tag-string
                                                  tag-keyword-symbol
                                                  syn-fieldspecs
                                                  invariant
                                                  fixvals)
      ;; go back to the old super-simple converter without require stuff
      (mv nil nil nil (list tag-keyword-symbol (field+type-to-field+type-list syn-fieldspecs))))))

;; sum-name and syn-ps-list are both pre-translated
(defun syntheto-prodspecs-to-deftagsum-prodspecs (sum-name syn-ps-list)
  (b* (((when (endp syn-ps-list))
        (mv nil nil nil nil))
       ((mv require-preds-f reqfix-fns-f enable-fns-f fty-prodspec-f)
        (syntheto-prodspec-to-deftagsum-prodspec sum-name (car syn-ps-list)))
       ((mv require-preds-r reqfix-fns-r enable-fns-r fty-prodspecs-r)
        (syntheto-prodspecs-to-deftagsum-prodspecs sum-name (cdr syn-ps-list))))
    (mv (append require-preds-f require-preds-r)
        (append reqfix-fns-f  reqfix-fns-r)
        (append enable-fns-f enable-fns-r)
        (cons fty-prodspec-f fty-prodspecs-r))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; sum types with invariants

;; (make-sum-type NAME
;;   :shortdoc "d"
;;   :longdoc "doc"
;;   alternative-spec1
;;   alternative-spec2 .. )

;; The :shortdoc and :longdoc args are optional, but if they occur,
;; they must occur before the alternative-specs.

;; Each alternative-spec includes a tag and a product type definition.
;; The tag is an indicator to the sum type which alternative is active.
;; The alternative-spec's product type definition is not separately named,
;; unlike a product type definition created with make-product-type.

;; An alternative-spec looks like:
;; simple alternative consisting of solely the tag:
;;   ("tag" ())
;; a product of two fields:
;;   ("tag" (("prodfield1" (s-type..))
;;           ("prodfield2" (s-type..)))
;; a product of one field with an invariant:
;;   ("tag" (("prodfield" (s-type..))
;;           :invariant <expr with free var "prodfield" returning boolean>
;;           :fixvals ( <val of same type as prodfield> ) )
;; Typically if you have an invariant, you will have more than one field.
;; (See also make-subtype for another way to restrict a type).
;; Rules:
;; * The :invariant and :fixvals are optional, but if one is provided
;;   the other must also be provided.
;; * The invariant expression, if specified, must mention all the
;;   field names as free variables and return a boolean.
;;   [we could relax this with ignorable decl]
;; * The invariant expression must evaluate to T if the params
;;   are bound to the <list-of-values>.
;; * The number and types of the fixvals must match the number
;;   and types of the fieldspecs.
;; Notes:
;; * The syntax of the product specs is different from fty::deftagsum.
;;   Here, the top list is just a doublet with a tag and a list of
;;   fieldspecs + keyword-args.  (The keyword args, if specified,
;;   increase the length of the fieldspec list by 4).
;;   In fty::deftagsum on the other hand, the :require and other
;;   keyword arguments come after the list of fieldspecs, so the
;;   product-specifier list there contains a tag, a list of fieldspecs,
;;   and then the keyword args.

#||
;; Working version without invariants:

(defmacro make-sum-type (name &rest name+prodspec-list)
    (mv-let (short-doc long-doc n+p-list)
        (extract-doc-keyword-args-from-list--both name+prodspec-list)
      (let ((type-defs (defining-forms-for-unnamed-types-in-s-exp name+prodspec-list)))
        `(encapsulate ()
           ,@type-defs
           (fty::deftagsum ,(intern-syndef name) ,@short-doc ,@long-doc
                           ,@(name+prodspecs-to-sum-alternatives-list n+p-list))))))
||#


(defmacro make-sum-type (name &rest name+prodspec-list)
  (b* (((mv short-doc long-doc n+p-list)
        (extract-doc-keyword-args-from-list--both name+prodspec-list))
       (type-defs (defining-forms-for-unnamed-types-in-s-exp n+p-list))

       ((mv require-preds reqfix-fns enable-fns new-prodspecs)
        (syntheto-prodspecs-to-deftagsum-prodspecs name n+p-list)))

    `(with-output :off :all :on error :gag-mode t
       (encapsulate ()
         ,@type-defs

         ;; try these when other stuff is working; if they work, take out the comments
         ;;(local (set-ignore-ok t))
         ;;(local (set-irrelevant-formals-ok t))

         ,@require-preds
         ,@reqfix-fns
         (local (in-theory (enable ,@enable-fns)))

         (fty::deftagsum ,(intern-syndef name)
                         ,@short-doc ,@long-doc
                         ,@new-prodspecs)))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; fty::deftagsum note

;; The :require keyword is briefly mentioned in the deftagsum doc under
;; "Product specifiers", but it mainly just says to look at the doc for defprod.

;; Here are some worked examples of using :require and :reqfix
;; in deftagsum's "product specifiers".
;; This is provided for discussion and reference.

#||
;; The following works, and is a template for how we handle invariants.

;(include-book "centaur/fty/top" :dir :system)

(define str-fill-pointer-compat ((str stringp) (fill-pointer integerp))
  :returns (yes/no booleanp)
  (and (stringp str) (integerp fill-pointer)
       (<= 0 fill-pointer) (<= fill-pointer (length str))))

(define str-reqfix ((str stringp) (fill-pointer integerp))
  :returns (fixed-str stringp :hyp (stringp str))
  (if (str-fill-pointer-compat str fill-pointer)
      str
    ""))

(define fp-reqfix ((str stringp) (fill-pointer integerp))
  :returns (fixed-fp integerp :hyp (integerp fill-pointer))
  (if (str-fill-pointer-compat str fill-pointer)
      fill-pointer
    0))

(encapsulate ()

(local (in-theory (enable str-reqfix fp-reqfix str-fill-pointer-compat)))

(fty::deftagsum test-invariants
  ;; the fill pointer must be nonnegative and less than or equal to the length of the string
  (:str-with-fill-pointer ((str STRING :reqfix (str-reqfix str fill-pointer))
                           (fill-pointer INT :reqfix (fp-reqfix str fill-pointer)))
                           ;; it would make most sense to reuse the following expression
                           ;; in the reqfix functions, but let's try this:
                           :require (str-fill-pointer-compat str fill-pointer)))
)

||#

#||
;; Expand the preceding to have more than one alternative.

;(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;
;; Fill pointer example

(define str-fill-pointer-compat ((str stringp) (fill-pointer integerp))
  :returns (yes/no booleanp)
  (and (stringp str) (integerp fill-pointer)
       (<= 0 fill-pointer) (<= fill-pointer (length str))))

(define str-reqfix ((str stringp) (fill-pointer integerp))
  :returns (fixed-str stringp :hyp (stringp str))
  (if (str-fill-pointer-compat str fill-pointer)
      str
    ""))

(define fp-reqfix ((str stringp) (fill-pointer integerp))
  :returns (fixed-fp integerp :hyp (integerp fill-pointer))
  (if (str-fill-pointer-compat str fill-pointer)
      fill-pointer
    0))

;;;;;;;;;;;;;;;;;;;;
;; Polar coordinates example

(define polar-coords-p ((r integerp) (theta integerp))
  :returns (polar? booleanp)
  (and (natp r)
       (natp theta)
       (< theta 360)))

(define radius-reqfix ((rad integerp) (ang integerp))
  :returns (fixed-radius integerp :hyp (integerp rad))
  (if (polar-coords-p rad ang)
      rad
    0))

(define angle-reqfix ((rad integerp) (ang integerp))
  :returns (fixed-angle integerp :hyp (integerp ang))
  (if (polar-coords-p rad ang)
      ang
    0))

(encapsulate ()

(local (in-theory (enable str-fill-pointer-compat str-reqfix fp-reqfix
                          polar-coords-p radius-reqfix angle-reqfix)))

(fty::deftagsum sum-of-two-invariants
  ;; the fill pointer must be nonnegative and less than or equal to the length of the string
  (:str-with-fill-pointer ((str STRING :reqfix (str-reqfix str fill-pointer))
                           (fill-pointer INT :reqfix (fp-reqfix str fill-pointer)))
                           ;; it would make most sense to reuse the following expression
                           ;; in the reqfix functions, but let's try this:
                           :require (str-fill-pointer-compat str fill-pointer))

  ;; the radius must be nonnegative and the angle must be 0 <= angle < 360
  (:polar-coords ((radius INT :reqfix (radius-reqfix radius angle))
                  (angle INT :reqfix (angle-reqfix radius angle)))
                  :require (polar-coords-p radius angle))
  )
)

;; How it is used:

;; (MAKE-sum-of-two-invariants-STR-WITH-FILL-POINTER :str "abc" :fill-pointer 1)
;;   => (:STR-WITH-FILL-POINTER "abc" 1)
;; (MAKE-sum-of-two-invariants-STR-WITH-FILL-POINTER :str "abc" :fill-pointer 4)
;;   => guard error
;; (set-guard-checking :none)
;; (MAKE-sum-of-two-invariants-STR-WITH-FILL-POINTER :str "abc" :fill-pointer 4)
;;   => (:STR-WITH-FILL-POINTER "" 0)
;; (set-guard-checking t)

;; (sum-of-two-invariants-P '(:STR-WITH-FILL-POINTER "" 0))
;;   => T
;; (sum-of-two-invariants-P '(:STR-WITH-FILL-POINTER " " 0))
;;   => T
;; (sum-of-two-invariants-P '(:STR-WITH-FILL-POINTER "" 1))
;;   => NIL

;; (MAKE-sum-of-two-invariants-POLAR-COORDS :radius 1 :angle 359)
;;   => (:POLAR-COORDS 1 359)
;; (MAKE-sum-of-two-invariants-POLAR-COORDS :radius 1 :angle 360)
;;   => guard error
;; (set-guard-checking :none)
;; (MAKE-sum-of-two-invariants-POLAR-COORDS :radius 1 :angle 360)
;;   => (:POLAR-COORDS 0 0)

;; (sum-of-two-invariants-P '(:POLAR-COORDS 10 10))
;;   => T
;; (sum-of-two-invariants-P '(:POLAR-COORDS -1 0))
;;   => NIL

||#
