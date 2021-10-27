; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macros for building type definitions.

;; See the UML diagram:
;; https://git.isis.vanderbilt.edu/midas/acl2.xtext/-/blob/devel/abstract-syntax/types-uml.png
;; and some more discussion
;; https://git.isis.vanderbilt.edu/midas/adm/-/wikis/MIDAS-Wiki/Ideas/Type-System-of-the-Specification-Language
;; https://git.isis.vanderbilt.edu/midas/adm/-/wikis/MIDAS-Wiki/Ideas/Target-ACL2-Construc

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defset" :dir :system)
(include-book "kestrel/fty/defomap" :dir :system)
(include-book "kestrel/fty/defsubtype" :dir :system)

(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "defsort/defsort" :dir :system)

(include-book "../syndef-package-utilities")
(include-book "basetype-info")
(include-book "type-constructors")

(include-book "expressions") ; for restriction expressions


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Discussion.
;; If source code uses a type like `set(sequence(integer))',
;; we will need to define both
;;   (fty::deflist SEQUENCE[INT] :elt-type INT ..)
;;   (fty::defset SET[SEQUENCE[INT]] :elt-type SEQUENCE[INT] ..)
;; How can we raise these definitions out to the top level?
;; Since macros are expanded from the outside to inside,
;; the outer macros will not know that the inner macros expanded to these
;; types.
;; There are a number of ways to handle this:
;; (1) the outer macro can call trans on the inner macros and assemble
;;     the results as the expansion of the outer macro.
;; (2) the outer macro can expand into a special OUTER-FN event function
;;     that is passed the expanded form and can analyze it in a functional
;;     way
;; (3) the outer macro can look at the unexpanded inner macros to see
;;     what to do.
;; In this case, the unexpanded inner type macros are a simple language
;; that can be easily gathered, so I suggest #3 in this case.
;; Each top-level defining macro can scan its contents
;; to find all such unnamed composite types in their unexpanded macro forms,
;; and then explicate them into the appropriate definitions.
;; Those definitions would be grouped together in a
;; "trivial ecapsulation" (see :doc encapsulate).
;; Let's take an example function that just calls arb to get an arbitrary
;; element of the set.  arb should be polymorphic: arb: set(A) -> maybe(A)
;; Actually, it probably will not be, it will be a language construct
;; that compiles into different things based on the types.
;; However, for now let's say that it is another function with the same
;; signature as myarb that we are calling.
;; Actually, if it has the same signature, then the types are already created,
;; but forget about that.  The point I am trying to make here is what happens
;; to the types when we have a new definition.
;;   def myarb (x: set(sequence(integer))): maybe(sequence(integer)) = arb(x)
;; This will be turned into something like
;;   (s-fun "myarb" :inputs (("x" (s-type-set (s-type-sequence (s-integer)))))
;;                  :outputs (("R!1" (s-type-option (s-type-sequence (s-integer)))))
;;                  :body (s-call "arb" (s-varref "x")))
;; When this is macroexpanded, the s-def first looks for the type constructors
;; and it finds this list in a traversal (depending on the search algorithm,
;; they may come out in a different order):
;;   (s-type-set (s-type-sequence (s-integer)))
;;   (s-type-sequence (s-integer))
;;   (s-type-option (s-type-sequence (s-integer)))
;;   (s-type-sequence (s-integer))
;; We can sort these by increasing number of conses and remove the duplicates
;; and then turn each one into a defining form.  Many are likely to be redundant
;; with previous unnamed types.
;; (As special cases, the simpler ones can be predefined and so don't need to
;; turn into defining forms.)
;; The result of what the top-level macro expands into, including the expansion
;; of the sub-macros (not the full expansion, just the part we are interested in)
;; is:
;; (encapsulate ()
;;    (fty::deflist SEQUENCE[INT] :elt-type INT :true-listp t :elementp-of-nil nil)
;;        ; NOTE: the :elementp-of-nil is conditional on whether nil is a valid
;;        ; value of the component type.  See nil-is-member-of-s-type-p below.
;;    (fty::defset SET[SEQUENCE[INT]] :elt-type SEQUENCE[INT])
;;    (fty::deftagsum OPTION[SEQUENCE[INT]] (:SOME ((GET SEQUENCE[INT]))) (:NONE ()))
;;    (define syndef::|myarb| ((SYNDEF::X SET[SEQUENCE[INT]]))
;;            :returns (SYNDEF::R OPTION[SEQUENCE[INT]])
;;            (OPTION[SEQUENCE[INT]]-FIX (let ((SYNDEF::X (SET[SEQUENCE[INT]]-FIX SYNDEF::X)))
;;                                 (SYNDEF::ARB SYNDEF::X))))
;;
;; Here is an example:
#||
SYNTHETO !>:trans1 (make-product-type "acid5" ("id" (s-type-option (s-type-set (s-type-sequence (s-type-integer))))))
 (ENCAPSULATE
      NIL
      (FTY::DEFLIST SYNDEF::SEQUENCE[INT]
                    :ELT-TYPE INT
                    :TRUE-LISTP T)
      (FTY::DEFSET SYNDEF::SET[SEQUENCE[INT]]
                   :ELT-TYPE SYNDEF::SEQUENCE[INT]
                   :ELEMENTP-OF-NIL T)
      (FTY::DEFTAGSUM SYNDEF::OPTION[SET[SEQUENCE[INT]]]
                      (:SOME ((GET SYNDEF::SET[SEQUENCE[INT]])))
                      (:NONE NIL))
      (FTY::DEFPROD SYNDEF::|acid5|
                    ((SYNDEF::|id| SYNDEF::OPTION[SET[SEQUENCE[INT]]]))
                    :TAG :|acid5|))
||#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; type name to recognizer predicate

;; The default automatically-generated type recognizers have "-P" appended
;; to the type name.
(define type-name-to-pred ((type-name symbolp))
  :returns (pred symbolp)
  (if (base-type-name-p type-name)
      (base-type-name-to-pred type-name)
    ;; If it is not a base type, restrict the type-name to be in the SYNDEF package.
    ;; Otherwise their could be accidental collisions due to imports.
    (if (err-if-not-in-syndef type-name) "error" ; string is ignored because error happend
      (add-suffix type-name "-P")
      ;; Note: since type-name is in the SYNDEF package,
      ;; the callto add-suffix is equivalent here to
      ;; (intern-in-package-of-symbol
      ;;   (string-append (symbol-name type-name) "-P") type-name)
      )))

;; type name string to recognizer predicate
(define type-name-string-to-pred ((type-name-string stringp))
  :returns (pred symbolp)
  (if (base-type-name-string-p type-name-string)
      (base-type-name-to-pred (intern type-name-string "ACL2"))
    (type-name-to-pred (intern-syndef type-name-string))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; type name to fixing function

;; The default automatically-generated fixing function names have "-FIX"
;; appended to the type name.
(define type-name-to-fix ((type-name symbolp))
  :returns (fixer symbolp)
  (if (base-type-name-p type-name)
      (base-type-name-to-fix type-name)
    ;; If it is not a base type, restrict the type-name to be in the SYNDEF package.
    ;; Otherwise their could be accidental collisions due to imports.
    (if (err-if-not-in-syndef type-name)
        "error" ; string is ignored because error happend
      (add-suffix type-name "-FIX"))))

;; type name string to fixing function
(define type-name-string-to-fix ((type-name-string stringp))
  :returns (fixer symbolp)
  (if (base-type-name-string-p type-name-string)
      (base-type-name-to-fix (intern type-name-string "ACL2"))
    (type-name-to-fix (intern-syndef type-name-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; type name to equiv function

;; The default automatically-generated equiv functions have "-EQUIV" appended
;; to the type name.
(define type-name-to-equiv ((type-name symbolp))
  :returns (equiv-fn symbolp)
  (if (base-type-name-p type-name)
      (base-type-name-to-equiv type-name)
    ;; If it is not a base type, restrict the type-name to be in the SYNDEF package.
    ;; Otherwise their could be accidental collisions due to imports.
    (if (err-if-not-in-syndef type-name)
        "error" ; string is ignored because error happend
      (add-suffix type-name "-EQUIV"))))

(define type-name-string-to-equiv ((type-name-string stringp))
  :returns (equiv-fn symbolp)
  (if (base-type-name-string-p type-name-string)
      (base-type-name-to-equiv (intern type-name-string "ACL2"))
    (type-name-to-equiv (intern-syndef type-name-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; gather-type-forms
;; walk an s-expression and gather all the type constructor forms

;; Does not do any validation of substructure.
;; This means that set(seq(int)) will return two type forms,
;; set(seq(int)) and seq(int).
(define gather-type-forms (s-exp)
  (if (atom s-exp)
      nil
    (if (toplevel-type-constructor-p s-exp)
        (cons s-exp
              (if (binary-type-constructor-p s-exp)
                  (append (gather-type-forms (second s-exp))
                          (gather-type-forms (third s-exp)))
                (gather-type-forms (second s-exp))))
      (append (gather-type-forms (car s-exp))
              (gather-type-forms (cdr s-exp))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; validate-type-forms

;; validates a list of forms,
;; returning (mv valid-forms invalid-forms)
(define validate-type-forms ((type-forms true-listp))
  (b* (((when (endp type-forms))
        (mv nil nil))
       (first-valid? (valid-full-type-form-p (car type-forms)))
       ((mv rest-valid rest-invalid)
        (validate-type-forms (cdr type-forms))))
    (mv (if first-valid?
            (cons (car type-forms) rest-valid)
          rest-valid)
        (if first-valid?
            rest-invalid
          (cons (car type-forms) rest-invalid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sorting by number of conses, which is guaranteed to put
;; subexpressions before their parent expressions.
;; This is used for defining types in the inside-out order.
;; For the purpose of defining types it is sufficient to use num-conses<.

;; We also define a total order num-conses<<
;; in case that comes in handy.

(define num-conses (x)
  :returns (r natp)
  (if (consp x)
      (+ 1 (num-conses (car x)) (num-conses (cdr x)))
    0))

(define num-conses< (x y)
  :returns (r booleanp)
  (< (num-conses x) (num-conses y)))

;; Make a total order
(define num-conses<< (x y)
  :returns (r booleanp)
  (let ((ncx (num-conses x)) (ncy (num-conses y)))
    (or (< ncx ncy)
        (and (= ncx ncy)
             (<< x y)))))

(encapsulate ()
  (local (in-theory (enable num-conses<)))

  (acl2::defsort sort-by-num-conses
                 :compare< num-conses<
                 :weak t)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Collect every subtree of def that looks like a valid type constructor.
;; If there are any invalid ones that have the right top,
;; report those.
;; Sorts and deduplicates.
(define gather-types-top (def)
  (b* ((type-forms (gather-type-forms def))
       ((mv valid invalid) (validate-type-forms type-forms))
       ((when invalid)
        (prog2$ (cw "These type forms are invalid: ~x0~%" invalid)
                (er hard? 'top-level "Invalid type forms")))
       (sorted-type-forms (sort-by-num-conses valid)) ; TODO: what is the comparator?
       (deduped-type-forms (remove-duplicates-equal sorted-type-forms)))
    deduped-type-forms))


#||
;; Examples of type descriptors.

;; The first five are macros that expand into the appropriate base type names
;; or in the case of s-type-ref, into a named type symbol.
;; When one is a component of a composite type descriptor, it may be separately
;; expanded by the defining form macro before macroexpansion sees it.

(s-type-boolean)
(s-type-integer)
(s-type-character)
(s-type-string)
(s-type-ref "ACTYPE")

;; The four composite type descriptors are not macros (*).  They are:
;;    (s-type-set ..)
;;    (s-type-sequence ..)
;;    (s-type-option ..)
;;    (s-type-map .., ..)
;; The macroexpansion of the top-level definition,
;; such as (s-fun ..) or (make-product-type ..)
;; should look for these and replace them by the appropriate type name or
;; recognizer predicate, and possibly add other dependent stuff like fixing.
;; To help with this, see
;;   (s-type-to-fty-name-symbol ..)
;;   (type-name-to-pred ..)
;;   (type-name-to-fix ..)
;;
;; (*) we may decide to make them macros that throw errors when expanded
;;     so we can detect early the failure to replace them by something

;; Examples:

(s-type-set (s-type-boolean)) ; not very useful
(s-type-map (s-type-boolean) (s-type-string)) ; two sets in one map
(s-type-sequence (s-type-character)) ; can APT turn this into a string?
(s-type-option (s-type-boolean)) ; for those opposed to the law of the excluded middle

(s-type-option (s-type-set (s-type-sequence (s-type-integer))))
(s-type-set (s-type-option (s-type-integer)))

;; Note, this depends on the existence of named types TT1, TT2, TT3, and TT4
(s-type-map (s-type-map (s-type-set (s-type-ref "TT1"))
                        (s-type-map (s-type-option (s-type-ref "TT2"))
                                    (s-type-ref "TT3")))
            (s-type-sequence (s-type-ref "TT4")))
||#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; check if NIL represents any member of a type,
;; where the type is expressed as an s-type form

(define nil-is-member-of-s-type-p (type-form)
  (if (atom type-form)
      (er hard? 'top-level "bad input to NIL-IS-MEMBER-OF-S-TYPE-P")
    (if (member-eq (car type-form)
                   '(s-type-set s-type-sequence s-type-map))
        T
      ;; Warning: we need to make sure that named types can't have nil,
      ;; or we need to have another macro s-type-ref-allowing-nil so
      ;; we can distinguish between them here.
      ;; Right now named types are for defprod (which we tag) and defsum.
      ;; s-type-option is now implemented as a deftagsum so it can't be NIL.
      (if (member-eq (car type-form) '(s-type-ref s-type-option))
          NIL
        (if (equal type-form '(s-type-boolean))
            T
          (if (member-equal type-form '((s-type-integer)
                                        (s-type-character)
                                        (s-type-string)))
              NIL
            (er hard? 'top-level "bad input to NIL-IS-MEMBER-OF-S-TYPE-P")))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Convert shallow type spec to fty defining form.

(defun s-type-set-to-defset (type-form def-name)
  (let* ((subdef-type-form (second type-form))
         (subdef-name (s-type-to-fty-name-symbol subdef-type-form)))
    (append
     (list 'fty::defset def-name
           :elt-type subdef-name)
     (if (nil-is-member-of-s-type-p subdef-type-form)
         '(:elementp-of-nil t)
       '(:elementp-of-nil nil))
     )))

(defun s-type-sequence-to-deflist (type-form def-name)
  (let* ((subdef-type-form (second type-form))
         (subdef-name (s-type-to-fty-name-symbol subdef-type-form)))
    (append
     (list 'fty::deflist def-name
           :elt-type subdef-name
           :true-listp t)
     (if (nil-is-member-of-s-type-p subdef-type-form)
         '(:elementp-of-nil t)
       '(:elementp-of-nil nil))
     )))

(defun s-type-option-to-deftagsum-option (type-form def-name)
  (let* ((subdef-type-form (second type-form))
         (subdef-name (s-type-to-fty-name-symbol subdef-type-form)))
     (list 'fty::deftagsum def-name
           `(:some ((get ,subdef-name)))
           '(:none ()))))

(defun s-type-map-to-defomap (type-form def-name)
  (let* ((domain-type-form (second type-form))
         (range-type-form (third type-form))
         (domain-name (s-type-to-fty-name-symbol domain-type-form))
         (range-name (s-type-to-fty-name-symbol range-type-form)))
    (list 'fty::defomap def-name
          :key-type domain-name
          :val-type range-name)))

(defun s-type-to-def (type-form)
  ;; The type spec should have been validated, but let's recheck in case
  ;; this function is being used elsewhere
  (b* (((unless (valid-full-type-form-p type-form))
        (er hard? 'top-level "invalid type form to s-type-to-def"))
       ;; might as well precompute the top def-name
       ;; but we will need to compute the subtype name(s)
       ;; separately since unary and binary are different
       (def-name (s-type-to-fty-name-symbol type-form)))
    (cond ((eq (car type-form) 's-type-set)
           (s-type-set-to-defset type-form def-name))
          ((eq (car type-form) 's-type-sequence)
           (s-type-sequence-to-deflist type-form def-name))
          ((eq (car type-form) 's-type-option)
           (s-type-option-to-deftagsum-option type-form def-name))
          ((eq (car type-form) 's-type-map)
           (s-type-map-to-defomap type-form def-name)))))

;; mapcar s-type-to-def
(defun s-types-to-defs (type-forms)
  (if (atom type-forms)
      nil
  (cons (s-type-to-def (car type-forms))
        (s-types-to-defs (cdr type-forms)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; create fty defining forms for all unnamed types mentioned in an S-expression

(defun defining-forms-for-unnamed-types-in-s-exp (def)
  (let ((type-forms (gather-types-top def)))
    (s-types-to-defs type-forms)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Product types
;; aka Record type

;; EM 2020-10-02: changed (field type) from (sym sym) to (string (typemacro ..)).
(defun field+type-to-field+type (field+type-pair)
  (list (intern-syndef (first field+type-pair))
        ;; NOTE: converting the type name to pred is not needed here.
        ;; The examples in the xdoc for defprod and other fty defining forms
        ;; use the recognizer pred to specify the component types,
        ;; but it works fine to specify them as the type names.
        ;; We suspect that the xdoc examples are a holdover from defaggregate.
        (let ((type-indicator (second field+type-pair)))
          (s-type-to-fty-name-symbol type-indicator))
        ))

(defun field+type-to-field+type-list (list-of-field+type-pairs)
  (if (atom list-of-field+type-pairs) nil
    (cons (field+type-to-field+type (first list-of-field+type-pairs))
          (field+type-to-field+type-list (rest list-of-field+type-pairs)))))

;; Sum types
;; aka disjoint union, variant, enumeration (in Rust)
;; The standard fty macro is deftagsum, which is a sum of products.
;; We duplicate this, so a sum type here is really a sum of products.
;; If you want one of the alternatives in the sum type to be a non-product type,
;; the typical usage is to make a field named GET whose value type is the
;; non-product, so you end up with an extra layer of a product with one field.

;; an S-expr ("NAME" ((field1 type1) (field2 type2) ..)) is converted to
;; (:NAME ((field1 type1) (field2 type2) ..))
;;
;; EM 2020-10-02: added call to field+type-to-field+type-list
;; Also (intern (symbol-name ..)) --> (intern (..)) since the subprod name is
;; already a string now.
(defun name+prodspec-to-sum-alternative (name+prodspec-pair)
  (list (intern (first name+prodspec-pair) "KEYWORD")
        (field+type-to-field+type-list (second name+prodspec-pair))))

(defun name+prodspecs-to-sum-alternatives-list (list-of-name+prodspec-pairs)
  (if (atom list-of-name+prodspec-pairs) nil
    (cons (name+prodspec-to-sum-alternative (first list-of-name+prodspec-pairs))
          (name+prodspecs-to-sum-alternatives-list (rest list-of-name+prodspec-pairs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parse the remaining macro args and extract keyword arguments
;; :shortdoc "doc" :longdoc "docdoc", which get returned as
;; (:short "doc") and (:long "docdoc") if there.
;; If either is not there, it is returned as the empty list.

(defun extract-doc-keyword-args-from-list--long (short-already l)
  (if (eq :LONGDOC (first l))
      (mv short-already (list ':long (second l)) (cddr l))
    (mv short-already () l)))

(defun extract-doc-keyword-args-from-list--short (long-already l)
  (if (eq :SHORTDOC (first l))
      (mv (list ':short (second l)) long-already (cddr l))
    (mv () long-already l)))

(defun extract-doc-keyword-args-from-list--both (l)
  (if (eq :SHORTDOC (first l))
      (extract-doc-keyword-args-from-list--long (list ':short (second l)) (cddr l))
    (if (eq :LONGDOC (first l))
        (extract-doc-keyword-args-from-list--short (list ':long (second l)) (cddr l))
      (mv () () l))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macros defining named composite types

;; IMPORTANT NOTE: when converting fty::defprod to make-product-type,
;; you must take out the parentheses grouping the (field type) pairs.
;; This makes make-product-type and make-sum-type more consistent.

#|| Moved to composite-types.lisp

;; EM 2020-10-02 changed name to string.  Now component-type should be
;; (s-type-ref "type-name-string")
(defmacro make-product-type (name &rest field+type-list)
    (mv-let (short-doc long-doc f+t-list)
        (extract-doc-keyword-args-from-list--both field+type-list)
      (let ((type-defs (defining-forms-for-unnamed-types-in-s-exp field+type-list)))
        `(encapsulate ()
           ,@type-defs
           (fty::defprod ,(intern-syndef name) ,@short-doc ,@long-doc
                         ,(field+type-to-field+type-list f+t-list)
                         ;; Prepend a tag so we can check types at runtime.
                         ;; This should not be necessary once we have static type
                         ;; checking, but it could be helpful for debugging.
                         :tag ,(intern name "KEYWORD"))))))
||#

#||  Moved to composite-types.lisp
(defmacro make-sum-type (name &rest name+prodspec-list)
    (mv-let (short-doc long-doc n+p-list)
        (extract-doc-keyword-args-from-list--both name+prodspec-list)
      (let ((type-defs (defining-forms-for-unnamed-types-in-s-exp name+prodspec-list)))
        `(encapsulate ()
           ,@type-defs
           (fty::deftagsum ,(intern-syndef name) ,@short-doc ,@long-doc
                           ,@(name+prodspecs-to-sum-alternatives-list n+p-list))))))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macro defining named subtype.

;; When defining a named subtype with fty::defsubtype, the restriction predicate
;; can be given as the name of a predicate or as a lambda expression.
;; However, make-subtype only uses the lambda expression case.
;; The lambda expression is constructed from the restriction-var
;; (the param name) and the restriction expression.

;; name is a string, and it goes in the syndef package
;; supertype is a type descriptor
;; restriction-var is a string
;; restriction is an expression with one free variable that defuns an
;;   additional predicate.  (That free variable must match restriction-var.
;;   We don't do that validation here, but it should be done somewhere.)
;; base-value is a canonical representative instance of the type
;;   that must satisfy both the supertype's recognizer predicate
;;   and the restriction predicate (and is returned by the "fixing function").
;;   Note, literal strings and literal integers are just ACL2 strings and
;;   integers (without reader macro base changes),
;;   and literal characters and booleans are specified with s-literal-char,
;;   s-literal-true, and s-literal-false.
;;
(defmacro make-subtype (name supertype restriction-var restriction base-value
                        &key (shortdoc '() shortdocp)
                             (longdoc '() longdocp))
  (let ((type-defs (defining-forms-for-unnamed-types-in-s-exp supertype))
        (expanded-component-type (s-type-to-fty-name-symbol supertype)))

    `(with-output :off :all :on error :gag-mode t 
       (encapsulate ()
         ,@type-defs
         (fty::defsubtype ,(intern-syndef name)
           :supertype ,expanded-component-type
           :restriction (lambda (,(intern-syndef restriction-var))
                          ,(translate-term restriction))
           :fix-value ,(translate-term base-value)
           ,@(if shortdocp (list :short shortdoc) ())
           ,@(if longdocp (list :long longdoc) ())
           )))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macros defining named composite types
;; that are NOT currently supposed to have top-level definitions
;; in the Syntheto language.

;; NOT Part of Syntheto Language, do not use!
;; It is here in case we want to add more kinds of named top-level
;; type definitions.
;; WARNING: this should be kept in sync with the relevant parts of
;; s-type-option-to-deftagsum-option.
;;
;; component-type should be an (s-type-xx ..) form
(defmacro make-option-type (name component-type
                             &key (shortdoc '() shortdocp)
                                  (longdoc '() longdocp))
  (let ((type-defs (defining-forms-for-unnamed-types-in-s-exp component-type))
        (expanded-component-type (s-type-to-fty-name-symbol component-type)))
    `(with-output :off :all :on error :gag-mode t
       (encapsulate ()
         ,@type-defs
         (fty::deftagsum ,(intern-syndef name)
            ,@(if shortdocp (list :short shortdoc) ())
            ,@(if longdocp (list :long longdoc) ())
            (:some ((get ,expanded-component-type)))
            (:none ()))))))

;; NOT Part of Syntheto Language, do not use!
;; It is here in case we want to add more kinds of named top-level
;; type definitions.
;; WARNING: this should be kept in sync with the relevant parts of
;; s-type-set-to-defset.
;;
;; component-type should be an (s-type-xx ..) form
(defmacro make-set-type (name component-type
                              &key (shortdoc '() shortdocp)
                                   (longdoc '() longdocp))

  (let ((type-defs (defining-forms-for-unnamed-types-in-s-exp component-type))
        (expanded-component-type (s-type-to-fty-name-symbol component-type)))

    `(with-output :off :all :on error :gag-mode t
       (encapsulate ()
         ,@type-defs
         (fty::defset ,(intern-syndef name)
           ,@(if shortdocp (list :short shortdoc) ())
           ,@(if longdocp (list :long longdoc) ())
           :elt-type ,expanded-component-type
           :elementp-of-nil ,(nil-is-member-of-s-type-p component-type))))))

;; NOT Part of Syntheto Language, do not use!
;; It is here in case we want to add more kinds of named top-level
;; type definitions.
;; WARNING: this should be kept in sync with the relevant parts of
;; s-type-sequence-to-deflist.
;;
;; component-type should be an (s-type-xx ..) form
(defmacro make-sequence-type (name component-type
                              &key (shortdoc '() shortdocp)
                                   (longdoc '() longdocp))

  (let ((type-defs (defining-forms-for-unnamed-types-in-s-exp component-type))
        (expanded-component-type (s-type-to-fty-name-symbol component-type)))

    `(with-output :off :all :on error :gag-mode t
       (encapsulate ()
         ,@type-defs
         (fty::deflist ,(intern-syndef name)
           ,@(if shortdocp (list :short shortdoc) ())
           ,@(if longdocp (list :long longdoc) ())
           :elt-type ,expanded-component-type
           :true-listp t
           :elementp-of-nil ,(nil-is-member-of-s-type-p component-type))))))

;; NOT Part of Syntheto Language, do not use!
;; It is here in case we want to add more kinds of named top-level
;; type definitions.
;; WARNING: this should be kept in sync with the relevant parts of
;; s-type-map-to-defomap
;;
;; component-type should be an (s-type-xx ..) form
(defmacro make-map-type (name domain-element-type range-element-type
                         &key (shortdoc '() shortdocp)
                              (longdoc '() longdocp))

  (let* ((prerequisite-type-defs (defining-forms-for-unnamed-types-in-s-exp
                                   (list domain-element-type range-element-type)))
         (expanded-component-type1 (s-type-to-fty-name-symbol domain-element-type))
         (expanded-component-type2 (s-type-to-fty-name-symbol range-element-type)))

    `(with-output :off :all :on error :gag-mode t
       (encapsulate ()
         ,@prerequisite-type-defs
         (fty::defomap ,(intern-syndef name)
           ,@(if shortdocp (list :short shortdoc) ())
           ,@(if longdocp (list :long longdoc) ())
           :key-type ,expanded-component-type1
           :val-type ,expanded-component-type2)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recursive Types

;; For now, a "recursive types" definition takes a sequence of
;; product and sum types, and results in a fty::deftypes.

;; Syntheto has no equivalent of fty::deflist, so some of the most common
;; kinds of recursive types that use lists between the recursive types
;; will have to use on-the-fly type definitions the lists like
;; sequence(mystruct).  Those type definitions will also need to be
;; in the deftypes, and may need to have a measure.

;; Probably make-recursive-types will need to add :measure to its subs.
;; However, how can it analyze the subs to know what measure to add?

;; Since the product and sum types can have "on-the-fly" component types,
;; there could be some unusual dependencies.  A good set of tests
;; would be helpful.

;; The initial goal is to be able to defun some recursive types
;; that are usable in practice.  For example, the aircraft maintenance
;; scheduling example.  As we get experience with these, we can
;; see what a more thorough solution will involve.

;; TODO.
