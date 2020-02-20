; Copyright (C) 2009-2015, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Defsum: a macro for defining recursive data types
; by Sol Swords & William Cook

; Please email bug reports to sswords@cs.utexas.edu.
;
; For primary documentation of the content of this book, see the :doc
; topics defsum, defsums, and pattern-match.
;
; This book defines the macros defsum and defsums which can be used to
; define recursive data types analogous to type definitions in
; Haskell. These types are recursive labeled sums of products.
;
; Proofs written using the new type are based on the abstract model of
; constructors, recognizers, and field access.  The underlying list
; representation is (almost) completely hidden: the definitions and
; executable-counterparts of functions operating on the list structure are
; disabled. As a result, proofs using the type only require reasoning about the
; type itself, not its representation. Unlike records, but like Haskell,
; components of a data type cannot be modified once constructed.
;
; A simple example, which defines a simple list structure, is:
;
; (defsum my-list
;    (my-empty)
;    (my-cons car (my-list-p cdr)))
;
; The first item of each list is the *constructor* and the remaining
; items are fields. Constructors with no arguments, like my-empty,
; represent abstract constants.  For each constructor, a recognizer is
; also defined, and functions to extract fields from the constructed
; values. The overall type also has a recognizer. Here
; are all the functions defined by the above:
;
; constructors: my-empty, my-cons
; recognizers: my-list-p, my-empty-p, my-cons-p
; fields: my-cons-car, my-cons-cdr
;
; The sum recognizer my-list-p recognizes only completely well-formed
; structures.  The product recognizers my-empty and my-cons, on the other hand,
; only check the top level "shape" and do not check any types.  (my-cons-p x),
; for example, equals (and (true-listp x) (= (len x) 3) (eq (car x) 'my-cons)).
;
; The example above corresponds to the standard Haskell definition:
;     data MyList a = MyEmpty | MyCons a (MyList a)
; Haskell also allows the fields to be named:
;     data MyList a = MyEmpty | MyCons { car :: a, cdr :: MyList a }
;
; Here is another example:
;
; (defsum person
;   (student (stringp name) (integerp year) major)
;   (professor name degree-year school (symbolp topic))
;   (administrator name title (person-p manager)))
;
; Using this example, we can illustrate the matching form:
;
; (pattern-match x
;               ((student nm yr maj) body1)
;               ((professor a b c d) body2)
;               ((administrator p d q) body3)
;               (& body4))
;
; This is still work in progress. Related work (which could be much more
; appropriate for any given application) includes the following (see the files
; for proper attribution):
;
; the records book, distributed as books/misc/records.lisp; the typed records
; book, distributed as books/workshops/2004/greve/support/defrecord.lisp; and
; the structures book, distributed as books/data-structures/structures.lisp.
;
; To see how this library works in detail, you can examine the events
; introduced by a defsum form such as, in this example, the above "my-list"
; form.  The following will print out the list of events:
; (include-book "defsum")
; (include-book "defsum-thms")
; :trans1 (defsum my-list
;           (my-empty)
;           (my-cons car (my-list-p cdr)))


(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "pattern-match")
(include-book "types-misc")

(set-ignore-ok t)
(set-bogus-mutual-recursion-ok t)

(defun product-type (x)
  (declare (xargs :guard (consp x)))
  (car x))

(in-theory (disable product-type (:executable-counterpart product-type)))

(program)





;; Uniform ways of accessing the structure information.

;; The top-level structure is just a list of sums.  The global keyword-alist is
;; passed around separately.



;; Each sum in the list has just a name and a product list.  The global keyword
;; alist is stored separately.  In a mutual-defsum, the keywords are assumed to
;; be shared.
(defun sum-name (sum)
  (car sum))

(defun sum-products (sum)
  (cdr sum))

(defun sum-recognizer (sum)
  (appsyms (list (sum-name sum) 'p)))


;; Each product also has an associated recognizer; by convention if the product
;; name (and constructor name) is foo, the recognizer is foo-p.  However, a
;; recognizer (possibly predefined) can also be specified with the :recognizer
;; keyword.

(defun sym-recognizer (sym)
  (appsyms (list sym 'p)))

(defun product-recognizer (product)
  (or (kwassoc :recognizer nil (product-kwalist product))
      (sym-recognizer (product-name product))))


;; That concludes the functions for accessing elements of the internal
;; structure.  Now we need the ability to transform user input into the
;; internal structure.




(defun defsum-munge-product (product)
    (mv-let (product kwalist)
            (strip-keywords product)
            (cons
             ;; name and component listing
             (cons (car product)
                   (munge-components (cdr product)))
             ;; keywords
             kwalist)))

(defun defsum-munge-products (products)
  (if (atom products)
      nil
    (cons (defsum-munge-product (car products))
          (defsum-munge-products (cdr products)))))

;; Separates external functions from product list (or sum list for
;; defsums.)  Thus we don't allow the sume "defun-p" or the
;; constructor defun.
(defun strip-extfns (products)
  (if (atom products)
      (mv nil nil)
    (mv-let (prods extfns)
            (strip-extfns (cdr products))
            (if (and (consp (car products))
                     (eq (caar products) 'defun))
                (mv prods (cons (car products) extfns))
              (mv (cons (car products) prods) extfns)))))

;; Converts top-level defsum input into internal form.  Returns the
;; list of sums (just one in this case), the list of functions to be
;; defined in the mutual-recursion with the sum recognizer, and the
;; global keyword alist.
(defun defsum-munge-input (name rest)
  (mv-let (products kwalist)
          (strip-keywords rest)
          (mv-let (products extfns)
                  (strip-extfns products)
                  (mv (list (cons name (defsum-munge-products products)))
                      extfns
                      kwalist))))

(defun defsums-munge-sums (sums)
  (if (atom sums)
      nil
    (cons
     (cons (caar sums) (defsum-munge-products (cdar sums)))
     (defsums-munge-sums (cdr sums)))))

;; Converts top-level defsums input into internal form.  Returns the
;; sums, the functions to be defined with the sums, and the global
;; keyword alist.
(defun defsums-munge-input (args)
  (mv-let (sums kwalist)
          (strip-keywords args)
          (mv-let (sums extfns)
                  (strip-extfns sums)
                  (mv (defsums-munge-sums sums) extfns kwalist))))





;; recognzier name given a constructor name; product-recognzier is preferred
(defun recognizer-name (sym)
  (appsyms (list sym 'p)))

;; add the -p to a list of symbols
(defun recognizer-list (syms)
  (if (atom syms)
      nil
    (cons (recognizer-name (car syms))
          (recognizer-list (cdr syms)))))



;; Constructor call given a complete product declaration
(defun constructor-call (product)
  (cons (product-name product)
        (components-names (product-components product))))


(defun product-accessor-list (product)
  (accessor-list product (product-components product)))

(defun accessor-call-list (product components)
  (if (consp components)
      (cons `(,(accessor-name product (car components)) x)
            (accessor-call-list product (cdr components)))
    nil))



;; Constructor definition for a product.
(defun constructor-def (product guard-opt hons-opt compact-opt)
  (let* ((constr (product-name product))
         (args (components-names (product-components product)))
         (cons (if hons-opt 'hons 'cons)))
  `(defun ,constr ,args
     ,@(if guard-opt
           `((declare (xargs :guard t)))
         nil)
     ,(if compact-opt
           `(,cons (quote ,constr)
                   ,(argtree cons args))
         `(,(if hons-opt 'hons-list 'list)
           (quote ,constr) ,@args)))))





;; Definition for the recognizer of a product
(defun product-recognizer-def (product compact-opt)
  (let* ((nargs (len (product-components product)))
         (tests (if compact-opt
                    (cons `(consp x) (recog-consp-list nargs `(cdr x)))
                  `((true-listp x) (= (length x) ,(1+ nargs))))))
  `(defun ,(product-recognizer product) (x)
     (declare (xargs :guard t))
     (and ,@tests
          (eq (car x) (quote ,(product-name product)))))))


;; Definition of the nth accessor for a product
(defun accessor-def (product component ncomps n guard-opt accessor-opt compact-opt)
  (let ((rec (product-recognizer product))
        (acc (if compact-opt (tree-accessor n ncomps `(cdr x) nil)
               `(nth ,n x))))
  `(defun ,(accessor-name product component) (x)
     ,@(if guard-opt
           `((declare (xargs :guard (,rec x))))
         nil)
     ,@(if (and guard-opt accessor-opt)
           `((mbe :logic (and (,rec x) ,acc)
                  :exec ,acc))
         (if accessor-opt
             `((and (,rec x) ,acc))
           `(,acc))))))

;; Define all accessors for a product
(defun accessors-def (product components ncomps n guard-opt accessor-opt compact-opt)
  (if (consp components)
      (cons (accessor-def product (car components) ncomps n guard-opt
                          accessor-opt compact-opt)
            (accessors-def product (cdr components) ncomps (1+ n) guard-opt
                           accessor-opt compact-opt))
    nil))

(defun product-function-defs (product guard-opt hons-opt compact-opt accessor-opt)
  (let* ((kwalist (product-kwalist product))
         (predef (kwassoc :predef nil (product-kwalist product)))
         (recog (kwassoc :recognizer nil kwalist)))
    (append (and (not (or recog predef))
                 (list (product-recognizer-def product compact-opt)))
            (and (not predef)
                 (cons (constructor-def product guard-opt hons-opt compact-opt)
                       (accessors-def product
                                      (product-components product)
                                      (len (product-components product)) 1
                                      guard-opt
                                      accessor-opt compact-opt))))))


;; Makes the pattern matcher macro for the product.
(defun product-pattern-matcher (product guard-opt)
  `(def-pattern-match-constructor
     ,(if (eq guard-opt :fast)
          (appsyms (list (product-name product) 'slow))
        (product-name product))
     ,(product-recognizer product) ,(product-accessor-list product)))


(defun product-compound-rec-thm (product compact-opt)
  `(defthm ,(appsyms (list (product-name product) 'p 'compound-recognizer))
     (implies (,(product-recognizer product) x)
              ,(if compact-opt `(consp x)
                 `(and (consp x)
                       (true-listp x))))
     :rule-classes :compound-recognizer))

(defun function-call-list (fn-preargs list postargs)
  (if (atom list)
      nil
    (cons (append fn-preargs (cons (car list) postargs))
          (function-call-list fn-preargs (cdr list) postargs))))

(defun args-cons-count (nargs)
  (if (or (zp nargs) (= nargs 1))
      0
    (let ((flo (floor nargs 2)))
      (+ 1 (args-cons-count flo)
         (args-cons-count (- nargs flo))))))

(defun constructor-acl2-count-thm (product compact-opt)
  (let* ((nargs (len (product-components product)))
         (conses (if compact-opt (1+ (args-cons-count nargs))
                   (1+ nargs))))
  `(defthm ,(appsyms (list (product-name product) 'acl2-count))
     (equal (acl2-count ,(constructor-call product))
            (+ ,conses
               ,@(function-call-list '(acl2-count)
                                     (components-names (product-components product))
                                     nil))))))

(defun accessor-short-circuit-thm (product component)
  (let* ((acc (accessor-name product component))
         (rec (product-recognizer product)))
    `(defthm ,(appsyms (list 'not rec acc))
       (implies (not (,rec x))
                (equal (,acc x) nil)))))

(defun accessor-short-circuit-thms (product components)
  (if (consp components)
      (cons (accessor-short-circuit-thm product (car components))
            (accessor-short-circuit-thms product (cdr components)))
    nil))

(defun accessor-acl2-count-thm (product component)
  (let ((acc (accessor-name product component))
        (recognizer (product-recognizer product)))
    `(defthm ,(appsyms (list acc 'acl2-count))
     (implies (,recognizer x)
              (< (acl2-count (,acc x))
                 (acl2-count x)))
     :hints (("Goal" :in-theory
              (e/d (acl2-count-car-cdr-of-cons-linear
                    acl2-count-nth-of-len-2-or-greater-linear)
                   (nth acl2-count))))
     :rule-classes (:rewrite :linear))))

(defun accessor-acl2-count-thms (product components)
  (if (consp components)
      (cons (accessor-acl2-count-thm product (car components))
            (accessor-acl2-count-thms product (cdr components)))
    nil))

(defun product-recognizer-constructor-thm (product)
  (let ((constructor (product-name product))
        (constr-call (constructor-call product))
        (recognizer (product-recognizer product)))
  `(defthm ,(appsyms (list recognizer constructor))
     (,recognizer ,constr-call))))


;; destructor elimination rule
(defun product-elim-thm (product compact-opt)
  (let ((recognizer (product-recognizer product))
        (name (product-name product))
        (components (product-components product)))
    (if (consp components)
        `(defthm ,(appsyms (list name 'elim))
           (implies (,recognizer x)
                    (equal (,name
                            ,@(accessor-call-list product components))
                           x))
           ,@(if compact-opt
                 nil
               `(:hints (("Goal" :in-theory
                          (enable nth-open
                                  len-0-true-listp-not-x)))))
           :rule-classes (:rewrite :elim))
      `(defthm ,(appsyms (list name 'unique))
         (implies (,recognizer x)
                  (equal x (,name)))
         :rule-classes :forward-chaining))))

(defun product-type-thms (product)
  (let ((recognizer (product-recognizer product))
        (name (product-name product))
        (call (constructor-call product))
        (components (product-components product)))
    `((defthm ,(appsyms (list recognizer 'product-type))
        (implies (,recognizer x)
                 (equal (product-type x) ',name)))
      (defthm ,(appsyms (list 'product-type recognizer))
        (implies (not (equal (product-type x) ',name))
                 (not (,recognizer x))))
      (defthm ,(appsyms (list name 'product-type))
        (equal (product-type ,call) ',name))
      (defthm ,(appsyms (list name 'equal-product-type))
        (implies (not (equal (product-type ,call) (product-type x)))
                 (not (equal ,call x)))))))



(defun accessor-constructor-thm (product component)
  (let ((acc (accessor-name product component))
        (constr-call (constructor-call product))
        (arg (component-name component)))
  `(defthm ,(appsyms (list acc (product-name product)))
     (equal (,acc ,constr-call)
            ,arg))))


(defun constructor-component-thm (product component)
  (let ((name (product-name product))
        (arg (component-name component)))
  `(defthm ,(appsyms (list name 'not-equal arg))
     (not (equal ,(constructor-call product)
                 ,arg))
     ;; :hints (("Goal" :use (:instance ,(appsyms (list name arg
;;                                                      'acl2-count))
;;                                      (x ,(constructor-call product)))
;;               :in-theory (disable ,(appsyms (list name arg 'acl2-count)))))
     )))

(defun product-component-thm (product component)
  (let* ((name (product-name product))
         (acc (accessor-name product component))
         (recognizer (product-recognizer product)))
  `(defthm ,(appsyms (list name 'not-equal acc))
     (implies (,recognizer x)
              (not (equal (,acc x) x)))
     :hints (("Goal" :use ,(appsyms (list name 'elim))
              :in-theory (disable ,name ,acc ,recognizer))))))

;; if one of the components is different, the product is different
(defun arg-difference-thm (product component)
  (let ((arg (component-name component))
        (name (product-name product))
        (acc (accessor-name product component)))
    `(defthm ,(appsyms (list 'difference arg name))
       (implies (not (equal ,arg (,acc x)))
                (not (equal ,(constructor-call product) x))))))

(defun product-arg-thms (product components)
  (if (consp components)
      `(,(accessor-constructor-thm product (car components))
        ,(constructor-component-thm product (car components))
        ,(product-component-thm product (car components))
        ,(arg-difference-thm product (car components))
        ,@(product-arg-thms product (cdr components)))
    nil))

(defun product-theorems (product accessor-opt compact-opt)
  (let* ((kwalist (product-kwalist product))
         (predef (kwassoc :predef nil kwalist))
         (recog (kwassoc :recognizer nil kwalist))
         (components (product-components product)))
    `(,@(and (not predef) (not recog)
             (list (product-compound-rec-thm product compact-opt)))
        ,@(and (not predef)
               (list (constructor-acl2-count-thm product compact-opt)))
        ,@(accessor-acl2-count-thms product components)
        ,@(if accessor-opt
              (accessor-short-circuit-thms product components)
            nil)
        ,(product-recognizer-constructor-thm product)
        ,(product-elim-thm product compact-opt)
        ,@(product-arg-thms product components))))



(defun basic-product-defs (product guard-opt accessor-opt hons-opt compact-opt)
  (append (product-function-defs product guard-opt hons-opt compact-opt accessor-opt)
          (product-theorems product accessor-opt compact-opt)
          (list (product-pattern-matcher product guard-opt))))

(defmacro defproduct (&rest product)
  (let ((product (defsum-munge-product product)))
    `(progn
       ,@(basic-product-defs product
                             (kwassoc :guard nil (product-kwalist product))
                             (kwassoc :short-accessors t (product-kwalist
                                                          product))
                             (kwassoc :hons nil (product-kwalist product))
                             (kwassoc :compact t (product-kwalist product))))))

(defun basic-products-defs (products guard-opt accessor-opt hons-opt
                                     compact-opt)
  (if (atom products)
      nil
    (append (basic-product-defs (car products) guard-opt accessor-opt hons-opt
                                compact-opt)
            (basic-products-defs (cdr products) guard-opt accessor-opt hons-opt
                                 compact-opt))))

(defun products-type-thms (products)
  (if (endp products)
      nil
    (append (product-type-thms (car products))
            (products-type-thms (cdr products)))))

;; list of statements about types from a product declaration
(defun type-checklist1 (components)
  (if (consp components)
      (let* ((component (car components))
             (type (component-type component))
             (name (component-name component)))
        (if type
            (cons (list type name)
                  (type-checklist1 (cdr components)))
          (type-checklist1 (cdr components))))
    nil))

;; type information from a product declaration, in the form of a single term:
;; t, a single predicate call, or (and ...).
(defun type-checklist (components)
  (let ((checklist (type-checklist1 components)))
    (if checklist
        (if (consp (cdr checklist))
            `(and ,@checklist)
          (car checklist))
      t)))

;; The clauses for pattern-matching for the sum recognizer
(defun sum-recognizer-clause (product guard-opt)
  (let* ((type-checklist (type-checklist (product-components product)))
         (constr (constructor-call product))
         (pattern (if (eq guard-opt :fast)
                      (cons (appsyms (list (car constr) 'slow))
                            (cdr constr))
                    constr)))
    (list pattern type-checklist)))

(defun sum-recognizer-clauses (products guard-opt)
  (if (consp products)
      (cons (sum-recognizer-clause (car products) guard-opt)
            (sum-recognizer-clauses (cdr products) guard-opt))
    nil))

;; Definition of the recognizer for a sum (with type information)
(defun sum-recognizer-def (sum guard-opt)
  `(defun ,(sum-recognizer sum) (x)
     (declare
      (xargs :measure (1+ (acl2-count x))
             ,@(if guard-opt
                   `(:guard t)
                 nil)
             :hints (("goal"
                      :in-theory
                      (enable
                       acl2-count-nth-of-len-2-or-greater-linear)))))
     (pattern-match x
       ,@(sum-recognizer-clauses (sum-products sum) guard-opt))))

(defun sum-recognizer-defs (sums guard-opt)
  (if (consp sums)
      (cons (sum-recognizer-def (car sums) guard-opt)
            (sum-recognizer-defs (cdr sums) guard-opt))
    nil))

;; if it's a mutual sum declaration or includes more functions for the mutual
;; recursion, then the mutual recursion for the sum recognizers. otherwise,
;; just the one sum recognizer function.
(defun sum-recognizers-def (sums extfns guard-opt)
  (if (and (= (len sums) 1) (not extfns))
      (sum-recognizer-def (car sums) guard-opt)
    `(mutual-recursion ,@(sum-recognizer-defs sums guard-opt)
                       ,@extfns)))


(defun sum-compound-rec-thm (sum compact-opt)
  (let ((sumname (sum-name sum))
        (recognizer (sum-recognizer sum)))
  `(defthm ,(appsyms (list sumname 'compound-recognizer))
     (implies (,recognizer x)
              ,(if compact-opt
                   `(consp x)
                 `(and (consp x)
                       (true-listp x))))
     :rule-classes :compound-recognizer)))

(defun sum-compound-rec-thms (sums compact-opt)
  (if (consp sums)
      (cons (sum-compound-rec-thm (car sums) compact-opt)
            (sum-compound-rec-thms (cdr sums) compact-opt))
    nil))


(defun recognizer-call-list (products)
  (if (consp products)
      (cons `(,(product-recognizer (car products))
              x)
            (recognizer-call-list (cdr products)))
    nil))

(defun sum-possibility-thm (sum)
  (let ((rec-list (recognizer-call-list (sum-products sum)))
        (name (sum-name sum))
        (recognizer (sum-recognizer sum)))
    `(defthm ,(appsyms (list name 'possibilities))
       (implies (,recognizer x)
                ,(if (consp (cdr rec-list))
                     `(or ,@rec-list)
                   (car rec-list)))
       :rule-classes :forward-chaining)))

(defun sum-possibility-thms (sums)
  (if (consp sums)
      (cons (sum-possibility-thm (car sums))
            (sum-possibility-thms (cdr sums)))
    nil))

(defun product-fast-recs (products sumrec)
  (if (atom products)
      nil
    (let* ((product (car products))
           (pname (product-name product))
           (prec (product-recognizer product))
           (prfast (appsyms (list prec 'fast))))
      (append
       `((defun ,prfast (x)
           (declare (xargs :guard (,sumrec x)))
           (mbe :exec (eq (car x) ',pname)
                :logic (,prec x)))
         (def-pattern-match-constructor ,pname ,prfast
           ,(product-accessor-list product)))
       (product-fast-recs (cdr products) sumrec)))))

(defun product-fast-recs-sums (sums)
  (if (atom sums)
      nil
    (append (product-fast-recs (sum-products (car sums))
                               (sum-recognizer (car sums)))
            (product-fast-recs-sums (cdr sums)))))


;; type checklist of accessor calls for a product
(defun accessor-type-checklist1 (product components)
  (if (consp components)
      (let ((ctype (component-type (car components)))
            (prodname (product-name product))
            (acc (accessor-name product (car components))))
        (if ctype
            (cons `(,ctype (,acc x))
                  (accessor-type-checklist1 product (cdr components)))
          (accessor-type-checklist1 product (cdr components))))
    nil))

;; the above, in the form of a single term
(defun accessor-type-checklist (product)
  (let ((checklist (accessor-type-checklist1 product (product-components product))))
    (if (consp checklist)
        (if (consp (cdr checklist))
            `(and ,@checklist)
          (car checklist))
      t)))

(defun strip-product-recognizers (products)
  (if (atom products)
      nil
    (cons (product-recognizer (car products))
          (strip-product-recognizers (cdr products)))))

;; if the term is a well-typed instance of the product type, then accessor
;; calls have the given types.  This function returns a singleton list
;; containing the theorem or nil if there are no types to worry about.
(defun accessor-type-thm (sum product)
  (let ((checklist (accessor-type-checklist product))
        (prodname (product-name product))
        (srecog (sum-recognizer sum))
        (sumname (sum-name sum))
        (recogs (strip-product-recognizers (sum-products sum)))
        (precog (product-recognizer product)))
    (if (eq checklist t)
        nil
      `((defthm ,(appsyms (list sumname prodname 'accessor-types))
          (implies (and (,srecog x)
                        (,precog x))
                   ,checklist)
          :hints (("Goal" :in-theory (disable ,@recogs ,prodname
                                              ,@(product-accessor-list
                                                 product))
                   :expand ((,srecog x)))))))))


(defun accessor-type-thms (sum products)
  (if (consp products)
      (append (accessor-type-thm sum (car products))
              (accessor-type-thms sum (cdr products)))
    nil))

(defun all-accessor-type-thms (sums)
  (if (consp sums)
      (append (accessor-type-thms (car sums) (sum-products (car sums)))
              (all-accessor-type-thms (cdr sums)))
    nil))

(defun negated-list (list)
  (if (atom list)
      nil
    (cons (list 'not (car list))
          (negated-list (Cdr list)))))


(defun negated-accessor-type-list (product)
  (let ((nlist (negated-list (accessor-type-checklist1
                              product (product-components product)))))
    (if (atom nlist)
        nil
      (if (atom (cdr nlist))
          (car nlist)
        `(or ,@nlist)))))

(defun bad-typing-thm (sum product)
  (let ((badtypes (negated-accessor-type-list product))
        (srecog (sum-recognizer sum))
        (precog (product-recognizer product))
        (sumname (sum-name sum))
        (pname (product-name product)))
    (if badtypes
        `((defthm ,(appsyms (list pname 'not sumname))
            (implies (and (,precog x)
                          ,badtypes)
                     (not (,srecog x)))
            :hints (("Goal" :in-theory
                     (disable ,precog
                              ,@(product-accessor-list product))))))
      nil)))

(defun sum-bad-typing-thms (sum products)
  (if (consp products)
      (append (bad-typing-thm sum (car products))
              (sum-bad-typing-thms sum (cdr products)))
    nil))

(defun all-bad-typing-thms (sums)
  (if (consp sums)
      (append (sum-bad-typing-thms (car sums) (sum-products (car sums)))
              (all-bad-typing-thms (cdr sums)))
    nil))






(defun sum-recognizer-constructor-thm (sum product)
  (let ((constructor (product-name product))
        (precog (product-recognizer product))
        (constr-call (constructor-call product))
        (recognizer (sum-recognizer sum))
        (type-checklist (type-checklist (product-components product))))
    `(defthm ,(appsyms (list recognizer constructor))
       ,(if (eq t type-checklist)
            `(,recognizer ,constr-call)
          `(iff (,recognizer ,constr-call) ,type-checklist))
     :hints (("Goal" :in-theory (disable ,precog ,constructor
                                         ,@(product-accessor-list product)))))))






(defun sum-recognizer-constructor-thms (sum products)
  (if (consp products)
      `(,(sum-recognizer-constructor-thm sum (car products))
        ,@(sum-recognizer-constructor-thms sum (cdr products)))
    nil))

(defun all-post-constructor-thms (sums)
  (if (consp sums)
      (append (sum-recognizer-constructor-thms (car sums) (sum-products (car sums)))
              (all-post-constructor-thms (cdr sums)))
    nil))

(defun recognizer-negate-list (products arg)
  (if (consp products)
      (cons `(not (,(product-recognizer (car products)) ,arg))
            (recognizer-negate-list (cdr products) arg))
    nil))

(defun not-equal-constructor-list (term products)
  (if (consp products)
      (cons `(not (equal ,term ,(constructor-call (car products))))
            (not-equal-constructor-list term (cdr products)))
    nil))

(defun exclusion-thm (product all-products)
  (let* ((rest (remove-equal product all-products))
         (not-prod (recognizer-negate-list
                    rest (constructor-call product)))
         (not-equal (not-equal-constructor-list
                     (constructor-call product) rest))
         (not-recs (recognizer-negate-list rest 'x))
         (name (product-name product))
         (recognizer (product-recognizer product)))
    (if not-prod
        `((defthm ,(appsyms (list name 'not-others))
            ,(if (= (len not-prod) 1)
                 (car not-prod)
               `(and ,@not-prod))
          :hints (("Goal" :in-theory (disable true-listp len))))

          (defthm ,(appsyms (list name 'not-other-constructors))
            ,(if (= (len not-equal) 1)
                 (car not-equal)
               `(and ,@not-equal)))
          (defthm ,(appsyms (list recognizer 'not-others))
            (implies (,recognizer x)
                     ,(if (= (len not-recs) 1)
                          (car not-recs)
                        `(and ,@not-recs)))
            :hints (("Goal" :in-theory (disable true-listp len)))
            :rule-classes :forward-chaining)
          )
      nil)))



(defun exclusion-thms (products all-products)
  (if (consp products)
      (append (exclusion-thm (car products) all-products)
              (exclusion-thms (cdr products) all-products))
    nil))

;; ;; strip the "-p" from the end of a sum/product recognizer name if the name's
;; ;; too short we'll get nil as the exploded name, which translates to the empty
;; ;; symbol '||, so don't use that as the name of a sum and also use a one- or
;; ;; two-letter predicate for the type of one of your fields.
;; (defun recognizer-strip (recname)
;;   (intern (coerce (butlast (explode-atom recname 10) 2) 'string) "ACL2"))


(defun name-matching-recognizer (sums predtyp)
  (if (atom sums)
      nil
    (if (eq predtyp (sum-recognizer (car sums)))
        (sum-name (car sums))
      (name-matching-recognizer (cdr sums) predtyp))))

(defun recursive-arg-and-call-list (sums components)
  (if (consp components)
      (let ((predtyp (component-type (car components))))
        (mv-let (args calls)
                (recursive-arg-and-call-list sums (cdr components))
                (if predtyp
                  (let ((typname (name-matching-recognizer sums predtyp))
                        (argname (component-name (car components))))
                    (if typname
                        (mv (cons argname args)
                            (cons `(,(appsyms (list typname 'measure)) ,argname)
                                  calls))
                      (mv (cons '& args) calls)))
                (mv (cons '& args) calls))))
    (mv nil nil)))

(defun measure-clause-list (sums products)
  (if (consp products)
      (let ((rest (measure-clause-list sums (cdr products))))
        (mv-let (args calls)
                (recursive-arg-and-call-list sums (product-components (car products)))
                (if (consp calls)
                    (cons `((,(product-name (car products)) ,@args)
                            (+ 1 ,@calls))
                          rest)
                  rest)))
    '((& 1))))


(defun measure-def (sum sums guard-opt)
  (let ((clauses (measure-clause-list sums (sum-products sum))))
    `(defun ,(appsyms (list (sum-name sum) 'measure)) (x)
       (declare (xargs :measure (acl2-count x)
                       ,@(case guard-opt
                           (:fast `(:guard (,(sum-recognizer sum) x)))
                           (nil nil)
                           (otherwise`(:guard t))))
                ,@(if (= (len clauses) 1)
                      `((ignore x))
                    nil))
       (pattern-match x
         ,@clauses))))

(defun measure-defs (sums all-sums guard-opt)
  (if (consp sums)
      (cons (measure-def (car sums) all-sums guard-opt)
            (measure-defs (cdr sums) all-sums guard-opt))
    nil))

(defun measure-mrec (sums guard-opt)
  (let ((mdefs (measure-defs sums sums guard-opt)))
    (if (= (len mdefs) 1)
        (car mdefs)
      `(mutual-recursion ,@mdefs))))

(defun field-measure-ineqs (sums measure prodname prodargs)
  (if (consp prodargs)
      (let* ((predtyp (component-type (car prodargs)))
             (arg (component-name (car prodargs)))
             (pred (name-matching-recognizer sums predtyp))
             (meas (appsyms (list pred 'measure)))
             (acc (appsyms (list prodname arg))))
        (if pred
            (cons `(< (,meas (,acc x))
                      (,measure x))
                  (field-measure-ineqs sums measure prodname
                                       (cdr prodargs)))
          (field-measure-ineqs sums measure prodname
                               (cdr prodargs))))
    nil))

(defun field-measure-thms (sums measure products)
  (if (consp products)
      (let ((ineqs (field-measure-ineqs sums measure (product-name (car products))
                                        (product-components (car products)))))
        (if ineqs
            (cons
             `(defthm ,(appsyms (list (product-name (car products)) 'measure-decr))
                (implies (,(product-recognizer (car products)) x)
                         ,(if (consp (cdr ineqs))
                              `(and ,@ineqs)
                            (car ineqs))))
             (field-measure-thms sums measure (cdr products)))
          (field-measure-thms sums measure (cdr products))))
    nil))

(defun sum-measure-thms (sums all-sums)
  (if (consp sums)
      (append
       (field-measure-thms all-sums (appsyms (list (sum-name (car sums)) 'measure))
                           (sum-products (car sums)))
       (sum-measure-thms (cdr sums) all-sums))
    nil))


(defun updater-defun (prodname args accs n guard-opt)
  (let ((name (nth (1- n) args)))
  `(defun ,(appsyms (list 'update prodname name)) (new x)
     ,@(if guard-opt
           `((declare (xargs :guard (,(recognizer-name prodname) x)
                             :guard-hints (("Goal" :in-theory (enable ,prodname))))))
         nil)
     (mbe :exec (update-nth ,n new x)
          :logic (,prodname ,@(update-nth (1- n) 'new accs))))))


(defun product-updater-defuns (prodname args accs n guard-opt)
  (if (zp n)
      nil
    (cons (updater-defun prodname args accs n guard-opt)
          (product-updater-defuns prodname args accs (1- n) guard-opt))))

(defun updater-defuns (products guard-opt)
  (if (atom products)
      nil
    (let* ((prodname (product-name (car products)))
           (components (product-components (car products)))
           (arglist (components-names components)))
      (append (product-updater-defuns prodname arglist
                                      (accessor-call-list (car products) components)
                                      (len arglist) guard-opt)
              (updater-defuns (cdr products) guard-opt)))))




(defun sums-products (sums)
  (if (atom sums)
      nil
    (append (sum-products (car sums))
            (sums-products (cdr sums)))))

(defun sums-names (sums)
  (if (atom sums)
      nil
    (cons (sum-name (car sums))
          (sums-names (cdr sums)))))

(defun defsums-fn (sums kwalist extfns)
  (let* ((products (sums-products sums))
         (guard-option (kwassoc :guard t kwalist))
         (hons-opt (kwassoc :hons nil kwalist))
         (compact-opt (kwassoc :compact t kwalist))
         (accessor-option (kwassoc :short-accessors t kwalist))
         (update-option (kwassoc :updatable nil kwalist))
         (arith-option (kwassoc :arithmetic t kwalist))
         (theory-name (appsyms (sums-names sums)))
         (before-label (appsyms (list 'before theory-name)))
        )
  `(encapsulate
    nil
; The use of set-bogus-measure-ok was added by Matt K. 2/20/2016, because ACL2
; started disallowing measures on non-recursive functions by default.
    (set-bogus-measure-ok t)
    (deflabel ,before-label)
    (local (in-theory (enable product-type (:executable-counterpart
                                            product-type))))
    ,@(if arith-option
          `((local (include-book
                    "arithmetic/top-with-meta" :dir :system)))
        nil)
    ,@(basic-products-defs products guard-option accessor-option hons-opt compact-opt)

    ,(sum-recognizers-def sums extfns guard-option)

    ,@(sum-compound-rec-thms sums compact-opt)

    ,@(sum-possibility-thms sums)

    ,@(exclusion-thms products products)

    ,@(all-accessor-type-thms sums)

    ,@(all-bad-typing-thms sums)

    ;; ,@(constructor-defs products guard-option)

    ,@(all-post-constructor-thms sums)

    (deftheory ,(appsyms (list theory-name 'functions))
      (rules-of-type :DEFINITION
                     (set-difference-theories
                      (current-theory :here)
                      (current-theory ',before-label))))

    ;; We want fast recognizer function definitions enabled but not executable
    ;; counterparts.
    ,@(if (eq guard-option :fast)
          (product-fast-recs-sums sums)
        nil)

    (deftheory ,(appsyms (list theory-name 'executable-counterparts))
      (rules-of-type :EXECUTABLE-COUNTERPART
                     (set-difference-theories
                      (current-theory :here)
                      (current-theory ',before-label))))

    (deftheory ,(appsyms (list theory-name 'inductions))
      (rules-of-type :INDUCTION
                     (set-difference-theories
                      (current-theory :here)
                      (current-theory ',before-label))))


    (deftheory ,(appsyms (list theory-name 'theorems))
      (set-difference-theories (set-difference-theories
                                (current-theory :here)
                                (current-theory ',before-label))
                               (union-theories
                                (theory ',(appsyms (list theory-name
                                                        'executable-counterparts)))
                                (union-theories
                                 (theory ',(appsyms (list theory-name
                                                         'functions)))
                                 (theory ',(appsyms (list theory-name 'inductions)))))))

    ,@(products-type-thms products)

    (deftheory ,(appsyms (list theory-name 'product-type-theorems))
      (set-difference-theories (current-theory :here)
                               (current-theory ',(appsyms (list theory-name 'theorems)))))


    (in-theory (disable ,(appsyms (list theory-name 'functions))
                        ,(appsyms (list theory-name
                                        'executable-counterparts))
                        ,(appsyms (list theory-name 'product-type-theorems))))

    ,@(and (not extfns)
           `(,(measure-mrec sums guard-option)
             ,@(sum-measure-thms sums sums)))

    ,@(if update-option
          (updater-defuns products guard-option)
        nil)

    (deftheory ,(appsyms (list theory-name 'entire-theory))
      (set-difference-theories (universal-theory :here)
                               (universal-theory ',before-label)))
    )))




(defxdoc defsum
  :parents (miscellaneous)
  :short "Define a recursive data type similar to a Haskell type definition."
  :long "<p>Example:</p>

 @({
 (include-book \"tools/defsum\" :dir :system)
 (set-ignore-ok :warn)
 (defsum my-list
   (my-empty)
   (my-cons car (my-list-p cdr)))
 })

<p>This declaration says that an object is of the type @('my-list') if it
is either of the type @('my-empty') or @('my-cons'), where @('my-empty')
is an empty structure and @('my-cons') is a structure with two fields:
the @('car'), an arbitrary object; and the @('cdr') which is of type
@('my-list').  In this case, recognizers @('my-list-p'), @('my-empty-p'),
and @('my-cons-p') are defined along with constructors @('my-empty') and
@('my-cons') and destructors @('my-cons-car') and @('my-cons-cdr').  The
necessary macros are also defined to enable pattern-matching using the
constructors (see @(see pattern-match)).  For mutually-recursive data types
see @(see defsums).  It may also be informative to look at the translated
version of a defsum form using :trans1.</p>

<p>Note that a defsum form produces several logic-mode events inside an
encapsulate.  Despite the author's best intentions, not every such
automatically-generated event will complete successfully.  If you
encounter a defsum form that fails, please email it to
sswords@cs.utexas.edu (with or without fixing the bug yourself.)</p>

<p>Several theorems about the new type are defined so as to enable
reasoning based on their abstract model rather than their underlying
list representation. For most reasoning these theorems should be
sufficient without enabling the function definitions or
executable-counterparts.  In case these do need to be enabled,
theories named (for the above example) @('my-list-functions') and
@('my-list-executable-counterparts') are defined.</p>

<p>In addition to the recognizer, constructor, and destructor functions,
a measure function is also defined which counts the number of nested
objects of the sum type.  In the example above, the measure function
is my-list-measure and the measure of an object is 1 if it is not a
my-cons, and 1 plus the measure of its my-cons-cdr if it is.</p>

<p>Defsum accepts some keyword arguments.  Be aware that not all
combinations of these arguments have been tested extensively.  Again,
please send bug reports to sswords@cs.utexas.edu if you find a defsum
form that does not succeed.</p>

<p>@(':arithmetic') - By default, each @('defsum') event expands to an
encapsulate which locally includes the book arithmetic/top-with-meta.
If an incompatible arithmetic book has already been included, this may
cause the defsum to fail.  But the other arithmetic book may also have
theorems that allow the defsum event to succeed if we don't attempt to
include the arithmetic book.  This can be done by setting
@(':arithmetic nil').</p>

<p>@(':guard') - may be set to @('t'), @('nil'), or @(':fast').  By default
it is set to @('t'), in which case minimal guards are set for all
functions.  If set to @('nil'), guards will not be verified for any
functions; this is useful in case some field type recognizers don't
have their guards verified.  If set to @(':fast'), an additional
recognizer for each product is defined named ``foo-p-fast'' if the
product is named foo.  This has a guard such that its argument must be
a valid sum object.  It is then logically equivalent to the other
recognizer, but in execution only checks that the symbol in the car of
the object matches the name of the product.  The pattern matcher for
each product then uses the fast recognizers.  Thus fast guards result
in a small (?) gain in performance in exchange for a (hopefully
trivial) degradation in logical complexity.</p>

<p>@(':short-accessors') - @('t') by default; may be set to @('nil').  If
@('t'), each field accessor first checks whether the object is of the
correct product type and returns nil if not.  This allows for an
additional theorem saying that if x is not of the correct product
type, then the accessor returns nil.  If @('nil'), the nth accessor
returns @('(nth n x)') regardless of x's type.  When guards are turned
on, this is implemented with an @('mbe') so there should be no
performance difference between the two options.  When guards are off,
performance will be somewhat better if this feature is turned off.</p>

<p>@(':compact') - By default, a defsum constructor makes a product
object by putting its components into a cons tree using n-1 conses,
but a prettier list representation is also supported which uses n
conses to store the elements in a flattened list which is easier to
read when printed.  Set @(':compact nil') if you prefer this
representation.</p>

<p>@(':hons') - If HONS mode is in use, the flag @(':hons t') causes all
defsum forms to be built with HONSes rather than regular conses.  See
@(see hons-and-memoization).</p>

<p>It may be necessary to include some function definition in a mutual
recursion with the sum recognizer function.  In this case simply put
the defun form inside the defsum form, i.e.</p>

 @({
 (defsum lisp-term
   (lisp-atom val)
   (func-app (symbolp function) (lisp-term-listp args))
   (defun lisp-term-listp (args)
     (declare (xargs :guard t))
     (if (atom args)
         (null args)
       (and (lisp-term-p (car args))
            (lisp-term-listp (cdr args))))))
 })

<p>If such a function is included, however, no measure function will be
defined for the sum.</p>

<p>Usually it is not necessary to specify a measure for such a function;
because there is currently no way of directly specifying the measure
for the sum's recognizer, specifying an exotic measure on such a
function is likely to fail.  If you come up against this limitation,
please send an example to sswords@cs.utexas.edu.</p>")

(defmacro defsum (name &rest defs)
  (mv-let
   (sum extfns kwalist) (defsum-munge-input name defs)
   (defsums-fn sum kwalist extfns)))



(defxdoc defsums
  :parents (miscellaneous)
  :short "Define a set of mutually-recursive data types."
  :long "<p>Example:</p>

 @({
 (defsums
   (my-term
    (my-atom val)
    (my-application (symbolp function) (my-term-list-p args)))
   (my-term-list
    (my-nil)
    (my-cons (my-term-p car) (my-term-list-p cdr))))
 })

<p>See @(see defsum).  This form is used when you want to define two or more
types which may be constructed from each other.  In the above example,
@('my-term') and @('my-term-list') could not be defined using independent
defsum forms; their recognizer functions need to be defined in a mutual
recursion.</p>

<p>Defsums accepts the same keyword arguments as defsum.</p>

<p>If you want some function to be defined inside the same mutual-recursion in
which the recognizers for each of the sums and products are defined, you may
insert the defun inside the def-mutual-sums form, i.e.</p>

 @({
 (defsums
  (foo
   (bla (bar-p x))
   (ble (foo-p x) (bar-p y)))
  (bar
   (blu (integerp k))
   (blo (symbolp f) (foo-list-p a)))
  (defun foo-list-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (null x)
      (and (foo-p (car x))
           (foo-list-p (cdr x))))))
 })

<p>Usually it is not necessary to specify a measure for such a function;
because there is currently no way of directly specifying the measures on the
sums' recognizers, specifying an exotic measure on such a function is likely to
fail.</p>

<p>As with defsum, def-mutual-sums requires the (possibly local) inclusion of
the defsum-thms book.</p>")

(defmacro defsums (&rest sums)
  (mv-let
   (sums extfns kwalist) (defsums-munge-input sums)
   (defsums-fn sums kwalist extfns)))



;; (logic)

;; ;; tests, so this book won't certify if it's broken


;; (local
;;  (defsum bla
;;    :guards :fast
;;    (foo (bla-p x) (integerp y))
;;    (bar a x (stringp y) (bla-p z))
;;    (abc)))

;; (local
;;  (defsums
;; ;   :updatable t
;;    (my-term
;;     (my-atom val)
;;     (my-application (symbolp function) (my-term-list-p args)))
;;    (my-term-list
;;     (my-nil)
;;     (my-cons (my-term-p car) (my-term-list-p cdr)))))

;; (local
;;  (defsum lisp-term
;;    :measure-multiplier 10
;;    (lisp-atom val)
;;    (func-app (symbolp function) (lisp-term-listp args))
;;    (defun lisp-term-listp (args)
;;      (declare (xargs :guard t
;;                      :measure (o* 10 (1+ (acl2-count args)))))
;;      (if (atom args)
;;          (null args)
;;        (and (lisp-term-p (car args))
;;             (lisp-term-listp (cdr args)))))))
