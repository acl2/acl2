;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (3rd May, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

;; (defsection fty-support
;;   :parents (verified)
;;   :short "Supports for ftytypes"

;;----------------------------------------------------------
;;     datatypes for storing fty related functions

;; guards and returns are assumed, not checked.
(defprod fty-info
  ((name symbolp :default nil) ;; without suffixes
   (category symbolp :default nil) ;; :prod :option :list :alist
   (type symbolp :default nil) ;; :recognizer :fix :field :constructor :others
   (guards symbol-listp :default nil) ;; input type
   (returns symbolp :default nil))) ;; output type

(defalist fty-info-alist
  :key-type symbolp
  :val-type fty-info-p
  :true-listp t)

;;----------------------------------------------------------
;;     datatypes for storing fty types information

(defalist fty-field-alist
  :key-type symbolp
  :val-type symbolp
  :true-listp t)

(defalist fty-prod-alist
  :key-type symbolp
  :val-type fty-field-alist-p
  :true-listp t)

(defalist fty-list-alist
  :key-type symbolp
  :val-type symbolp
  :true-listp t)

(defprod fty-alist
  ((key-type symbolp)
   (val-type symbolp)))

(defalist fty-alist-alist
  :key-type symbolp
  :val-type fty-alist-p
  :true-listp t)

(defalist fty-option-alist
  :key-type symbolp
  :val-type symbolp ;; the :some type
  :true-listp t)

(defprod fty-types
  ((prod fty-prod-alist-p)
   (list fty-list-alist-p)
   (alist fty-alist-alist-p)
   (option fty-option-alist-p)))

;;----------------------------------------------------------
;;                      functions

(define make-inline ((name symbolp))
  :returns (i symbolp)
  (b* ((name (symbol-fix name))
       (name-str (symbol-name name))
       (pkg-str (symbol-package-name name))
       (inlined-name (concatenate 'string name-str "$INLINE")))
    (intern$ inlined-name pkg-str)))

(verify-termination fty::flexprod-field-p)
(verify-termination fty::flexprod-field->acc-name$inline)
(verify-termination fty::flexprod-field->type$inline)
(verify-termination fty::flexprod-field-p)
(verify-termination fty::flexprod-field->name$inline)
(verify-termination fty::flexprod-p)
(verify-termination fty::flexprod->kind$inline)
(verify-termination fty::flexsum-p)
(verify-termination fty::flexsum->fix$inline)
(verify-termination fty::flexsum->pred$inline)
(verify-termination fty::flexsum->name$inline)
(verify-termination fty::flexlist-p)
(verify-termination fty::flexlist->fix$inline)
(verify-termination fty::flexlist->pred$inline)
(verify-termination fty::flexlist->name$inline)
(verify-termination fty::flexalist-p)
(verify-termination fty::flexalist->fix$inline)
(verify-termination fty::flexalist->pred$inline)
(verify-termination fty::flexalist->name$inline)
(verify-termination fty::flexprod->fields$inline)
(verify-termination fty::flexsum->prods$inline)
(verify-termination fty::flextypes-p)
(verify-termination fty::flextypes->types$inline)

(define generate-field-acc ((name symbolp)
                            (pred symbolp)
                            (field fty::flexprod-field-p)
                            (acc fty-info-alist-p))
  :returns (alst fty-info-alist-p)
  (b* ((acc (fty-info-alist-fix acc))
       ((unless (fty::flexprod-field-p field)) acc)
       (name (symbol-fix name))
       (pred (symbol-fix pred))
       (field-acc (fty::flexprod-field->acc-name field))
       ((unless (symbolp field-acc))
        (prog2$ (er hard? 'fty=>generate-field-acc "Should be a symbolp: ~q0"
                    field-acc)
                acc))
       (field-type (fty::flexprod-field->type field))
       ((unless (symbolp field-type))
        (prog2$ (er hard? 'fty=>generate-field-acc "Should be a symbolp: ~q0"
                    field-type)
                acc)))
    (acons
     (make-inline field-acc)
     (make-fty-info :name name
                    :category :prod
                    :type :field
                    :guards (list pred)
                    :returns field-type)
     acc)))

(define generate-field-acc-lst ((name symbolp)
                                (pred symbolp)
                                (fields t)
                                (acc fty-info-alist-p))
  :returns (alst fty-info-alist-p)
  (b* ((acc (fty-info-alist-fix acc))
       ((unless (consp fields)) acc)
       ((cons first rest) fields)
       ((unless (fty::flexprod-field-p first))
        (generate-field-acc-lst name pred rest acc)))
    (generate-field-acc-lst name pred rest
                            (generate-field-acc name pred first acc))))

(define generate-field-type-lst ((fields t))
  :returns (g symbol-listp)
  (b* (((unless (consp fields)) nil)
       ((cons first rest) fields)
       ((unless (fty::flexprod-field-p first))
        (generate-field-type-lst rest))
       (type (fty::flexprod-field->type first))
       ((unless (symbolp type))
        (er hard? 'fty=>generate-field-type-lst "Should be a symbolp: ~q0"
            type)))
    (cons type
          (generate-field-type-lst rest))))

(define generate-prod ((name symbolp)
                       (pred symbolp)
                       (fix symbolp)
                       (prod fty::flexprod-p)
                       (acc fty-info-alist-p))
  :returns (alst fty-info-alist-p)
  (b* ((acc (fty-info-alist-fix acc))
       ((unless (fty::flexprod-p prod)) acc)
       (name (symbol-fix name))
       (pred (symbol-fix pred))
       (fix (symbol-fix fix))
       (fields (fty::flexprod->fields prod))
       (acc-p
        (acons
         pred (make-fty-info :name name
                             :category :prod
                             :type :recognizer
                             :guards nil
                             :returns 'booleanp)
         acc))
       (acc-fix
        (acons (make-inline fix)
               (make-fty-info :name name
                              :category :prod
                              :type :fix
                              :guards (list pred)
                              :returns pred)
               acc-p))
       (acc-const
        (acons name (make-fty-info :name name
                                   :category :prod
                                   :type :fix
                                   :guards (generate-field-type-lst fields)
                                   :returns pred)
               acc-fix)))
    (generate-field-acc-lst name pred fields acc-const)))

;; defoption has functions:
;; maybe-xxx-p, maybe-xxx-fix$inline
(define generate-option ((name symbolp)
                         (pred symbolp)
                         (fix symbolp)
                         (acc fty-info-alist-p))
  :returns (alst fty-info-alist-p)
  (b* ((name (symbol-fix name))
       (pred (symbol-fix pred))
       (fix (symbol-fix fix))
       (acc (fty-info-alist-fix acc))
       (acc-p
        (acons
         pred (make-fty-info :name name
                             :category :option
                             :type :recognizer
                             :guards nil
                             :returns 'booleanp)
         acc)))
    (acons (make-inline fix)
           (make-fty-info :name name
                          :category :option
                          :type :fix
                          :guards (list pred)
                          :returns pred)
           acc-p)))

(define generate-flexsum ((type fty::flexsum-p)
                          (acc fty-info-alist-p))
  :returns (alst fty-info-alist-p)
  (b* ((acc (fty-info-alist-fix acc))
       ((unless (fty::flexsum-p type)) acc)
       (prods (fty::flexsum->prods type))
       ((unless (consp prods))
        (prog2$ (cw "Warning: empty defprod ~q0" prods) acc))
       (name (fty::flexsum->name type))
       ((unless (symbolp name))
        (prog2$ (er hard? 'fty=>generate-flexsum "Should be a symbolp: ~q0"
                    name)
                acc))
       (pred (fty::flexsum->pred type))
       ((unless (symbolp pred))
        (prog2$ (er hard? 'fty=>generate-flexsum "Should be a symbolp: ~q0"
                    pred)
                acc))
       (fix (fty::flexsum->fix type))
       ((unless (symbolp fix))
        (prog2$ (er hard? 'fty=>generate-flexsum "Should be a symbolp: ~q0"
                    fix)
                acc))
       ((unless (or (equal (len prods) 1)
                    (equal (len prods) 2)))
        (prog2$ (cw "Warning: tagsum not supported ~q0" prods) acc)))
    (cond
     ((and (equal (len prods) 1) (fty::flexprod-p (car prods)))
      (generate-prod name pred fix (car prods) acc))
     ((and (equal (len prods) 2)
           (fty::flexprod-p (car prods)) (fty::flexprod-p (cadr prods))
           (or (and (equal (fty::flexprod->kind (car prods)) :none)
                    (equal (fty::flexprod->kind (cadr prods)) :some))
               (and (equal (fty::flexprod->kind (cadr prods)) :none)
                    (equal (fty::flexprod->kind (car prods)) :some))))
      (generate-option name pred fix acc))
     (t acc))))

(define generate-flexlist ((flexlst fty::flexlist-p)
                           (acc fty-info-alist-p))
  :returns (alst fty-info-alist-p)
  (b* ((acc (fty-info-alist-fix acc))
       ((unless (fty::flexlist-p flexlst)) acc)
       (name (fty::flexlist->name flexlst))
       ((unless (symbolp name))
        (prog2$ (er hard? 'fty=>generate-flexlist "Should be a symbolp: ~q0"
                    name)
                acc))
       (pred (fty::flexlist->pred flexlst))
       ((unless (symbolp pred))
        (prog2$ (er hard? 'fty=>generate-flexlist "Should be a symbolp: ~q0"
                    pred)
                acc))
       (fix (fty::flexlist->fix flexlst))
       ((unless (symbolp fix))
        (prog2$ (er hard? 'fty=>generate-flexlist "Should be a symbolp: ~q0"
                    fix)
                acc))
       (acc-p
        (acons
         pred (make-fty-info :name name
                             :category :option
                             :type :recognizer
                             :guards nil
                             :returns 'booleanp)
         acc)))
    (acons (make-inline fix)
           (make-fty-info :name name
                          :category :option
                          :type :fix
                          :guards (list pred)
                          :returns pred)
           acc-p)))

(define generate-flexalist ((flexalst fty::flexalist-p)
                            (acc fty-info-alist-p))
  :returns (alst fty-info-alist-p)
  (b* ((acc (fty-info-alist-fix acc))
       ((unless (fty::flexalist-p flexalst)) acc)
       (name (fty::flexalist->name flexalst))
       ((unless (symbolp name))
        (prog2$ (er hard? 'fty=>generate-flexalist "Should be a symbolp: ~q0"
                    name)
                acc))
       (pred (fty::flexalist->pred flexalst))
       ((unless (symbolp pred))
        (prog2$ (er hard? 'fty=>generate-flexalist "Should be a symbolp: ~q0"
                    pred)
                acc))
       (fix (fty::flexalist->fix flexalst))
       ((unless (symbolp fix))
        (prog2$ (er hard? 'fty=>generate-flexalist "Should be a symbolp: ~q0"
                    fix)
                acc))
       (acc-p
        (acons
         pred (make-fty-info :name name
                             :category :option
                             :type :recognizer
                             :guards nil
                             :returns 'booleanp)
         acc)))
    (acons (make-inline fix)
           (make-fty-info :name name
                          :category :option
                          :type :fix
                          :guards (list pred)
                          :returns pred)
           acc-p)))

;; This function finds a list of fty symbols from the global table flextypes.
;; It then constructs functions about these fty types.
;; Supported fty types are: defprod, defoption, deflist, defalist.
;; The defprod is restricted to be non-recursive.
(define generate-fty-info-alist-rec ((fty symbol-listp) (acc fty-info-alist-p)
                                     (state))
  :returns (alst fty-info-alist-p)
  :measure (len fty)
  (b* ((fty (symbol-list-fix fty))
       (acc (fty-info-alist-fix acc))
       ((unless (consp fty)) acc)
       ((cons first rest) fty)
       (flex-table (table-alist 'fty::flextypes-table (w state)))
       ((unless (alistp flex-table)) acc)
       (exist? (assoc-equal first flex-table))
       ((unless exist?)
        (prog2$ (cw "Warning: fty type not found ~q0" first)
                acc))
       (agg (cdr exist?))
       ((unless (fty::flextypes-p agg))
        (prog2$ (er hard? 'fty=>generate-fty-info-alist-rec "Should be a flextypes, but ~
  found ~q0" agg) acc))
       (types (fty::flextypes->types agg))
       ((if (or (atom types) (> (len types) 1)))
        (prog2$ (er hard? 'fty=>generate-fty-info-alist-rec "Possible recursive types ~
    found, not supported in Smtlink yet.")
                acc))
       (type (car types)))
    (cond
     ;; if it's a flexsum, its a defprod or a defoption
     ((fty::flexsum-p type)
      (generate-fty-info-alist-rec rest (generate-flexsum type acc) state))
     ;; if it's a flexlist, it's a deflist
     ((fty::flexlist-p type)
      (generate-fty-info-alist-rec rest (generate-flexlist type acc) state))
     ;; if it's a flexalist, it's a defalist
     ((fty::flexalist-p type)
      (generate-fty-info-alist-rec rest (generate-flexalist type acc) state))
     ;; else, ignore
     (t (generate-fty-info-alist-rec rest acc state)))))

  (define fncall-of-flextype ((fn-name symbolp) (fty-info fty-info-alist-p))
    :returns (flex? booleanp)
    :short "Checking if a function call is a flextype related call.  These calls
    will be translated directly to SMT solver, therefore won't need to be expanded."
    :long "<p>There are five categories of flextype supported in Smtlink.  Examples
    are taken from @('fty::defprod'), @('fty::deflist'), @('fty::defalist')
    and @('fty::defoption').</p>
    <p>Supported functions for @(see fty::defprod):</p>
    <ul>
    <li>Type recognizers, for example, @('sandwich-p')</li>
    <li>Fixing functions, for example, @('sandwich-fix$inline')</li>
    <li>Constructors, for example, @('sandwich')</li>
    <li>Field accessors, for example, @('sandwich->bread$inline')</li>
    </ul>
    <p>Supported functions for @(see fty::deflist): (note Smtlink only support
    deflists that are true-listp)</p>
    <ul>
    <li>Type recognizers, for example, @('foolist-p')</li>
    <li>Fixing functions, for example, @('foolist-fix$inline')</li>
    <li>Constructor @('cons')</li>
    <li>Destructors @('car') and @('cdr')</li>
    <li>Base list @('nil'), this is not a function, but needs special care</li>
    </ul>
    <p>Supported functions for @(see fty::defalist): (note Smtlink only support
    defalists that are true-listp)</p>
    <ul>
    <li>Type recognizers, for example, @('fooalist-p')</li>
    <li>Fixing functions, for example, @('fooalist-fix$inline')</li>
    <li>Constructor @('acons')</li>
    <li>Destructors are not supported for alists due to soundness issues</li>
    <li>Search function @('assoc-equal'), we support this version of assoc for
    simplicity</li>
    </ul>
    <p>Supported functions for @(see fty::defoption): </p>
    <ul>
    <li>Type recognizers, for example, @('maybe-foop')</li>
    <li>Fixing functions, for example, @('maybe-foo-fix$inline')</li>
    <li>Nothing case @('nil'), this is not a function, but needs special
    care</li>
    </ul>"
    (b* ((fn-name (symbol-fix fn-name))
         (fty-info (fty-info-alist-fix fty-info))
         ;; if it's a function existing in the fty-info table
         (item (assoc-equal fn-name fty-info))
         ((if item) t)
         ;; special cases
         ((if (and
               ;; lists
               (equal fn-name 'CONS)
               (equal fn-name 'CAR)
               (equal fn-name 'CDR)
               ;; alists
               (equal fn-name 'ACONS)
               (equal fn-name 'ASSOC-EQUAL)
               ))
          t))
      nil))

(define typedecl-of-flextype ((fn-name symbolp) (fty-info fty-info-alist-p))
  :returns (flex? booleanp)
  (b* ((fn-name (symbol-fix fn-name))
       (fty-info (fty-info-alist-fix fty-info))
       (item (assoc-equal fn-name fty-info))
       ((unless item) nil)
       (info (cdr item))
       (type (fty-info->type info)))
    (if (equal type :recognizer)
        t
      nil)))

;;  )
