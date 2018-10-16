;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (3rd May, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/alists/alist-fix" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "basics")

(defsection fty-support
  :parents (verified)
  :short "Supports for ftytypes"

  (verify-termination fty::flexprod-field-p)
  (verify-termination fty::flexprod-field->acc-name$inline)
  (verify-termination fty::flexprod-field->type$inline)
  (verify-termination fty::flexprod-field-p)
  (verify-termination fty::flexprod-field->name$inline)
  (verify-termination fty::flexprod-p)
  (verify-termination fty::flexprod->type-name$inline)
  (verify-termination fty::flexprod->kind$inline)
  (verify-termination fty::flexsum-p)
  (verify-termination fty::flexsum->fix$inline)
  (verify-termination fty::flexsum->pred$inline)
  (verify-termination fty::flexsum->name$inline)
  (verify-termination fty::flexlist-p)
  (verify-termination fty::flexlist->fix$inline)
  (verify-termination fty::flexlist->pred$inline)
  (verify-termination fty::flexlist->name$inline)
  (verify-termination fty::flexlist->true-listp$inline)
  (verify-termination fty::flexlist->elt-type$inline)
  (verify-termination fty::flexlist->true-listp$inline)
  (verify-termination fty::flexalist-p)
  (verify-termination fty::flexalist->fix$inline)
  (verify-termination fty::flexalist->pred$inline)
  (verify-termination fty::flexalist->name$inline)
  (verify-termination fty::flexalist->true-listp$inline)
  (verify-termination fty::flexalist->key-type$inline)
  (verify-termination fty::flexalist->val-type$inline)
  (verify-termination fty::flexprod->fields$inline)
  (verify-termination fty::flexsum->prods$inline)
  (verify-termination fty::flextypes-p)
  (verify-termination fty::flextypes->types$inline)

  ;;----------------------------------------------------------
  ;;     datatypes for storing fty related functions

  ;; guards and returns are assumed, not checked.
  (defprod fty-info
    ((name symbolp :default nil) ;; without suffixes
     (category symbolp :default nil) ;; :prod :option :list :alist
     (type symbolp :default nil) ;; :recognizer :fix :field :constructor
     (guards symbol-listp :default nil) ;; input type
     (returns symbolp :default nil))) ;; output type

  (defalist fty-info-alist
    :key-type symbolp
    :val-type fty-info-p
    :true-listp t)

  ;;----------------------------------------------------------
  ;;                      functions

  (define make-inline ((name symbolp))
    :returns (i symbolp)
    (b* ((name (symbol-fix name))
         (name-str (symbol-name name))
         (pkg-str (symbol-package-name name))
         (inlined-name (concatenate 'string name-str "$INLINE")))
      (intern$ inlined-name pkg-str)))

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
                                     :type :constructor
                                     :guards (generate-field-type-lst fields)
                                     :returns pred)
                 acc-fix)))
      (generate-field-acc-lst name pred fields acc-const)))

  ;; defoption has functions:
  ;; maybe-xxx-p, maybe-xxx-fix$inline
  (define generate-option ((name symbolp)
                           (pred symbolp)
                           (fix symbolp)
                           (prod fty::flexprod-p)
                           (acc fty-info-alist-p))
    :returns (alst fty-info-alist-p)
    :guard-debug t
    (b* ((name (symbol-fix name))
         (pred (symbol-fix pred))
         (fix (symbol-fix fix))
         (acc (fty-info-alist-fix acc))
         ((unless (fty::flexprod-p prod)) acc)
         (fields (fty::flexprod->fields prod))
         ((unless (and (consp fields) (null (cdr fields))))
          (prog2$ (er hard? 'fty=>generate-option "fields incorrect for option some type: ~q0"
                      fields)
                  acc))
         (some-name (fty::flexprod->type-name prod))
         ((unless (symbolp some-name))
          (prog2$ (er hard? 'fty=>generate-option "Should be a symbolp: ~q0"
                      some-name)
                  acc))
         (field (car fields))
         ((unless (fty::flexprod-field-p field))
          (prog2$ (er hard? 'fty=>generate-option "needs to be a field: ~q0"
                      field)
                  acc))
         (accessor (fty::flexprod-field->acc-name field))
         ((unless (symbolp accessor))
          (prog2$ (er hard? 'fty=>generate-option "Should be a symbolp: ~q0"
                      accessor)
                  acc))
         (acc-type (fty::flexprod-field->type field))
         ((unless (symbolp acc-type))
          (prog2$ (er hard? 'fty=>generate-option "Should be a symbolp: ~q0"
                      acc-type)
                  acc))
         (acc-p
          (acons
           pred (make-fty-info :name name
                               :category :option
                               :type :recognizer
                               :guards nil
                               :returns 'booleanp)
           acc))
         (acc-some
          (acons some-name
                 (make-fty-info :name name
                                :category :option
                                :type :constructor
                                :guards (list acc-type)
                                :returns pred)
                 acc-p))
         (acc-some-val
          (acons (make-inline accessor)
                 (make-fty-info :name name
                                :category :option
                                :type :field
                                :guards (list pred) ;; this guard is not complete
                                :returns acc-type)
                 acc-some)))
      (acons (make-inline fix)
             (make-fty-info :name name
                            :category :option
                            :type :fix
                            :guards (list pred)
                            :returns pred)
             acc-some-val)))

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
             (and (equal (fty::flexprod->kind (car prods)) :none)
                  (equal (fty::flexprod->kind (cadr prods)) :some)))
        (generate-option name pred fix (cadr prods) acc))
       ((and (equal (len prods) 2)
             (fty::flexprod-p (car prods)) (fty::flexprod-p (cadr prods))
             (and (equal (fty::flexprod->kind (cadr prods)) :none)
                  (equal (fty::flexprod->kind (car prods)) :some)))
        (generate-option name pred fix (car prods) acc))
       (t acc))))

  (define generate-flexlist ((flexlst fty::flexlist-p)
                             (acc fty-info-alist-p))
    :returns (alst fty-info-alist-p)
    (b* ((acc (fty-info-alist-fix acc))
         ((unless (fty::flexlist-p flexlst)) acc)
         ((unless (fty::flexlist->true-listp flexlst))
          (prog2$ (er hard? 'fty=>generate-flexlist "Smtlink only supports ~
                             deflist that are true-listp. This one is not a ~
                             true-listp : ~q0"
                      flexlst)
                  acc))
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
                               :category :list
                               :type :recognizer
                               :guards nil
                               :returns 'booleanp)
           acc)))
      (acons (make-inline fix)
             (make-fty-info :name name
                            :category :list
                            :type :fix
                            :guards (list pred)
                            :returns pred)
             acc-p)))

  (define generate-flexalist ((flexalst fty::flexalist-p)
                              (acc fty-info-alist-p))
    :returns (alst fty-info-alist-p)
    (b* ((acc (fty-info-alist-fix acc))
         ((unless (fty::flexalist-p flexalst)) acc)
         ((unless (fty::flexalist->true-listp flexalst))
          (prog2$ (er hard? 'fty=>generate-flexalist "Smtlink only supports ~
                             deflist that are true-listp. This one is not a ~
                             true-listp : ~q0"
                      flexalst)
                  acc))
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
                               :category :alist
                               :type :recognizer
                               :guards nil
                               :returns 'booleanp)
           acc)))
      (acons (make-inline fix)
             (make-fty-info :name name
                            :category :alist
                            :type :fix
                            :guards (list pred)
                            :returns pred)
             acc-p)))

  ;; This function finds a list of fty symbols from the global table flextypes.
  ;; It then constructs functions about these fty types.
  ;; Supported fty types are: defprod, defoption, deflist, defalist.
  ;; The defprod is restricted to be non-recursive.
  (define generate-fty-info-alist-rec ((fty symbol-listp) (acc fty-info-alist-p)
                                       (flextypes-table alistp))
    :returns (alst fty-info-alist-p)
    :measure (len fty)
    (b* ((fty (symbol-list-fix fty))
         (acc (fty-info-alist-fix acc))
         ((unless (consp fty)) acc)
         ((cons first rest) fty)
         (flextypes-table (acl2::alist-fix flextypes-table))
         (exist? (assoc-equal first flextypes-table))
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
        (generate-fty-info-alist-rec rest (generate-flexsum type acc)
                                     flextypes-table))
       ;; if it's a flexlist, it's a deflist
       ((fty::flexlist-p type)
        (generate-fty-info-alist-rec rest (generate-flexlist type acc)
                                     flextypes-table))
       ;; if it's a flexalist, it's a defalist
       ((fty::flexalist-p type)
        (generate-fty-info-alist-rec rest (generate-flexalist type acc)
                                     flextypes-table))
       ;; else, ignore
       (t (generate-fty-info-alist-rec rest acc flextypes-table)))))

  (define fncall-of-flextype-special ((fn-name symbolp))
    :returns (special? booleanp)
    (if (or
         ;; lists
         (equal fn-name 'CONS)
         (equal fn-name 'CAR)
         (equal fn-name 'CDR)
         (equal fn-name 'CONSP)
         ;; alists
         (equal fn-name 'ACONS)
         (equal fn-name 'ASSOC-EQUAL)
         )
        t nil))

  (define fncall-of-flextype ((fn-name symbolp) (fty-info fty-info-alist-p))
    :parents (fty-support)
    :returns (flex? t)
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
         ((if item) t))
      ;; special cases
      (fncall-of-flextype-special fn-name))
    ///
    (more-returns
     (flex? (implies (and flex?
                          (symbolp fn-name)
                          (fty-info-alist-p fty-info))
                     (or (assoc-equal fn-name fty-info)
                         (fncall-of-flextype-special fn-name)))
            :name fncall-of-flextype-conclusion)))

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

  (define fixing-of-flextype ((fn-name symbolp) (fty-info fty-info-alist-p))
    :returns (mv (fixing? symbolp)
                 (guards symbol-listp))
    (b* ((fn-name (symbol-fix fn-name))
         (fty-info (fty-info-alist-fix fty-info))
         (item (assoc-equal fn-name fty-info))
         ((unless item) (mv nil nil))
         (info (cdr item))
         (type (fty-info->type info))
         ((unless (equal type :fix)) (mv nil nil)))
      (mv (fty-info->name info)
          (fty-info->guards info))))

  (define fixing-of-flextype-option ((fn-name symbolp)
                                     (fty-info fty-info-alist-p))
    :returns (fixing? symbolp)
    (b* ((fn-name (symbol-fix fn-name))
         (fty-info (fty-info-alist-fix fty-info))
         (item (assoc-equal fn-name fty-info))
         ((unless item) nil)
         (info (cdr item))
         (type (fty-info->type info))
         ((unless (equal type :fix)) nil))
      (equal (fty-info->category info) :option)))

  (define fncall-of-flextype-option ((fn-name symbolp)
                                     (fty-info fty-info-alist-p))
    :returns (option? booleanp)
    (b* ((fn-name (symbol-fix fn-name))
         (fty-info (fty-info-alist-fix fty-info))
         (item (assoc-equal fn-name fty-info))
         ((unless item) nil)
         (info (cdr item)))
      (equal (fty-info->category info) :option)))


  ;;----------------------------------------------------------
  ;;     datatypes for storing fty types information

  ;; All type names are without -p/p in the end

  (defalist fty-field-alist
    :key-type symbolp
    :val-type symbolp
    :true-listp t)

  ;; combine all
  (fty::deftagsum
   fty-type
   (:prod ((fields fty-field-alist-p)))
   (:list ((elt-type symbolp)))
   (:alist ((key-type symbolp)
            (val-type symbolp)))
   (:option ((some-type symbolp))))

  (defalist fty-types
    :key-type symbolp
    :val-type fty-type
    :true-listp t)

  (define generate-type-measure ((fty-info fty-info-alist-p)
                                 (acc fty-types-p))
    :returns (m natp)
    (b* ((fty-info (fty-info-alist-fix fty-info))
         (acc (fty-types-fix acc))
         (measure (- (len fty-info)
                     (len acc))))
      (if (<= measure 0) 0 measure))
    ///
    (more-returns
     (m (equal (generate-type-measure fty-info (fty-types-fix acc)) m)
        :name generate-type-measure-with-fty-types-fix)
     (m (implies (and (not (equal m 0)))
                 (< (generate-type-measure
                     fty-info
                     (acons name prod (fty-types-fix acc)))
                    m))
        :name generate-type-measure-increase-prod)
     (m (implies (and (not (equal m 0)))
                 (< (generate-type-measure
                     fty-info
                     (acons name option (fty-types-fix acc)))
                    m))
        :name generate-type-measure-increase-option)
     (m (implies (and (not (equal m 0)))
                 (< (generate-type-measure
                     fty-info
                     (acons name list (fty-types-fix acc)))
                    m))
        :name generate-type-measure-increase-list)
     (m (implies (and (not (equal m 0)))
                 (< (generate-type-measure
                     fty-info
                     (acons name alist (fty-types-fix acc)))
                    m))
        :name generate-type-measure-increase-alist)))

  (define SMT-types ()
    :returns (SMT-types alistp)
    *SMT-types*)


  (local
   (defthm crock1
     (implies (and (fty-info-alist-p fty-info)
                   (assoc-equal a fty-info))
              (consp (assoc-equal a fty-info))))
   )

  (local
   (defthm crock2
     (implies (and (fty-info-alist-p fty-info)
                   (assoc-equal a fty-info))
              (fty-info-p (cdr (assoc-equal a fty-info)))))
   )

  (define generate-fty-field-alist ((fields t)
                                    (fty-info fty-info-alist-p))
    :returns (mv (type-lst symbol-listp)
                 (field-alst fty-field-alist-p))
    (b* ((fty-info (fty-info-alist-fix fty-info))
         ((unless (consp fields))
          (mv nil nil))
         ((cons first rest) fields)
         ((unless (fty::flexprod-field-p first))
          (prog2$ (er hard? 'fty=>generate-fty-field-alist "Should be a field: ~q0"
                      first)
                  (mv nil nil)))
         (name (fty::flexprod-field->name first))
         ((unless (symbolp name))
          (prog2$ (er hard? 'fty=>generate-fty-field-alist "Should be a symbolp: ~q0"
                      name)
                  (mv nil nil)))
         (type (fty::flexprod-field->type first))
         ((unless (symbolp type))
          (prog2$ (er hard? 'fty=>generate-fty-field-alist "Should be a symbolp: ~q0"
                      type)
                  (mv nil nil)))
         ((mv cdr-type-lst cdr-field-alst)
          (generate-fty-field-alist rest fty-info))
         ;; is the type a basic type?
         (basic? (assoc-equal type (SMT-types)))
         ((if basic?)
          (mv (cons type cdr-type-lst)
              (acons name type cdr-field-alst)))
         (info (assoc-equal type fty-info))
         ((unless info)
          (prog2$ (er hard? 'fty=>generate-fty-field-alist "type ~p0 doesn't ~
                                 exist~%" type)
                  (mv nil nil)))
         (type-name (fty-info->name (cdr info)))
         )
      (mv (cons type-name cdr-type-lst)
          (acons name type-name cdr-field-alst)))
    ///
    )

  (local
   (defthm crock0
     (implies (consp name-lst)
              (< (len (cdr (symbol-list-fix name-lst)))
                 (len name-lst))))
   )

  (defines generate-fty-types-mutual
    :flag-local nil
    :flag-hints
    (("Goal"
      :in-theory (e/d () (generate-type-measure-increase-prod
                          generate-type-measure-increase-alist
                          generate-type-measure-increase-list
                          generate-type-measure-increase-option
                          (SMT-types)))
      :use ((:instance
             generate-type-measure-increase-prod
             (acc acc)
             (fty-info fty-info)
             (name (symbol-fix name))
             (prod
              (FTY-TYPE-PROD
               (MV-NTH
                1
                (GENERATE-FTY-FIELD-ALIST (CDR (ASSOC-EQUAL 'FTY::FIELDS (CDR PROD)))
                                          FTY-INFO)))))
            (:instance
             generate-type-measure-increase-list
             (acc acc)
             (fty-info fty-info)
             (name (fty::flexlist->name flexlst))
             (list (FTY-TYPE-LIST
                    (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                                        (CDR FLEXLST)))
                                                      FTY-INFO))))))
            (:instance
             generate-type-measure-increase-option
             (acc acc)
             (fty-info fty-info)
             (name (symbol-fix name))
             (option
              (FTY-TYPE-OPTION
               (FTY-INFO->NAME
                (CDR (ASSOC-EQUAL
                      (CDR (ASSOC-EQUAL 'TYPE
                                        (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                (CDR OPTION))))))
                      FTY-INFO))))))
            (:instance
             generate-type-measure-increase-alist
             (acc acc)
             (fty-info fty-info)
             (name (fty::flexalist->name flexalst))
             (alist
              (FTY-TYPE-ALIST
               (fty::flexalist->key-type flexalst)
               (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                                   (CDR FLEXALST)))
                                                 FTY-INFO)))))
             )
            (:instance
             generate-type-measure-increase-alist
             (acc acc)
             (fty-info fty-info)
             (name (fty::flexalist->name flexalst))
             (alist
              (FTY-TYPE-ALIST
               (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                                   (CDR FLEXALST)))
                                                 FTY-INFO)))
               (fty::flexalist->val-type flexalst)))
             )
            (:instance
             generate-type-measure-increase-alist
             (acc acc)
             (fty-info fty-info)
             (name (fty::flexalist->name flexalst))
             (alist
              (FTY-TYPE-ALIST
               (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                                   (CDR FLEXALST)))
                                                 FTY-INFO)))
               (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                                   (CDR FLEXALST)))
                                                 FTY-INFO))))))
            ))
     )

    (define generate-flexprod-type ((name symbolp)
                                    (prod fty::flexprod-p)
                                    (flextypes-table alistp)
                                    (fty-info fty-info-alist-p)
                                    (acc fty-types-p)
                                    (ordered-acc fty-types-p))
      :returns (mv (updated-acc fty-types-p)
                   (updated-ordered-acc fty-types-p))
      :measure (list (generate-type-measure fty-info acc) 0 0)
      :well-founded-relation acl2::nat-list-<
      :verify-guards nil
      (b* ((acc (fty-types-fix acc))
           (ordered-acc (fty-types-fix ordered-acc))
           (name (symbol-fix name))
           ((if (equal (generate-type-measure fty-info acc) 0))
            (prog2$ (er hard? 'fty=>generate-flexprod-type "accumulator exceeding
                                length of all fty functions.~%")
                    (mv acc ordered-acc)))
           ((if (assoc-equal name acc)) (mv acc ordered-acc))
           ((unless (fty::flexprod-p prod)) (mv acc ordered-acc))
           (fields (fty::flexprod->fields prod))
           ((mv type-lst field-alst)
            (generate-fty-field-alist fields fty-info))
           (new-prod
            (make-fty-type-prod :fields field-alst))
           (new-acc-1 (acons name new-prod acc))
           ((mv new-acc-2 updated-ordered-acc)
            (generate-fty-type-list type-lst flextypes-table fty-info new-acc-1
                                    ordered-acc)))
        (mv new-acc-2
            (acons name new-prod updated-ordered-acc))))

    (define generate-flexoption-type ((name symbolp)
                                      (option fty::flexprod-p)
                                      (flextypes-table alistp)
                                      (fty-info fty-info-alist-p)
                                      (acc fty-types-p)
                                      (ordered-acc fty-types-p))
      :returns (mv (updated-acc fty-types-p)
                   (updated-ordered-acc fty-types-p))
      :measure (list (generate-type-measure fty-info acc) 0 0)
      :well-founded-relation acl2::nat-list-<
      :verify-guards nil
      (b* ((acc (fty-types-fix acc))
           (ordered-acc (fty-types-fix ordered-acc))
           (name (symbol-fix name))
           ((if (equal (generate-type-measure fty-info acc) 0))
            (prog2$ (er hard? 'fty=>generate-flexprod-type "accumulator exceeding
                                length of all fty functions.~%")
                    (mv acc ordered-acc)))
           ((if (assoc-equal name acc)) (mv acc ordered-acc))
           ((unless (fty::flexprod-p option)) (mv acc ordered-acc))
           (fields (fty::flexprod->fields option))
           ((unless (and (consp fields) (null (cdr fields))))
            (prog2$ (er hard? 'fty=>generate-flexoption-type "A flexoption type ~
                                  with more than one field?: ~q0" fields)
                    (mv acc ordered-acc)))
           (first (car fields))
           ((unless (fty::flexprod-field-p first))
            (prog2$ (er hard? 'fty=>generate-flexoption-type "Found a none field
                                  type in a flexprod :field field: ~q0" first)
                    (mv acc ordered-acc)))
           (some-type (fty::flexprod-field->type first))
           ((unless (symbolp some-type))
            (prog2$ (er hard? 'fty=>generate-flexoption-type "Must be a symbol ~q0"
                        some-type)
                    (mv acc ordered-acc)))
           ;; is the type a basic type?
           (basic? (assoc-equal some-type (SMT-types)))
           ((if basic?)
            (mv (acons name
                       (make-fty-type-option :some-type some-type)
                       acc)
                (acons name
                       (make-fty-type-option :some-type some-type)
                       ordered-acc)))
           (some-info (assoc-equal some-type fty-info))
           ((unless some-info)
            (prog2$ (er hard? 'fty=>generate-flexoption-type "some-type ~p0 doesn't ~
                                 exist~%" some-type)
                    (mv acc ordered-acc)))
           (some-name (fty-info->name (cdr some-info)))
           (new-option
            (make-fty-type-option :some-type some-name))
           (new-acc-1 (acons name new-option acc))
           ((mv new-acc-2 new-ordered-acc)
            (generate-fty-type some-name flextypes-table fty-info new-acc-1
                               ordered-acc)))
        (mv new-acc-2
            (acons name new-option new-ordered-acc)))
      )

    (define generate-flexsum-type ((flexsum fty::flexsum-p)
                                   (flextypes-table alistp)
                                   (fty-info fty-info-alist-p)
                                   (acc fty-types-p)
                                   (ordered-acc fty-types-p))
      :returns (mv (updated-acc fty-types-p)
                   (updated-ordered-acc fty-types-p))
      :measure (list (generate-type-measure fty-info acc) 1 0)
      :well-founded-relation acl2::nat-list-<
      :verify-guards nil
      (b* ((acc (fty-types-fix acc))
           (ordered-acc (fty-types-fix ordered-acc))
           ((unless (fty::flexsum-p flexsum)) (mv acc ordered-acc))
           (prods (fty::flexsum->prods flexsum))
           ((unless (consp prods))
            (prog2$ (cw "Warning: empty defprod ~q0" prods)
                    (mv acc ordered-acc)))
           (name (fty::flexsum->name flexsum))
           ((unless (symbolp name))
            (prog2$ (er hard? 'fty=>generate-flexsum-type "Should be a symbolp: ~q0"
                        name)
                    (mv acc ordered-acc)))
           ((unless (or (equal (len prods) 1)
                        (equal (len prods) 2)))
            (prog2$ (cw "Warning: tagsum not supported ~q0" prods)
                    (mv acc ordered-acc)))
           )
        (cond
         ((and (equal (len prods) 1) (fty::flexprod-p (car prods)))
          (generate-flexprod-type name (car prods) flextypes-table fty-info acc
                                  ordered-acc))
         ((and (equal (len prods) 2)
               (fty::flexprod-p (car prods)) (fty::flexprod-p (cadr prods))
               (and (equal (fty::flexprod->kind (car prods)) :none)
                    (equal (fty::flexprod->kind (cadr prods)) :some))
               )
          (generate-flexoption-type name (cadr prods) flextypes-table fty-info
                                    acc ordered-acc))
         ((and (equal (len prods) 2)
               (fty::flexprod-p (car prods)) (fty::flexprod-p (cadr prods))
               (and (equal (fty::flexprod->kind (cadr prods)) :none)
                    (equal (fty::flexprod->kind (car prods)) :some)))
          (generate-flexoption-type name (car prods) flextypes-table fty-info
                                    acc ordered-acc))
         (t (mv acc ordered-acc))))
      )

    (define generate-flexalist-type ((flexalst fty::flexalist-p)
                                     (flextypes-table alistp)
                                     (fty-info fty-info-alist-p)
                                     (acc fty-types-p)
                                     (ordered-acc fty-types-p))
      :returns (mv (updated-acc fty-types-p)
                   (updated-ordered-acc fty-types-p))
      :measure (list (generate-type-measure fty-info acc) 1 0)
      :well-founded-relation acl2::nat-list-<
      :verify-guards nil
      (b* ((acc (fty-types-fix acc))
           (ordered-acc (fty-types-fix ordered-acc))
           ((if (equal (generate-type-measure fty-info acc) 0))
            (prog2$ (er hard? 'fty=>generate-flexprod-type "accumulator exceeding
                                length of all fty functions.~%")
                    (mv acc ordered-acc)))
           ((unless (fty::flexalist-p flexalst)) (mv acc ordered-acc))
           (name (fty::flexalist->name flexalst))
           ((unless (symbolp name))
            (prog2$ (er hard? 'fty=>generate-flexalist-type "Should be a symbolp: ~q0"
                        name)
                    (mv acc ordered-acc)))
           ((if (assoc-equal name acc)) (mv acc ordered-acc))
           (key-type (fty::flexalist->key-type flexalst))
           ((unless (symbolp key-type))
            (prog2$ (er hard? 'fty=>generate-flexalist-type "Should be a symbolp: ~q0"
                        key-type)
                    (mv acc ordered-acc)))
           (val-type (fty::flexalist->val-type flexalst))
           ((unless (symbolp val-type))
            (prog2$ (er hard? 'fty=>generate-flexalist-type "Should be a symbolp: ~q0"
                        val-type)
                    (mv acc ordered-acc)))
           (basic-key? (assoc-equal key-type (SMT-types)))
           (basic-val? (assoc-equal val-type (SMT-types)))
           (key-info (assoc-equal key-type fty-info))
           (val-info (assoc-equal val-type fty-info)))
        (cond ((and basic-key? basic-val?)
               (mv (acons name
                          (make-fty-type-alist :key-type key-type
                                               :val-type val-type)
                          acc)
                   (acons name
                          (make-fty-type-alist :key-type key-type
                                               :val-type val-type)
                          ordered-acc)))
              ((and basic-key? val-info)
               (b* ((val-name (fty-info->name (cdr val-info)))
                    (new-alist (make-fty-type-alist
                                :key-type key-type
                                :val-type val-name))
                    (new-acc-1 (acons name new-alist acc))
                    ((mv new-acc-2 new-ordered-acc)
                     (generate-fty-type val-name flextypes-table fty-info
                                        new-acc-1 ordered-acc)))
                 (mv new-acc-2
                     (acons name new-alist new-ordered-acc))))
              ((and basic-val? key-info)
               (b* ((key-name (fty-info->name (cdr key-info)))
                    (new-alist (make-fty-type-alist
                                :key-type key-name
                                :val-type val-type))
                    (new-acc-1 (acons name new-alist acc))
                    ((mv new-acc-2 new-ordered-acc)
                     (generate-fty-type key-name flextypes-table fty-info
                                        new-acc-1 ordered-acc)))
                 (mv new-acc-2
                     (acons name new-alist new-ordered-acc))))
              ((and key-info val-info)
               (b* ((val-name (fty-info->name (cdr val-info)))
                    (key-name (fty-info->name (cdr key-info)))
                    (new-alist (make-fty-type-alist
                                :key-type key-name
                                :val-type val-name))
                    (new-acc (acons name new-alist acc))
                    ((mv new-acc-1 new-ordered-acc-1)
                     (generate-fty-type key-name flextypes-table fty-info
                                        new-acc ordered-acc))
                    (new-acc-1
                     (mbe :logic (if (o<= (generate-type-measure fty-info new-acc-1)
                                          (generate-type-measure fty-info new-acc))
                                     new-acc-1
                                   nil)
                          :exec new-acc-1))
                    ((if (null new-acc-1)) (mv new-acc new-ordered-acc-1))
                    ((mv new-acc-2 new-ordered-acc-2)
                     (generate-fty-type val-name flextypes-table fty-info
                                        new-acc-1 new-ordered-acc-1)))
                 (mv new-acc-2
                     (acons name new-alist new-ordered-acc-2))))
              (t (prog2$ (er hard? 'fty=>generate-flexalist-type "key-type ~p0 ~
                             and val-type ~p1 doesn't exist~%" key-type val-type)
                         (mv acc ordered-acc))))))

    (define generate-flexlist-type ((flexlst fty::flexlist-p)
                                    (flextypes-table alistp)
                                    (fty-info fty-info-alist-p)
                                    (acc fty-types-p)
                                    (ordered-acc fty-types-p))
      :returns (mv (updated-acc fty-types-p)
                   (updated-ordered-acc fty-types-p))
      :measure (list (generate-type-measure fty-info acc) 1 0)
      :well-founded-relation acl2::nat-list-<
      :verify-guards nil
      (b* ((acc (fty-types-fix acc))
           (ordered-acc (fty-types-fix ordered-acc))
           ((if (equal (generate-type-measure fty-info acc) 0))
            (prog2$ (er hard? 'fty=>generate-flexprod-type "accumulator exceeding ~
                                length of all fty functions.~%")
                    (mv acc ordered-acc)))
           ((unless (fty::flexlist-p flexlst)) (mv acc ordered-acc))
           (name (fty::flexlist->name flexlst))
           ((unless (symbolp name))
            (prog2$ (er hard? 'fty=>generate-flexlist-type "Name should be a symbol ~
                                ~q0" name)
                    (mv acc ordered-acc)))
           ((if (assoc-equal name acc)) (mv acc ordered-acc))
           (true-listp? (fty::flexlist->true-listp flexlst))
           ((unless true-listp?)
            (prog2$ (er hard? 'fty=>generate-flexlist-type "Smtlink can't handle ~
                                lists that are not true-listp yet due to ~
                                soundness concerns: ~q0"
                        name)
                    (mv acc ordered-acc)))
           (elt-type (fty::flexlist->elt-type flexlst))
           ((unless (symbolp elt-type))
            (prog2$ (er hard? 'fty=>generate-flexlist-type "Should be a symbolp: ~q0"
                        elt-type)
                    (mv acc ordered-acc)))
           ;; is the type a basic type?
           (basic? (assoc-equal elt-type (SMT-types)))
           ((if basic?)
            (mv (acons name
                       (make-fty-type-list :elt-type elt-type)
                       acc)
                (acons name
                       (make-fty-type-list :elt-type elt-type)
                       ordered-acc)))
           (info (assoc-equal elt-type fty-info))
           ((unless info)
            (prog2$ (er hard? 'fty=>generate-flexlist-type "elt-type ~p0 doesn't ~
                                exist in fty-info~%" elt-type)
                    (mv acc ordered-acc)))
           (elt-name (fty-info->name (cdr info)))
           (new-list (make-fty-type-list :elt-type elt-name))
           (new-acc-1 (acons name new-list acc))
           ((mv new-acc-2 new-ordered-acc)
            (generate-fty-type elt-name flextypes-table fty-info
                               new-acc-1 ordered-acc)))
        (mv new-acc-2 (acons name new-list new-ordered-acc)))
      )

    (define generate-fty-type ((name symbolp)
                               (flextypes-table alistp)
                               (fty-info fty-info-alist-p)
                               (acc fty-types-p)
                               (ordered-acc fty-types-p))
      :returns (mv (updated-acc fty-types-p)
                   (updated-ordered-acc fty-types-p))
      :measure (list (generate-type-measure fty-info acc) 2 0)
      :well-founded-relation acl2::nat-list-<
      :verify-guards nil
      (b* ((acc (fty-types-fix acc))
           (ordered-acc (fty-types-fix ordered-acc))
           ((unless (alistp flextypes-table))
            (prog2$ (er hard? 'fty=>generate-fty-type "flextypes-table is not an ~
                           alist?~%")
                    (mv acc ordered-acc)))
           ;; is the type a flextype?
           (exist? (assoc-equal name flextypes-table))
           ((unless exist?)
            (prog2$
             (er hard? 'fty=>generate-fty-type "Found a type that's ~
                                  not basic and not fty: ~q0"
                 name)
             (mv acc ordered-acc)))
           (agg (cdr exist?))
           ((unless (fty::flextypes-p agg))
            (prog2$ (er hard? 'fty=>generate-fty-type "Should be a flextypes, but ~
                       found ~q0" agg)
                    (mv acc ordered-acc)))
           (types (fty::flextypes->types agg))
           ((if (or (not (true-listp types))
                    (atom types)
                    (not (null (cdr types)))))
            (prog2$ (er hard? 'fty=>generate-fty-type "Possible recursive types ~
                      found, not supported in Smtlink yet.~%")
                    (mv acc ordered-acc)))
           (type (car types)))
        (cond
         ;; if it's a flexsum, its a defprod or a defoption
         ((fty::flexsum-p type)
          (generate-flexsum-type type flextypes-table fty-info acc ordered-acc))
         ;; if it's a flexlist, it's a deflist
         ((fty::flexlist-p type)
          (generate-flexlist-type type flextypes-table fty-info acc ordered-acc))
         ;; if it's a flexalist, it's a defalist
         ((fty::flexalist-p type)
          (generate-flexalist-type type flextypes-table fty-info acc ordered-acc))
         ;; else, ignore
         (t (mv acc ordered-acc)))))

    (define generate-fty-type-list ((name-lst symbol-listp)
                                    (flextypes-table alistp)
                                    (fty-info fty-info-alist-p)
                                    (acc fty-types-p)
                                    (ordered-acc fty-types-p))
      :returns (mv (updated-acc fty-types-p)
                   (updated-ordered-acc fty-types-p))
      :measure (list (generate-type-measure fty-info acc) 3 (len name-lst))
      :well-founded-relation acl2::nat-list-<
      :hints
      (("Goal"
        :in-theory (e/d () (generate-type-measure-increase-prod
                            generate-type-measure-increase-alist
                            generate-type-measure-increase-list
                            generate-type-measure-increase-option
                            (SMT-types)))
        :use ((:instance
               generate-type-measure-increase-prod
               (acc acc)
               (fty-info fty-info)
               (name (symbol-fix name))
               (prod
                (FTY-TYPE-PROD
                 (MV-NTH
                  1
                  (GENERATE-FTY-FIELD-ALIST (CDR (ASSOC-EQUAL 'FTY::FIELDS (CDR PROD)))
                                            FTY-INFO)))))
              (:instance
               generate-type-measure-increase-list
               (acc acc)
               (fty-info fty-info)
               (name (fty::flexlist->name flexlst))
               (list (FTY-TYPE-LIST
                      (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                                          (CDR FLEXLST)))
                                                        FTY-INFO))))))
              (:instance
               generate-type-measure-increase-option
               (acc acc)
               (fty-info fty-info)
               (name (symbol-fix name))
               (option
                (FTY-TYPE-OPTION
                 (FTY-INFO->NAME
                  (CDR (ASSOC-EQUAL
                        (CDR (ASSOC-EQUAL 'TYPE
                                          (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                  (CDR OPTION))))))
                        FTY-INFO))))))
              (:instance
               generate-type-measure-increase-alist
               (acc acc)
               (fty-info fty-info)
               (name (fty::flexalist->name flexalst))
               (alist
                (FTY-TYPE-ALIST
                 (fty::flexalist->key-type flexalst)
                 (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                                     (CDR FLEXALST)))
                                                   FTY-INFO)))))
               )
              (:instance
               generate-type-measure-increase-alist
               (acc acc)
               (fty-info fty-info)
               (name (fty::flexalist->name flexalst))
               (alist
                (FTY-TYPE-ALIST
                 (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                                     (CDR FLEXALST)))
                                                   FTY-INFO)))
                 (fty::flexalist->val-type flexalst)))
               )
              (:instance
               generate-type-measure-increase-alist
               (acc acc)
               (fty-info fty-info)
               (name (fty::flexalist->name flexalst))
               (alist
                (FTY-TYPE-ALIST
                 (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                                     (CDR FLEXALST)))
                                                   FTY-INFO)))
                 (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                                     (CDR FLEXALST)))
                                                   FTY-INFO))))))
              ))
       )
      :verify-guards nil
      (b* ((name-lst (symbol-list-fix name-lst))
           (acc (fty-types-fix acc))
           (ordered-acc (fty-types-fix ordered-acc))
           ((unless (consp name-lst)) (mv acc ordered-acc))
           ((cons first rest) name-lst)
           ;; is the type a basic type?
           (basic? (assoc-equal first (SMT-types)))
           ((if basic?)
            (generate-fty-type-list rest flextypes-table fty-info acc ordered-acc))
           ((mv new-acc new-ordered-acc)
            (generate-fty-type first flextypes-table fty-info acc ordered-acc))
           (new-acc (mbe :logic (if (o<= (generate-type-measure fty-info new-acc)
                                         (generate-type-measure fty-info acc))
                                    new-acc
                                  nil)
                         :exec new-acc))
           ((if (null new-acc)) (mv acc new-ordered-acc)))
        (generate-fty-type-list rest flextypes-table fty-info new-acc new-ordered-acc))
      )

    )

  (local
   (defthm crock1-1
     (IMPLIES (AND (FTY-INFO-ALIST-P FTY-INFO)
                   (SYMBOLP (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                              (CDR FLEXLST))))
                   (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                  (CDR FLEXLST)))
                                FTY-INFO))
              (CONSP (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                    (CDR FLEXLST)))
                                  FTY-INFO)))
     :hints (("Goal" :induct (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                            (CDR FLEXLST)))
                                          FTY-INFO))))
   )

  (local
   (defthm crock1-2
     (IMPLIES (AND (FTY-INFO-ALIST-P FTY-INFO)
                   (SYMBOLP (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                              (CDR FLEXLST))))
                   (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                  (CDR FLEXLST)))
                                FTY-INFO))
              (FTY-INFO-P (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                              (CDR FLEXLST)))
                                            FTY-INFO)))))
   )

  (local
   (defthm crock2-1
     (IMPLIES (AND (FTY-INFO-ALIST-P FTY-INFO)
                   (SYMBOLP (CDR (ASSOC-EQUAL 'TYPE
                                              (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                      (CDR OPTION)))))))
                   (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'TYPE
                                                  (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                          (CDR OPTION))))))
                                FTY-INFO))
              (CONSP (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'TYPE
                                                    (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                            (CDR OPTION))))))
                                  FTY-INFO)))
     :hints (("Goal" :induct (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'TYPE
                                                            (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                                    (CDR OPTION))))))
                                          FTY-INFO))))
   )

  (local
   (defthm crock2-2
     (IMPLIES (AND (FTY-INFO-ALIST-P FTY-INFO)
                   (symbolp (CDR (ASSOC-EQUAL 'TYPE
                                              (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                      (CDR OPTION)))))))
                   (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'TYPE
                                                  (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                          (CDR OPTION))))))
                                FTY-INFO))
              (FTY-INFO-P
               (CDR
                (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'TYPE
                                               (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                       (CDR OPTION))))))
                             FTY-INFO)))))
   )

  (local
   (defthm crock3-1
     (IMPLIES
      (AND (FTY-INFO-ALIST-P FTY-INFO)
           (symbolp (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                      (CDR FLEXALST))))
           (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                          (CDR FLEXALST)))
                        FTY-INFO))
      (FTY-INFO-P (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                      (CDR FLEXALST)))
                                    FTY-INFO)))))
   )

  (local
   (defthm crock3-2
     (IMPLIES (AND (FTY-INFO-ALIST-P FTY-INFO)
                   (SYMBOLP (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                              (CDR FLEXALST))))
                   (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                  (CDR FLEXALST)))
                                FTY-INFO))
              (CONSP (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                    (CDR FLEXALST)))
                                  FTY-INFO)))
     :hints (("Goal" :induct (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                            (CDR FLEXALST)))
                                          FTY-INFO))))
   )

  (local
   (defthm crock4-1
     (IMPLIES
      (AND (FTY-INFO-ALIST-P FTY-INFO)
           (symbolp (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                      (CDR FLEXALST))))
           (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                          (CDR FLEXALST)))
                        FTY-INFO))
      (FTY-INFO-P (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                      (CDR FLEXALST)))
                                    FTY-INFO)))))
   )

  (local
   (defthm crock4-2
     (IMPLIES (AND (FTY-INFO-ALIST-P FTY-INFO)
                   (SYMBOLP (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                              (CDR FLEXALST))))
                   (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                  (CDR FLEXALST)))
                                FTY-INFO))
              (CONSP (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                    (CDR FLEXALST)))
                                  FTY-INFO)))
     :hints (("Goal" :induct (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                            (CDR FLEXALST)))
                                          FTY-INFO))))
   )

  (local
   (defthm crock5-lemma
     (cond
      ((equal flag 'generate-fty-type)
       (implies
        (and
         (fty-types-p acc)
         (fty-info-alist-p fty-info)
         (alistp flextypes-table)
         (symbolp name))
        (<= (generate-type-measure fty-info
                                   (mv-nth 0 (generate-fty-type name
                                                                flextypes-table fty-info acc ordered-acc)))
            (generate-type-measure fty-info acc))))
      ((equal flag 'generate-fty-type-list)
       (implies
        (and
         (fty-types-p acc)
         (fty-info-alist-p fty-info)
         (alistp flextypes-table)
         (symbol-listp name-lst))
        (<= (generate-type-measure fty-info
                                   (mv-nth 0 (generate-fty-type-list name-lst flextypes-table
                                                                     fty-info acc ordered-acc)))
            (generate-type-measure fty-info acc))))
      ((equal flag 'generate-flexlist-type)
       (implies
        (and
         (fty::flexlist-p flexlst)
         (alistp flextypes-table)
         (fty-info-alist-p fty-info)
         (fty-types-p acc))
        (<= (generate-type-measure fty-info
                                   (mv-nth 0 (generate-flexlist-type flexlst
                                                                     flextypes-table fty-info
                                                                     acc ordered-acc)))
            (generate-type-measure fty-info acc))))
      ((equal flag 'generate-flexalist-type)
       (implies
        (and
         (fty::flexalist-p flexalst)
         (alistp flextypes-table)
         (fty-info-alist-p fty-info)
         (fty-types-p acc))
        (<= (generate-type-measure fty-info
                                   (mv-nth 0 (generate-flexalist-type flexalst
                                                                      flextypes-table fty-info
                                                                      acc ordered-acc)))
            (generate-type-measure fty-info acc))))
      ((equal flag 'generate-flexsum-type)
       (implies
        (and
         (fty::flexsum-p flexsum)
         (alistp flextypes-table)
         (fty-info-alist-p fty-info)
         (fty-types-p acc))
        (<= (generate-type-measure fty-info
                                   (mv-nth 0 (generate-flexsum-type flexsum
                                                                    flextypes-table fty-info
                                                                    acc ordered-acc)))
            (generate-type-measure fty-info acc))))
      ((equal flag 'generate-flexprod-type)
       (implies
        (and
         (symbolp name)
         (fty::flexprod-p prod)
         (alistp flextypes-table)
         (fty-info-alist-p fty-info)
         (fty-types-p acc))
        (<= (generate-type-measure fty-info
                                   (mv-nth 0 (generate-flexprod-type name prod
                                                                     flextypes-table fty-info
                                                                     acc ordered-acc)))
            (generate-type-measure fty-info acc))))
      ((equal flag 'generate-flexoption-type)
       (implies
        (and
         (symbolp name)
         (fty::flexprod-p option)
         (alistp flextypes-table)
         (fty-info-alist-p fty-info)
         (fty-types-p acc))
        (<= (generate-type-measure fty-info
                                   (mv-nth 0 (generate-flexoption-type name option
                                                                       flextypes-table fty-info
                                                                       acc ordered-acc)))
            (generate-type-measure fty-info acc))))
      (t t))
     :hints (("Goal"
              :in-theory (e/d (generate-flexoption-type
                               generate-flexprod-type
                               generate-flexsum-type
                               generate-flexlist-type
                               generate-flexalist-type
                               generate-fty-type
                               generate-fty-type-list)
                              (generate-type-measure-increase-list
                               (SMT-types)))
              :induct (GENERATE-FTY-TYPES-MUTUAL-FLAG
                       FLAG PROD
                       OPTION FLEXSUM FLEXALST FLEXLST NAME
                       NAME-LST FLEXTYPES-TABLE FTY-INFO ACC
                       ORDERED-ACC))
             ("Subgoal *1/42"
              :in-theory (e/d (generate-flexlist-type)
                              (generate-type-measure-increase-list
                               (SMT-types)))
              :use ((:instance
                     generate-type-measure-increase-list
                     (acc acc)
                     (fty-info fty-info)
                     (name (fty::flexlist->name flexlst))
                     (list
                      (FTY-TYPE-LIST
                       (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                                           (CDR FLEXLST)))
                                                         FTY-INFO))))))))
             ("Subgoal *1/41"
              :in-theory (e/d (generate-flexlist-type)
                              (generate-type-measure-increase-list
                               (SMT-types)))
              :use ((:instance
                     generate-type-measure-increase-list
                     (acc acc)
                     (fty-info fty-info)
                     (name (fty::flexlist->name flexlst))
                     (list
                      (FTY-TYPE-LIST (CDR (ASSOC-EQUAL 'FTY::ELT-TYPE
                                                       (CDR FLEXLST))))))))
             ("Subgoal *1/33"
              :in-theory (e/d (generate-flexalist-type)
                              (generate-type-measure-increase-alist
                               (SMT-types)))
              :use ((:instance
                     generate-type-measure-increase-alist
                     (acc acc)
                     (fty-info fty-info)
                     (name (fty::flexlist->name flexalst))
                     (alist
                      (FTY-TYPE-ALIST
                       (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                                           (CDR FLEXALST)))
                                                         FTY-INFO)))
                       (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                                           (CDR FLEXALST)))
                                                         FTY-INFO))))))))
             ("Subgoal *1/32"
              :in-theory (e/d (generate-flexalist-type)
                              (generate-type-measure-increase-alist))
              :use ((:instance
                     generate-type-measure-increase-alist
                     (acc acc)
                     (fty-info fty-info)
                     (name (fty::flexlist->name flexalst))
                     (alist
                      (FTY-TYPE-ALIST
                       (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                                           (CDR FLEXALST)))
                                                         FTY-INFO)))
                       (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                                           (CDR FLEXALST)))
                                                         FTY-INFO))))))))
             ("Subgoal *1/30"
              :in-theory (e/d (generate-flexalist-type)
                              (generate-type-measure-increase-alist))
              :use ((:instance
                     generate-type-measure-increase-alist
                     (acc acc)
                     (fty-info fty-info)
                     (name (fty::flexlist->name flexalst))
                     (alist
                      (FTY-TYPE-ALIST
                       (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::KEY-TYPE
                                                                           (CDR FLEXALST)))
                                                         FTY-INFO)))
                       (fty::flexalist->val-type flexalst))))))
             ("Subgoal *1/28"
              :in-theory (e/d (generate-flexalist-type)
                              (generate-type-measure-increase-alist))
              :use ((:instance
                     generate-type-measure-increase-alist
                     (acc acc)
                     (fty-info fty-info)
                     (name (fty::flexlist->name flexalst))
                     (alist
                      (FTY-TYPE-ALIST
                       (fty::flexalist->key-type flexalst)
                       (FTY-INFO->NAME (CDR (ASSOC-EQUAL (CDR (ASSOC-EQUAL 'FTY::VAL-TYPE
                                                                           (CDR FLEXALST)))
                                                         FTY-INFO))))))))
             ("Subgoal *1/27"
              :in-theory (e/d (generate-flexalist-type)
                              (generate-type-measure-increase-alist))
              :use ((:instance
                     generate-type-measure-increase-alist
                     (acc acc)
                     (fty-info fty-info)
                     (name (fty::flexlist->name flexalst))
                     (alist
                      (FTY-TYPE-ALIST
                       (fty::flexalist->key-type flexalst)
                       (fty::flexalist->val-type flexalst))))))
             ("Subgoal *1/7"
              :in-theory (e/d (generate-flexoption-type)
                              (generate-type-measure-increase-option))
              :use ((:instance
                     generate-type-measure-increase-option
                     (acc acc)
                     (fty-info fty-info)
                     (name name)
                     (option
                      (FTY-TYPE-OPTION
                       (FTY-INFO->NAME
                        (CDR (ASSOC-EQUAL
                              (CDR (ASSOC-EQUAL 'TYPE
                                                (CDR (CADR (ASSOC-EQUAL 'FTY::FIELDS
                                                                        (CDR OPTION))))))
                              FTY-INFO))))))))
             ("Subgoal *1/6"
              :in-theory (e/d (generate-flexoption-type)
                              (generate-type-measure-increase-option))
              :use ((:instance
                     generate-type-measure-increase-option
                     (acc acc)
                     (fty-info fty-info)
                     (name name)
                     (option
                      (fty-type-option
                       (fty::flexprod-field->type
                        (car (fty::flexprod->fields option))))))))
             ("Subgoal *1/3"
              :in-theory (e/d (generate-flexprod-type)
                              (generate-type-measure-increase-prod))
              :use ((:instance
                     generate-type-measure-increase-prod
                     (acc acc)
                     (fty-info fty-info)
                     (name (symbol-fix name))
                     (prod
                      (fty-type-prod
                       (mv-nth
                        1
                        (generate-fty-field-alist
                         (fty::flexprod->fields prod)
                         fty-info)))))))
             ))
   )

  (local
   (defthm crock5
     (implies
      (and
       (fty-types-p acc)
       (fty-info-alist-p fty-info)
       (alistp flextypes-table)
       (symbol-listp name-lst)
       (consp name-lst))
      (<= (generate-type-measure fty-info
                                 (mv-nth 0 (generate-fty-type (car name-lst)
                                                              flextypes-table
                                                              fty-info acc ordered-acc)))
          (generate-type-measure fty-info acc)))
     :hints (("goal"
              :use ((:instance crock5-lemma
                               (flag 'generate-fty-type)
                               (name (car name-lst)))))))
   )

  (local
   (defthm crock6
     (implies
      (and (fty-types-p acc)
           (fty-info-alist-p fty-info)
           (alistp flextypes-table)
           (consp flexalst)
           (equal (car flexalst) :alist)
           (alistp (cdr flexalst))
           (consp (cdr flexalst))
           (not (equal (generate-type-measure fty-info acc)
                       0))
           (symbolp (cdr (assoc-equal 'fty::name
                                      (cdr flexalst))))
           (not (assoc-equal (cdr (assoc-equal 'fty::name (cdr flexalst)))
                             acc))
           (symbolp (cdr (assoc-equal 'fty::key-type
                                      (cdr flexalst))))
           (symbolp (cdr (assoc-equal 'fty::val-type
                                      (cdr flexalst))))
           (assoc-equal (cdr (assoc-equal 'fty::key-type
                                          (cdr flexalst)))
                        fty-info)
           (assoc-equal (cdr (assoc-equal 'fty::val-type
                                          (cdr flexalst)))
                        fty-info))
      (>=
       (generate-type-measure
        fty-info
        (cons
         (cons
          (cdr (assoc-equal 'fty::name (cdr flexalst)))
          (fty-type-alist
           (fty-info->name (cdr (assoc-equal (cdr (assoc-equal 'fty::key-type
                                                               (cdr flexalst)))
                                             fty-info)))
           (fty-info->name (cdr (assoc-equal (cdr (assoc-equal 'fty::val-type
                                                               (cdr flexalst)))
                                             fty-info)))))
         acc))
       (generate-type-measure
        fty-info
        (mv-nth 0
                (generate-fty-type
                 (fty-info->name (cdr (assoc-equal (cdr (assoc-equal 'fty::key-type
                                                                     (cdr flexalst)))
                                                   fty-info)))
                 flextypes-table fty-info
                 (cons
                  (cons
                   (cdr (assoc-equal 'fty::name (cdr flexalst)))
                   (fty-type-alist
                    (fty-info->name (cdr (assoc-equal (cdr (assoc-equal 'fty::key-type
                                                                        (cdr flexalst)))
                                                      fty-info)))
                    (fty-info->name (cdr (assoc-equal (cdr (assoc-equal 'fty::val-type
                                                                        (cdr flexalst)))
                                                      fty-info)))))
                  acc)
                 ordered-acc)))))
     :hints (("goal"
              :use ((:instance crock5-lemma
                               (flag 'generate-fty-type)
                               (name (fty-info->name
                                      (cdr (assoc-equal
                                            (cdr (assoc-equal 'fty::key-type
                                                              (cdr flexalst)))
                                            fty-info))))
                               (acc (cons
                                     (cons
                                      (cdr (assoc-equal 'fty::name (cdr flexalst)))
                                      (fty-type-alist
                                       (fty-info->name (cdr (assoc-equal (cdr (assoc-equal 'fty::key-type
                                                                                           (cdr flexalst)))
                                                                         fty-info)))
                                       (fty-info->name (cdr (assoc-equal (cdr (assoc-equal 'fty::val-type
                                                                                           (cdr flexalst)))
                                                                         fty-info)))))
                                     acc)))))))
   )

  (verify-guards generate-fty-type-list
    :guard-debug t
    :hints nil)
  )
