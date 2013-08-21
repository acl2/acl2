#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")

;;;;Main Author: Peter Dillinger
;;;;Extended by Harsh Raju C
;;;;Data definition Framework (ACL2 Sedan)
;;;;It can be used independently, but is primarily intended
;;;;to support the CGEN/TESTING framework!!

(acl2::begin-book t);$ACL2s-Preamble$|#


(in-package "DEFDATA")

(include-book "utilities" :load-compiled-file :comp)
(include-book "basis")
(include-book "acl2s-parameter")
(include-book "splitnat")
(include-book "switchnat")

(set-verify-guards-eagerness 2)

;Introduce data definitions conveniently in ACL2
(defdoc acl2::DATA-DEFINITIONS
  ":Doc-Section DATA-DEFINITIONS
  
  A Data Definition Framework for ACL2~/
                                
  The Data Definition Framework supports ground ACL2
  ~em[types] and any custom ~em[types] introduced by
  a user. It also helps the user conveniently construct
  enumerated, union, record and list ~em[types]. 
  The framework is integrated with our random testing
  framework. It also provides ways to specify subtype
  and disjoint relations among the supported ~em[types].~/
  
  The ACL2 value universe is broadly divided into 5 kinds of data
  objects. They are Numbers, Characters, Strings, Symbols and Conses
  (Ordered Pairs). These disjoint sets serve as types for our purposes;
  we shall call them ground data types. Although ACL2 is an ~em[untyped]
  logic, it uses type information internally to deduce types.
  ACL2 users provide the prover with type information by specifying
  type  hypotheses on variables in a conjecture.
  Note again that ACL2 is syntactically ~em[untyped], but that 
  doesn't prevent us from having and using a notion of a type.
  One ~st[cannot create] new ~em[types] in ACL2, in the sense
  that one cannot create a new non-empty set of values that
  provably extends the ACL2 value universe.  Rather, one
  typically partitions the existing universe in potentially
  new ways to form 'new' sets. These sets (``types'') are
  presently characterized by just a type predicate. 
  ~nl[]
  The task of specifying user-defined data definitions (``types'') and supporting
  random testing is elegantly solved by characterizing 'type' using both a 
  type predicate and a type enumerator. 
  ~nl[]
  ~nl[]
  What is a ~em[type] in our data definition framwork?
  We say that ~c[foo] is a 'type' if there exists a predicate
  function ~c[foop] and either a constant list of values 
  ~c[*foo-values*] (if it's finite) or an enumerator function 
  ~c[nth-foo] (if it's infinite) that maps natural numbers to data
  objects that satisfy ~c[foop].  If ~em[foo] is ~st[supported]
  by our framework, i.e. the forementioned conditions are met, then
  the name ~em[foo] can be used in defining other types using
  ~c[defdata].
  ~nl[]
  The framework supports all the ground data types and the common
  data types present in the initial(ground) ACL2 world.
  The framework also treats each data object in the ACL2 universe as a
  singleton 'type', i.e. a set with just one element, the data object
  itself. The type which represents all of the ACL2 universe is 
  called ~c[all]; every 'type' is thus a subset of ~c[all].
  ~nl[]
  
  Sophisticated users may want to define custom
  types manually, for example to define a type which represents
  positive multiples of 3. In ACL2 we can define such a type by the
  following predicate:

 ~bv[]
 (defun pos-multiple-of-threep (v)
  (if (posp v)
    (equal 0 (mod v 3))
    nil))
 ~ev[]
 In order to ~st[support] this type within our framework, all one needs to do
 is to define its enumerator, which is a bijection from the set of natural numbers
 to the set of positive multiples of 3:
 ~bv[]
 (defun nth-pos-multiple-of-three (n)
  (if (natp n) 
   (* 3 (1+ n))
   3))
  ~ev[]
  
  The framework provides a macro ~c[defdata] to specify combinations of
  supported 'types', thus relieving the user of the trouble of
  defining predicates and enumerators by hand. 'Types' allow users
  to refer to them by name in these data definitions. One can also
  use ~c[register-data-constructor] to introduce custom notions of
  product data. ~c[defdata-subtype] and ~c[defdata-disjoint] are 
  used to specify relations among supported 'types'.
  
  We illustrate some uses of the framework:
  ~bv[]
                               
  (register-data-constructor (consp cons)
                             ((allp car) (allp cdr))
                             :proper t)
                             
  (register-custom-type nat (t nth-nat . natp))
  
  (defdata loi (oneof 'nil
                      (cons integer loi)))
                                          
  (defdata-subtype nat rational)
  
  (defdata-disjoint symbol string)
  ~ev[]
  For more details on data-definitions framework refer ___.
  ")


;set verbose and printstats & only-counterexample flags
(defmacro set-acl2s-defdata-verbose (v)
   ":Doc-Section ACL2::DATA-DEFINITIONS
   Control amount of output printed by defdata~/
   By default this parameter is set to ~c[nil]. 
   If set to ~c[t], you will see all of the output
   generated by ACL2 and the defdata macro.
   Recommend ~em[not] setting it, unless you want to debug
   or want to peek into whats happening below the hood.
   ~bv[]
   Usage:
   (set-acl2s-defdata-verbose nil)
   ~ev[]~/
   "
 `(assign acl2s-defdata-verbose ,v))

;internal debug flag
(defmacro set-acl2s-defdata-debug (v)
 `(assign acl2s-defdata-debug ,v))
(defun get-acl2s-defdata-debug-fn (state)
  (declare (xargs :stobjs (state)))
  (let ((b (acl2::f-boundp-global 'acl2s-defdata-debug state)))
    (if b
      (acl2::f-get-global 'acl2s-defdata-debug state)
      nil)))
(defmacro get-acl2s-defdata-debug ()
 `(get-acl2s-defdata-debug-fn state))
;end of internal debug flag

(defconst *default-defdata-verbose* nil)

(defun get-acl2s-defdata-verbose-fn (state)
  (declare (xargs :stobjs (state)))
  (let ((b (acl2::f-boundp-global 'acl2s-defdata-verbose state)))
    (if b
      (acl2::f-get-global 'acl2s-defdata-verbose state)
      *default-defdata-verbose*)))

(defmacro get-acl2s-defdata-verbose ()
   ":Doc-Section ACL2::DATA-DEFINITIONS
   Get the current verbosity for output printed by defdata~/
   Returns ~c[t] if verbosity is turned on, ~c[nil] otherwise.
   ~bv[]
   Usage:
   (get-acl2s-defdata-verbose)
   ~ev[]~/
   "
 `(get-acl2s-defdata-verbose-fn state))

(defconst *default-defdata-use-guards* nil);Sep 3rd 2012

(defun get-acl2s-defdata-use-guards-fn (state)
  (declare (xargs :stobjs (state)))
  (let ((b (acl2::f-boundp-global 'acl2s-defdata-use-guards state)))
    (if b
      (acl2::f-get-global 'acl2s-defdata-use-guards state)
      *default-defdata-use-guards*)))

(defmacro get-acl2s-defdata-use-guards ()
   ":Doc-Section ACL2::DATA-DEFINITIONS
   Get the setting for use of guards in functions generated by defdata~/
   Returns ~c[t] if use of guards is turned on, ~c[nil] otherwise.
   ~bv[]
   Usage:
   (get-acl2s-defdata-use-guards)
   ~ev[]~/
   "
 `(get-acl2s-defdata-use-guards-fn state))

(defmacro set-acl2s-defdata-use-guards (v)
   ":Doc-Section ACL2::DATA-DEFINITIONS
   Use(and verify) guards in functions generated by defdata~/
   By default this parameter is set to ~c[t]. 
   ~bv[]
   Usage:
   (set-acl2s-defdata-use-guards t)
   ~ev[]~/
   "
 `(assign acl2s-defdata-use-guards ,v))

(set-state-ok t)

;------- define some useful constructors -------;

#||
(defun find-elim-rules (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (endp wrld)
    nil
    (let ((trip (car wrld)))
      (if (eq (second trip) 'eliminate-destructors-rule)
        (cons trip (find-elim-rules (cdr wrld)))
        (find-elim-rules (cdr wrld))))))

||#

(defun get-constructor-predicate-and-destructors (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (if (endp wrld)
    nil
    (let ((trip (car wrld)))
      (if (and (eq (second trip) 'eliminate-destructors-rule)
               (>= (len trip) 6))
        (let ((info (fifth trip))
              (foo (sixth trip)))
           (if (and (consp foo)
                    (consp (car foo))
                    (eq (caar foo) fn)
                    (alistp (cdar foo)))
             (cons
              (if (and (consp info)
                       (consp (car info))
                       (consp (caar info))
                       (symbolp (caaar info)))
                (caaar info)
                'allp)
              (strip-cars (cdar foo)))
             (get-constructor-predicate-and-destructors fn (cdr wrld))))
        (get-constructor-predicate-and-destructors fn (cdr wrld))))))



; TODO: what about well-foundedness?
#|
(thm (implies (consp x)
              (and (o< (acl2-count (car x)) (acl2-count x))
                   (o< (acl2-count (cdr x)) (acl2-count x)))))
(default-well-founded-relation (w state))
|#
; nah.  doesn't imply compositions well-founded. ASK Peter!!

;;-- stores information about data contructors
;;--i.e. constructor name, cons predicate and (pred destructor) pairs, measure-fn and the foll:
;;--flags :proper ((:proper) for proper constructors and nil otherwise)
;eg :
; (/    ( () rationalp ((numerator . integerp) ( denominator . posp)) . acl2-count))
; (cons ( (:proper) consp ((car . allp) ( cdr . allp)) . acl2-count))
;;--
;;--completely modifed by harshrc on 27-Aug-2009 from a table to a global
;;--CHANGED BACK to TABLE

(table data-constructors nil nil :guard
       (and ;; len >= 3 ;;--modified by harshrc
            (consp val)
            (consp (cdr val))
            (consp (cddr val))
            (let ((flags (car val))
                  (predicate (cadr val))
                  (dlst (caddr val))
                  (msr-fn (cdddr val)));;--modifed by harshrc 
              (and
               ;; list of flags
               (keyword-listp flags)
               ;; predicate function (allp for all) for image of constructor
               (symbolp predicate)
               (plausible-predicate-functionp predicate world)
               (symbolp msr-fn)
               (or (allows-arity msr-fn 1 world)
                   (eq msr-fn 'none));;-- msr a one-param fn?? -harshrc
               ;; (dfn . pfn) alist in parameter order where
               ;; dfn names destructor
               ;; pfn intended domain predicate function (allp for all)
               (alistp dlst)
               (allows-arity key (len dlst) world)
               (allow-arity-lst (strip-cars dlst) 1 world)
               (plausible-predicate-function-listp (strip-cdrs dlst)
                                                   world)))))
       



            
       

;auto-generated constructors have only synctatic guards
(table record-constructors nil nil :guard
       (and
         (consp val)
         (consp (cdr val))
         (consp (cddr val))
         (let ((flags (car val))
               (predicate (cadr val))
               (dlst (caddr val))
               (msr-fn (cdddr val))) 
           (and
            ;; list of flags
            (keyword-listp flags)
            (symbolp predicate)
            (symbolp msr-fn)
            (symbol-alistp dlst)))))




#|
;auto-generated constructors have only synctatic guards
(defun add-to-record-constructors-global (constructor cons-info ctx state)
  (declare (xargs :stobjs (state) :mode :program                  
                  :guard (and (symbolp constructor)
                              (consp cons-info))))
  (let ((key constructor)
        (val cons-info))
        
    (if (and
         (consp val)
         (consp (cdr val))
         (consp (cddr val))
         (let ((flags (car val))
               (predicate (cadr val))
               (dlst (caddr val))
               (msr-fn (cdddr val))) 
           (and
            ;; list of flags
            (keyword-listp flags)
            (symbolp predicate)
            (symbolp msr-fn)
            (symbol-alistp dlst))))
      (let* ((data-cons-alst (get-data-constructors-global))
            (cons-entry (assoc-eq key data-cons-alst)))
            
        (if (consp cons-entry)
          (if (not (equal (cdr cons-entry) cons-info))
            (er soft ctx "~x0 already present in the global record-constructors table! Illegal to modify it!!~%" key)
            (value '(value-triple :redundant)))
          (let ((data-cons-alst (acons key val data-cons-alst)))
            (er-progn
             (set-record-constructors-global data-cons-alst)
             (value `(value-triple ,(cons key val)))))))
      (er soft ctx "Constructor ~x0 and its Info ~x1 are invalid, and cannot be added to generated-constructor table!~%" key val))))

|#


;selectors for the above constructors stored in the *-constructor tables, use them only.
(defun cons-name-entry (constructor-table-entry)
  (declare (xargs :guard (and (consp constructor-table-entry)
                              (consp (cdr constructor-table-entry))
                              (consp (cddr constructor-table-entry))
                              (consp (cdddr constructor-table-entry)))))
  (car constructor-table-entry))
(defun predicate-name-entry (constructor-table-entry)
  (declare (xargs :guard (and (consp constructor-table-entry)
                              (consp (cdr constructor-table-entry))
                              (consp (cddr constructor-table-entry))
                              (consp (cdddr constructor-table-entry)))))
  (caddr constructor-table-entry))
(defun dex-pairs-entry (constructor-table-entry)
  (declare (xargs :guard (and (consp constructor-table-entry)
                              (consp (cdr constructor-table-entry))
                              (consp (cddr constructor-table-entry))
                              (consp (cdddr constructor-table-entry)))))
  (cadddr constructor-table-entry))
(defun measure-fn-entry (constructor-table-entry)
  (declare (xargs :guard (and (consp constructor-table-entry)
                              (consp (cdr constructor-table-entry))
                              (consp (cddr constructor-table-entry))
                              (consp (cdddr constructor-table-entry)))))
  (cddddr constructor-table-entry))



;;--normalise a constructor/destructor form
;;-- sfn => (sfn . allp)
;;-- (sfn . pfn) ==> (sfn . pfn)
;;-- (pfn sfn) ==> (sfn . pfn) where sfn is constructor/destructor? and pfn is pred
(defun fix-structor-and-pred (p ctx)
  (cond ((symbolp p)
         (cons p 'allp))
        ((and (consp p)
              (symbolp (car p))
              (symbolp (cdr p))) ; (sfn . pfn)
         p)
        ((and (consp p)
              (symbolp (car p))
              (consp (cdr p))
              (symbolp (cadr p))
              (null (cddr p)))   ; (pfn sfn)
         (cons (cadr p) (car p)))
        (t
         (er hard? ctx
             "Invalid function with predicate: ~x0"
             p))))

;;-- returns list of form ((numerator . rationalp) ...)
(defun fix-structor-and-pred-lst (lst ctx)
  (declare (xargs :guard (and (true-listp lst) (symbolp ctx))))
  (if (endp lst)
    nil
    (cons (fix-structor-and-pred (car lst) ctx)
          (fix-structor-and-pred-lst (cdr lst) ctx))))

;;--return a list of single argument(x) calls
;;--(apply-to-x-lst '(ap bp cp))
;;-- ==> ((AP X) (BP X) (CP X))
(defun apply-to-x-lst (fns)
  (declare (xargs :guard (true-listp fns)))
  (if (endp fns)
    nil
    (cons (list (car fns) 'x)
          (apply-to-x-lst (cdr fns)))))

(defun apply-mget-to-x-lst (fields quotep)
  (declare (xargs :guard (and (booleanp quotep)
                              (symbol-listp fields))))
  (if (endp fields)
    nil
    (let ((d-keyword-name (intern (symbol-name (car fields)) "KEYWORD")))
      (cons (list 'acl2::mget (if quotep (kwote d-keyword-name) d-keyword-name) 'x)
            (apply-mget-to-x-lst (cdr fields) quotep)))))

;;--eg:(get-proper-dex-theorems 'cons '(car cdr))
;;--         ==>
;;--((EQUAL (CAR (CONS CAR CDR)) CAR)
;;-- (EQUAL (CDR (CONS CAR CDR)) CDR))
(defun get-proper-dex-theorems1 (conx-name dex-names rem-dex-names recordp)
  (declare (xargs :guard (and (symbol-listp dex-names)
                              (booleanp recordp)
                              (symbol-listp rem-dex-names))))
  (if (endp rem-dex-names)
    nil
    (if recordp
      (let ((d-keyword-name (intern (symbol-name (car rem-dex-names)) "KEYWORD")))
        (cons `(equal (mget ,d-keyword-name (,conx-name . ,dex-names))
                      ,(car rem-dex-names))
              (get-proper-dex-theorems1 conx-name dex-names
                                      (cdr rem-dex-names) recordp)))
      (cons `(equal (,(car rem-dex-names) (,conx-name . ,dex-names))
                    ,(car rem-dex-names))
            (get-proper-dex-theorems1 conx-name dex-names
                                      (cdr rem-dex-names) recordp)))))

(defun get-proper-dex-theorems (conx-name dex-names recordp)
  (declare (xargs :guard (and (booleanp recordp) (symbol-listp dex-names))))
  (get-proper-dex-theorems1 conx-name dex-names dex-names recordp))

;;-- (get-improper-dex-theorems 'rational '(numerator denominator) '(integerp posp))
;;-- gives
;;-- ((INTEGERP (NUMERATOR (RATIONAL NUMERATOR DENOMINATOR)))
;;-- (POSP (DENOMINATOR (RATIONAL NUMERATOR DENOMINATOR))))
(defun get-improper-dex-theorems1 (conx-name dex-names
                                             rem-dex-names 
                                             rem-dex-prexs
                                             recordp)
  (declare (xargs :guard (and (symbol-listp dex-names)
                              (symbol-listp rem-dex-names)
                              (booleanp recordp);records
                              (symbol-listp rem-dex-prexs))))
  (if (endp rem-dex-names)
    nil
    (if recordp
      (let ((d-keyword-name (intern (symbol-name (car rem-dex-names)) "KEYWORD")))
        (cons `(,(car rem-dex-prexs) (mget ,d-keyword-name (,conx-name . ,dex-names)))
          (get-improper-dex-theorems1 conx-name dex-names
                                      (cdr rem-dex-names)
                                      (cdr rem-dex-prexs) recordp)))

      (cons `(,(car rem-dex-prexs) (,(car rem-dex-names) (,conx-name . ,dex-names)))
            (get-improper-dex-theorems1 conx-name dex-names
                                        (cdr rem-dex-names)
                                        (cdr rem-dex-prexs) recordp)))))

(defun get-improper-dex-theorems (conx-name dex-names dex-prexs recordp)
  (declare (xargs :guard (and (symbol-listp dex-names)
                              (booleanp recordp);records
                              (symbol-listp dex-prexs))))
  (get-improper-dex-theorems1 conx-name dex-names
                              dex-names dex-prexs recordp))

(defun build-one-param-calls-forcep (fns params forcep)
  (declare (xargs :guard (and (true-listp fns)
                              (true-listp params)
                              (booleanp forcep)
                              (= (len fns) (len params)))))
  (if (endp fns)
    nil
    (cons (if forcep
              (list 'acl2::force (list (car fns) (car params)))
              (list (car fns) (car params)))
          (build-one-param-calls-forcep (cdr fns) (cdr params) forcep))))

(defun build-one-param-calls (fns params)
  (declare (xargs :guard (and (true-listp fns)
                              (true-listp params)
                              (= (len fns) (len params)))))
  (if (endp fns)
    nil
    (cons (list (car fns) (car params))
          (build-one-param-calls (cdr fns) (cdr params)))))


;(o< (acl2-count (car x)) (acl2-count x))
;(o< (acl2-count (cdr x)) (acl2-count x))
(defun build-measure-calls (dex-names)
  (declare (xargs :guard (true-listp dex-names)))
  (if (endp dex-names)
    nil
    (cons `(o< (acl2-count (,(car dex-names) x)) (acl2-count x))
          (build-measure-calls (cdr dex-names)))))

;;--added measure-fn flag with default 'none
(defmacro register-data-constructor (constructor destructor-lst
                                                 &key 
                                                 hints proper
                                                 measure-fn ;added by harshrc
                                                 rule-classes
                                                 forcep ;force typ hyps
                                                 )
  
  ":Doc-Section DATA-DEFINITIONS
  Register a data constructor to be used in data definitions(FOR ADVANCED USERS)~/
  This is an advanced macro to be used only by power users and people who
  would like to add their own custom notions of product data. 
  It can be used to register a data-constructor like ~c[cons]
  with the data-definition framework, so that ~em[product datatypes] 
  can be specified using ~c[defdata]. 
  For example ~em[cons] is already registered for you:
  ~bv[]
  (register-data-constructor (consp cons)
                             ((allp car) (allp cdr))
                             :proper t)
  ~ev[]                           
  It says that ~c[cons] is a constructor and anything that satisfies
  ~c[consp] can be constructed with this constructor, like ~c[(cons nat pos)].
  The destructor ~c[car] tells what the first argument to ~c[cons] was, and
  anything specifying ~c[allp] can be given in that argument position. The
  destructor ~c[cdr] tells what the second argument to ~c[cons] was, and
  anything satisfying ~c[allp] can be given in that argument position. The
  proper keyword specifies that any product data that was formed using 
  ~c[cons] can be uniquely destructed back to its original arguments. For
  e.g ~c[(car (cons 1 3))] gives you 1. Compare this with an improper constructor
  ~c[/] which is shown in the examples below, where ~c[(denominator (/ 6 42))]
  gives back 7 instead of 42.
  
  
  ~bv[]
  Examples(These are already registered(like all ground acl2 constructors)):
  (register-data-constructor (acl2-numberp complex)
                             ((rationalp realpart) (rationalp imagpart))
                             :proper t)
  
  ;an improper constructor                           
  (register-data-constructor (rationalp /)
                             ((integerp numerator) (posp denominator)))
  ~ev[]                      
  ~bv[]
  Usage:
  (register-data-constructor (<constructor-predicate> <constructor>)
                             ((<destructor-predicate> <destructor>) ...)
                             [:proper <boolean>]
                             [:hints hints]
                             [:rule-classes rule-classes]
                             [:forcep <boolean>]
                             )
  ~ev[]~/
  "
  (declare (xargs :guard (and (true-listp destructor-lst)
                              (booleanp proper)
                              (booleanp forcep))))
  (let* ((ctx 'register-data-constructor)
         (conx-pair (fix-structor-and-pred constructor ctx))
         (dex-pairs (fix-structor-and-pred-lst destructor-lst ctx))
         (conx-name (car conx-pair))
         (conx-prex (cdr conx-pair))
         (dex-names (strip-cars dex-pairs))
         (dex-prexs (strip-cdrs dex-pairs))
         (table-name 'data-constructors)
         (msr-fn  measure-fn))
       ;(thm (implies (consp x)
       ;      (and (o< (acl2-count (car x)) (acl2-count x))
       ;           (o< (acl2-count (cdr x)) (acl2-count x)))))
       ; (local (defthm ,(modify-symbol nil conx-name "-MEASURE-FN-VALID")
       ;          (and (o-p (,msr-fn x))
       ;               (implies (,conx-prex x)
       ;                        (and . ,(build-measure-calls dex-names) )))))
        
    `(progn
       (defthm ,(modify-symbol "" conx-name "-CONSTRUCTOR-PRED")
         (implies (and . ,(build-one-param-calls-forcep dex-prexs dex-names forcep))
                  (,conx-prex (,conx-name . ,dex-names)))
         :hints ,hints
         :rule-classes ,rule-classes)
                      
       (defthm ,(modify-symbol "" conx-name "-CONSTRUCTOR-ELIM-RULE")
         (implies (,conx-prex x)
                  (equal (,conx-name . ,(apply-to-x-lst dex-names))
                         x))
         :hints ,hints
         :rule-classes ,(if rule-classes '(:elim) 'nil))
       
       (defthm ,(modify-symbol "" conx-name "-CONSTRUCTOR-DESTRUCTORS")
         (implies (and . ,(build-one-param-calls-forcep dex-prexs dex-names forcep))
                  (and . ,(if proper
                              (append (get-proper-dex-theorems conx-name dex-names nil)
                                      (get-improper-dex-theorems conx-name dex-names dex-prexs nil))
                            (get-improper-dex-theorems conx-name dex-names dex-prexs nil))))
         :rule-classes ,rule-classes
         :hints ,hints)
      
      (table
       ,table-name
       ',conx-name
       ',(list* (if proper '(:proper) '())
                conx-prex dex-pairs 
                (if msr-fn msr-fn 'none))
       :put)
      
      (value-triple (list ',constructor ',destructor-lst)))))
  

(table record-elim-table nil nil 
       :guard (consp val)) ;elim-rule-p

(table map-elim-table nil nil 
       :guard (consp val))

(defun get-elim-rule (nume term destructor-term)
  "see add-elim-rule in defthms.lisp"
  (declare (xargs :mode :program))
  (let* ((lst (acl2::unprettyify term))
         (hyps (caar lst))
         (equiv (acl2::ffn-symb (cdar lst)))
         (lhs (acl2::fargn (cdar lst) 1))
         (rhs (acl2::fargn (cdar lst) 2))
         (dests (cdr lhs))
         (rule (acl2::make acl2::elim-rule
                     :rune -1 ;dummy
                     :nume nume
                     :hyps hyps
                     :equiv equiv
                     :lhs lhs
                     :rhs rhs
                     :crucial-position 1 ;(mget :fieldname x) or (mget a x)
                     :destructor-term destructor-term
                     :destructor-terms dests)))
    rule))
 
(defun record-gen-theorem-conclusions (rem-dex-names rem-dex-prexs)
  (declare (xargs :guard (and (symbol-listp rem-dex-names)
                              (symbol-listp rem-dex-prexs))))
  (if (endp rem-dex-names)
    nil
    (let ((d-keyword-name (intern (symbol-name (car rem-dex-names)) "KEYWORD"))) ;term
      (cons `(,(car rem-dex-prexs) (mget ,d-keyword-name x)) 
            (record-gen-theorem-conclusions (cdr rem-dex-names)
                                            (cdr rem-dex-prexs))))))

      

(defun make-generalize-rules-for-records (conx-prex dex-names concls hints)
  (declare (xargs :guard (and (symbol-listp dex-names)
                              (true-listp concls)
                              (symbolp conx-prex))))
  (if (endp concls)
      '()
    (cons `(defthm ,(modify-symbol (string-append (symbol-name (car dex-names)) "-") conx-prex "-RECORD-ELIM-GENERALIZE")
             (implies (,conx-prex x)
                      ,(car concls))
                      :rule-classes :generalize
                      :hints ,hints)
          (make-generalize-rules-for-records conx-prex (cdr dex-names) (cdr concls) hints))))

(defmacro register-record-constructor (constructor destructor-lst
                                                   &key 
                                                   hints
                                                   (rule-classes '(:rewrite :tau-system))
                                                   forcep ;force typ hyps
                                                   measure-fn
                                                   )
  
  (declare (xargs :guard (and (true-listp destructor-lst)
                              (booleanp forcep))))
  (let* ((ctx 'register-record-constructor)
         (conx-pair (fix-structor-and-pred constructor ctx))
         (dex-pairs destructor-lst)
         (conx-name (car conx-pair))
         (conx-prex (cdr conx-pair))
         (dex-names (strip-cars dex-pairs))
         (dex-prexs (strip-cdrs dex-pairs))
         (msr-fn  measure-fn)
         (elim-rule-name (modify-symbol "" conx-name "-RECORD-ELIM-RULE"))
         (nume (list :elim elim-rule-name))
         (elim-term `(implies (,conx-prex x)
                              (equal (,conx-name
                                      . ,(apply-mget-to-x-lst dex-names t))
                                     x)))
         (elim-rule (get-elim-rule nume elim-term '?))
         (gen-concls (record-gen-theorem-conclusions dex-names dex-prexs))
         (generalize-rules (make-generalize-rules-for-records conx-prex dex-names gen-concls hints)))
    
        
    `(progn
       (defthm ,(modify-symbol "" conx-name "-RECORD-PRED")
         (implies (and . ,(build-one-param-calls-forcep dex-prexs dex-names forcep))
                  (,conx-prex (,conx-name . ,dex-names)))
         :hints ,hints
         :rule-classes ,rule-classes)
                       
       (defthm ,elim-rule-name
         (implies (,conx-prex x)
                  (equal (,conx-name
                          . ,(apply-mget-to-x-lst dex-names nil))
                         x))
         :hints ,hints
         :rule-classes nil) ;elim form not satisfied TODO

       (defthm ,(modify-symbol "" conx-name "-RECORD-DESTRUCTORS")
         (implies (and . ,(build-one-param-calls-forcep dex-prexs dex-names forcep))
                  
                  (and . ,(append (get-proper-dex-theorems conx-name dex-names t)
                                  (get-improper-dex-theorems conx-name dex-names dex-prexs t))))
         :rule-classes nil ;subsumed by record theorems
         :hints ,hints)

       ,@generalize-rules

      (table record-constructors
             ',conx-name
             ',(list* '(:generated :proper)
                      conx-prex dex-pairs 
                      (if msr-fn msr-fn 'none))
             :put)

      (table record-elim-table ',conx-name ',elim-rule :put)
      
      (value-triple (list ',constructor ',destructor-lst)))))


;;--(get-enumerator-symbol 'int) ==> NTH-INT
(defun get-enumerator-symbol (sym)
  (declare (xargs :guard (symbolp sym)))
  (modify-symbol "NTH-" sym ""))

(defun get-enumerator-symbol-lst (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
    nil
    (cons (get-enumerator-symbol (car syms))
          (get-enumerator-symbol-lst (cdr syms)))))

(defun get-uniform-enumerator-symbol (sym)
  (declare (xargs :guard (symbolp sym)))
  (modify-symbol "NTH-" sym "-UNIFORM"))

(defun get-uniform-enumerator-symbol-lst (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
    nil
    (cons (get-uniform-enumerator-symbol (car syms))
          (get-uniform-enumerator-symbol-lst (cdr syms)))))


;;--(get-values-symbol 'foo) ==> *FOO-VALUES*
(defun get-values-symbol (sym)
  (declare (xargs :guard (symbolp sym)))
  (modify-symbol "*" sym "-VALUES*"))

(defun get-values-symbol-lst (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
    nil
    (cons (get-values-symbol (car syms))
          (get-values-symbol-lst (cdr syms)))))



(defun get-predicate-testthm-symbol (sym)
  (declare (xargs :guard (symbolp sym)))
  (modify-symbol "" sym "P-TESTTHM"))

(defun get-predicate-def-thm-symbol (sym)
  (declare (xargs :guard (symbolp sym)))
  (modify-symbol "" sym "P-DEFINITION-THM"))

(defun get-predicate-def-thm-symbol-lst (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
    nil
    (cons (get-predicate-def-thm-symbol (car syms))
          (get-predicate-def-thm-symbol-lst (cdr syms)))))

(defun get-predicate-testthm-symbol-lst (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (if (endp syms)
    nil
    (cons (get-predicate-testthm-symbol (car syms))
          (get-predicate-testthm-symbol-lst (cdr syms)))))

;;--add enumeration events maintaining consistency with history
(defun compute-define-enumeration-type-events (nm psym vsym tsym values wrld)
  (declare (xargs :mode :program))
  (let ((len-v (len values)))
  (list (if (decode-logical-name vsym wrld)
          `(assert-event (set-equalp-equal ',values ,vsym))
          `(progn 
             (defconst ,vsym ',values)
             (defun ,(get-enumerator-symbol nm) (n)
               (declare (xargs :guard (natp n)))
               (nth (mod n ,len-v) ,vsym))))
        (if (decode-logical-name psym wrld)
          `(local (defthm ,tsym
                    (iff (member-equal x ,vsym)
                         (,psym x))
                    :rule-classes nil))
          `(defun ,psym (x)
             (declare (xargs :guard t))
             (if (member-equal x ,vsym) t nil)))
        `(register-custom-type ,nm ,len-v ,vsym ,psym 
                               :type-class enum))))

;--TODO: Instead of guards, the syntax check should be explicit!
(defmacro define-enumeration-type (name values)
  (declare (xargs :guard (and (symbolp name))))
                              ;(true-listp values)))) ;can pass a defconst name too
  `(make-event
    (cons 'progn
          (append
            (compute-define-enumeration-type-events 
               ',name
               (get-predicate-symbol ',name)
               (get-values-symbol ',name)
               (get-predicate-testthm-symbol ',name)
               ,values
               (w state))
            `((value-triple ',',name))))))


#|;Test code
(define-enumeration-type boolean '(t nil))
(define-enumeration-type zero '(0))
(define-enumeration-type asdf '(a s d f))
;|#


; a symbol FOO is a "type" if
;   - FOOP is a recognizer for it and
;   either -NTH-FOO is an enumerator for it (infinite)
;          -*FOO-VALUES* is the set of values for it (finite)



; a "type operator" is, for now, ONEOF or ANYOF (for now, the same)
(deflabel oneof)
(deflabel anyof)

; got rid of LISTOF because it's hard to do implicit recursion
; plus it's pedagogically dubious
;-- got it back in view of its usability --modified by --harshrc
(deflabel listof)
(deflabel record)
(deflabel map);ADDED 3rd May 2011 and again on 17 July '13
(deflabel set)
(deflabel enum)


; a "constructor" is registered as above, with proper arity
; or a macro which expands to function(s) that are constructors



;;--eg:(build-dex-exprs '((car . allp) (cdr . allp)) '(cons x y))
;;-- ==> ((CAR (CONS X Y)) (CDR (CONS X Y))) 
(defun build-dex-exprs (dex-info expr)
  (declare (xargs :mode :program
                  :guard (alistp dex-info)))
  (if (endp dex-info)
    nil
    (cons `(,(caar dex-info) ,expr)
          (build-dex-exprs (cdr dex-info) expr))))




;; syntax-directed translation of data definition
;; to obtain predicate expression list
(mutual-recursion
 (defun er-trans-datadef-as-predicate-lst (defbody-lst new-preds expr-lst
                                            new-constructors ctx wrld state)
   (declare (xargs :mode :program
                   :guard (and (symbol-listp new-preds)
                               (true-listp expr-lst)
                               (= (len expr-lst) (len defbody-lst))
                               (symbol-alistp new-constructors)
                               (symbolp ctx)
                               (plist-worldp wrld))))
   (if (atom defbody-lst)
       (if (null defbody-lst)
           (value nil)
         (er soft ctx "Expecting a true list but last cdr is ~x0" defbody-lst))
     (er-let* ((car-pred
                (er-trans-datadef-as-predicate (car defbody-lst)
                                               new-preds (car expr-lst)
                                               new-constructors
                                               ctx wrld state))
               (cdr-pred-lst
                (er-trans-datadef-as-predicate-lst (cdr defbody-lst)
                                                   new-preds (cdr expr-lst)
                                                   new-constructors
                                                   ctx wrld state)))
      
      (value (cons car-pred cdr-pred-lst)))))

;;-- translate type-expression(defbody) to obtain a predicate expression body
;;-- for a predicate function with argument 'expr', lets say the [[expr]] = v
;;-- cases defbody := 
;;--       1. constant value 'val' => (eq val v) 
;;--       2. predicate symbol(new/in-history) => (pred v)
;;--       3. (oneof ...) => (or ...)
;;--       4. (cons texp1 texp2)  => (and (consp v)
;;--                                      (pred1 (car v))
;;--                                      (pred2 (cdr v)))
;;--       5. new constructor: (node t1 t2 t2) => (nodep v)
;;--       6. macro calls are expanded, then recurse on result
  
 (defun er-trans-datadef-as-predicate (defbody new-preds expr 
                                        new-constructors
                                        ctx wrld state)
   (declare (xargs :guard (and (symbol-listp new-preds)
                               (symbol-alistp new-constructors)
                               (symbolp ctx)
                               (plist-worldp wrld))))
   (cond ((possible-constant-valuep defbody)
          (er-let* ((val (er-get-constant-value defbody ctx wrld state)))
           (let ((comparison (cond ((symbolp val) 'eq)
                                   ((eqlablep val) 'eql)
                                   (t 'equal))))
            (value `(,comparison ,expr ',val)))))
         
         ((symbolp defbody)
          (if (member-eq (get-predicate-symbol defbody) new-preds)
              (let* ((pred (get-predicate-symbol defbody)))
                (value `(,pred ,expr)))
            (er-let* ((pred (er-get-predicate defbody ctx wrld state)))
             (value `(,pred ,expr)))))
         
; should be a cons if we get here
         (t
          (let ((comb (car defbody)))
           (cond 
            ((or (eq comb 'oneof)
                 (eq comb 'anyof))
             (er-let* ((rst (er-trans-datadef-as-predicate-lst
                             (cdr defbody) new-preds
                             (make-list (len (cdr defbody))
                                        :initial-element expr)
                             new-constructors
                             ctx wrld state)))
              (value `(or . ,rst))))

            
            (t ; look up as constructor, then as macro
             (let* ((registered-conx-info 
                     (or (assoc-eq comb (table-alist 'data-constructors wrld))
                         (assoc-eq comb (table-alist 'record-constructors wrld))))
                    (to-be-created-conx-info (assoc-eq comb new-constructors))
                    (conx-info (or registered-conx-info to-be-created-conx-info)))
               (if conx-info
                   (let ((conx-pred (predicate-name-entry conx-info))
                         (dex-info (dex-pairs-entry conx-info)))
                    (if registered-conx-info
                        (er-let* ((rst (er-trans-datadef-as-predicate-lst
                                        (cdr defbody) new-preds
                                        (build-dex-exprs dex-info expr)
                                        new-constructors
                                        ctx wrld state)))
                         (value `(and (,conx-pred ,expr)
                                      . ,rst)))
;harshrc: The reason why the following is different from the
;registered-conx-info, is that one can have a (cons string int), where
;the string and int are stronger requirements than allp of cons
;requires. But when we are constructing a new record on the fly, say
;(oneof 'Leaf (node (key . int) (left . tree) (right . tree))), the
;requirements are tight and hence there is no reason to recur on the
;components, since their type constraints are reflected in nodep itself.
                      (value (list conx-pred expr))))
                 (if (true-listp (acl2-getprop comb 'macro-args wrld
                                               :default :undefined))
                     
                     ;; attempt macro expansion
                     (er-let* ((newdefbody (macroexpand1 defbody ctx state)))
                      (er-trans-datadef-as-predicate newdefbody new-preds expr
                                                     new-constructors
                                                     ctx wrld state))
                   ;; otherwise, illegal
                   (er soft ctx "~x0 is not a recognized constructor or ~
                                 type combinator." comb))))))))))
)

;;--If all arguments are constant values, then the constructor calls can be
;;--evaluated/combined using the following functions to obtain constant values.
;;e.g:
#||
(EVAL-FN-COMBINE-ARG-LSTS 'cons
                             '((a b) ("g" ((12) . c) ((x "no") . ok)))
                             'top-level state)
 ((A . "g")
  (B . "g")
  (A (12) . C)
  (B (12) . C)
  (A (X "no") . OK)
  (B (X "no") . OK))
||#

(defun eval-fn-combine-arg-lsts0 (fn arglst-sofar rev-arglsts ctx state)
  (declare (xargs :mode :program))
  (cond ((endp rev-arglsts)
         (er-let* ((v (trans-eval-single-value (cons fn arglst-sofar) ctx state)))
           (value (list v))))
        ((endp (car rev-arglsts))
         (value nil))
        (t
         (er-let*
           ((values1 (eval-fn-combine-arg-lsts0 fn
                                                (cons (list 'quote (caar rev-arglsts))
                                                      arglst-sofar)
                                                (cdr rev-arglsts)
                                                ctx state))
            (values2 (eval-fn-combine-arg-lsts0 fn
                                                arglst-sofar
                                                (cons (cdar rev-arglsts)
                                                      (cdr rev-arglsts))
                                                ctx state)))
           (value (union-equal values1 values2))))))

(defun eval-fn-combine-arg-lsts (fn arglsts ctx state)
  (declare (xargs :mode :program))
  (eval-fn-combine-arg-lsts0 fn nil (reverse arglsts) ctx state))




;static analysis of data-definitions to get finite data defs:
;fixed point iteration over data def structure.
(mutual-recursion
 (defun er-get-finite-data-def-lst (defbody-lst finite-defs 
                                     new-constructors
                                     ctx wrld state)
   (declare (xargs :mode :program
                   :guard (and (true-listp defbody-lst)
                               (symbol-alistp finite-defs)
                               (symbol-alistp new-constructors)
                               (symbolp ctx)
                               (plist-worldp wrld))))
   (if (endp defbody-lst)
       (value nil)
     (er-let* ((fst (er-get-finite-data-def (car defbody-lst) finite-defs
                                            new-constructors ctx wrld state))
               (rst (er-get-finite-data-def-lst (cdr defbody-lst) finite-defs
                                                new-constructors ctx wrld state)))
      (value (cons fst rst)))))  

 ;; (value nil) if infinite or (value <list of values>) if finite 
 (defun er-get-finite-data-def (defbody finite-defs new-constructors ctx wrld state)
   (declare (xargs :guard (and (symbol-alistp finite-defs)
                               (symbol-alistp new-constructors)
                               (symbolp ctx)
                               (plist-worldp wrld))))
   (cond ((possible-constant-valuep defbody);is a constant(singleton type)
          (er-let* ((val (er-get-constant-value defbody ctx wrld state)))
           (value (list val))))
         ((symbolp defbody) ;is a symbol (typename)
          (if (assoc-eq defbody finite-defs)
              (value (cdr (assoc-eq defbody finite-defs)))
            (let* ((vsym (get-values-symbol defbody))
                   (quoted-values (acl2-getprop vsym 'const wrld)))
              ;; assume infinite if values not available
              (if quoted-values
                  (value (cadr quoted-values)) ; unquote
                (value nil)))))
         ;; should be a cons if we get here
         (t ; either a product or union type expression or a macro call
          (let ((comb (car defbody)))
           (cond 
            ((or (eq comb 'oneof)
                 (eq comb 'anyof)) ;UNION
             (er-let* ((rst (er-get-finite-data-def-lst
                             (cdr defbody) finite-defs
                             new-constructors
                             ctx wrld state)))
              (if (member-eq nil rst) ; at least one infinite branch
                  (value nil)
                (value (union-lsts rst)))))
            (t ; look up as constructor(registered or new), then as macro
             (let* ((reg-conx-info 
                     (or (assoc-eq comb (table-alist 'data-constructors wrld))
                         (assoc-eq comb (table-alist 'record-constructors wrld))))
                    (to-be-created-conx-info (assoc-eq comb new-constructors))
                    (conx-info (or reg-conx-info 
                                   to-be-created-conx-info)))
                    
                    ;;--conx-info e.g: (cons (:proper)
                    ;;--                 consp (car . allp) (cdr . allp))
                    ;;-- what if its a macro? say list, will it already be
                    ;;-- expanded when it reaches here? No, it gets expanded here only.
               (if conx-info ;PRODUCT TYPE EXPRESSION
                   (er-let* ((rst (er-get-finite-data-def-lst
                                   (cdr defbody) finite-defs
                                   new-constructors
                                   ctx wrld state)))
                    (if (or (member-eq nil rst) ; at least one infinite branch

; added the following condition to fix BUG below (June 26th '13), but this
; breaks the invariant that this function returns nil only for
; infinite types (ACHTUNG)
                            to-be-created-conx-info) ;records
                        (value nil)
                      (eval-fn-combine-arg-lsts 
; harshrc 28th Aug '12: TODO - check if list* is a mistake or not. (BUG)
; 26th June '13 - list* is wrong, records are implemented differently now.
                       comb ;(if reg-conx-info comb 'list*) 
                       rst ctx state)))
                 (if (true-listp (acl2-getprop comb 'macro-args wrld 
                                               :default :undefined))
;MACRO CALL
                     ;; attempt macro expansion
                     (er-let* ((newdefbody (macroexpand1 defbody ctx state)))
                      (er-get-finite-data-def newdefbody finite-defs
                                              new-constructors
                                              ctx wrld state))
                   ;; otherwise, illegal
                   (er soft ctx "~x0 is not a recognized constructor or ~
                                  type combinator." comb))))))))))
)

; step in iteration
 (defun er-get-finite-data-defs1 (defs finite-defs new-constructors ctx wrld state)
   (declare (xargs :mode :program
                   :guard (and (symbol-alistp defs)
                               (symbol-alistp finite-defs)
                               (symbol-alistp new-constructors)
                               (symbolp ctx)
                               (plist-worldp wrld))))
   (cond ((endp defs)
          (value finite-defs))
         ((assoc-eq (caar defs) finite-defs)
          (er-get-finite-data-defs1 (cdr defs) finite-defs new-constructors ctx wrld state))
         (t
          (er-let* ((new-def (er-get-finite-data-def (cadar defs) finite-defs
                                                     new-constructors
                                                     ctx wrld state)))
           (er-get-finite-data-defs1 (cdr defs)
                                     (if new-def ; finite (nil -> infinite)
                                         (cons (cons (caar defs)
                                                     new-def)
                                               finite-defs)
                                       finite-defs)
                                     new-constructors 
                                     ctx wrld state)))))


             

; iterate until fixed point
 (defun er-get-finite-data-defs0 (defs finite-defs new-constructors ctx wrld state)
   (declare (xargs :mode :program
                   :guard (and (symbol-alistp defs)
                               (symbol-alistp finite-defs)
                               (symbol-alistp new-constructors)
                               (symbolp ctx)
                               (plist-worldp wrld))))
   (er-let* ((new-finite-defs (er-get-finite-data-defs1 defs finite-defs
                                                        new-constructors
                                                        ctx wrld state)))
    (if (equal finite-defs new-finite-defs)
        (value new-finite-defs)
      (er-get-finite-data-defs0 defs new-finite-defs new-constructors ctx wrld state))))
    
; Start fix-point iteration
(defun er-get-finite-data-defs (defs new-constructors ctx wrld state)
  (declare (xargs :mode :program
                  :guard (and (symbol-alistp defs)
                              (symbolp ctx)
                              (symbol-alistp new-constructors)
                              (plist-worldp wrld))))
  (er-get-finite-data-defs0 defs nil new-constructors ctx wrld state))



#|| ;test code

(define-enumeration-type boolean '(t nil))
(register-data-constructor (consp cons)
                           ((allp car) (allp cdr))
                           :proper t)


; harshrc Jun 26 '13: why would anyone define such a type clique?
(er-get-finite-data-defs '((foo (oneof 42 (cons boolean baz)))
                           (bar (oneof nil
                                       (cons foo bar)))
                           (moo nil)
                           (baz (cons boolean moo)))
                         nil
                         'top-level (w state) state)
||#



;;-- gives back enumerator information
;;-- e.g:
;;-- (er-get-enumeration-info 'integer 'x nil '(acl2::nth-integer acl2::nth-rational) 'top-level (w state) state)
;;-- ==> (T ACL2::NTH-INTEGER X)
;;-- if nth-integer is already defined in current world then:
;;-- (er-get-enumeration-info 'integer 'x nil nil 'top-level (w state) state)
;;-- ==> (T ACL2::NTH-INTEGER X)
;;-- (er-get-enumeration-info 'boolean 'x nil nil 'top-level (w state) state)
;;-- ==> (2 NTH X *BOOLEAN-VALUES*)
 
(defun er-get-enumeration-info (type-name expr finite-defs inf-enum-syms uniform? ctx wrld state)
"returns (cons size enumcall), where size is the size of type-name and enumcall is
formed from expr and the enumerator associated with type-name."
  (declare (xargs :mode :program
                  :guard (and (symbolp type-name)
                              (symbol-alistp finite-defs)
                              (symbol-listp inf-enum-syms)
                              (symbolp ctx)
                              (booleanp uniform?)
                              (plist-worldp wrld))))
  (let* ((vsym (get-values-symbol type-name))
         (values (or (second (acl2-getprop vsym 'const wrld))
                     (cdr (assoc-eq vsym finite-defs)))))
    (if values
      (let ((len-v (len values)))
        (value (cons len-v
                     (if (= len-v 1)  
                       (if uniform?
                           `(mv ',(car values) seed)
                         `',(car values))
                       (if uniform?
                           `(mv (nth (mod seed ,len-v) ,vsym) seed)
                         `(nth ,expr ,vsym))))))
      (let* ((esym (if uniform? 
                       (get-uniform-enumerator-symbol type-name)
                     (get-enumerator-symbol type-name))))
             
        ;;-check if arity matches(implicit check if enum is defined in wrld)
        (cond ((allows-arity esym (if uniform? 2 1) wrld)
               (if uniform? 
                   (value (cons t `(,esym m seed)))
                 (value (cons t `(,esym ,expr)))))
              ((member-eq esym inf-enum-syms)
               (if uniform? 
;14 July 2013
;every recursive call is given a probably different measure argument
; 21 July - due to termination issues in mutual-recursive defs, lets simply do a 1-/zp recursion. todo hack 
                   (value (cons t ;(mv-let (m seed) (random-index-seed m seed) 
                                           `(,esym m seed)))
                   (value (cons t `(,esym ,expr)))))
              (t       
               (er soft ctx
                   "Type specifier ~x0 is invalid. To be valid, it needs a valid ~
                    enumerator ~x1 or a valid list of values ~x2."
                   type-name esym vsym)))))))

#||
(define-enumeration-type boolean '(t nil))

(register-data-constructor (consp cons)
                           ((allp car) (allp cdr))
                           :proper t)

(defconst *foo-values* '(1 2 3))
(defconst *bar-values* '(a))
(er-get-enumeration-info 'foo 'x nil nil nil 'top-level (w state) state)
(er-get-enumeration-info 'bar 'x nil nil nil 'top-level (w state) state)
||#

(defun get-inf-enum-infos (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l)
         l)
        ((and (consp (car l))
              (eq 't (caar l)))
         (cons (car l)
               (get-inf-enum-infos (cdr l))))
        (t
         (get-inf-enum-infos (cdr l)))))

; finite size = 1 i.e.  singleton values)
(defun get-singleton-enum-infos (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l)
         l)
        ((and (consp (car l))
              (equal 1 (caar l));size 1
              ;(possible-constant-valuep (cdar l)) ;Comes from trusted code, so no need.
              );singleton value
         (cons (car l)
               (get-singleton-enum-infos (cdr l))))
        (t
         (get-singleton-enum-infos (cdr l)))))

; fin = finite size > 1 (i.e. finite but not singleton values)
(defun get-fin-enum-infos (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l)
         l)
        ((and (consp (car l))
              (natp (caar l))
              (not (and (equal 1 (caar l))
                        ;(possible-constant-valuep (cdar l)) ;Comes from trusted code, so no need.
                   )));not singleton value
                    
         (cons (car l)
               (get-fin-enum-infos (cdr l))))
        (t
         (get-fin-enum-infos (cdr l)))))



(defun +-cars0 (l acc)
  (declare (xargs :mode :program))
  (if (endp l)
      acc
    (+-cars0 (cdr l) (+ acc (caar l)))))

(defun +-cars (l)
  (declare (xargs :mode :program))
  (+-cars0 l 0))

(defun *-cars0 (l acc)
  (declare (xargs :mode :program))
  (if (endp l)
      acc
    (*-cars0 (cdr l) (* acc (caar l)))))

(defun *-cars (l)
  (declare (xargs :mode :program))
  (*-cars0 l 1))



;NOTE: enum-info-lst that the following 2 functions
;gets as arguments is a sorted one, with singleton enums
; finite-enums occurring before the inf-enums in the lst
;enum-info-lst is of form : (size/magnitude . (enumerator call)) or (1 . constant-value)

;build union expressions for generating enumerator functions
(defun build-inf-choices-enum-n (enum-info-lst n)
  (declare (xargs :mode :program))
  (cond ((not (consp enum-info-lst))
         ':error)
        ((not (consp (cdr enum-info-lst)))
         (cdar enum-info-lst))
        (t
         `(if (= n ,n)
              ,(cdar enum-info-lst)
            ,(build-inf-choices-enum-n (cdr enum-info-lst) (1+ n))))))

; enum-info-lst should always be a cons
(defun build-choice-enum1 (enum-info-lst)
  (declare (xargs :mode :program))
  (cond ((not (consp enum-info-lst))
         ':error);should not get here
        ((not (consp (cdr enum-info-lst)))
         (cdar enum-info-lst));the last choice
;remaining have atleast 2 choices
        ((natp (caar enum-info-lst)) ; finite
         `(if (< x ,(caar enum-info-lst)) ;pushed the (not integerp) call to build-choice-enum
              ,(cdar enum-info-lst)
            ,(if (and (not (consp (cddr enum-info-lst))) ;if the next choice is the last one
                      (equal 1 (caadr enum-info-lst))) ;and is a singleton
                 (build-choice-enum1 (cdr enum-info-lst));dont do a let
               `(let ((x (- x ,(caar enum-info-lst))))
                  ,(build-choice-enum1 (cdr enum-info-lst))))))
        (t ; assume all remaining are infinite
         (let ((nchoices (len enum-info-lst)))
           `(mv-let 
             (n x)
             (switch-nat ,nchoices (nfix x)) ;nfix helps termination
             ,(build-inf-choices-enum-n enum-info-lst 0))))))


;harshrc: we dont need repeated (or (not (integerp x) ..) calls, once in the
;beginning is enough. This improves readability of generated enums

(defun build-choice-enum (enum-info-lst)
  (declare (xargs :mode :program))
  (cond ((not (consp enum-info-lst))
         ':error)
        ((not (consp (cdr enum-info-lst)))
         (cdar enum-info-lst)) ;no need to change here anything(cos this is a top-level call only)
        ((natp (caar enum-info-lst)) ; finite
         `(if (or (not (integerp x));top-level check for non-integers
                  (< x ,(caar enum-info-lst)))
              ,(cdar enum-info-lst)
            ;;if the next choice is the last one
            ,(if (and (not (consp (cddr enum-info-lst)))
                      (equal 1 (caadr enum-info-lst))) ;and is a singleton
                 (build-choice-enum1 (cdr enum-info-lst));dont do a let
               `(let ((x (- x ,(caar enum-info-lst))))
                  ,(build-choice-enum1 (cdr enum-info-lst))))))
        (t ; assume all remaining are infinite
         (let ((nchoices (len enum-info-lst)))
           `(mv-let (n x)
                    (switch-nat ,nchoices  (nfix x));nfix helps termination
                    ,(build-inf-choices-enum-n enum-info-lst 0))))))

#||
(build-choice-enum '((5 nth x *blah5*)
                     (7 nth x *blah7*)
                     (1 quote nil)
                     (t nth-whatever x)
                     (t nth-moo x)))

(build-choice-enum '((1 quote nil)
                     (1 quote pl)
                     (5 nth x *blah5*)
                     (7 nth x *blah7*)
                     (t nth-whatever x)
                     (t nth-moo x)
                     ))
                     
||#

(defun build-case-clauses-enum-uniform (enum-info-lst i)
  (declare (xargs :verify-guards nil
                  :guard (and (true-listp enum-info-lst)
                              (implies (consp enum-info-lst) (consp (car enum-info-lst)))
                              (natp i))))
  (if (endp enum-info-lst)
      '()
    (if (endp (cdr enum-info-lst))
        `((otherwise ,(cdar enum-info-lst)))
    (b* ((enum-call (cdar enum-info-lst)))
      (cons `(,i ,enum-call)
            (build-case-clauses-enum-uniform (cdr enum-info-lst) (1+ i)))))))
         


(defun build-choice-enum-uniform-nonrec (nonrec-eil len-nonrec)
  (declare (xargs :verify-guards nil));(consp nonrec-eil)
  (if (<= len-nonrec 1)
      (cdar nonrec-eil)
    `(mv-let (n seed)
             (random-index-seed ,len-nonrec seed)
             (case n ,@(build-case-clauses-enum-uniform nonrec-eil 0)))))

(defun build-choice-enum-uniform (nonrec-eil rec-eil)
  (declare (xargs :verify-guards nil)) ;(consp nonrec-eil)
  (b* ((len-nonrec (len nonrec-eil))
       (len-rec (len rec-eil)))
    (if (consp rec-eil)
        `(if (or (zp m)
                 (not (unsigned-byte-p 31 seed))) ;for termination proofs
             ,(build-choice-enum-uniform-nonrec nonrec-eil len-nonrec)
           ,(if (<= len-rec 1)
                `(let ((m (1- m))) ;to ensure termination
                   ,(cdar rec-eil))
              `(let ((m (1- m))) ;to ensure termination
                 (mv-let (n seed)
                         (random-index-seed ,len-rec seed)
                         (case n ,@(build-case-clauses-enum-uniform rec-eil 0))))))
      (build-choice-enum-uniform-nonrec nonrec-eil len-nonrec))))
      


;build up product expressions for enumerator functions to be generated
;order is maintained while generating values
;enum-info-lst is of form : (size/magnitude . (enumerator call)) or (1 . constant-value)
(defun build-product-comb-enum-actuals (enum-info-lst fin-n inf-n)
  (declare (xargs :mode :program))
  (cond ((endp enum-info-lst)
         nil)
        ((equal 1 (caar enum-info-lst));singleton
         (cons (cdar enum-info-lst)
               (build-product-comb-enum-actuals (cdr enum-info-lst) fin-n inf-n)))
        ((natp (caar enum-info-lst)) ; finite enum info
         (cons `(let ((x (nth ,fin-n finxlst)))
                  ,(cdar enum-info-lst))
               (build-product-comb-enum-actuals (cdr enum-info-lst) (1+ fin-n) inf-n)))
        (t                           ; infinite
         (cons `(let ((x (nth ,inf-n infxlst)))
                  ,(cdar enum-info-lst))
               (build-product-comb-enum-actuals (cdr enum-info-lst) fin-n (1+ inf-n))))))

(defun get-fin-and-sing-enum-infos (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l)
         l)
        ((and (consp (car l))
              (natp (caar l)))
         (cons (car l)
               (get-fin-and-sing-enum-infos (cdr l))))
        (t
         (get-fin-and-sing-enum-infos (cdr l)))))


(defun build-product-comb-enum (enum-info-lst conx)
  (declare (xargs :mode :program))
  (let* ((fin-info-lst (get-fin-and-sing-enum-infos enum-info-lst))
         (fin-info-lst1 (get-fin-enum-infos enum-info-lst))
         (inf-info-lst (get-inf-enum-infos enum-info-lst))
         (call (cons conx (build-product-comb-enum-actuals enum-info-lst 0 0)))
         (expr1 (if (consp inf-info-lst)
                    (if (null (cdr inf-info-lst)) ;len=1
                        `(let ((infxlst (list (nfix x))));29 Apr 2011 fix termination of mut-rec enum-fns
                           ,call)
                      `(let ((infxlst (split-nat ,(len inf-info-lst) (nfix x))));29 Apr 2011 fix termination of mut-rec enum-fns
                         ,call))
                  call))
         (expr2 (if fin-info-lst1 ;only if there are choices to be made(in singleton theres no choice)
                    (if inf-info-lst
                        `(mv-let 
                          (finxlst x)
                          (multiple-switch-nat ',(strip-cars fin-info-lst)
                                               (nfix x));nfix helps termination
                          ;;pass on the seed if there are inf enums ahead
                          ,expr1)
                      `(mv-let 
                        (finxlst x)
                        (multiple-switch-nat ',(strip-cars fin-info-lst)
                                             (nfix x));nfix helps termination
                        (declare (acl2::ignorable x))
                        ;;dont pass on seed if no inf enums ahead
                        ,expr1))
                  ;;else
                  expr1)))
    expr2))

(program)
(defun make-name-with-pos-suffix (expr i ans)
  (if (zp i)
      ans
    (make-name-with-pos-suffix expr (1- i) 
                               (cons (modify-symbol "" expr (to-string i)) ans))))

(defun build-product-comb-enum-uniform1 (enum-info-lst expr i body)
  (if (endp enum-info-lst)
      body
    `(mv-let (,(modify-symbol "" expr (to-string i)) seed)
             ,(cdar enum-info-lst)
             ,(build-product-comb-enum-uniform1 (cdr enum-info-lst) 
                                                     expr (1+ i) body))))

(defun build-product-comb-enum-uniform (enum-info-lst comb)
  (let ((expr 'val))
    (build-product-comb-enum-uniform1 
     enum-info-lst expr  1 
     `(mv (,comb ,@(make-name-with-pos-suffix expr (len enum-info-lst) '())) 
          (the (unsigned-byte 31) seed)))))
    
(logic)

#||
(build-product-comb-enum '((t nth-whatever x)
                           (1  quote nil)
                           (5 nth x *blah5*)
                           (7 nth x *blah7*)
                           (t nth-moo x)
                           )
                 'list)
(build-product-comb-enum '((1  quote nil)
                           (1  quote 1)
                           (1 .  2)
                           (t nth-what x)
                           (t nth-moo x))
                 'woo)

||#



;2 funs added by harshrc
(defun found-recursive-enum-call (inf-enum-call inf-enum-syms)
  (declare (xargs :guard (true-listp inf-enum-syms)))
  (if (endp inf-enum-syms)
      nil
    (if (mem1 (car inf-enum-syms) (flatten inf-enum-call nil)) 
;if found a inf-enum in the call its recursive return immediately
        t 
      (found-recursive-enum-call inf-enum-call (cdr inf-enum-syms)))))
    
(local (defthm append-of-2-lists-is-true-list
         (implies (and (true-listp x1)
                       (true-listp x2))
              (true-listp (append x1 x2)))
         :rule-classes :type-prescription))
     
;partition enums by those which are base cases first, ie non-recursive
;This fun fixes a bug where theres a recursive defdata and the sequence is
;such that in the oneof the recursive case comes first than the base case
;BUG-FIX: This sorting function is not stable i.e it changes the order
;of those enums with the same size.
(defun partition-inf-enum-infos (inf-enum-infos inf-enum-syms non-rec-ans rec-ans)
  (declare (xargs :verify-guards nil
                  :guard (and (true-listp inf-enum-syms)
                              (true-listp rec-ans)
                              (true-listp non-rec-ans))))
  (if (endp inf-enum-infos)
      (mv non-rec-ans rec-ans)
    (if (found-recursive-enum-call (cdr (car inf-enum-infos)) inf-enum-syms)
        (partition-inf-enum-infos (cdr inf-enum-infos) 
                                  inf-enum-syms
                                  non-rec-ans
                                  ;;add to rec-ans in order
                                  (append rec-ans (list (car inf-enum-infos))))
      (partition-inf-enum-infos (cdr inf-enum-infos) 
                                inf-enum-syms
                                ;;add to non-rec-ans in order
                                (append non-rec-ans (list (car inf-enum-infos)))
                                rec-ans))))
                
                           
                           
         
  
;; (sort-inf-enum-infos '( (T LET ((INFXLST (SPLIT-NAT 2 X)))
;;                            (CONS (LET ((X (NTH 0 INFXLST)))
;;                                       (ACL2::NTH-INTEGER X))
;;                                  (LET ((X (NTH 1 INFXLST)))
;;                                       (NTH-FOO X))))
;;                        (T ACL2::NTH-INTEGER X)) '(nth-foo) nil)


;;; the following clique builds enumerators of product and union types
;;; inf <- inf * inf - use split-nat to get two naturals
;;; inf <- inf * fin - use switch-nat to get one natural and one bounded val
;;; inf <- inf + inf - use switch-nat with 2 possibilies to determine which
;;;                    possibility to choose and the natural number to give it
;;; inf <- inf + fin - if < #finite posibilities, use that.  otherwise,
;;;                    subtract #finite possibilities to get natural
;;; split-nat : bijection from N -> N * N (takes a Nat and returns two Nat)
;;; switch-nat: takes a number of possibilities and another natural number
;;; and returns a value from 0 to possibilities-1 and a natural number.
(mutual-recursion
(defun er-trans-datadef-as-enumerator-lst (defbody-lst finite-defs 
                                            inf-enum-syms uniform?
                                             new-constructors ctx wrld state)
   (declare (xargs :mode :program 
                   :guard (and (symbol-alistp finite-defs)
                               (symbol-listp inf-enum-syms)
                               (symbol-alistp new-constructors)
                               (symbolp ctx)
                               (booleanp uniform?)
                               (plist-worldp wrld))))
   (if (atom defbody-lst)
       (if (null defbody-lst)
           (value nil)
         (er soft ctx "Expecting a true list but last cdr is ~x0" defbody-lst))
     (er-let* ((car-stuff
                (er-trans-datadef-as-enumerator (car defbody-lst)
                                                finite-defs inf-enum-syms
                                                uniform? new-constructors
                                                ctx wrld state))
               (cdr-stuff-lst
                (er-trans-datadef-as-enumerator-lst (cdr defbody-lst)
                                                    finite-defs inf-enum-syms
                                                    uniform? new-constructors
                                                    ctx wrld state)))
       (value (cons car-stuff cdr-stuff-lst)))))

(defun er-trans-datadef-as-enumerator (defbody finite-defs inf-enum-syms
                                         uniform? new-constructors ctx wrld state)
   (declare (xargs :guard (and (symbol-alistp finite-defs)
                               (symbol-listp inf-enum-syms)
                               (symbol-alistp new-constructors)
                               (symbolp ctx)
                               (booleanp uniform?)
                               (plist-worldp wrld))))
   (cond ((possible-constant-valuep defbody)
          (er-let* ((val (er-get-constant-value defbody ctx wrld state)))
           (value (cons 1 (if uniform? 
                              `(mv ',val seed)
                            `',val)))))
         ((symbolp defbody)
          (er-get-enumeration-info defbody 'x
                                   finite-defs inf-enum-syms uniform?
                                   ctx wrld state)) ;the only place finite-defs is used
; should be a cons if we get here
         (t
          (let ((comb (car defbody)))
           (cond 
            ((or (eq comb 'oneof)
                 (eq comb 'anyof))
             (if (atom (cdr defbody))
                 (er soft ctx "~x0 must be given at least one argument." comb)
               (er-let* ((rst (er-trans-datadef-as-enumerator-lst
                               (cdr defbody) finite-defs inf-enum-syms
                               uniform? new-constructors
                               ctx wrld state)))
                 (b* ((singleton-rst (get-singleton-enum-infos rst))
                      (fin-rst (get-fin-enum-infos rst))
                      (inf-rst (get-inf-enum-infos rst))
                      ((mv nonrec-inf-rst rec-inf-rst) 
                       (partition-inf-enum-infos inf-rst inf-enum-syms nil nil))
;finite values enumerated first and in inf case, base case come first
;by base case i mean non-recursive enums --harshrc (this fixes a bug)
                      (new-rst (append singleton-rst 
                                       fin-rst
                                       nonrec-inf-rst
                                       rec-inf-rst)) 
;build union enum expression
                      (enumerator (if uniform?
                                      (build-choice-enum-uniform (append singleton-rst fin-rst nonrec-inf-rst) 
                                                                 rec-inf-rst)
                                    (build-choice-enum new-rst)))
                      (magnitude (or (consp inf-rst) 
;add finite sizes if no inf exists
                                     (+ (len singleton-rst)
                                        (+-cars fin-rst)))))
                  (value (cons magnitude enumerator))))))

            (t 
; look up as constructor(registered or new), then as macro
             (b* ((registered-conx-info (or (assoc-eq comb (table-alist 'data-constructors wrld))
                                            (assoc-eq comb (table-alist 'record-constructors wrld))))
                  (to-be-created-conx-info (assoc-eq comb new-constructors))
                  ((unless (or registered-conx-info 
                               to-be-created-conx-info
                               (true-listp (acl2-getprop comb 'macro-args wrld
                                               :default :undefined))))
                   ;; illegal
                   (er soft ctx "~|~x0 is not a type combinator, a recognized constructor or a macro expanding to one.~|" comb)))
                   
                    
               (er-let* ((rst (er-trans-datadef-as-enumerator-lst
                               (cdr defbody) finite-defs inf-enum-syms
                               uniform? new-constructors
                               ctx wrld state)))
                 (let* (;(singleton-rst (get-singleton-enum-infos rst)) ;No need to multiple below by 1
                        (fin-rst (get-fin-enum-infos rst))
;build product enum expression
                        (inf-rst (get-inf-enum-infos rst)) 
                        (enumerator (if uniform? 
                                        (build-product-comb-enum-uniform rst comb) 
                                      (build-product-comb-enum rst comb))) ; order matters
                        (magnitude (or (consp inf-rst) 
;multiply finite sizes if no inf exists
                                       (*-cars fin-rst))))
                   (value (cons magnitude enumerator))))
                     ;; ;; attempt macro expansion -- 12 July 2013 - no need to do this here like in trans-predicate
                     ;; (er-let* ((newdefbody (macroexpand1 defbody ctx state)))
                     ;;  (er-trans-datadef-as-enumerator newdefbody
                     ;;                                  finite-defs 
                     ;;                                  inf-enum-syms
                     ;;                                  uniform?
                     ;;                                  new-constructors 
                     ;;                                  ctx wrld state))
                   )))))))
)


#||
(define-enumeration-type boolean '(t nil))
(register-data-constructor (consp cons)
                           ((allp car) (allp cdr))
                           :proper t)
;(defconst *foo-values* '(1 2 3))
(er-trans-datadef-as-enumerator-lst
 '((oneof (cons integer
                foo)
          integer))
 nil
 '(nth-foo acl2::nth-integer) ;;-- changed from foo
 nil
 'top-level
 (w state)
 state)
||#


(defun cons-up-names-decls-lls-bodies (names decls lls bodies)
  (declare (xargs :guard (and (true-listp names)
                              (true-listp decls)
                              (true-listp lls)
                              (true-listp bodies))))
  (if (endp names)
    nil
    (cons (if (consp decls);not null (only include declare if its not empty)
            (list (car names) (car lls) (car decls) (car bodies))
            (list (car names) (car lls) (car bodies)))
          (cons-up-names-decls-lls-bodies (cdr names)
                                    (cdr decls)
                                    (cdr lls)
                                    (cdr bodies)))))


(defun collect-with-plausible-pred-fns (lst wrld)
  (declare (xargs :guard (and (symbol-listp lst)
                              (plist-worldp wrld))))
  (if (endp lst)
    nil
    (if (plausible-predicate-functionp (get-predicate-symbol (car lst)) wrld)
      (cons (car lst)
            (collect-with-plausible-pred-fns (cdr lst) wrld))
      (collect-with-plausible-pred-fns (cdr lst) wrld))))


;;Record types
;;1. make constructor, its predicate, and the destructors
;;2. register the above using register-data-constructor
#|
(defdata tree (oneof nil
                     (node (val . symbol) (left . tree) (right . tree))))

==>
(defdata tree (oneof nil
                     (node symbol tree tree))) ;just like peters version
X:tree = (node 'a (node 'b nil nil) nil)
X:tree = (node (val . 'a) (left . (node (val . 'b) (left . nil) (right . nil))) (right . nil)) 

(defdata cons (record (car . all) (cdr . all)))

X:cons = (record (car . '("sd" 2 3)) (cdr . 'abc))
X:cons = (cons '("sd 2 3) 'abc)

(defdata triple (record (fst . all) (scd . all) (thd . all)))
X:triple = (record (fst . 1) (scd . "hello") (thd . '(+ 23 45))) ;can be recog, cos destr are unique
X:triple = (triple 1 "hello" '(+ 23 45))


(defdata hyperlink (record (protocol . string)
                           (address . string)
                           (display . string)))
X:hyperlink = (record (protocol . "httpx") (display . "my site") (address . "192.168.1.10"))
==>
X:hyperlink = (hyperlink "httpx" "my site" "192.168.1.10")
|#


(defun build-dex-recordImpl-bindings (dex-names dex-var-names rec-expr)
  (declare (xargs :guard (and (symbol-listp dex-names)
                              (symbol-listp dex-var-names)
                              (= (len dex-var-names)
                                 (len dex-names)))))
  (if (endp dex-names)
    nil
    (let* ((dname (car dex-names))
           (dname-var (car dex-var-names))
           (d-keyword-name (intern (symbol-name dname) "KEYWORD")))
      (cons (list dname-var (list 'mget d-keyword-name rec-expr))
            (build-dex-recordImpl-bindings (cdr dex-names) (cdr dex-var-names) rec-expr)))))

(defthm build-dex-recordImpl-bindings-sig1
  (acl2::all->=-len (build-dex-recordImpl-bindings dex-names dex-var-names rec-expr)
                    2))

(defun build-dex-alist (dex-names dex-var-names)
  (declare (xargs :guard (and (symbol-listp dex-names)
                              (symbol-listp dex-var-names)
                                 )))
                  
  (if (endp dex-names)
    nil
    (let* ((dname (car dex-names))
           (dvar-name (car dex-var-names))
           (d-keyword-name (intern (symbol-name dname) "KEYWORD")))
      `(mset ,d-keyword-name ,dvar-name
          ,(build-dex-alist (cdr dex-names) (cdr dex-var-names))))))

;;make a constructor defun and corresponding predicate
(defun make-constructor-predicate (conx-name dex-pairs)
  (declare (xargs :guard (and (symbolp conx-name)
                              (symbol-alistp dex-pairs))))
                  ;:guard-hints (("Goal" :in-theory (disable modify-symbol string-append)))))
  (let* ((dex-orig-names (strip-cars dex-pairs))
         (prefix (string-append (symbol-name conx-name) "-"))
         (dex-names (modify-symbol-lst prefix dex-orig-names "")) ;make new prefixed destr names
         (dex-preds (strip-cdrs dex-pairs))
         (dex-var-names (modify-symbol-lst "Var" dex-names ""))
         (dex-prex-calls (build-one-param-calls dex-preds dex-var-names))
         (dex-alist (build-dex-alist dex-orig-names dex-var-names))
         (dex-bindings  (build-dex-recordImpl-bindings dex-orig-names dex-var-names 'v))
        
         (conx-pred (get-predicate-symbol conx-name)))
    `((defund ,conx-pred (v) ;disabled def
        (declare (xargs :guard t))
        (if (not (acl2::good-map v));for guards and termination (CCG)
          nil
          (let ,dex-bindings 
            (and  (equal v (mset 'constructor ',conx-name ,dex-alist))
                  ,@dex-prex-calls 
                  )))))))
  

;cons-up calls of above function
(defun cons-up-conx-prex-ev (conx-names dex-pairs-lst)
  (declare (xargs :guard (and (symbol-listp conx-names)
                              (true-list-symbol-alistp dex-pairs-lst)
                              (= (len conx-names) (len dex-pairs-lst)))))
  (if (endp conx-names)
    nil
    (append (make-constructor-predicate (car conx-names) (car dex-pairs-lst))
            (cons-up-conx-prex-ev (cdr conx-names) (cdr dex-pairs-lst)))))





;guard verif thm
(defthm symbol-alistp-strip-cars-is-symbol-listp
  (implies (symbol-alistp P)
           (symbol-listp (strip-cars P)))
  :rule-classes :tau-system)
           

;make the event for defining constructor
(defun make-constructor (conx-name dex-pairs)
  (declare (xargs :guard (and (symbolp conx-name)
                              (symbol-alistp dex-pairs))))
  (let* ((dex-orig-names (strip-cars dex-pairs))
         (prefix (string-append (symbol-name conx-name) "-"))
         (dex-names (modify-symbol-lst prefix dex-orig-names "")) ;make new prefixed destr names
         (dex-prex (strip-cdrs dex-pairs))
         (dex-var-names (modify-symbol-lst "Var" dex-names ""))
         (dex-prex-calls (build-one-param-calls dex-prex dex-var-names))
         (dex-alist (build-dex-alist dex-orig-names dex-var-names)))
    `((defun ,conx-name ,dex-var-names
        (declare (xargs :guard (and . ,dex-prex-calls))) ;guards not working with new record impl
                        ;:verify-guards nil))
        (mset 'constructor ',conx-name ,dex-alist)))))

;cons-up calls of above function
(defun cons-up-conx-ev (conx-names dex-pairs-lst)
  (declare (xargs :guard (and (symbol-listp conx-names)
                              (true-list-symbol-alistp dex-pairs-lst)
                              (= (len conx-names) (len dex-pairs-lst)))))
  (if (endp conx-names)
    nil
    (append (make-constructor (car conx-names) (car dex-pairs-lst));append instead of cons
          (cons-up-conx-ev (cdr conx-names) (cdr dex-pairs-lst)))));bcos (append (X) Y) = (cons X Y)

(defun make-measure-fn (conx-name dex-pairs)
  (declare (xargs :mode :program
                  :guard (and (symbolp conx-name)
                              (symbol-alistp dex-pairs))))
  (let* ((dex-names (strip-cars dex-pairs))
         (prefix (string-append (symbol-name conx-name) "-"))
         (dex-names (modify-symbol-lst prefix dex-names "")) ;make new prefixed destr names
         ;(dex-prex (strip-cdrs dex-pairs))
         (conx-pred (get-predicate-symbol conx-name))
         (msr-fn (modify-symbol "" conx-name "-COUNT")))
    `((defun ,msr-fn (v)
        (if (,conx-pred v)
          (+ 1  . ,(list-up-lists
                    (make-list (len dex-names) :initial-element msr-fn)
                    (build-one-param-calls dex-names 
                                           (make-list (len dex-names)
                                                      :initial-element 'v))))
          0)))))


;cons up events that define destructor functions
(defun cons-up-dex-defuns (conx-pred selector-fn-names dex-names)
  (declare ;(ignore conx-pred)
           (xargs :guard (and (symbol-listp selector-fn-names)
                              (symbol-listp dex-names)
                              (equal conx-pred conx-pred))))
  (if (endp dex-names)
    nil
    (let* ((sel-fn-name (car selector-fn-names))
           (dname (car dex-names))
           (d-keyword-name (intern (symbol-name dname) "KEYWORD")))
    (cons `(defun ,sel-fn-name (v)
             (declare (xargs :guard (,conx-pred v))) ;not working with new record impl
                             ;:verify-guards nil))
             (mget ,d-keyword-name v))
          (cons-up-dex-defuns conx-pred
                              (cdr selector-fn-names)
                              (cdr dex-names))))))
                              
;top level call for the previous function, basically generate code for destrs
(defun make-destructors (conx-name dex-pairs)
  (declare (xargs :guard (and (symbolp conx-name)
                              (symbol-alistp dex-pairs))))
  (let* ((dex-names (strip-cars dex-pairs))
         (prefix (string-append (symbol-name conx-name) "-"))
         (selector-fn-names (modify-symbol-lst prefix dex-names "")) ;make new prefixed destr names
         (conx-pred (get-predicate-symbol conx-name)))
    (cons-up-dex-defuns conx-pred selector-fn-names dex-names)))

;do the above for more than one constructors defined during a datadef
(defun append-up-dex-ev (conx-names dex-pairs-lst)
  (declare (xargs :guard (and (symbol-listp conx-names)
                              (true-list-symbol-alistp dex-pairs-lst)
                              (= (len conx-names) (len dex-pairs-lst))
                              )))
  (if (endp conx-names)
    nil
    (append (make-destructors (car conx-names) (car dex-pairs-lst))
            (append-up-dex-ev (cdr conx-names) (cdr dex-pairs-lst)))))


(defun compute-reg-conx-dex (conx-name dex-pairs)   
  (declare (xargs :guard (and (symbolp conx-name)
                              (symbol-alistp dex-pairs))))
  (let* ((conx-pred (get-predicate-symbol conx-name))
         (dex-names (strip-cars dex-pairs))
         ;(prefix (string-append (symbol-name conx-name) "-"))
         ;(dex-names (modify-symbol-lst prefix dex-names nil));make new prefixed destr names
         (dex-prex (strip-cdrs dex-pairs))
         (dex-pairs (cons-up-lists dex-names dex-prex))
        ;(msr-fn (modify-symbol nil conx-name "-COUNT"))
        (conx-pair (cons conx-name conx-pred)))
    `((register-record-constructor ,conx-pair 
                                   ,dex-pairs
                                   :hints (("Goal" :in-theory (enable ,conx-pred)))))))

(defun cons-up-reg-conx-dex-ev (conx-names dex-pairs-lst)
  (declare (xargs :guard (and (symbol-listp conx-names)
                              (true-list-symbol-alistp dex-pairs-lst)
                              (= (len conx-names) (len dex-pairs-lst)))))
  (if (endp conx-names)
    nil
    (append (compute-reg-conx-dex (car conx-names) (car dex-pairs-lst))
            (cons-up-reg-conx-dex-ev (cdr conx-names) (cdr dex-pairs-lst)))))


;;Enumerated types should not occur in mutually rec defs
#|
Enum types:
(defdata boolean (enum '(t nil))
(defdata rgbcolors (enum '(red blue green)))
(defdata suit (enum '(spades hearts diamonds clubs)))
X:suit = spades
X:rgbcolors = blue
|#
;;process enum form : compute enumeration events
;;Return value-triple nil if not of form enum
;;Returns a define-enumeration-type event form otherwise

(defun process-enum-form (defs ctx wrld)
  (declare (xargs :mode :program))
; 08/28/12 refactoring using b*
  (b* (((when (> (len defs) 1)) ;;mutually recursive
        (let ((defbodies (strip-cadrs defs)))
         (if (and (true-list-listp defbodies)
                  (member-eq 'enum (strip-cars defbodies)))
             (er hard? ctx 
"Syntax error in use of enum: Enumerated type cannot appear ~
                     in mutually recursive definitions.~%")
           nil)))
       (def (car defs)) ;;single def
       (name (car def))
       (enumbody (cadr def))
       (enumlen (len enumbody))
       ((unless (consp enumbody)) nil)
       ((unless (eq 'enum (car enumbody))) nil)
       ((unless (= enumlen 2))
        (er hard? ctx 
"Syntax error in enum: Enum ~x0 should be of following form: ~
     (defdata <id> (enum <list-of-values>)) or ~
     (defdata <id> (enum <val1> ...)) .~%" enumbody))
       (values (cadr enumbody))
       ((unless (true-listp values))
        (er hard? ctx 
"Syntax error in enum: ~x0 must evaluate to a list of values.~%" values)))
   (append
    (compute-define-enumeration-type-events name
                                            (get-predicate-symbol name)
                                            (get-values-symbol name)
                                            (get-predicate-testthm-symbol name)
                                            values wrld)
    `((value-triple ',name)))))
       

;;check for empty defs
(defun found-empty-defp (defs)
  (declare (xargs :guard (true-listp defs)))
  (if (endp defs)
    nil
    (let ((def (car defs)))
      (if (< (len def) 2)
        t
        (if (and (= (len def) 2)
                 (consp (cadr def))
                 (and (= (len (cadr def)) 1)
                      (or (eq (caadr def) 'oneof)
                          (eq (caadr def) 'anyof)
                          (eq (caadr def) 'listof)
                          (eq (caadr def) 'record)
                          (eq (caadr def) 'map)
                          (eq (caadr def) 'set)
                          (eq (caadr def) 'enum))))
          t
          (found-empty-defp (cdr defs)))))))

(defun type-class-simple-p (x)
  (mem-eq x '(:undefined 
                  acl2::union acl2::product 
                  acl2::singleton acl2::alias acl2::custom
                  enum record map set listof)))
(defthm type-class-simple-p-is-tau-pred
  (booleanp (type-class-simple-p x))
  :rule-classes :tau-system)

(defun type-class-simple-lst-p (xs)
  (if (atom xs)
      (null xs)
    (and (type-class-simple-p (car xs))
         (type-class-simple-lst-p (cdr xs)))))

(defun type-class-p (x)
  (if (atom x)
      (type-class-simple-p x)
    (and (eq (car x) 'acl2::mutually-recursive)
         (symbol-alistp (cdr x))
         (type-class-simple-lst-p (strip-cdrs (cdr x))))))

(defthm type-class-p-is-tau-pred
  (booleanp (type-class-p x))
  :rule-classes :tau-system)
      
(defun len-values-enum (values-enum wrld)
  (declare (xargs :mode :program))
  (if (and (symbolp values-enum)
           (quotep (acl2-getprop values-enum 'const wrld)))
      (len (cadr (acl2-getprop values-enum 'const wrld)))
    nil))


;;; Utility functions copied back from utilities.lisp

(defun is-a-constant-symbolp (x)
  (or (keywordp x);a keyword
      (booleanp x);t or nil
      (legal-constantp x)));ACL2::CONSTANT

;Sig: Any -> Bool
;check if x can be used as an identifier, i.e. has not been previously defined
(defun is-a-identifier (x wrld)
  (declare (xargs :mode :program))
  (if (and (is-a-variablep x)
           (acl2::new-namep x wrld))
    x
    nil))


;--------------------------TYPE Metadata Table----------------------------------------------
(defrec types-info%
  (size enumerator predicate test-enumerator enum-uniform
        recursivep derivedp
        type-class defs) NIL)

(defun types-info%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (
     ('types-info% size enumerator predicate test-enumerator enum-uniform
            recursivep derivedp
            typeclass defs)
     (declare (ignorable enumerator test-enumerator defs))
     (and (or (natp size)
              (eq 't size))
          (symbolp predicate)
          (symbolp enum-uniform)
          (booleanp recursivep)
          (booleanp derivedp)
          (type-class-p typeclass)))))
  
(defun tau-predicate-p (pred world)
  (declare (xargs :mode :program))
  (b* ((td (acl2::tau-data-fn pred world))
       ((unless (consp td)) nil)
       (entry (assoc-eq 'acl2::recognizer-index (cdr td)))
       ((unless (and (consp entry) (consp (cdr entry)))) nil))
    (natp (cadr entry))))

;;-- stores information about types introduced using defdata
;;-- (key val)
;;;--Modified Oct2-2009 added test enumerator
;;-- (type-name (type-size type-enum . predicate))
;;-- (rational (t nth-rational rationalp nth-rational-test)) 
;;-- type-size is t for infinite type and a natural number if finite
;;-- type-enum can be either NTH-type-name or *type-name-VALUES* 
;;--Note: predicate still can be such that name restriction is not there,
;;--for example we add atom in base.lisp. But for enum its strictly followed
;;Modified Jun 26 2011 harshrc
;;Use a records data structure for values in the table for easy
;;extensibility
;; Modified Aug 28 '12 to cutil record utility
;; 7th April 2013 - predicate constrained to be a tau predicate
;; 12 July 2013 - added uniform enumerator field
(table types-info-table nil nil :guard
       (and 
        (types-info%-p val)
        (b* ((TI.predicate (acl2::access types-info%  val :predicate))
             (TI.size (acl2::access types-info%  val :size))
             (TI.enumerator (acl2::access types-info%  val
                                          :enumerator))
             (TI.enum-uniform (acl2::access types-info%  val
                                            :enum-uniform))
             (TI.test-enumerator (acl2::access types-info%  val
                                          :test-enumerator))
             
          
             ;;(plausible-predicate-functionp TI.predicate world)
             ;; April 5th 2013 - should be a tau predicate
             ((unless (tau-predicate-p TI.predicate world))
              (prog2$ 
               (cw "~|~x0 is not a tau predicate. .
~|Possible debugging leads:
~| 1. (tau-data ~x0) is probably nil.
~| 2. Is ~x0 a everywhere constant function?
~| 3. Its not obvious that ~x0 is a predicate in which case, 
~| submit the followingas a :tau-system rule:
~|   (booleanp ~x0) ~|" TI.predicate)
               nil))

             ((unless (if (is-a-variablep TI.test-enumerator) 
                          (or (allows-arity TI.test-enumerator 1 world)
                              (quotep (acl2-getprop TI.test-enumerator 'const world)))
                        t))
              (prog2$
               (cw "~|~x0 is not a valid test enumerator.~|" TI.test-enumerator)
               nil))
             ((unless (and (eq TI.enum-uniform (get-uniform-enumerator-symbol key))
                           (allows-arity TI.enum-uniform 2 world)))
              (prog2$ 
               (cw "~|~x0 is not a valid uniform enumerator.~|" TI.enum-uniform)
               nil))
             ((unless (if (eq TI.size 't)
                          (and (eq TI.enumerator (get-enumerator-symbol key))
                               (allows-arity TI.enumerator 1 world))
                        (or (and (eql 1 TI.size)
                                 (possible-constant-valuep TI.enumerator));singleton
                            (and (natp TI.size) ;added a empty type (although it shudnt be allowed in normal defdata)
;(eq TI.enumerator (get-values-symbol key))
                                 (eql TI.size (len-values-enum TI.enumerator world))))))
              (prog2$ 
               (cw "~|~x0 is not a valid enumerator.~|" TI.enumerator)
               nil)))
          t)))



;TYPES
;check if fn-name is a type-pred by checking for corresponding typ pres rule
;; (defun has-type-prescription-rule (fn-name wrld)
;;   (declare (xargs :guard (and (symbolp fn-name)
;;                               (plist-worldp wrld))))
;;   (acl2-getprop fn-name 'acl2::type-prescriptions wrld))
                  

;if true then returns the type name (not the predicate)
;is true is Tp is a predicate and nth-T or *T-values* is defined in world
;Sig: Sym * World -> Sym
(defun is-custom-type-predicate (pred wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp pred)
                              (plist-worldp wrld)
                              )))
(let* ((typ (get-typesymbol-from-pred-P-naming-convention pred))
       (values (modify-symbol "*"  typ "-VALUES*"))
       (enum   (modify-symbol "NTH-" typ "")))
  (if (plausible-predicate-functionp pred wrld)
    (if (or (allows-arity enum 1 wrld) ;is enum defined in wrld
            (acl2-getprop values 'acl2::const wrld) 
;;or is values defined in wrld
            )
      typ ;THIS CAN BE NIL, if pred doesnt follow naming convention, works out well in any case
      nil)
    nil)))

;;is a predicate explicitly recognized in the defdata framework? 
;;if true then returns the corresponding type
;; BUG here, with every change of type table, you might have to change this function
(defun is-datadef-type-predicate (fn-name typtable-alst)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp fn-name)
                              (symbol-alistp typtable-alst))))
  (if (endp typtable-alst)
    nil
    (b* (((cons typ info%) (car typtable-alst)))
      (if (eq fn-name (acl2::access types-info% info% :predicate)) ;TODO: here for multiple pred aliases
          typ
        (is-datadef-type-predicate fn-name (cdr typtable-alst))))))



;is a possible type (ASK:should we also pick compound recognizers?)
;is either custom type pred or datadef pred
;if true then returns the type name (not the predicate)
;Sig: Sym * World -> Sym
(defun is-type-predicate-current (fn-name wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp fn-name)
                              (plist-worldp wrld))))
  (or (is-datadef-type-predicate fn-name (table-alist 'types-info-table wrld));is in types table
      (is-custom-type-predicate fn-name wrld)));is a custom type in the current world

(defun is-type-predicate-gv (fn w)
  (ec-call (is-type-predicate-current fn w)))

(defattach is-type-predicate is-type-predicate-gv)

;Sig: Sym * State -> bool
;purpose: Check wether id is an identifier, which has not been previously defined as a type
(defun is-a-typeId-p (id wrld)
  (declare (xargs :verify-guards nil
                  :guard (plist-worldp wrld)))
  (and (is-a-variablep id)
       (let ((typ-alst (table-alist 'types-info-table wrld))
             (pred (get-predicate-symbol id)))
         (and (not (assoc-eq id typ-alst))
              (not (is-custom-type-predicate pred wrld))))))

;Sig: Sym * World -> Sym (typename)
;type has been defined using register-custom-type
(defun is-a-registered-custom-type (type wrld)
  (declare (xargs :verify-guards nil))
  (if (is-a-variablep type);shud be a variable symbol
    (let* ((typ-alst (table-alist 'types-info-table wrld))
          (typ-entry (assoc-eq type typ-alst))) 
      (if (and (consp typ-entry)
               (not (acl2::access types-info% (cdr typ-entry) :derivedp)))
        type ;if not derived by defdata but in the type table return type
        nil))
    nil))

;type has been defined using the defdata form
(defun is-a-defdata-type (type wrld)
  (declare (xargs :verify-guards nil))
  (if (is-a-variablep type);shud be a variable symbol
    (let* ((typ-alst (table-alist 'types-info-table wrld))
          (typ-entry (assoc-eq type typ-alst))) 
      (if (and (consp typ-entry)
               (acl2::access types-info% (cdr typ-entry) :derivedp))
        type ;if derived by defdata return type
        nil))
    nil))

;purpose: Check wether argument has been previously defined as a type
;using defdata or is clearly recognized by the defdata framework,
;i.e. it could also be a custom type which has been added into the
;types-info-table using register-custom-type.  could also have been
;implemented in terms of is-datadef-type-predicate
(defun is-registered (type wrld)
  (declare (xargs :verify-guards nil))
  (if (is-a-variablep type);shud be a variable symbol
    (let* ((typ-alst (table-alist 'types-info-table wrld))
          (typ-entry (assoc-eq type typ-alst))) 
      (if (consp typ-entry)
          type
        nil))
    nil))

;Sig: Sym * World -> Sym (typename)
;purpose: Check wether argument is a custom defined type and not a
;defdata pred
(defun is-a-custom-type-current (type wrld)
  (declare (xargs :verify-guards nil))
  (if (is-a-variablep type);shud be a variable symbol
    (if (is-registered type wrld)
      nil
      (let ((pred (get-predicate-symbol type)))
        (if (is-custom-type-predicate pred wrld) ;or is a custom type
          type
          nil)))
    nil))

(defun is-a-custom-type-gv (type wrld)
  (ec-call (is-a-custom-type-current type wrld)))

(defattach is-a-custom-type is-a-custom-type-gv)



;is either a defdata defined type or a custom typename
(defun is-a-typeName-current (type wrld)
  (declare (xargs :verify-guards nil))
  (or (is-registered type wrld)
      (is-a-custom-type type wrld)))

(defun is-a-typeName-gv (type wrld)
  (ec-call (is-a-typeName-current type wrld)))

(defattach is-a-typeName is-a-typeName-gv)

;------------------------------------------------------------------------



;User-controlled testing
;;;Per type syntax:
;;;(defdata-testing <type-name>
;;;                 :test-enumerator <enum-fn>
;;;                 :filter <filter-fn>
;;;                 ...)                              
;register the type by adding it into the types info table
 (defmacro defdata-testing  (typename &key test-enumerator)
   ":Doc-Section acl2::DATA-DEFINITIONS
  Specify a custom testing enumerator for a type~/
  ~c[(defdata-testing T1 :test-enumerator nth-T1-testing)]
  adds a user-specified enumerator to be used for randomly
  generating values for type ~c[T1]. This can be used
  to restrict the testing domain of any type for the
  purposes of random testing.
  
  ~bv[]
  Examples:
  (defdata-testing nat :test-enumerator nth-nat-small-values)
  (defdata-testing list :test-enumerator nth-list-test-small-lists) ;to test small lists
  (defdata-testing character :test-enumerator *special-chars-only*) ;to test special chars
  (defdata-testing foo :test-enumerator 999) ;restrict domain of foo to a singleton value
  ~ev[]                      
  ~bv[]
  Usage:
  (defdata-testing <Type-name1> :test-enumerator <test-enum>)
  ~ev[]~/
  "
  `(with-output
       :stack :push
       :off (warning warning! observation prove 
                     proof-checker event expansion
                     summary proof-tree)

       (make-event
        (er-let* ((type-info (table defdata::types-info-table ',typename)))
          (if type-info
              (value `(progn
                        ,@(and ',test-enumerator
                               (make-enum-uniform-defun-ev 
                                (modify-symbol "" ',test-enumerator "-UNIFORM")
                                ',test-enumerator))
                        (table defdata::types-info-table 
                               ',',typename 
                               (acl2::change types-info% ',type-info
                                             :test-enumerator
                                             ',',test-enumerator))
                        (value-triple (list ',',typename ',',test-enumerator))))
               (er soft 'defdata-testing "~x0 is not a registered type. Use register-custom-type to register it.~%" ',typename))))))
 
(defun make-enum-uniform-defun-ev (name enum)
  (declare (xargs :guard (symbolp enum)))
  `((defund ,name (m seed)
     (declare (ignorable m))
     (declare (type (unsigned-byte 31) seed))
     (declare (xargs :verify-guards nil ;todo
                     :guard (and (natp m)
                                 (unsigned-byte-p 31 seed))))
; 12 July 2013 - adding uniform random seed distribution to cgen enum
; we will take advantage of the recent addition for an uniform
; interface to both infinite and finite enum (defconsts)
     (mv-let (n seed)
             (random-natural-seed seed)
             (mv (,enum n) (the (unsigned-byte 31) seed))))))
     
     
     
 ;register the type by adding it into the types-info-table
 (defmacro register-custom-type  (typename typesize enum pred 
                                           &key test-enum
                                                enum-uniform
                                                (type-class 'acl2::custom))
   "Usage: (register-custom-type foo t nth-foo foop :test-enum my-nth-foo :type-class custom)
    Purpose: add foo to type metadata table 'types-info-table'. 
    Second argument is t if foo is infinite, and a positive number o.w., in which case the
    standard naming convention for the third arg (enumerator) is *foo-values*.
    keyword args are optional."
  `(with-output
    :stack :push
    :off (warning warning! observation prove 
                  proof-checker event expansion
                  summary proof-tree)

    (make-event
     '(progn
        (in-theory (disable ,(get-enumerator-symbol typename)))
        ,@(and (not enum-uniform)
               (make-enum-uniform-defun-ev 
                (get-uniform-enumerator-symbol typename)
                (get-enumerator-symbol typename)))
        ,@(and test-enum
             (make-enum-uniform-defun-ev
              (get-uniform-enumerator-symbol test-enum) test-enum))
        (table defdata::types-info-table ',typename 
               ',(acl2::make types-info%
                  :size typesize 
                  :enumerator enum
                  :predicate pred
                  :test-enumerator test-enum
                  :enum-uniform (if enum-uniform 
                                    enum-uniform 
                                  ;; shudnt be empty
                                  (get-uniform-enumerator-symbol typename))
                  :defs nil
                  :derivedp nil
                  :recursivep nil
                  :type-class type-class))
        (add-datatype-node-batch ,typename)
        (sync-globals-for-dtg) ;sync globals with SCC and TC 
        (value-triple (list ',typename 
                            ',(list typesize enum pred test-enum 
                                    nil nil type-class)))
        ))))

 #|
 (defconst *foo1-values* '(1 2 3))
 (defun foop (x)
   (and (posp x)
        (< x 4)))
 (defconst *foo1-values-testing* '(1 2))
 (include-book ;; fool dependency scanners
   "graph")
(register-custom-type foo1 3 *foo1-values* foop nil)
(defdata-testing foo1 :test-enumerator *foo1-values-testing*)
 |#



;is a new constuctor Id
(defun is-a-newconsId (id n wrld)
  (declare (xargs :mode :program
                  :guard (and (symbolp id)
                              (natp n)
                              (plist-worldp wrld))))
  (let ((conx-pred (get-predicate-symbol id)))
    (if (and (is-a-identifier id wrld) ;this makes the following check redundant
             (not (allows-arity id n wrld));not a predefined function or macro
             (not (allows-arity conx-pred 1 wrld)));the corresponding pred is also not predefined
             
      id
      nil)))


;is a already existing constructor
(defun is-a-consId (id n wrld)
  (declare (xargs :mode :program
                  :guard (and (symbolp id)
                              (natp n)
                              (plist-worldp wrld))))
  (if (and (is-a-variablep id)
           (allows-arity id n wrld));is a predefined constructor function with correct arity
    id
    nil))


(defrec supp-lemmas%
  (set listof record oneof map)
  NIL)

(defun supp-lemmas%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (
     ('supp-lemmas% set listof record oneof map)
     (and (true-listp set)
          (true-listp listof)
          (true-listp record)
          (true-listp oneof)
          (true-listp map)))))


(defconst *initial-supp-lemmas*
  (acl2::make supp-lemmas%
   :set '() 
   :listof '() 
   :record '()
   :map '()
   :oneof '()))



;defdata temp storage
(defstobj ds$
  (defdata-world :type T :initially nil)
  (newconstructors :type T :initially nil);list
  (support-lemmas :type T;(satisfies supp-lemmas%-p)
                  :initially nil);*initial-supp-lemmas*)
;(struct (set . list) (listof . list) (record . list) (oneof . list))
  (custom-types :type T :initially nil)
  (defdata-debug :type (satisfies booleanp) :initially nil)
  (type-class :type (satisfies type-class-p) :initially :undefined)
  (record-constituents :type T :initially nil)
  (product-constituents :type T :initially nil)
  (union-constituents :type T :initially nil)
  (is-recursive :type (satisfies booleanp) :initially nil)
  )
  
;Ideally write a macro to generate these forms
(defmacro add-record-constituent-types-to-ds$ (type)
`(update-record-constituents (cons ,type (record-constituents ds$)) ds$))

(defmacro add-product-constituent-types-to-ds$ (type)
`(update-product-constituents (cons ,type (product-constituents ds$)) ds$))

(defmacro add-union-constituent-types-to-ds$ (type)
`(update-union-constituents (cons ,type (union-constituents ds$)) ds$))
  
(defmacro add-custom-types-to-ds$ (type)
`(update-custom-types (cons ,type (custom-types ds$)) ds$))

;add generated constructor information in a record to a temporary
;global variable changed pred-body-lst to pred-lst since only
;typenames are allowed not type expressions.
;July 8 2010, this was checked with the datadef syntax document
;June 26 2011, changed to ds$ transient/temp storage stobj for defdata
(defun add-newconstructor-to-ds$ (newconsid dex pred-lst ds$)
  (declare (xargs :mode :program 
                  :stobjs (ds$)))
  (let ((new-constructor-info 
         (cons newconsid (list* (list ':generated ':proper)
                                (get-predicate-symbol newconsid)
                                (cons-up-lists dex pred-lst)
                                'none)))
        (newconstructors-alreadyseen-lst (newconstructors ds$)))
    (update-newconstructors (cons new-constructor-info
                                  newconstructors-alreadyseen-lst) ds$)))

(defun update-type-class-top-level$ (tc nm ds$)
  (declare (xargs :guard (and (type-class-p tc)
                              (symbolp nm)
                              (ds$p ds$))
                  :verify-guards nil
                  :stobjs (ds$)))
  (declare (ignorable nm))
  (let ((current-tc (type-class ds$)))
    (cond ((eq current-tc :undefined)
           (let ((ds$ (update-type-class tc ds$)))
             ds$))
          ((and (consp current-tc)
                (eq (car current-tc) 'acl2::mutually-recursive))
           (b* ((alst (cdr current-tc))
                (entry (assoc-eq nm alst))
                (ctx 'update-type-class-top-level$)
                ((when (null entry)) (prog2$ (er hard ctx "~| ~x0 not found in ~x1~|" nm alst) ds$))
                ((unless (and (consp entry)
                              (eq (cdr entry) :undefined))) ds$)
                (alst~ (put-assoc-eq nm tc alst))
                (ds$ (update-type-class (cons 'acl2::mutually-recursive alst~) ds$)))
             ds$))
        (t ds$))))

(program)


;is dexpair a destructor type declaration
(defun trans-dest-type-decl (conx-name dexpair tnames ctx ds$)
  (declare (xargs :stobjs (ds$)))
  (b* (((unless (consp dexpair))
        (prog2$
         (er hard ctx "~x0 destructor type decl should be a cons. ~%" dexpair)
         (mv t nil ds$)))
       (conx-prefix-str (string-append (symbol-name conx-name) "-"))
       (id-name (modify-symbol conx-prefix-str (car dexpair) ""))
       (id (is-a-identifier id-name (defdata-world ds$)))
       (dte (cdr dexpair))
      ((unless id)
       (prog2$
         (er hard ctx "~x0 is a bad choice for a field name in ~x1.~ 
Choose something different~%" (car dexpair) dexpair)
         (mv t nil ds$)))
;strip away the destructor information for uniform product data treatment
      ((when (is-registered dte (defdata-world ds$)))
       (let ((ds$ (if (not (eq 'acl2::union (type-class ds$)))
;check if we are not inside union
                      (add-record-constituent-types-to-ds$ dte)
                    ds$)))
         (mv nil dte ds$)))
      ((when (mem1 dte tnames))
       (let ((ds$ (update-is-recursive 't ds$)))
         (mv nil dte ds$)));recursive type reference
      ((unless (is-a-custom-type dte (defdata-world ds$)))
       (prog2$
        (er hard ctx "~x0 should be a type name. ~%" dte)
        (mv t nil ds$)))
;Custom type (only remaining case)
;add custom types used in defdata form to be validated later  
      (ds$ (if (not (eq 'acl2::union (type-class ds$)))
;check if we are not inside union
               (add-record-constituent-types-to-ds$ dte)
             ds$))
;July 9 2011
;TODO NOTE: I do add the constituents, but I generate the
;disjoint theorems only when the original expression is a
;purely product expression and I have an handle on its names!!
;So this is fluff code for the moment, if we are inside a union
      (ds$ (add-custom-types-to-ds$ dte)))
    (mv nil dte ds$)))
          
  
;check and construct(stripping away destructors) dex-pair list      
 (defun trans-dest-typ-decl-lst (conx-name dex-pairs tnames ctx ds$)
   (declare (xargs :stobjs (ds$)))
   (if (symbol-alistp dex-pairs)
     (if (endp dex-pairs)
         (mv nil nil ds$)
       (b* (((mv erp dest-decl ds$)
             (trans-dest-type-decl conx-name (car dex-pairs) tnames ctx ds$))
            ((when erp)
             (prog2$ 
              (er hard ctx "Bad ~x0~%" (car dex-pairs))
              (mv t nil ds$)))
            ((mv & dest-decl-lst ds$) 
             (trans-dest-typ-decl-lst conx-name (cdr dex-pairs) tnames ctx ds$))
            )
         (mv nil (cons dest-decl dest-decl-lst) ds$)))
      (prog2$ 
       (er hard ctx 
           "Destructor type decl list ~x0 should be a symbol-alist. ~%"
           dex-pairs)
       (mv t nil ds$))))
       
       
(mutual-recursion
;; checks wether texp is a constituent type: 
;; Either typeName | SingletonType | Union-or-Prod-type
;; if it isnt then give syntax error. 
;; The reason why its a soft syntax error? (not the case anymore)
;;  rather than a nil is
;; that all calls to this function occur from inside 
;; either a union or prod function which occurs last
;; in the series of syntax check and so if its not a 
;; union or prod then its not legal syntax.
 (defun trans-constituent-type (texp typid tnames ctx ds$)
   (declare (xargs :stobjs (ds$)))
   (b* (((when (is-singleton-type-p texp))
         (mv nil texp ds$))
        ((when (is-registered texp (defdata-world ds$)))
          (let ((ds$ 
                 (case (type-class ds$)
                   ('acl2::product (add-product-constituent-types-to-ds$ texp))
                   ('record (add-record-constituent-types-to-ds$ texp))
;might be buggy, right now im not supporting union constituents
                   (otherwise (add-union-constituent-types-to-ds$ texp)))))
            (mv nil texp ds$)))
        ((when (is-a-custom-type texp (defdata-world ds$)))
         (let* ((ds$ (add-custom-types-to-ds$ texp))
                (ds$ 
                 (case (type-class ds$)
                   ('acl2::product (add-product-constituent-types-to-ds$ texp))
                   ('record (add-record-constituent-types-to-ds$ texp))
;might be buggy, right now im not supporting union constituents
                  (otherwise (add-union-constituent-types-to-ds$ texp)))))
           (mv nil texp ds$)))
        ((when (mem1 texp tnames)) 
         (let ((ds$ (update-is-recursive 't ds$)))
           (mv nil texp ds$)));is a recursive type reference
        ((unless (consp texp))
         (prog2$
          (er hard ctx "~x0 is an illegal Constituent type expression,
expecting either previously ~ 
defined typeName, Singleton or Union/Product type here~%" texp )
          (mv t nil ds$)))
        ((mv erp texp1 ds$)
         (trans-prod-or-union-type texp typid tnames ctx ds$))
        ((unless (and (not erp) texp1))
         (prog2$ 
          (er hard ctx "~x0 is an illegal Constituent type expression, expecting either ~ 
previously defined typeName, Singleton or Union/Product type here~%" texp )
          (mv t nil ds$))))
       (mv nil texp1 ds$)))
       
 ;check and construct the constituent type list
 (defun trans-constituent-type-lst (texp-lst typid tnames ctx ds$)
   (declare (xargs :stobjs (ds$)))
   (if (endp texp-lst)
         (mv nil nil ds$)
       (b* (((mv erp1 ctype1 ds$)
;ignore errors since they will already be caught. Hard errors!! save typing
             (trans-constituent-type (car texp-lst) typid tnames ctx ds$))
            ((mv erp2 ctype-lst1 ds$)
             (trans-constituent-type-lst (cdr texp-lst) typid tnames ctx ds$))) 
         (mv (or erp1 erp2) (cons ctype1 ctype-lst1) ds$))))
    

;;; if texp is a union expression then check and preprocess 
;;; the argument constituent type expressions 
;;; otherwise give nil, dont give any errors, cos we still 
;;; have product expression in the sequential check left
 (defun trans-union-type-exp (texp typid tnames ctx ds$)
   (declare (xargs :guard (consp texp)
                   :stobjs (ds$)))
   (b* (((unless (and (consp texp)
                      (or (eq (car texp) 'oneof) 
                          (eq (car texp) 'anyof))))
         (mv nil nil ds$))
;it is a union expression
        ((unless (> (len (cdr texp)) 1))
         (prog2$
          (er hard ctx "Union type expression ~x0 should have at least 2 constituent types~%" texp)
          (mv t nil ds$)))
        (ds$ (update-type-class-top-level$ 'acl2::union typid ds$))
            
        ((mv erp texp-lst1 ds$)
         (trans-constituent-type-lst (cdr texp) typid tnames ctx ds$)))
     (mv erp (cons (car texp) texp-lst1) ds$))) ;reconstruct
 
 
 (defun trans-product-type-exp (texp typid tnames ctx ds$)
   (declare (xargs :guard (consp texp)
                   :stobjs (ds$)))
   (b* (((when (and (consp texp)
                    (or (eq (car texp) 'oneof) 
                        (eq (car texp) 'anyof))))
;is an union, so return nil (indicating not a product)
         (mv nil nil ds$))
        (consid (is-a-consId (car texp) (len (cdr texp)) 
                             (defdata-world ds$)))
        ((when consid)
         (mv-let (erp ctype-lst1 ds$)
                 (let ((ds$ (update-type-class-top-level$ 'acl2::product typid ds$)))
;only updates if top-level-call from translate-defbody
                                
                   (trans-constituent-type-lst (cdr texp) typid tnames ctx ds$))
                 (mv erp (cons consid ctype-lst1) ds$))) ;reconstruct


        (newconsid (is-a-newconsId (car texp) (len (cdr texp)) 
                                   (defdata-world ds$)))
        ((unless newconsid)
         (prog2$
            (er hard ctx "~|~x0 is an illegal Constructor id~|" (car texp))
            (mv t nil ds$)))
        (dest-decl-lst (cdr texp)) 
        (dex (strip-cars dest-decl-lst))
        (dex-types (strip-cdrs dest-decl-lst))
        (pred-lst (get-predicate-symbol-lst dex-types))
;only update if top-level call
        (ds$ (update-type-class-top-level$ 'record typid ds$))
            
        ((mv erp ct-lst1 ds$)
;get stripped constituent types
         (trans-dest-typ-decl-lst newconsid dest-decl-lst tnames ctx ds$))
        ((unless (not erp))
          (prog2$
            (er hard ctx "Malformed destructor declarations~%")
            (mv t nil ds$)))
        (ds$ (add-newconstructor-to-ds$ newconsid dex pred-lst ds$)))
     
     (mv nil (cons newconsid ct-lst1) ds$)))
         
 (defun trans-prod-or-union-type (texp typid tnames ctx ds$)
;returns (mv erp trans-texp ds$)
    (declare (xargs :guard (consp texp)
                    :stobjs (ds$)))
   (b* (((mv erp un-texp ds$)
         (trans-union-type-exp texp typid tnames ctx ds$)))
     (if (and (not erp)
              un-texp)
         (mv nil un-texp ds$)
;SOLVED BUG: order is important
       (trans-product-type-exp texp typid tnames ctx ds$)))) 
 
)

;;check well-foundedness (dead code now 04/07/2013)
(mutual-recursion
 (defun WF-constituent-type (texp tnames rpath ctx)
   (cond ((is-singleton-type-p texp) 't);singleton type exp is well-founded
         ((symbolp texp) 't);previosly defined types are well-founded
         ((mem1 texp tnames) 
          (if (mem1 'P rpath)
            'nil;is a recursive type reference, i.e. not well-founded
            ;but if this reference occurs inside a union type expression, that is illegal, raise error!
            (er hard? ctx "Not Well-formed: Recursive reference ~x0 should occur within a outer Product type expression~%" texp)))
         (t (WF-prod-or-union-type texp tnames rpath ctx ))))
              
 
 (defun WF-product-constituent-type-lst (texp-lst tnames rpath ctx )
   (if (endp texp-lst)
       't
       (and (WF-constituent-type (car texp-lst) tnames rpath ctx )
            (WF-product-constituent-type-lst (cdr texp-lst) tnames rpath ctx ))))
 
 (defun WF-union-constituent-type-lst (texp-lst tnames rpath ctx )
   (if (endp texp-lst)
       'nil
       (or (WF-constituent-type (car texp-lst) tnames rpath ctx )
           (WF-product-constituent-type-lst (cdr texp-lst) tnames rpath ctx )))) 
         
(defun WF-dest-type-decl (dexpair tnames rpath ctx )
   (WF-constituent-type (cdr dexpair) tnames rpath ctx ))
   
  
 (defun WF-dest-typ-decl-lst (dex-pairs tnames rpath ctx )
   (if (endp dex-pairs)
     't
     (and (WF-dest-type-decl (car dex-pairs) tnames rpath ctx )
          (WF-dest-typ-decl-lst (cdr dex-pairs) tnames rpath ctx ))))
 
(defun WF-union-type-exp (texp tnames rpath ctx )
   (if (or (eq (car texp) 'oneof) (eq (car texp) 'anyof))
     (WF-union-constituent-type-lst (cdr texp) tnames (cons 'U rpath) ctx )
     nil))
 
 
 (defun WF-product-type-exp (texp tnames rpath ctx )
   (if (symbolp (car texp));cons-id
       (WF-product-constituent-type-lst (cdr texp) tnames (cons 'P rpath) ctx )
       (WF-dest-typ-decl-lst (cdr texp) tnames (cons 'P rpath) ctx )))
          
 
 (defun WF-prod-or-union-type (texp tnames rpath ctx )
   (or (WF-union-type-exp texp tnames rpath ctx )
       (WF-product-type-exp texp tnames rpath ctx )))
 
)

;preprocessing
;(enum <expr-evals-to-a-list-of-constants>)
(defun is-enum-type (texp ctx w)
;returns trans-enum, where trans-enum is nil if texp is 
;not an enum type expression
  (declare (xargs :guard (plist-worldp w)))
  (b* (((unless (and (consp texp)
                     (eq (car texp) 'enum)))
        nil)
;Is an enum
       ((unless (and (= 2 (len texp))
                     (possible-constant-value-expressionp (cadr texp))))
        (er hard ctx "Enum should be of form (enum <list-expr>) where ~
list-expr is a constant value expression evaluating to a list of objects.~%"))
       ((mv erp list-val) 
        (trans-my-ev-w (cadr texp) ctx w nil))
       ((when erp)
        (er hard ctx "Evaluating list expression ~x0 failed!~%" (cadr texp)))
       ((unless (true-listp list-val))
        (er hard ctx "Enum ~x0 expected a (true-) list expression.~%" texp)))
    (list 'enum list-val)))

#|
(defmacro define-map-list-lambda-fn (nm lambda-fn &key guard)
 `(make-event
   (defun ,nm
     ,@(if guard 
          '((declare (xargs :guard guard)))
         nil)
     (if (endp lst)
         nil
       (cons 
|#
   
(defun map-get-field-name (dnames)
  (declare (xargs :guard (symbol-listp dnames)))
  (if (endp dnames)
      nil
    (cons (intern (symbol-name (car dnames)) "KEYWORD")
          (map-get-field-name (cdr dnames)))))



(defun get-typesymbol-from-pred (sym wrld)
  (b* ((typ (get-typesymbol-from-pred-P-naming-convention sym))
       (types-info-table (table-alist 'types-info-table wrld))
       (entry (assoc-eq typ types-info-table))
       (naming-consistent? (and (consp entry)
                                (eq sym (acl2::access types-info% (cdr entry) :predicate))))
       ((when naming-consistent?) typ)
       (ans (is-datadef-type-predicate sym types-info-table)))
    (if ans
        ans
      (er hard 'get-typesymbol-from-pred "~x0 doesnt follow our convention of predicates ending with 'p'.~%" sym))))
    

(defun len-<-0-syms (syms)
  (declare (xargs :guard (symbol-listp syms)))
                  ;:VERIFY-GUARDS NIL))
  (if (endp syms)
    't
    (and (if (symbolp (car syms)) 't 'nil)
         (< 0 (length (symbol-name (car syms))))
         (len-<-0-syms (cdr syms)))))

(defun get-typesymbol-from-pred-lst (syms wrld)
  (declare (xargs :guard (and (symbol-listp syms)
                              (len-<-0-syms syms))))
                         
  (if (endp syms)
    nil
    (let ((type (get-typesymbol-from-pred (car syms) wrld)))
      (if type ;it might be NIL (Ideally it shud be an ERROR??)
        (cons type
              (get-typesymbol-from-pred-lst (cdr syms) wrld))
        (get-typesymbol-from-pred-lst (cdr syms) wrld)))))

;TODO: wherever you use get-predicate-symbol, you should check for
;the non-syntactic restricted version from names-info-table

(defun runes-to-be-disabled1 (names wrld ans)
  (if (endp names)
      ans
  (b* ((name (car names)))
               
    (if (acl2::rule-name-designatorp name nil wrld);filter runes
        (runes-to-be-disabled1 (cdr names) wrld (cons name ans))
      (runes-to-be-disabled1 (cdr names) wrld ans)))))

(defun runes-to-be-disabled (names wrld)
  (remove-duplicates (runes-to-be-disabled1 names wrld '())))

(defun make-generic-record-implies-consp/good-map-ev (conx-name dex-pairs wrld)
  (declare (xargs :guard (and (symbolp conx-name)
                              (symbol-alistp dex-pairs))))
  (b* ((dex-orig-names (strip-cars dex-pairs))
       (prefix (string-append (symbol-name conx-name) "-"))
       (dex-names (modify-symbol-lst prefix dex-orig-names "")) ;make new prefixed destr names
       (dex-preds (strip-cdrs dex-pairs))
       (dex-var-names (modify-symbol-lst "VAR" dex-names ""))
       (dex-bindings  (build-dex-recordImpl-bindings dex-orig-names dex-var-names 'v))
       (conx-pred (get-predicate-symbol conx-name))
       (disabled (runes-to-be-disabled dex-preds wrld)))
       
    `((encapsulate
      ()
      (local
       (progn
         (value-triple 
          (prog2$ 
           (time-tracker :defdata-generic-record-lemmas :start)
           :invisible))
         (in-theory (enable ,conx-pred))
         (defthm ,(modify-symbol "" conx-name "-IMPLIES1-LEMMA")
           (implies (,conx-pred v)
                    (equal (EQUAL v ,(cons conx-name (strip-cadrs dex-bindings)));(mget :key x) (mget :LEVEL x) (mget :LEFT x)  (mget :RIGHT x)))
                           t))
           :hints (("Goal" :in-theory (disable . ,disabled)))
           :rule-classes (:forward-chaining))
         
         (defthm ,(modify-symbol "" conx-name "-IMPLIES2-LEMMA")
           (implies (EQUAL x ,(cons conx-name dex-names));AA-KEY  AA-LEVEL AA-LEFT AA-RIGHT))
                    (mget 'DEFDATA::CONSTRUCTOR x)))
         
         (defthm ,(modify-symbol "" conx-name "-IS-CONSP-LEMMA");node-is-consp-lemma
           (implies (,conx-pred x)
                    (mget 'DEFDATA::CONSTRUCTOR x))
           :hints (("goal" :in-theory (e/d () (,@disabled))))
           :rule-classes (:forward-chaining))

         (in-theory (disable ,conx-pred))))

      (value-triple 
          (prog2$ 
           (time-tracker :defdata-generic-record-lemmas :print?)
           :invisible))

      (defthm ,(modify-symbol "" conx-name "-UNIQUE-TAG")
        (implies (,conx-pred x)
                 (equal (mget 'defdata::constructor x) ',conx-name))
        :hints (("goal" :expand ((,conx-pred x))
                        :in-theory (e/d () (,@disabled))))
        :rule-classes ((:rewrite :backchain-limit-lst 1)
                       :forward-chaining :type-prescription))

      (defthm ,(modify-symbol "" conx-name "-IMPLIES-CONSP")
        (implies (,conx-pred x)
                 (consp x))
        :rule-classes ((:rewrite :backchain-limit-lst 1)
                       :forward-chaining :compound-recognizer))

      (defthm ,(modify-symbol "" conx-name "-IMPLIES-GOOD-MAP")
        (implies (,conx-pred x)
                 (acl2::good-map x))
        :hints (("goal" :in-theory (e/d (,conx-pred))))
        :rule-classes ((:rewrite :backchain-limit-lst 1) 
                       (:forward-chaining)))
      
      (defthm ,(modify-symbol "" conx-name "-EXCLUDES-ATOM-LIST")
        (implies (,conx-pred x)
                 (not (atom-listp x)))
        :hints (("goal" :in-theory (e/d (,conx-pred) (,@disabled))))
        :rule-classes (:tau-system))

      (value-triple 
       (progn$ 
       (time-tracker :defdata-generic-record-lemmas :print?)
       (time-tracker :defdata-generic-record-lemmas :stop)
       :invisible))
      ;; (defthm ,(modify-symbol "" conx-name "-IMPLIES-PROPER-CONS/ALIST")
      ;;   (implies (,conx-pred x)
      ;;            (and (proper-consp x)
      ;;                 (alistp x)))
      ;;   :hints (("goal" :in-theory (e/d (,conx-pred))))
      ;;   :rule-classes (:tau-system))

      ))))

;cons-up calls of above function
(defun cons-up-record-implies-consp/good-map-ev (conx-names dex-pairs-lst wrld)
  (declare (xargs :guard (and (symbol-listp conx-names)
                              (true-list-symbol-alistp dex-pairs-lst)
                              (= (len conx-names) (len dex-pairs-lst)))))
  (if (endp conx-names)
    nil
    (append (make-generic-record-implies-consp/good-map-ev (car conx-names) (car dex-pairs-lst) wrld)
            (cons-up-record-implies-consp/good-map-ev (cdr conx-names) (cdr dex-pairs-lst) wrld))))

(defun record-selector-lemmas (nms tpred fnames dprex disabled)
  (if (endp fnames)
      (list '(value-triple 
              (prog2$ 
               (time-tracker :defdata-record-lemmas :print?)
               :invisible)))
              
    (cons
     `(defthm ,(car nms)
          (implies (,tpred x)
                   (,(car dprex) (mget ,(car fnames) x)))
          :hints (("Goal" :in-theory (e/d (,tpred) (,@disabled))))
          :rule-classes (:rewrite 
                         (:forward-chaining
                          :trigger-terms ((mget ,(car fnames) x)))))
     (record-selector-lemmas (cdr nms) tpred (cdr fnames) (cdr dprex) disabled))))

(defun record-modifier-lemmas (nms tpred fnames dprex disabled)
  (if (endp fnames)
      (list '(value-triple 
              (prog2$ 
               (time-tracker :defdata-record-lemmas :print?)
               :invisible)))
    (cons 
     `(defthm ,(car nms)
        (implies (and (,tpred x)
                      (,(car dprex) v))
                 (,tpred (mset ,(car fnames) v x)))
        :hints (("Goal" :in-theory (e/d (,tpred) (,@disabled))))
        :rule-classes (:rewrite 
                       (:forward-chaining
                        :trigger-terms ((mset ,(car fnames) v x)))))
     (record-modifier-lemmas (cdr nms) tpred (cdr fnames) (cdr dprex) disabled))))


(defun record-disjoint-constituent-lemmas (nms tpred dex-types wrld)
  (if (endp nms)
      (list '(value-triple 
              (prog2$ 
               (time-tracker :defdata-record-lemmas :print?)
               :invisible)))
    (append 
     (b* ((dex-type (car dex-types))
          (dpred (get-predicate-symbol dex-type))
; bugfix defdata-record-all-field-bug
          ((when (or (is-alias dex-type 'acl2::all wrld)
                     (is-alias dex-type 'acl2::cons wrld) 
                     (is-alias dex-type 'acl2::list wrld)
                     (is-alias dex-type 'acl2::alist wrld)
                     (is-alias dex-type 'acl2::acons wrld) 
                     (is-alias dex-type 'acl2::true-list wrld)
                     ;; TODO
                     ;; 16 July 2013 - due to example from mitesh
                     ;; the disjoint lemma generation is nowhere near
                     ;; complete
                     (is-subtype dex-type 'acl2::true-list wrld)))

           '()))
       `((defthm ,(car nms)
          (implies (,tpred x)
                   (not (,dpred x)))
; 13 July 2013 -- equiv enum and oneof defs of Lett dont work
; equivalently for disjoint lemmas:
#|
(defdata Lett (enum '(a b c d)) :type-lemmas t)
(defdata Lett1 (oneof 'a 'b 'c 'd) :type-lemmas t)
(LETTP (RECOGNIZER-INDEX 330)
       (POS-IMPLICANTS (AND (LETTP V) (NOT (RECP V))))
       (NEG-IMPLICANTS (NOT (LETTP V)))
       (SIGNATURES (BOOLEANP (LETTP V)))
       (BIG-SWITCH? :NO)
       (MV-NTH-SYNONYM? :NO))|#
; both have same tau-data, but defdata rec works in second def but not
; not first. the disjoint lemma fails.
; Q: How does tau-system discharge the obligation in one case and
; not the other?
          :hints (("Goal" :in-theory (e/d (,dpred) (,tpred ))))))) 
     (record-disjoint-constituent-lemmas (cdr nms) tpred (cdr dex-types) wrld))))

(defun record-constructor-lemma (nm cname tpred dprex vnames disabled)
  `(defthm ,nm ;TODO: of no use if cname is not disabled!
     (implies (and ,@(build-one-param-calls dprex vnames))
              (,tpred (,cname . ,vnames)))
     :hints (("Goal" :in-theory (e/d (,tpred ,cname) (,@disabled))))))
       

;find recursive records
(defun find-recursive-record (pred new-constructors)
  (declare (xargs :mode :program
                  :guard (and (symbolp pred)
                              (symbol-alistp new-constructors))))
  (if (endp new-constructors)
    nil
    (let* ((conx-info (car new-constructors))
           (dex-pairs (dex-pairs-entry conx-info)))
    (if (member-eq pred (flatten (strip-cdrs dex-pairs) '()));TODO.BUG: simple trick, but may give false positives
      (cons conx-info (find-recursive-record pred (cdr new-constructors)))
      (find-recursive-record pred (cdr new-constructors))))))
;TODO::Check if a mutually recursive record is possible and test it.
(defun find-recursive-records (preds new-constructors)
  (declare (xargs :mode :program
                  :guard (and (symbol-listp preds)
                              (symbol-alistp new-constructors))))
  (if (endp preds)
    nil
    (let ((rrecs  (find-recursive-record (car preds) new-constructors)))
      (if rrecs
        (union-equal rrecs
                     (find-recursive-records (cdr preds) new-constructors))
        (find-recursive-records (cdr preds) new-constructors)))))
              

(defun add-record-type-support-lemmas-to-ds$ (typid dnames dex-types ds$)
  (declare (xargs :stobjs (ds$)))
  (b* ((tpred (get-predicate-symbol typid))
       (dprex (get-predicate-symbol-lst dex-types))
       (s-lemm (support-lemmas ds$))
       (fnames (map-get-field-name dnames))
       (snms (modify-symbol-lst (string-append (symbol-name tpred) "-")
                                     dnames "-SELECTOR-LEMMA"))
       (mnms (modify-symbol-lst (string-append (symbol-name tpred) "-")
                                     dnames "-MODIFIER-LEMMA"))
       (wrld (defdata-world ds$))
       (disabled (runes-to-be-disabled dprex wrld))
       (selector-lemmas (record-selector-lemmas snms tpred fnames dprex disabled))
       
       (modifier-lemmas (record-modifier-lemmas mnms tpred fnames dprex disabled))
       (vs (modify-symbol-lst "VAR-" dnames ""))
       (cnm (modify-symbol "" tpred "-CONSTRUCTOR-LEMMA"))
       (constructor-lemma (record-constructor-lemma cnm typid tpred dprex vs disabled))
       (dnms (modify-symbol-lst (string-append (symbol-name tpred) "-")
                                dprex "-DISJOINT-LEMMA"))
       (disjoint-lemmas 
        (record-disjoint-constituent-lemmas dnms tpred dex-types (defdata-world ds$)))
                         
       (record-lemmas (append disjoint-lemmas
                              (cons constructor-lemma
                                    (append selector-lemmas modifier-lemmas)))))
    
    (update-support-lemmas
     (acl2::change supp-lemmas%
      s-lemm
      :record
      (append record-lemmas (acl2::access supp-lemmas% s-lemm :record)))
     ds$)))
      
(defun is-record-type (texp typId ctx ds$)
;returns (mv trans-record-def ds$) where trans-record-def is nil if texp is
;not a record
  (declare (xargs :stobjs (ds$)))
  (b* (((unless (and (consp texp)
                    (eq (car texp) 'record)))
        (mv nil ds$))
       ((unless (>= (len (cdr texp)) 1))
        (prog2$
         (er hard ctx "~|Record ~x0 should have atleast 1 constituent.~%" texp )
         (mv nil ds$)))
;definitely a record (and right now anonymous records cant be nested)
       (ds$ (update-type-class-top-level$ 'record typId ds$))
       (dest-decl-lst (cdr texp))
       (dnames (strip-cars dest-decl-lst))
       (dex-types (strip-cdrs dest-decl-lst))
       (dprex (get-predicate-symbol-lst dex-types))
       ((mv erp dest-decl-lst1 ds$)
        (trans-dest-typ-decl-lst typId dest-decl-lst nil ctx ds$))
       ((when erp)
        (prog2$
         (er hard ctx 
             "~|Record ~x0 has malformed destructor declarations.~%"
             texp)
         (mv nil ds$)))
       (ds$ (add-newconstructor-to-ds$ typId dnames dprex ds$))
       (ds$ (add-record-type-support-lemmas-to-ds$ typId dnames dex-types ds$))
       )
;just use the product-datadef function, so record is just syntactic
;sugar. TODO: But you dont generate record lemmas for this desugared
;version.
    (mv (cons typId dest-decl-lst1) ds$)))
        


(defun add-map-type-support-lemmas-to-ds$ (typid t1 t2 ds$)
  (declare (xargs :stobjs (ds$)))
  (b* ((tpred (get-predicate-symbol typid))
       (t1p (get-predicate-symbol t1))
       (t2p (get-predicate-symbol t2))
       (s-lemm (support-lemmas ds$))
       (s-nm (modify-symbol "" tpred "-SELECTOR-LEMMA"))
       (m-nm (modify-symbol "" tpred "-MODIFIER-LEMMA"))
       (d-nm1 (modify-symbol "DISJOINT-" tpred 
                             (string-append "-" (symbol-name t1p))))
       (d-nm2 (modify-symbol "DISJOINT-" tpred 
                             (string-append "-" (symbol-name t2p))))

       (elim-rule-name (modify-symbol "" typid "-MAP-ELIM-RULE"))
       (nume (list :elim elim-rule-name))
       (elim-term `(implies (if (,tpred x) ;x is important in elim-rule representation
                                (mget a x)
                              'nil)
                            (equal (mset a (mget a x) (acl2::map-identity x))
                                   x)))
       (elim-rule (get-elim-rule nume elim-term '(mget a x)))

       (generic-lemmas
        `((defthm ,(modify-symbol "" tpred "-IMPLIES-GOOD-MAP")
            (implies (,tpred x)
                     (acl2::good-map x))
            :hints (("goal" :in-theory (e/d (,tpred))))
            :rule-classes ((:rewrite :backchain-limit-lst 1) 
                           (:forward-chaining)))
          
          (defthm ,(modify-symbol "" typid "-EXCLUDES-ATOM-LIST")
            (implies (and (,tpred x)
                          (consp x))
                     (not (atom-listp x)))
            :hints (("goal" :in-theory (e/d (,tpred) )))
            :rule-classes (:tau-system))
          (defthm ,(modify-symbol "" typid "-MAP-IDENTITY-GENERALIZE")
            (implies (,tpred x)
                     (,tpred (acl2::map-identity x)))
            :rule-classes (:generalize))))
       

       

       (disjoint-lemma1
        `(defthm ,d-nm1
           (implies (,tpred x)
                    (not (,t1p x)))
           :hints (("Goal" :in-theory (e/d (,tpred ,t1p))))))
       
       (?disjoint-lemma2
        `(defthm ,d-nm2
           (implies (,tpred x)
                    (not (,t2p x)))
           :hints (("Goal" :in-theory (e/d (,tpred ,t2p))))))
       
       (wf-key-lemma
        `(defthm ,(modify-symbol "" t1p "-IS-WELL-FORMED")
           (implies (,t1p x)
                    (acl2::wf-keyp x))
           :rule-classes ((:rewrite :backchain-limit-lst 1)
                          (:forward-chaining))))
       
       (address-in-domain-lemma 
        `(defthm ,(modify-symbol "" tpred "-DOMAIN-LEMMA")
           (implies (and (,tpred x)
                         (mget a x))
                    (,t1p a))
           :hints (("Goal" :in-theory (e/d 
                                       (,tpred mget acl2::acl2->map)
                                       (,t1p))))
           :rule-classes ((:rewrite :backchain-limit-lst 1)
                          :forward-chaining :generalize)))

       (selector-lemma 
        `(defthm ,s-nm
           (implies (and (,tpred x)
                         (mget acl2::a x))
                    (,t2p (mget acl2::a x)))
           :hints (("Goal" :in-theory (e/d 
                                       (,tpred mget acl2::acl2->map)
                                       (,t1p ,t2p))))
           :rule-classes (:rewrite :generalize)))

       (modifier-lemma
        `(defthm ,m-nm
           (implies (and (,tpred x)
                         (,t1p acl2::a)
                         (,t2p v))
                    (,tpred (mset acl2::a v x)))
           :hints (("Goal" :in-theory 
                    (e/d (,tpred mset acl2::mset-wf
                                 acl2::acl2->map acl2::map->acl2)
                         (,t1p ,t2p acl2::wf-keyp))))
           :rule-classes (:rewrite :generalize)))
       
       (map-elim-put-table-event       
        `(table map-elim-table ',typid ',elim-rule :put))

       (map-lemmas (append generic-lemmas
                           (list disjoint-lemma1
;disjoint-lemma2 ;TODO
                                 address-in-domain-lemma
                                 selector-lemma 
                                 wf-key-lemma
                                 modifier-lemma
                                 map-elim-put-table-event
                                 ))))
                          
    (update-support-lemmas
     (acl2::change supp-lemmas%
      s-lemm
      :map
      (append map-lemmas (acl2::access supp-lemmas% s-lemm :map)))
     ds$)))


(defun is-map-type (texp typId ctx ds$)
;returns (mv trans-map ds$) trans-map is nil if not a map
  (declare (xargs :stobjs (ds$)))
  (b* (((unless (and (consp texp)
                     (eq (car texp) 'map)))
        (mv nil ds$))
      ;Is a map
       ((unless (= (len (cdr texp)) 2))
        (prog2$
         (er hard ctx "Map should be of form (map typeId1 typeId2), ~
 but given ~x0.~%" texp)
         (mv nil ds$)))
       (lpair (cdr texp))
       (keyT (car lpair))
       (valT (cadr lpair))
       (w (defdata-world ds$))
       ((unless (and (is-registered keyT w)
                     (is-registered valT w)))
        (prog2$
         (er hard ctx "~x0 and ~x1 should be predefined types.~%" keyT valT)
         (mv nil ds$)))
       (ds$ (add-map-type-support-lemmas-to-ds$ typId keyT valT ds$)))
;map is just syntactic sugar
    (mv `(oneof nil (mset ,keyT ,valT ,typId)) ds$)))


;add generated set type lemmas to a temporary global variable
;For each type only one set type is added
(defun add-set-type-support-lemmas-to-ds$ (typid ds$)
  (declare (xargs :stobjs (ds$)))
  (let ((tpred (get-predicate-symbol typid))
        (s-lemm (support-lemmas ds$)))
  (update-support-lemmas
   (acl2::change supp-lemmas%
    s-lemm
    :set
    (cons `(defthm ,(modify-symbol "" tpred "-SETP")
             (implies (,tpred x)
                      (SETS::setp x))
             :rule-classes ((:forward-chaining)
                            (:rewrite :backchain-limit-lst 1)
                            ))
          (acl2::access supp-lemmas%  s-lemm :set)))
   ds$)))


  
;add generated list type lemmas to a temporary global variable
;For each type only one list type is added
(defun add-list-type-support-lemmas-to-ds$ (typid ctype1 ds$)
  (declare (xargs :stobjs (ds$)))
  (b* ((tpred (get-predicate-symbol typid))
       (s-lemm (support-lemmas ds$))
       (wrld (defdata-world ds$))
       (atom-list-subtypep (and (symbolp ctype1)
                                (is-subtype ctype1 'acl2::atom wrld)))
       
       (tlp-forms `((defthm ,(modify-symbol "" tpred "-IMPLIES-TLP")
                      (implies (,tpred x)
                               (true-listp x))
                      :rule-classes ((:forward-chaining)
                                     (:compound-recognizer)
                                     (:rewrite :backchain-limit-lst 1)))
                    (defthm ,(modify-symbol "" tpred "-TLP-APPEND")
                      (implies (and (,tpred x)
                                    (,tpred acl2::y))
                               (,tpred (acl2::append x acl2::y))) ;July 11th v941 - why is induction on binary-append disabled? ans: coi/lists/basic
                      :hints (("Goal" :induct (true-listp x)))
                      :rule-classes ((:rewrite :backchain-limit-lst 1)))
                    ))
       
       (tlp-ctype1-forms (if (is-a-typeName ctype1 wrld)
                             (let ((ctype1-pred (get-predicate-symbol ctype1)))
                               `((defthm ,(modify-symbol "" tpred "-TLP-CONS")
                                   (implies (and (,ctype1-pred x)
                                                 (,tpred acl2::y))
                                            (,tpred (cons x acl2::y)))
                                   :rule-classes :tau-system)
                                 (defthm ,(modify-symbol "" tpred "-TLP-DESTR")
                                   (implies (and (,tpred l) 
                                                 (not (equal l nil)))
                                            (and (,ctype1-pred (car l))
                                                 (,tpred (cdr l))))
                                   :rule-classes :tau-system)
                                 ))
                           '()))
       (atom-list-subtype-form
        `(defthm ,(modify-symbol "" tpred "-SUBTYPE-OF-ATOM-LIST")
                    (implies (,tpred x)
                             (atom-listp x))
                    :rule-classes :tau-system))
       (ev-forms (append tlp-ctype1-forms tlp-forms))
       (ev-forms (if atom-list-subtypep
                    (cons atom-list-subtype-form ev-forms)
                  ev-forms)))
       

   
  (update-support-lemmas
   (acl2::change supp-lemmas%
    s-lemm
    :listof
    (append ev-forms
            (acl2::access supp-lemmas% s-lemm :listof)))
   ds$)))

;;PETE: Should we get rid of the compound recognizer rule above?
;;It can be dangerous, eg, Harsh had the rule (tlp x) => (tlp x)
;;as a compound recognizer and it slowed down proofs *a lot*, but
;;maybe we just need to avoid this case and it will work out
;;fine. With the bad rule disabled, a proof went through in 13
;;seconds that previously took 205 seconds. More experiments are
;;needed. I did more experiments. The rule is fine as is. Just
;;make sure not to screw up with the above rules.

(defun is-list-type (texp typid tnames ctx ds$)
  (declare (xargs :stobjs (ds$)))
;return (mv constituentTypeExpr|nil ds$)
  (b* (((unless (and (consp texp)
                     (eq (car texp) 'listof)))
        (mv nil ds$))
      ;Is a list type
      ((unless (= (len (cdr texp)) 1))
       (prog2$
        (er hard ctx "~|listof should be of form (listof typeExpr) but ~x0 if not.~%" texp)
        (mv nil ds$)))
      (ds$ (update-type-class-top-level$ 'listof typid ds$))
      ((mv & ctype1 ds$)
       (trans-constituent-type (cadr texp) typid tnames ctx ds$))
      ;;skipped error check.
      (ds$ (add-list-type-support-lemmas-to-ds$ typid ctype1 ds$)))
    (mv `(oneof nil (cons ,ctype1 ,typid)) ds$)))
       
(defun is-set-type (texp typid tnames ctx ds$)
;returns (mv trans-list|nil ds$)
  (declare (xargs :stobjs (ds$)))
 (b* (((unless (and (consp texp)
                     (eq (car texp) 'set)))
        (mv nil ds$))
      ;Is a set type
      ((unless (= (len (cdr texp)) 1))
       (prog2$
        (er hard ctx "set should be of form (set typeId) ~
but ~x0 if not.~%" texp)
        (mv nil ds$)))
      (ds$ (update-type-class-top-level$ 'set typid ds$))
      ((mv & ctype1 ds$)
       (trans-constituent-type (cadr texp) typid tnames ctx ds$))
      ;;skipped error check.
      (ds$ (add-set-type-support-lemmas-to-ds$ typid ds$)))
   (mv `(oneof nil (SETS::insert ,ctype1 ,typid)) ds$)))
 
;gives back pre-processed data-type-exp or error
;Sig: Any * Sym * Sym-List * Sym * State -> (mv erp trans-dtexp ds$) 
;dtexp : TypeName | Singleton | Enum | Map | Record | List | Set | Prod-Union-type
;record, list, map, set have been normalized (converted
;to constituentTypeExpr) in trans-dtexp
(defun translate-defbody (dtexp typId tnames ctx ds$)
  (declare (xargs :stobjs (ds$)))
;returns (mv erp trans-defbody ds$)
  (b* (((when (is-singleton-type-p dtexp))
        (let ((ds$ (update-type-class-top-level$ 'acl2::singleton typId ds$)))
          (mv nil dtexp ds$)));constant expression or constant value?
       ((when (is-a-typeName dtexp (defdata-world ds$)))
        (let ((ds$ (update-type-class-top-level$ 'acl2::alias typId ds$)))
          (mv nil dtexp ds$)))
       ((unless (consp dtexp))
        (prog2$
          (er hard ctx "~x0 is an atom, but is neither a singleton-type ~ 
nor a predefined typename~%" dtexp)
          (mv t dtexp ds$)))
;is a data type expression (either union or product or some syntactic sugar
       (is-enum 
;preprocessing and eval called inside enum
         (is-enum-type dtexp ctx (defdata-world ds$)))
       ((when is-enum) 
         (let ((ds$ (update-type-class-top-level$ 'enum typId ds$)))
           (mv nil is-enum ds$)))
       ((mv is-map ds$) (is-map-type dtexp typId ctx ds$))
       ((when is-map)     
        (let ((ds$ (update-type-class-top-level$ 'map typId ds$)))
          (mv nil is-map ds$))) ;ADDED 3rd May 2011 REMOVED 28th Aug '12 ADDED 17 July '13
       ((mv is-record ds$) (is-record-type dtexp typId ctx ds$))
;type class of record also gets update on successful entry and not here
       ((when is-record) 
           (prog2$
            (cw? (defdata-debug ds$)
                          "record support lemmas: ~x0~%" (support-lemmas ds$))
            (mv nil is-record ds$)))
       ((mv is-list ds$) (is-list-type dtexp typId tnames ctx ds$))
       ((when is-list) (mv nil is-list ds$))
       ((mv is-set ds$) (is-set-type dtexp typId tnames ctx ds$))
       ((when is-set) (mv nil is-set ds$))
       ((mv erp is-un ds$)
         (trans-union-type-exp dtexp typId tnames ctx ds$))
;For product and union  we update type class in the top-level call
;of trans-product-type-exp and trans-union-type-exp respectively
       ((when is-un)
        (mv erp is-un ds$))
       ((mv erp is-prod ds$)
        (trans-product-type-exp dtexp typId tnames ctx ds$))
       ((when is-prod)
        (mv erp is-prod ds$))
       ((when erp)
        (prog2$
         (er hard ctx "Error in translating type expression ~x0~%" dtexp)
         (mv t nil ds$))))
    (prog2$
     (er hard ctx 
         "Illegal DataType Expression ~x0.~
               Should be either: typename, singletonType, enum, set~
               record, listof, oneof (union), product type. ~%" dtexp )
     (mv t nil ds$))))

        
;do the foll checks:
;1. Def is a true-list and is of form (typeId dataTypeExp [:hints ])
;2. typeId is a symbol TODO: We should check if its not already defined
;3. dataTypeExp is a legal data type expression
;4. keyword-list [:hints ...] TODO: should it be defined per mut-rec def or for defdata whole?
;5. dataTypeExp is also pre-processed 
(defun translate-defs0 (def tnames ctx ds$)
;return (trans-def ds$) or aborts on error
  (declare (xargs :stobjs (ds$)))
  (b* (((unless (and (true-listp def)
                     (>= (len def) 2)))
        (prog2$
         (er hard ctx "Definition ~x0 incorrectly formed.~%" def)
         (mv nil ds$)))
       (typId (car def))
       (dataTypExp (cadr def))
       ((unless (is-a-typeId-p typId (defdata-world ds$)))
        (prog2$
         (er hard ctx "~x0 is not a valid Type Identifier .~%" typId)
         (mv nil ds$)))
       ((mv erp dtexp ds$) 
        (translate-defbody dataTypExp typId tnames ctx ds$))
       ((unless (not erp))
        (prog2$
         (er hard ctx "Could not translate defdata body ~x0~%" dataTypExp)
         (mv nil ds$)))
       (rst (cddr def)) ;hints etc keyword list
       ((unless (acl2::keyword-value-listp rst)) ;check for hints
        (prog2$
         (er hard ctx "Expecting :hints but found ~x0.~%" rst)
         (mv nil ds$))))
;reconstruct. cddr may be hints
       (mv (append (list typId dtexp) rst) ds$))) 

        
(defun translate-defs0-lst (defs tnames ctx ds$ ans)
  (declare (xargs :stobjs (ds$)))
  (if (endp defs)
    (mv ans ds$)
    (b* ((def (car defs))
;check for errors in syntax and also preprocess (translate)
         ((mv cdef ds$) (translate-defs0 def tnames ctx ds$)))
      (translate-defs0-lst (cdr defs) 
                           tnames 
                           ctx  ds$
                           (append ans (list cdef))))))
                                                                                 
    
;;; normalise single and mutually-recursive defs 
;;; into (defdata (typeId dataTypeExp)+ )
;;; and then call check-syntax-defs on resulting normalised form
;;; Additionaly check for empty definitions and 
;;; empty enum/oneof/anyof/record/listof(Not required i guess, redundant)
(defun translate-defs (defs ctx ds$)
;returns (mv trans-defs ds$) or aborts on error
  (declare (xargs :stobjs (ds$)
                  :mode :program))

  (b* (((unless (and (consp defs) 
                     (true-listp defs)))
        (prog2$
         (er hard ctx "Empty form not allowed.~%")
         (mv nil ds$)))
       ((when (and (not (symbolp (car defs)));not single def
                   (found-empty-defp defs))) 
;check for empty defs and empty enum/oneof/record/anyof/listof
        (prog2$
         (er hard ctx 
             "Empty definition or Empty body in ~x0 not allowed.~%"
             defs)
         (mv nil ds$)))
       ((when (and (not (symbolp (car defs)))
                   (consp (cdr defs)))) ;atleast 2 types
        ;;should i name this in acl2 package (mut-rec)?
        (let* ((tnames (strip-cars defs))
               (undef-lst (make-list (len tnames) :initial-element :undefined))
               (ds$ (if (eq (type-class ds$) :undefined)
                         (update-type-class (cons 'acl2::mutually-recursive 
                                                  (pairlis$ tnames undef-lst)) ds$)
                       ds$)))
          (translate-defs0-lst defs tnames ctx ds$ nil)))
;single defn to be normalised
       (def (if (symbolp (car defs)) defs (car defs))) 
;rename defs to def to avoid confusion, def is the single definition
       ((unless (> (len def) 1))
        (prog2$
         (er hard ctx "Syntax Error in defdata: Empty definition.~%" )
         (mv nil ds$)))
       ((unless (acl2::keyword-value-listp (cddr def)))
;check for hints
        (prog2$
         (er hard ctx "Definitions that are not mutually-recursive should be ~
                      of form (defdata <id> <type-definition> [:hints <hints>
                     ...]).~%" )
         (mv nil ds$)))
       ((when (found-empty-defp (list def)))
        (prog2$
         (er hard ctx "Found empty definition or Empty body in ~x0.~%"
             def)
         (mv nil ds$))))
    (translate-defs0-lst (list def) (list (car def)) ctx ds$ nil)))
         
 

(logic)    

; See first issue in acl2s-issues. 5 July '13
; common interface for enumerators (both inf and fin)
; TODO: what if names enum-sym and values-sym are already in history
(defun cons-up-defconsts (names lens vals)
  (declare (xargs :guard (and (symbol-listp names)
                              (nat-listp lens)
                              (true-listp vals))))
  (if (endp names)
    nil
    (b* ((name (car names))
         (values-sym (get-values-symbol name))
         (enum-sym (get-enumerator-symbol name))
         (enum-uniform-sym (get-uniform-enumerator-symbol name)))
    (append (list* `(defconst ,values-sym ',(car vals))
                   `(defun ,enum-sym (n)
                      (declare (xargs :guard (natp n)))
                      (nth (mod n ,(car lens)) ,values-sym))
                   (make-enum-uniform-defun-ev enum-uniform-sym enum-sym))
            (cons-up-defconsts (cdr names)
                               (cdr lens)
                               (cdr vals))))))

(defun cons-up-pred-defthms (tnames pnames bodies rsts)
   (declare (xargs :guard (and (true-listp tnames)
                               (true-listp bodies)
                               (true-listp pnames)
                               (true-listp rsts))))
                               
  (if (endp tnames)
    nil
    (cons `(defthm ,(car tnames)
             (equal (,(car pnames) v)
                    ,(car bodies))
             :rule-classes nil
             . ,(car rsts))
          (cons-up-pred-defthms (cdr tnames)
                                (cdr pnames)
                                (cdr bodies)
                                (cdr rsts)))))

(defun cons-up-non-recursive-pred-definition-defthms (tnames pnames bodies)
   (declare (xargs :guard (and (true-listp tnames)
                               (true-listp bodies)
                               (true-listp pnames))))
                               
  (if (endp tnames)
    nil
    (cons `(defthm ,(car tnames)
             (equal (,(car pnames) v)
                    ,(car bodies))
             :hints (("Goal" :in-theory (enable ,(car pnames)))))
          (cons-up-non-recursive-pred-definition-defthms (cdr tnames)
                                                         (cdr pnames)
                                                         (cdr bodies)))))


(defun lens (l)
  (declare (xargs :guard (true-list-listp l)))
  (if (endp l)
    nil
    (cons (len (car l))
          (lens (cdr l)))))

(defun cons-up-register-custom-type-ev (tnames)
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-listp tnames))))
                              
  (if (endp tnames)
      '()
    (cons `(register-custom-type ,(car tnames)
                                 t 
                                 ,(get-enumerator-symbol (car tnames))
                                 ,(get-predicate-symbol (car tnames)))
          (cons-up-register-custom-type-ev (cdr tnames)))))
               
(defun cons-up-add-type-info-calls 
  (tsizes tnames tpreds tenums ttestenums defs 
          recursive-tnames type-class)
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-listp tnames)
                              (true-listp tsizes)
                              (implies (consp tsizes)
                                       (or (equal (car tsizes) t)
                                           (natp (car tsizes))))
                              (symbol-listp recursive-tnames)
                              (symbol-listp tpreds)
                              (symbol-listp tenums)
                              (symbol-listp ttestenums)
;(alistp defs)
                              (type-class-p type-class))))

                              
  (if (endp tnames)
    nil
    (cons `(table
            defdata::types-info-table
             ',(car tnames)
             ',(acl2::make types-info%
                  :size (car tsizes) 
                  :enumerator (car tenums)
                  :predicate (car tpreds)
                  :test-enumerator (car ttestenums)
                  :enum-uniform (get-uniform-enumerator-symbol (car tnames))
                  :defs defs
                  :derivedp t;defdata == derived data-type
                  :recursivep (if (member-equal (car tnames)
                                                recursive-tnames)
                                  t
                                nil)
                  :type-class type-class)
             :put)
          (cons-up-add-type-info-calls (cdr tsizes)
                                       (cdr tnames)
                                       (cdr tpreds)
                                       (cdr tenums)
                                       (cdr ttestenums)
                                       defs 
                                       recursive-tnames
                                       type-class
                                       ))))
;generate add-datatype-node-dtg-batch calls for each tname in tnames
(defun cons-up-add-datatype-node-dtg-calls (tnames)
  (declare (xargs :guard (symbol-listp tnames)))
  (if (endp tnames)
    nil 
    (cons `(add-datatype-node-batch ,(car tnames)) ;macro call, so dont quote like elsewhere
          (cons-up-add-datatype-node-dtg-calls (cdr tnames)))))

;filter typ-exps which are typenames
(defun filter-typeName (texp-lst tnames state)
  (declare (xargs :stobjs (state)
                  :mode :program
                  :guard (and (true-listp texp-lst)
                              (symbol-listp tnames))))
  (if (endp texp-lst)
    nil
    (let* ((texp (car texp-lst))
           (istype  (or (is-a-typeName texp (w state))
                        (mem1 texp tnames))))
      (if istype
        (cons texp (filter-typeName (cdr texp-lst) tnames state))
        (filter-typeName (cdr texp-lst) tnames state)))))

(program)
;list together calls that add a edge in the subtype graph for each
;constituent-type -> union-type
; TODO - not general, doesnt treat product constituents
(mutual-recursion
 (defun collect-defdata-oneof-subtype-event (dtexp typ tnames w)
   (let* ((T1p (get-predicate-symbol typ)))
     (cond ((is-singleton-type-p dtexp)
            (b* ((ev-form-print `(defthm ,(modify-symbol "EVAL-" T1p (string-append "-TAU-RULE-EQUAL-"(to-string dtexp)))
                                   (,T1p ,dtexp) :rule-classes :tau-system))
                 (ev-forms `((value-triple (cw? (get-acl2s-defdata-verbose) "~|Submitting ~x0~|" ',ev-form-print))
                             ,ev-form-print)))
              ev-forms))
            ((or (member-eq dtexp tnames) (is-a-typeName dtexp w))
             `((defdata-subtype ,dtexp ,typ)))
            ((and (consp dtexp)
                  (or (eq (car dtexp) 'oneof) (eq (car dtexp) 'anyof)))
             (collect-defdata-oneof-subtype-events (cdr dtexp) typ tnames w))
            (t '()))))
            
 (defun collect-defdata-oneof-subtype-events (c-typexp-lst typ tnames w)
   (declare (xargs :guard (and (true-listp c-typexp-lst)
                               (symbolp typ)
                               (symbol-listp tnames)
                               (plist-worldp w))))
   
   (if (endp c-typexp-lst)
       '()
     (append (collect-defdata-oneof-subtype-event (car c-typexp-lst) typ tnames w)
             (collect-defdata-oneof-subtype-events (cdr c-typexp-lst) typ tnames w))))
)

; generate subtype edge calls for each tname in tnames (not recursive
; types are also dealt uniformly)
(defun constituent-types-oneof-subtype-events (defs tnames w)
  (declare (xargs :mode :program
                  :guard (and (true-listp defs)
                              (symbol-listp tnames)
                              (plist-worldp w))))
  (if (endp defs)
      '()
    (let* ((def (car defs))
          (nm (car def))
          (tbody (cadr def)))
      (if (and (consp tbody) ;not a singleton or typename
               (or (eq (car tbody) 'oneof) ;is a union type expression
                   (eq (car tbody) 'anyof)))
          (append (collect-defdata-oneof-subtype-events (cdr tbody) nm tnames w)
                  (constituent-types-oneof-subtype-events (cdr defs) tnames w))
        (constituent-types-oneof-subtype-events (cdr defs) tnames w)))))

(logic)                            

(defun defsp (x)
  (if (atom x)
    (equal x nil)
    (and (= 2 (len (car x)))
         (symbolp (first (car x)))
         (defbodyp (second (car x)))
         (defsp (cdr x)))))

        
(defthm rec-type-defbody-type
  (implies (defsp defs)
           (defbodyp (second (assoc-eq typ defs)))))





;TODO singleton types not yet dealt with
(defun make-subtype-events1 (tc defs)
"defs are all defs of type-class tc. generate defdata-subtype events for each def"
  (declare (xargs :guard (and (defsp defs))))
  (if (endp defs)
      '()
    (let* ((def (car defs))
          (nm (car def));shud be a symbol
          (tbody (cadr def)))
      (case tc
        (acl2::alias (append (list (list 'defdata-subtype nm tbody)
                                   (list 'defdata-subtype tbody nm))
                             (make-subtype-events1 tc (cdr defs))))
        (listof (cons (list 'defdata-subtype nm 'acl2::true-list)
                      (make-subtype-events1 tc (cdr defs))))
        (map (cons (list 'defdata-subtype nm 'acl2::alist)
                   (make-subtype-events1 tc (cdr defs))))
        (otherwise (make-subtype-events1 tc (cdr defs)))))))


(local
 (defthm filter-defs-guard1
   (implies (and (symbol-alistp x)
                 (not (consp x)))
            (equal x nil))
   :rule-classes :tau-system))
            

(defun filter-defs (tc defs alst)
  "filter out defs of type-class tc"
   (declare (xargs :verify-guards nil
                   :guard (and (type-class-simple-p tc)
                               (defsp defs)
                               (symbol-alistp alst))))
  (if (endp defs)
      '()
    (let ((entry (assoc-eq (caar defs) alst)))
      (if (and (consp entry)
               (eq tc (cdr entry)))
          (cons (car defs)
                (filter-defs tc (cdr defs) alst))
        (filter-defs tc (cdr defs) alst)))))

(local (defthm filter-defs-guard2
         (implies (and (type-class-simple-p tc)
                       (defsp x))
                  (defsp (filter-defs tc x y)))
         :rule-classes :tau-system))

(verify-guards filter-defs)


(defun make-subtype-events (tc defs)
  (declare (xargs :guard (and (defsp defs)
                              (type-class-p tc))))
  (cond ((eq tc 'acl2::alias) (make-subtype-events1 tc defs))
        ((and (consp tc) (eq (car tc) 'acl2::mutually-recursive))
         (append (make-subtype-events1 'acl2::alias (filter-defs 'acl2::alias defs (cdr tc)))
                 (make-subtype-events1 'listof (filter-defs 'listof defs (cdr tc))))) ;can map be in clique?
        ((member-eq tc '(listof map)) (make-subtype-events1 tc defs))
        (t '())))


(defun make-boolean-tau-rule-event (typs)
  (declare (xargs :guard (and (symbol-listp typs))))
                  
  (if (endp typs)
      '()
    (let ((pred (get-predicate-symbol (car typs))))
    (cons `(defthm ,(modify-symbol "" pred "-IS-BOOLEAN-TAU")
             (booleanp (,pred x))
             :rule-classes :tau-system
             :hints (("goal" :in-theory (enable ,pred))))
          (make-boolean-tau-rule-event (cdr typs))))))

;; (defun record-tau-subtype-events (preds P)
;;   (declare (xargs :guard (and (symbol-listp preds)
;;                               (symbolp P))))
;;   (if (endp preds)
;;       '()
;;     (cons `(defthm ,(modify-symbol "" (car preds) (string-append "-SUBTYPE-OF-" (symbol-name P)))
;;              (implies (,(car preds) x) (,P x))
;;              :rule-classes (:tau-system)
;;              :hints (("goal" :in-theory (enable ,(car preds)))))
;;           (record-tau-subtype-events (cdr preds) P))))
          
;; (defun record-defdata-subtype-events (typs P)
;;   (declare (xargs :guard (and (symbol-listp typs)
;;                               (symbolp P))))
;;   (if (endp typs)
;;       '()
;;     (cons `(defdata-subtype ,(car typs) ,P 
;;              :hints (("goal" :in-theory (enable ,(get-predicate-symbol (car typs)) ))))
;;           (record-defdata-subtype-events (cdr typs) P))))

;extract destructor-predicate pairs
(defun strip-dex-pairx (new-constructors)
  (declare (xargs :mode :program
                  :guard (alistp new-constructors)))
  (if (endp new-constructors)
    nil
    (cons (dex-pairs-entry (car new-constructors))
          (strip-dex-pairx (cdr new-constructors)))))

;extract predicates
(defun strip-preds (new-constructors)
  (declare (xargs :mode :program
                  :guard (alistp new-constructors)))
  (if (endp new-constructors)
    nil
    (cons (predicate-name-entry (car new-constructors))
          (strip-preds (cdr new-constructors)))))



;ADD this to the syntactic check!!! TODO. THis gives some false positives
(mutual-recursion
;Is typename defined in a (defdata (tname1 ...) ...) a recursive type?
;Implicit contract: (in typename tnames)
(defun is-recursive-type-lst (typename tnames defbody-lst)
  (declare (xargs :guard (and (symbolp typename)
                              (symbol-listp tnames)
                              (defbody-listp defbody-lst))))
                  ;:verify-guards nil))
  (if (endp defbody-lst)
    nil
  (or (is-recursive-type typename tnames (car defbody-lst))
      (is-recursive-type-lst typename tnames (cdr defbody-lst)))))

(defun is-recursive-type (typename tnames defbody)
  (declare (xargs :guard (and (symbolp typename)
                              (symbol-listp tnames)
                              (defbodyp defbody))))
  (cond ((possible-constant-valuep defbody) nil)
        ((symbolp defbody) (mem1 defbody tnames))
        (t (is-recursive-type-lst typename tnames (cdr defbody)))))
)
           
(defthm rec-type-consp-defbody-type
  (implies (and (consp defbody)
                (defbodyp defbody)
                (is-recursive-type typename tnames defbody))
           (defbody-listp (cdr defbody))))

(defun get-recursive-typenames (types defs tnames)
  (declare (xargs ;:mode :program 
                  :guard-hints (("Goal" :in-theory (disable is-recursive-type)))
                  :guard (and (symbol-listp types)
                              (symbol-listp tnames)
                              (defsp defs))))
  (if (endp types)
    nil
    (let ((typename (car types)))
      (if  (is-recursive-type typename tnames (second (assoc-eq typename defs)))
        (cons typename
              (get-recursive-typenames (cdr types) defs tnames))
        (get-recursive-typenames (cdr types) defs tnames)))))

(defun my-append (Xs Ys)
  (declare (xargs :guard (and (true-listp Xs)
                              (true-listp Ys))))
                  
  (append Xs Ys));for debugging

;;make type consistency check event for all types in arg
;;Generate the foll form:
;; (thm (implies (natp x) (Tp (nth-T x)))) or
;; (thm (implies (< n (len *T-values*)) (Tp (nth n *T-values*))))
;; TODO.Note: *T-values* might be very big list in that case, there must be a cleaner/efficient way.
(defun cons-up-type-consistent-thm-ev (tnames wrld)
  (declare (xargs :mode :program
                  :guard (symbol-listp tnames)))
  (if (endp tnames)
    nil
    (let* ((tname (car tnames))
           (tpred (get-predicate-symbol tname))
           (tenum (get-enumerator-symbol tname))
           (tvalues (get-values-symbol tname))
           (tpred-lst (modify-symbol "" tpred "-LST-AUTO-GENERATED"))) 
      (append (if (allows-arity tenum 1 wrld)
                (list `(thm (implies (natp n) (,tpred (,tenum n)))
                            :hints (("Goal" :in-theory (e/d (,tpred ,tenum))))))
                (list `(defun ,tpred-lst (xs) 
                         (if (endp xs)
                           t
                           (and (,tpred (car xs))
                                (,tpred-lst (cdr xs)))))
                      `(thm (,tpred-lst ,tvalues))))
              (cons-up-type-consistent-thm-ev (cdr tnames) wrld)))))

  


;this function takes care of records, where the constructor name is the
;same as the name of the type and hence to avoid a bad redefinition\
;we collect only that preds that need predicates , excluding
;the constructor predicate which is generated anyway!
(defun names-need-predicates (nms nms-with-pred new-constructors)
  (declare (xargs :guard (and (symbol-listp nms)
                              (symbol-listp nms-with-pred)
                              (symbol-alistp new-constructors))))
  
  (let* ((nms-need (set-difference-eq nms nms-with-pred))
         (new-names (strip-cars new-constructors)))
    (set-difference-eq nms-need new-names)))
          

;;harshrc: changed name of the main function (from compute-defdata)
;; defs - ((typeid . constituentTypeExpr) ...)
(defun compute-typecombs (defs kwd-options-lst 
                           new-record-constructors 
                           support-lemmas custom-types
                           type-class
                           ctx wrld state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((names (strip-cars defs))
       (?verbose (get-acl2s-defdata-verbose))
;(defbodies (strip-cadrs defs))
       (pred-syms (get-predicate-symbol-lst names))
       
;with predicates already defined --ASK: what if its defined inconsistently??BUG?
       (names-with-preds (collect-with-plausible-pred-fns names wrld))
       (defs-with-preds (assoc-lst names-with-preds defs))
       (defbodies-with-preds (strip-cadrs defs-with-preds))
       (rsts-with-preds (acl2::strip-cddrs defs-with-preds))
       (pred-syms-with-preds (get-predicate-symbol-lst names-with-preds))
       (thm-syms-with-preds (get-predicate-testthm-symbol-lst names-with-preds))
       
;predicates need to be defined
       (names-need-preds (names-need-predicates names names-with-preds new-record-constructors))
       (pred-syms-need-preds (get-predicate-symbol-lst names-need-preds))
       
       (defs-need-preds (assoc-lst names-need-preds defs))
       (defbodies-need-preds (strip-cadrs defs-need-preds))
       
;non recursive predicates(from names that need preds) need to be treated separately
       (recursive-names (get-recursive-typenames names-need-preds defs names))
       (non-recursive-names (set-difference-eq names-need-preds recursive-names))
       (?non-recursive-pred-syms (get-predicate-symbol-lst non-recursive-names))
       (defs-non-recursive (assoc-lst non-recursive-names defs))
       (defbodies-non-recursive (strip-cadrs defs-non-recursive))
       
       ;;events from new constructors (records)
       (conx-names (strip-cars new-record-constructors))
       (conx-recursive-alst (find-recursive-records pred-syms-need-preds new-record-constructors))
       (conx-non-recur-alst (set-difference-eq new-record-constructors conx-recursive-alst))
       (conx-recur-names (strip-cars conx-recursive-alst))
       (conx-non-recur-names (set-difference-eq conx-names conx-recur-names)) 
       (dex-pairs-non-recur-lst (strip-dex-pairx conx-non-recur-alst))
       (dex-pairs-lst (strip-dex-pairx new-record-constructors))
       (dex-pairs-recur-lst (strip-dex-pairx conx-recursive-alst))
       (conx-pred-recur-events (cons-up-conx-prex-ev conx-recur-names dex-pairs-recur-lst))
       (conx-pred-recur-defun-cdrs (strip-cdrs conx-pred-recur-events));strip defun
       (conx-pred-recur-names (strip-cadrs conx-pred-recur-events))
       (conx-pred-non-recur-events (cons-up-conx-prex-ev conx-non-recur-names dex-pairs-non-recur-lst))
       (?conx-pred-non-recur-names (strip-cadrs conx-pred-non-recur-events))
;(dex-events (append-up-dex-ev conx-names dex-pairs-lst))
       (conx-events (cons-up-conx-ev conx-names dex-pairs-lst))
       (register-conx-dex-events (cons-up-reg-conx-dex-ev conx-names dex-pairs-lst))
       
       ;; generating supporting lemmas
       (gen-lemmasp (if (mem1 :type-lemmas kwd-options-lst)
                        (get-value-from-keyword-value-list :type-lemmas kwd-options-lst)
                      t)) ;changed default for project 11th april '13
       (record-implies-consp/good-map-lemmas (cons-up-record-implies-consp/good-map-ev conx-names dex-pairs-lst wrld))
;lemmas for syntactic sugar
       (list-type-support-lemmas (acl2::access supp-lemmas%
                                               support-lemmas :listof))
       (set-type-support-lemmas (acl2::access supp-lemmas%
                                              support-lemmas :set))
       (record-type-support-lemmas (and gen-lemmasp
                                        (acl2::access supp-lemmas%
                                                      support-lemmas :record)))
       (map-type-support-lemmas (and gen-lemmasp
                                     (acl2::access supp-lemmas%
                                                      support-lemmas :map)))
; lemmas for base union-product type lemmas
;(base-type-support-lemmas (g :base support-lemmas))
;(verbose (get-acl2s-defdata-verbose))
       (generate-allp-alias-boolean-tau-rule-p (and (eq type-class 'acl2::alias)
                                                    (is-subtype 'ACL2::ALL (cadr (car defs)) wrld)))
                                         
       )
    (if (not (no-duplicatesp names))
        (er soft ctx "Duplicate found in the names being defined: ~x0" names)
      (b* (((er pred-bodies-with) (er-trans-datadef-as-predicate-lst
                                   defbodies-with-preds
                                   pred-syms
                                   (make-list (len defbodies-with-preds)
                                              :initial-element 'v)
                                   new-record-constructors
                                   ctx wrld state))
           ;;-- pred-bodies-need e.g:
           ;;-- ((OR (EQ V 'NIL)
           ;;-- (AND (CONSP V)
           ;;--   (FOOP (CAR V))
           ;;--   (BARP (CDR V)))))
           ((er pred-bodies-need) (er-trans-datadef-as-predicate-lst
                                   defbodies-need-preds
                                   pred-syms
                                   (make-list (len defbodies-need-preds)
                                              :initial-element 'v)
                                   new-record-constructors
                                   ctx wrld state))
           ((er ?non-recur-pred-bodies-need) (er-trans-datadef-as-predicate-lst
                                             defbodies-non-recursive
                                             pred-syms
;TODO:Possible bug, shudnt it be non-recursive preds only
                                             (make-list (len defbodies-non-recursive)
                                                        :initial-element 'v)
                                             new-record-constructors
                                             ctx wrld state))


           ;;-- fin-binds e.g =
           ;;--((FOO 42 (T T) (NIL T) (T NIL) (NIL NIL))
           ;;-- (BAZ (T) (NIL))
           ;;-- (MOO NIL))
           ((er fin-binds) (er-get-finite-data-defs defs new-record-constructors ctx wrld state))
           (fin-names (strip-cars fin-binds))
           (fin-enum-syms (get-values-symbol-lst fin-names))
           (fin-values (strip-cdrs fin-binds))
           (fin-lens (lens fin-values))
           (fin-defs  (cons-up-lists fin-enum-syms fin-values))
           (inf-names (set-difference-eq names fin-names))
           (inf-enum-syms (get-enumerator-symbol-lst inf-names))
;CHANGED by harshrc Jan 24 2011(earlier hack on Jun 6 2010)
           (declare-guardsp (if (mem1 :declare-guards kwd-options-lst)
                                (get-value-from-keyword-value-list :declare-guards kwd-options-lst)
                              (get-acl2s-defdata-use-guards)))
           (inf-bodies (strip-cadrs (assoc-lst inf-names defs)))
           ((er inf-enums) (er-trans-datadef-as-enumerator-lst
                            inf-bodies
                            fin-defs
                            inf-enum-syms
                            nil
                            new-record-constructors
                            ctx wrld state))
           (?inf-uniform-enum-syms (get-uniform-enumerator-symbol-lst inf-names))
           ((er inf-uniform-enums) (er-trans-datadef-as-enumerator-lst
                                    inf-bodies
                                    fin-defs
                                    (append (get-uniform-enumerator-symbol-lst custom-types) inf-uniform-enum-syms)
                                    t
                                    new-record-constructors
                                    ctx wrld state))
           (testing-enabled (acl2s-defaults :get testing-enabled))
           (acl2-defaults-tbl (table-alist 'acl2::acl2-defaults-table wrld))
           (current-termination-method-entry (assoc :termination-method acl2-defaults-tbl))
           );*b
;in
        (value `
         (progn
           ;; (set-internal-acl2s-inside-defdata-flag t)
           
           (acl2s-defaults :set testing-enabled nil)
           ,@(and 
              conx-pred-non-recur-names
              `((value-triple
                 (cw? t
                      "Submitting (non-recursive) record predicate functions ~x0.~%"
                      ',conx-pred-non-recur-names))))
           
           ,@conx-pred-non-recur-events

           ,@(and 
              (append pred-syms-need-preds
                      conx-pred-recur-names)
              `((value-triple
                 (cw? t
                      "Submitting predicate functions ~x0.~%"
                      ',(append pred-syms-need-preds
                                conx-pred-recur-names)))))
           ,@(and 
              pred-syms-need-preds
              `((defuns . ,(append 
                            conx-pred-recur-defun-cdrs
                            (cons-up-names-decls-lls-bodies
                             pred-syms-need-preds
                             (if T;declare-guardsp  
;harshrc Sep 3rd 2012 -- OK, predicates need their guards to be
;verified. I hope this wont break anything, since this change though
;it reduces flexibility it does not change the behavior of
;declare-guardsp for now, since the default value for it was T anyway.
                                 (make-list (len pred-syms-need-preds) 
                                            :initial-element 
                                            '(declare (xargs :guard t
                                                             :ruler-extenders :all
                                                             )))
                               (make-list (len pred-syms-need-preds) 
                                          :initial-element 
                                          '(declare (xargs :ruler-extenders :all)))
                               );end of if , this gives the declare form for the predicate
                             (make-list (len pred-syms-need-preds)
                                        :initial-element '(v))
                             pred-bodies-need)))))
           ;; ,@(and 
           ;;    (or non-recursive-pred-syms conx-pred-non-recur-names)
           ;;    `((in-theory (disable ,@(union-eq non-recursive-pred-syms 
           ;;                                      conx-pred-non-recur-names)))))
           
           ,@conx-events
           
; 10th April 2013 - Generate record=>consp/good-map for all records
; (earlier only recursive records were getting these lemmas)
           
           ,@(and conx-names
                  `((value-triple
                     (progn$
                      (time-tracker :defdata-generic-record-lemmas :end)
                      (time-tracker :defdata-generic-record-lemmas :init
                                    :times '(2 7)
                                    :interval 5
                                    :msg "Elapsed runtime in generic lemma proofs for records is ~st secs;~|~%")
                      (cw? t
                           "Submitting generic record lemmas... ~%")
                      (cw? t;,verbose
                           "~x0~%" ',record-implies-consp/good-map-lemmas)))))
           ,@(and conx-names record-implies-consp/good-map-lemmas)
           
;,@ dex-events (Jan25 2011 No need, mget handles it)
           ,@register-conx-dex-events
; TODO: check if the fin and enum names of fin-names are fresh!
           ,@(cons-up-defconsts fin-names ;fin-enum-syms -- 5 july '13 add defuns too
                                fin-lens
                                fin-values)
           ,@(cons-up-pred-defthms thm-syms-with-preds
                                   pred-syms-with-preds
                                   pred-bodies-with
                                   rsts-with-preds)

           ,@(and list-type-support-lemmas
                  `((value-triple
                     (progn$
                      (cw? t
                           "Submitting list type lemmas... ~%")
                      (cw? t;,verbose
                          "~x0~%" ',list-type-support-lemmas)))))
           ,@list-type-support-lemmas   
           
           ,@(and set-type-support-lemmas
                  `((value-triple
                     (cw? t
                          "Submitting set type lemmas... ~%"))))
           ,@set-type-support-lemmas

           ,@(and record-type-support-lemmas
                  `((value-triple
                     (progn$
                      (time-tracker :defdata-record-lemmas :end)
                      (time-tracker :defdata-record-lemmas :init
                                    :times '(2 7)
                                    :interval 5
                                    :msg "Elapsed runtime in type proofs for records is ~st secs;~|~%")
                      (time-tracker :defdata-record-lemmas :start)
                      
                     (cw? t
                          "Submitting record type lemmas... ~%")
                     (cw? t;,verbose
                          "~x0~%" ',record-type-support-lemmas)))))
           ,@record-type-support-lemmas
           ,@(and record-type-support-lemmas
                  '((value-triple (prog2$
                                   (time-tracker :defdata-record-lemmas :stop)
                                   :invisible))))
            
           
           ,@ (and map-type-support-lemmas
                   `((value-triple
                      (cw? t
                                    "Submitting map type lemmas... ~%"))))
           ,@ map-type-support-lemmas

           ;; ;,@ base-type-support-lemmas
           
           ,@(and inf-enums
                  `((value-triple
                     (cw? t
                          "Submitting enumerator functions ~x0.~%"
                          ',inf-enum-syms))))
           
           
           ,@(and 
              inf-enums
              `((defuns . 
                  ,(cons-up-names-decls-lls-bodies
                    inf-enum-syms
                    (if declare-guardsp
                        (make-list (len inf-enums)
                                   :initial-element 
                                   (if current-termination-method-entry
                                       '(declare (xargs :consider-only-ccms ((nfix x))
                                                        :guard (natp x)))
                                     '(declare (xargs :measure (nfix x)
                                                      :guard (natp x) ))
                                     
                                     ))
                      (make-list (len inf-enums)
                                 :initial-element 
                                 (if current-termination-method-entry
                                     '(declare (xargs :consider-only-ccms ((nfix x))))
                                   '(declare (xargs :measure (nfix x))))
                                 )
                      );end of if , this gives the declare form for the enum
                    (make-list (len inf-enums)
                               :initial-element '(x))
                    (strip-cdrs inf-enums)))))
           (in-theory (disable ,@inf-enum-syms))
           ,@(cons-up-register-custom-type-ev custom-types)
           
           ;;hack
           ,@(and current-termination-method-entry
                  '((acl2::set-termination-method :measure)))
                
           ,@(and 
              inf-uniform-enums
              `((defuns . 
                  ,(cons-up-names-decls-lls-bodies
                    inf-uniform-enum-syms
                    (make-list (len inf-uniform-enums)
                               :initial-element 
                               `(declare (ignorable m)
                                         (type (unsigned-byte 31) seed)
                                         (xargs ,@(if nil;current-termination-method-entry 
                                                      '(:consider-only-ccms ((nfix m)))
                                                    '(:measure (nfix m)))
                                                :verify-guards nil
                                                :guard (and (natp m)
                                                            (unsigned-byte-p 31 seed))))
                               )
                    (make-list (len inf-uniform-enums)
                               :initial-element '(m seed))
                    (strip-cdrs inf-uniform-enums)))))
           ;;hack
           ,@(and current-termination-method-entry
                  `((acl2::set-termination-method ,(cdr current-termination-method-entry))))

           (in-theory (disable ,@inf-uniform-enum-syms))
           (value-triple
            (cw? t
                 "Updating defdata type table (type-class ~x0).~%" ',type-class))
           
           ,@(and generate-allp-alias-boolean-tau-rule-p ;TODO HACK, shud i do this for all names?
                  (make-boolean-tau-rule-event names))
           
;add fin and inf type information to types-table 
;(but seperately because we have to do this outside make-event)
           ,@(cons-up-add-type-info-calls 
              fin-lens
              fin-names (get-predicate-symbol-lst fin-names)
              fin-enum-syms nil defs
              nil type-class);test-enums=nil, recursive-names=nil
;Question: How can u have multiple finite types? Multiple type defs 
;invariably mean mutually-recursive!! Put an assert?
           ,@(cons-up-add-type-info-calls 
              (make-list (len inf-enums) :initial-element 't)
              inf-names (get-predicate-symbol-lst inf-names)
              inf-enum-syms nil defs;test-enums = nil
              (get-recursive-typenames names defs names)
              type-class)
           
           (value-triple
            (cw? t
                 "Adding ~x0 to the type relation graphs.~%" ',names))
           
;test-enums will only be explicitly provided by the user and added to the table
           ,@(cons-up-add-datatype-node-dtg-calls names) ;add the noded to datatype-graph
           (sync-globals-for-dtg) ;o.w following call to defdata-subtype fails
           (value-triple
            (cw? t
                 "Updating the defdata subtype/disjoint graphs.~%"))
           ,@(let* ((ev-forms0 (constituent-types-oneof-subtype-events defs names (w state)))
                    (ev-forms1 ;hack 16 July '13
                     (cond ((and (eq type-class 'acl2::listof)
                                 (is-registered 'acl2::true-list wrld))
                            (make-subtype-events type-class defs))
;assumption: there are no mutual-recursive types in base.lisp where true-list is still undefined.
                           ((member-eq type-class '(acl2::mutually-recursive acl2::alias map)) 
                            (make-subtype-events type-class defs))
                           (t '())))
                    (ev-forms (append ev-forms1 ev-forms0)))
               (if (and gen-lemmasp ev-forms)
                   (append ev-forms 
;sync globals with SCC and TC graph algorithm calc
                           (list '(sync-globals-for-dtg)))
                 (list '(sync-globals-for-dtg))))

           (acl2s-defaults :set testing-enabled ,testing-enabled)
           (value-triple ',names)
           ;; (set-internal-acl2s-inside-defdata-flag nil)
           ))
         
         ))))

;defs-ans is accumlated defs to be extracted
(defun get-defs-and-keyword-list (args defs-ans)
  (declare (xargs :guard (and (true-listp args)
                              (true-listp defs-ans))))
  (if (endp args)
    (mv defs-ans nil)
    (if (keyword-value-listp args);not null
      (mv defs-ans args) ;abort and give back answer
      (get-defs-and-keyword-list (cdr args) 
                                 (append defs-ans (list (car args)))))))

(defun initialize-ds$ (debug wrld ds$)
  (declare (xargs :stobjs (ds$)
                  :guard (and (booleanp debug)
                              (ds$p ds$))))
                 
  (b* ((ds$ (update-defdata-world wrld ds$))
       (ds$ (update-newconstructors nil ds$))
       (ds$ (update-custom-types nil ds$))
       (ds$ (update-support-lemmas *initial-supp-lemmas* ds$))
       (ds$ (update-defdata-debug debug ds$)))
      ds$))
  
;;process enums and normalise listof/record/set etc
(defun compute-defdata (args debug-flag ctx wrld state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* (((mv defs0 kwd-options-lst)
         (get-defs-and-keyword-list args nil)))
    (acl2::with-local-stobj
     ds$
     (mv-let 
      (erp result state ds$)
      (b* ((ds$ (initialize-ds$ debug-flag wrld ds$))
           ((mv defs1 ds$) (translate-defs defs0 ctx ds$))
           (enum-event (process-enum-form defs1 ctx wrld)))
        (if enum-event
;submit enumeration event form
            (mv nil `(progn ,@enum-event) state ds$) 
          (let* ((cust-types (custom-types ds$))
                 (validate-type-consistency-ev 
                  (cons-up-type-consistent-thm-ev cust-types wrld))
                (mk-ev-form
                 `(make-event
                   (mv-let 
                    (erp res state)
                    (er-progn 
                     (value (and ',validate-type-consistency-ev
                                 (cw? t "~|Proving consistency of custom types ~x0...~%" ',cust-types)))
                     ,@validate-type-consistency-ev
                     (value ':Type-is-consistent))
                     (declare (ignorable res))
                     (if erp ;if error
                         (prog2$
                          (er hard ',ctx "~|One or more custom Types used in defdata form are not consistent, i.e. type predicate ~
                               and corresponding type enumerator are not consistent. Here's the list of events that failed: ~
                               ~x0 ~%" ',validate-type-consistency-ev)
                          (mv t nil state))
                                      
                       (compute-typecombs ',defs1 ',kwd-options-lst 
                                          ',(newconstructors ds$)
                                          ',(support-lemmas ds$)
                                          ',(custom-types ds$)
                                          ',(type-class ds$)
                                          ',ctx (w state) state))))))
            (mv nil mk-ev-form state ds$))))
      (mv erp result state)))))


#|
(define-enumeration-type boolean '(t nil))
(register-data-constructor (consp cons)
                           ((allp car) (allp cdr))
                           :proper t)

;(trace$ er-trans-datadef-as-enumerator
;        er-get-enumeration-info
;        er-trans-datadef-as-enumerator-lst
;        )


(compute-defdata '((foo (oneof 42 (cons boolean baz)))
                   (bar (oneof nil
                               (cons foo bar)))
                   (moo nil)
                   (baz (cons boolean moo)))
                 'top-level (w state) state)
|#

(defmacro defdata (&rest args)
  (declare (xargs :guard (and (true-listp args)
                              (>= (len args) 1)))) ;just (defdata) not allowed
   ":Doc-Section DATA-DEFINITIONS
  Specify a data definition ('type')~/
  
  The ~c[defdata] macro can be used to specify union and product
  combinations of 'types'(See :doc data-definitions for what we mean 
  by a 'type'). In addition to these it provides
  syntactic sugar to conveniently specify enumeration types,
  list types and record types. It also supports mutually-recursive
  data definitions.
  ~c[oneof] creates a union combination of constituent 'types'.
  ~c[enum] creates an enumeration type, it can take as arguments
  any number of acl2 constant expressions. Alternatively you can
  give it one argument which can be any acl2 expression that
  evaluates to a list of acl2 constants.
  You can use any of the built-in constructors like ~c[cons],
  ~c[/], ~c[complex], ~c[succ] etc, to create product type
  combinations. See examples below.
  ~c[record] is a syntactic sugar for the fore-mentioned 
  product type combination. It creates a new constructor with the
  same name as the type being defined and it 
  also creates the destructor/selector functions for you in
  addition to the predicate and enumerator as mentioned in :doc
  data-definitions. 
  ~c[(listof T)] is syntactic sugar for ~c[(oneof nil (cons T <typeId>))].
  ~c[enum], ~c[record] and ~c[listof] cannot be nested and are normally
  used seperately at the top-level. For complex nested type combinations
  just use the regular union, product combination as described above.
  Remember that each successful ~c[(defdata T ...)] will generate for you two
  functions ~c[Tp] and either ~c[nth-T] or ~c[*T-values*] depending on 
  wether ~c[T] is infinite or finite. As mentioned in :doc data-definitions
  all acl2 data objects are treated as singleton 'types' and can be used
  in any ~c[defdata] form. 
  
  ~bv[]
  Examples:
  (defdata (int integer))
  (defdata foo (cons (cons (oneof boolean 'ok) (cons 2 'as))
                     (oneof (cons int string) (oneof nat pos) 42)))
  (defdata natural (oneof 0 
                          (succ natural))
                          
  (defdata BorC (oneof boolean character))
  (defdata foo (oneof (cons integer foo)
                       integer)) 
  (defdata loi (listof integer))
  (defdata lop (listof (oneof (cons boolean nat) integer)))
  (defdata RGB (enum 'red 'green 'blue))
  (defdata RGBY (enum (list 'r 'g 'b 'y))
  (defdata hyperlink (record (protocol . string)
                             (address . string)
                             (display . string)))
  (defdata
    (bexpr (oneof boolean
                  (cons boolean bexpr-list)))
    (bexpr-list (oneof nil
                       (cons bexpr bexpr-list))))                           
  (defdata tree (oneof 'Leaf
                       (node (val . string) (left . tree) (right . tree))))  
  ~ev[]                      
  ~bv[]
  Usage(EBNF format):
  (defdata <typeId> <dataTypeExpression>)
  (defdata (<typeId> <dataTypeExpression>)+ ) ;mutually-recursive types
  where <typeId> := A new identifier/symbol thats not already defined in the world
        <dataTypeExpression> := <enumTypeExp> | <recordTypeExp> | <listTypeExp> | <constituentTypeExp>
        <constituentTypeExp> := <typeName> | <singletonTypeExp> | <typeCombinationExp>        
        <typeName> := name of 'type' as described in :doc data-definitions
        <singletonTypeExp> :=  acl2 constant expression as described in acl2 book
        <typeCombinationExp> := <unionTypeExp> | <productTypeExp>
        <unionTypeExp> := (oneof <constituentTypeExp> <constituentTypeExp>+)
        <productTypeExp> := (<constructorId> <constituentTypeExp>*) |
                            (<recordConstructorId> <destructorTypeDeclaration>*)
        
        <constructorId> := A defined constructor (see :doc register-data-constructor)                        
        <recordConstructorId> := A new identifier/symbol thats not already defined in the world
                                 or an already defined record constructor
        <destructorTypeDeclaration> := (<destructorId> . <typeName>)
        <destructorId> := A new identifier/symbol thats not already defined in the world
                          or a destructor fn corresponding to the record constructor
        <enumTypeExp> := (enum <singletonTypeExp>+ ) | (enum <acl2-enum-expr>)
        <acl2-enum-expr> := Any acl2 expression which evaluates to a list of acl2 constants.
        <listTypeExp> := (listof <constituentTypeExp>)
        <recordTypeExp> := (record destructorTypeDeclaration*)
  ~ev[]~/
  "
  
  `(with-output
    :stack :push
    :off :all
    (make-event
    `(with-output
      :stack :pop
      :off ,(cond ((get-acl2s-defdata-debug)
                    '(summary proof-checker))
                   ((get-acl2s-defdata-verbose)
                    '(summary warning! observation warning proof-checker expansion))
                   (t 
                    '(warning warning! observation prove 
                              proof-checker event expansion
                              summary proof-tree))
               
               )
      :gag-mode ,(if (get-acl2s-defdata-debug) 'nil 't)
      (make-event
        (compute-defdata ',',args  ,(get-acl2s-defdata-debug)
                         ','defdata (w state) state))))))


(defun make-subsumes-relation-name (T1 T2)
  (declare (xargs :guard (and (is-a-variablep T1)
                              (is-a-variablep T2))))
  (let* ((str1 (symbol-name T1))
        (str2 (symbol-name T2))
        (str11 (string-append str1 "-IS-SUBTYPE-OF-"))
        (str (string-append str11 str2)))
    (intern$ str "DEFDATA")))

(defun make-disjoint-relation-name (T1 T2)
  (declare (xargs :guard (and (is-a-variablep T1)
                              (is-a-variablep T2))))
  (let* ((str1 (symbol-name T1))
         (str2 (symbol-name T2))
         (str11 (string-append str1 "-IS-DISJOINT-WITH-"))
         (str (string-append str11 str2)))
    (intern$ str "DEFDATA")))

(defstub is-disjoint (* * *) => *)
(defstub is-subtype (* * *) => *)
(defstub is-alias (* * *) => *)
#||
(defun allp (x)
  (or (atom x)
      (consp x)))

(defthm allp-is-tau-predicate
  (booleanp (allp x))
  :rule-classes :tau-system)

;; (defthm allp-is-t
;;   (equal (allp x) t)
;;   :rule-classes (:rewrite))

;; (in-theory (disable allp))

(defun atomp (x) (atom x))

(defthm atomp-is-tau-predicate
  (booleanp (atomp x))
  :rule-classes :tau-system)

(DEFTHM ATOM-is-disjoint-with-CONS
  (IMPLIES (ATOM X) (NOT (CONSP X)))
  :rule-classes :tau-system)

(defthm atom-subtype-all
  (implies (atom x) (allp x))
  :rule-classes :tau-system)

(defthm cons-subtype-all
  (implies (consp x) (allp x))
  :rule-classes :tau-system)

BUT replacing atom with atomp in last 3 defthms fails.

Note that J specifically precludes predicates that are
constant-everywhere in tau-system.
||# 

(defun compute-defdata-relation (T1 T2 ctx wrld hints rule-classes otf-flg doc)
  (declare (xargs :mode :program
                  :guard (and (is-a-variablep T1)
                              (is-a-variablep T2)
                              (keyword-listp rule-classes)
                              )))
  (b* ((T1p (get-predicate-symbol T1))
       (T2p (get-predicate-symbol T2))
       ((unless (and (is-a-typeName T1 wrld)
                     (is-a-typeName T2 wrld)))
;if not existing typenames raise error
        (er hard ctx  "~|One of ~x0 and ~x1 is not a defined type!~%" T1 T2))
       
;; ((when (and rule-classes
;;                    (or (eq T1 'ACL2::ALL)
;;                        (eq T2 'ACL2::ALL))))
;; ;if not existing typenames raise error
;;         (er hard ctx  "~|Subtype/disjoint relation not allowed on predicate ALL with non-empty rule-classes~%"))
       (rule-classes (if (or (is-subtype 'ACL2::ALL T1 wrld)
                             (is-subtype 'ACL2::ALL T2 wrld))
                         '() 
; force not to be a tau-rule bcos tau complains
                          rule-classes))
       ((when (or (and (eq ctx 'defdata-disjoint)
                       (is-disjoint T1 T2 wrld))
                  (and (eq ctx 'defdata-subtype)
                       (is-subtype T1 T2 wrld))))
          '(value-triple :redundant))
       (form (if (eq ctx 'defdata-disjoint)
                 `(implies (,T1p x) (not (,T2p x)))
               `(implies (,T1p x) (,T2p x))))
       (nm (if (eq ctx 'defdata-disjoint)
               (make-disjoint-relation-name T1 T2)
             (make-subsumes-relation-name T1 T2)))

;27 june 13 - aborted a hack to enable non-rec preds
       ;; (types-info-table (table-alist 'types-info-table wrld))
       ;; (ti1 (cdr (assoc-eq T1 types-info-table)))
       ;; (?non-recursive1? (and (acl2::access types-info% ti1 :derivedp)
       ;;                       (not (acl2::access types-info% ti1 :recursivep))))
       ;; (ti1 (cdr (assoc-eq T1 types-info-table)))
       ;; (?non-recursive2? (and (acl2::access types-info% ti2 :derivedp)
       ;;                       (not (acl2::access types-info% ti2 :recursivep))))
       ;; (enable-names '())
       ;; (enable-names (if non-recursive1? (cons T1p enable-names) enable-names))
       ;; (enable-names (if non-recursive2? (cons T2p enable-names) enable-names))
       ;; (hints (append `((:in-theory (enable (,(if 

       (event-form `((defthm ,nm
                       ,form
                       :hints ,hints
                       :rule-classes ,rule-classes
                       :otf-flg ,otf-flg
                       :doc ,doc)))
       (ev-form-to-print `(defthm ,nm
                            ,form 
                            ,@(and hints
                                   `((:hints ,hints)))
                            ,@(and rule-classes
                                  `((:rule-classes ,rule-classes)))))

       (- (cw "~|Submitting ~x0~|" ev-form-to-print)))
           
      ;; `(make-event 
      ;;   (er-progn
      ;;    ,@ (and (null rule-classes)
      ;;            event-form)
      ;;       (let ((T1 ',T1)
      ;;             (T2 ',T2)
      ;;             (ctx ',ctx)
      ;;             (rule-classes ',rule-classes)
      ;;             (event-form ',event-form))
      ;;       (value
             `(progn
;macros call so dont need quotes
                ,@event-form
                ,(if (eq ctx 'defdata::defdata-disjoint)
                     `(add-edge-to-disjoint-graph-batch ,T1 ,T2)
                   `(add-edge-to-subtype-graph-batch ,T1 ,T2))
                (sync-globals-for-dtg)
                (value-triple :success))))

;; (defun compute-defdata-subtype (T1 T2 state rule-classes hints otf-flg doc)
;;   (declare (xargs :stobjs (state)
;;                   :mode :program
;;                   :guard (and (is-a-variablep T1)
;;                               (is-a-variablep T2)
;;                               (keyword-listp rule-classes)
;;                               )))
;;   (let* ((T1p (get-predicate-symbol T1))
;;          (T2p (get-predicate-symbol T2))
;;          (rule-classes (union-eq rule-classes '(:tau-system)))
;;          (name (make-subsumes-relation-name T1 T2)))
;;     (if (and (is-a-typeName T1 (w state))
;;              (is-a-typeName T2 (w state))) ;if not existing typenames raise error
;;       (let ((form `(implies (,T1p x) (,T2p x))))
;;         (mv-let (erp res state)
;;                 (acl2::thm-fn form state hints otf-flg doc)
;;                 (declare (ignore res))
;;                 (if erp
;;                   (er soft 'defdata-subtype "Failed to prove subtype relation: ~x0 ~%" form)
;;                   (value `(progn
;;                             (defthm ,name ,form
;;                                  :rule-classes ,rule-classes
;;                                  :hints ,hints 
;;                                  :otf-flg ,otf-flg :doc ,doc)
;;                             (add-edge-to-subtype-graph-batch ,T1 ,T2);macro calls so dont need quotes
;;                             (sync-globals-for-dtg)
;;                             (value-triple :defdata-subtype-success))))))
;;       (er soft 'defdata-subtype "One of ~x0 and ~x1 is not a defined type!~%" T1 T2))))


(defmacro defdata-subtype (T1 T2 
                              &key (rule-classes '(:tau-system)) 
                              hints otf-flg doc)
  (declare (xargs :guard (and (is-a-variablep T1)
                              (is-a-variablep T2))))
  ":Doc-Section DATA-DEFINITIONS
  Specify a subtype relation between two types~/
  ~c[(defdata-subtype T1 T2)] tries to prove that the first
  argument to it T1(which should be a ~st[supported type-name],
  to check what we mean by that ~pl[data-definitions]) is
  a subtype of the second argument T2. If the ACL2 is 
  successful in proving the following conjecture using defthm:
  ~c[(implies (T1p x) (T2p x))] then this information
  is stored in a internal subtype data type graph, where
  we perform closure of the subtype relation. Henceforth
  one can just call ~c[(subtype-p T1 T2)] to get an 
  affirmative which is just a lookup instead of calls
  to the ACL2 theorem prover. And note that once you submit
  ~c[(defdata-subtype boolean symbol)] and ~c[(defdata-subtype symbol atom)]
  successfully, you can call ~c[(subtype-p boolean atom)] and because we
  closed the subtype relation, we know that if T1 is a subtype
  of T2 and T2 is a subtype of T3, then T1 is also a subtype of
  T3 and we get back an affirmative answer, i.e ~c[t].
  If the rule-classes is not explicitly given, the
  default is to use (:tau-system).
  ~bv[]
   Examples:
   (defdata-subtype boolean symbol)
   (defdata-subtype pos nat)
   (defdata-subtype integer acl2-number)
  ~ev[]                      
  ~bv[]
   Usage:
    (defdata-subtype <Type-name1> <Type-name2> 
                     &key rule-classes hints otf-flag doc)
  ~ev[]~/
  "
  
  `(with-output
    :stack :push
    :off :all
    (make-event
     `(with-output
       :stack :pop
       :off ,(cond ((get-acl2s-defdata-debug)
                    'acl2::proof-checker)
                   ((get-acl2s-defdata-verbose)
                    '(warning! observation warning acl2::proof-checker event acl2::expansion))
                   (t 
                    '(warning warning! observation prove acl2::proof-checker event acl2::expansion
                             summary proof-tree))
               
               )
       :gag-mode ,(if (get-acl2s-defdata-debug) 'nil 't)
       (make-event
        (compute-defdata-relation ',',T1 ',',T2 'defdata::defdata-subtype (w state) 
                                 ',',hints ',',rule-classes ',',otf-flg ',',doc))))))
        ;(compute-defdata-subtype ',',T1 ',',T2 state ',',hints ',',otf-flg ',',doc))))))

  
;Note: Its good practice to use ctx,  otherwise u make copy-paste mistakes

 
 
(defmacro defdata-disjoint (T1 T2 
                               &key (rule-classes '(:tau-system))
                               hints otf-flg doc)
  (declare (xargs :guard (and (is-a-variablep T1)
                              (is-a-variablep T2)
                              (keyword-listp rule-classes))))
  ":Doc-Section DATA-DEFINITIONS
  Specify a disjoint relation between two types~/
  ~c[(defdata-disjoint T1 T2)] tries to prove that the first
  argument to it T1(which should be a ~st[supported type-name],
  to check what we mean by that ~pl[data-definitions]) is
  disjoint with the second argument T2. If the ACL2 is 
  successful in proving the conjecture using defthm:
  ~c[(implies (T1p x) (not (T2p x)))] then this information is
  stored in a internal disjoint data type graph, where
  we perform closure of the disjoint relation. Henceforth
  one can just call ~c[(disjoint-p T1 T2)] to get an 
  affirmative which is just a lookup instead of calls
  to the ACL2 theorem prover. And note that once you submit
  ~c[(defdata-disjoint acl2-number symbol)] successfully,
  you can call ~c[(disjoint-p nat boolean)] and because we
  closed the disjoint relation, we know that all subtypes
  of disjoint types are pairwise disjoint and we get back
  an affirmative , i.e ~c[t]. 
  If the rule-classes is not explicitly given, the
  default is to use (:tau-system).
  ~bv[]
  Examples:
  (defdata-disjoint cons atom)
  (defdata-disjoint character string)
  (defdata-disjoint integer complex :rule-classes nil)
  ~ev[]                      
  ~bv[]
  Usage:
  (defdata-disjoint <Type-name1> <Type-name2>
                    &key rule-classes hints otf-flag doc)
  ~ev[]~/
  "
  `(with-output
    :stack :push
    :off :all
    (make-event
     `(with-output
       :stack :pop
       :off ,(cond ((get-acl2s-defdata-debug)
                    'proof-checker)
                   ((get-acl2s-defdata-verbose)
                    '(warning! observation warning 
                               proof-checker event expansion))
                   (t 
                    '(warning warning! observation prove
                              proof-checker event expansion
                              summary proof-tree))
               
               )
       :gag-mode ,(if (get-acl2s-defdata-debug) 'nil 't)
       (make-event 
        (compute-defdata-relation ',',T1 ',',T2 'defdata::defdata-disjoint (w state) 
                                  ',',hints ',',rule-classes',',otf-flg ',',doc))))))#|ACL2s-ToDo-Line|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;---------------------Debugging Space below ------------------------------------------; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
;:set-ignore-ok t
(logic)

(trace$ list-calls-union-constituent-is-subtype-aux filter-typeName)
(defdata::cons-up-add-edge-union-constituent-is-subtype 
  '((UX (oneof (cons boolean nat)
              nat
              pos
              (cons nat nat)
              (oneof pos neg)))
    (RX (oneof UX (cons boolean RX) string)))
  '(UX RX) state)

(defun acl2::nth-integer (n)
  (declare (xargs :guard (natp n)))
  (let ((mag (floor n 2))
        (sign (rem n 2)))
    (if (= sign 0)
      mag
      (- -1 mag))))

(register-data-constructor (consp cons)
                           ((allp car) (allp cdr))
                           :proper t)


(define-enumeration-type boolean '(t nil))

(set-verify-guards-eagerness 0)

(trace$ er-trans-datadef-as-enumerator-lst)


(DEFDATA::COMPUTE-DEFDATA '(WOO (list (ONEOF BOOLEAN 'OK)
                                      (CONS 2 'AS)
                                      (ONEOF (CONS integer integer)
                                             (ONEOF integer integer)
                                             woo)
                                                ))
                          'DEFDATA
                          (W STATE)
                          STATE)                 
(ER-TRANS-DATADEF-AS-ENUM-new-LST '((LIST (ONEOF BOOLEAN 'OK)
                                              (CONS 2 'AS)
                                              (ONEOF (CONS INTEGER INTEGER)
                                                     (ONEOF INTEGER INTEGER)
                                                     WOO)))
                                       'NIL '(NTH-WOO)
                                       0 'DEFDATA (w state)
                                       state)




;given (/ (numerator denominator) rationalp) is constructor
;defs & theorems for this defdata:

(thm
 (implies (and (integerp i)
                (posp p))
          (and
           (rationalp (/ i p))
           (integerp (numerator (/ i p)))
           (posp   (denominator (/ i p))))))
           
(defun my-rationalp (x)
  (and (rationalp x)
       (integerp (numerator x))
       (posp (denominator x))))

(defun nth-my-rational (n)
  (let* ((pair (split-nat n))
         (a (nth-integer (car pair)))
         (b (nth-pos (cdr pair))))
    (/ a b)))


(defdata
     (coo integer  
             :hints (:in-theory (set-difference-theories (current-theory :here) '(assoc))
                     :use ((:instance assoc-of-append (x a) (y b) (z c))))
             :otf-flg t))

      

(defexec succ (x)
  (declare (xargs :guard (natp x)))
  (mbe :logic
       (if (natp x)
         (1+ x)
         1)
       :exec (1+ x)))

(defun pred (x)
  (declare (xargs :guard (natp x)))
  (if (zp x)
    0
    (1- x)))

(defthm succ-pred
  (implies (posp x)
           (equal (succ (pred x)) x)))

(register-data-constructor (posp succ)



(defdata
  (my-rational (/ integer pos)))


(defdata
  (tm (listof
       (cons all
             (listof tm-action))))
  (tm-action (list (field cursym all)
                   (field nextstate all)
                   (field newsym all)
                   (field direction boolean))))
|#
