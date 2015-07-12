; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "Is anyone using this?  If so please remove this error.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; defstructure-definitions.lisp
;; John D. Powell
(in-package "DEFSTRUCTURE")

;;
;; This file isolates defstructure definitions and types. The file currently 
;; contains the following ACL2 constructs as they occur in the defstructure book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(mutual-recursion

 (defun mlambda-fn-lst (args list)
   (cond
    ((atom list) ())
    (t (cons (mlambda-fn args (car list))
             (mlambda-fn-lst args (cdr list))))))

 (defun mlambda-fn (args form)
   (declare (xargs :guard (symbol-listp args)))
   (cond ((atom form) (cond ((member form args) form)
                            (t (list 'QUOTE form))))
         ((eq (car form) 'QUOTE) (list 'QUOTE form))
         (t (cons 'LIST
                  (cons (list 'QUOTE (car form))
                        (mlambda-fn-lst args (cdr form))))))))

;;;****************************************************************************
;;;
;;;    Utility Functions
;;;
;;;****************************************************************************

(defun acons$ (key datum value)
  (cons (cons key datum) value))

(defun ncars (n l)
  "The 1st n CARs of l."
  (cond
   ((= n 0) ())
   ((null l) ())
   (t (cons (car l) (ncars (- n 1) (cdr l))))))

(defun fold (args)
  "Folds a list into a somewhat balanced tree."
  (cond
   ((null args) nil)
   ((null (cdr args)) (car args))
   (t (cons (fold (ncars (truncate (length args) 2) args))
            (fold (nthcdr (truncate (length args) 2) args))))))

(defun flatten (args)
  "An `improper' list flattener.  NIL is always flattened away."
  (cond
   ((atom args) (cond
                 ((null args) nil)
                 (t (list args))))
   (t (append (flatten (car args))
              (flatten (cdr args))))))

(defun dotify (l)
  "Make the last CONS of l a `dotted pair' if possible."
  (cond
   ((atom l) l)
   ((atom (cdr l)) l)
   ((atom (cdr (cdr l))) (cond
                          ((null (cdr (cdr l))) (cons (car l) (cadr l)))
                          (t l)))
   (t (cons (car l) (dotify (cdr l))))))

(defun duplicates-equal (lst)
  (cond
   ((atom lst) nil)
   ((member-equal (car lst) (cdr lst))
    (add-to-set-equal (car lst)
                      (duplicates-equal (cdr lst))))
   (t (duplicates-equal (cdr lst)))))

(defun keywordify (string-designator)
  (intern-in-package-of-symbol (string string-designator) :keyword))

(defun keywordify-tree (tree)
  (cond
   ((atom tree)
    (cond
     ((not tree) nil)
     ((not (symbolp tree)) (bomb-from 'KEYWORDIFY-TREE "Bug. ~p0" tree))
     (t (keywordify tree))))
   (t (cons (keywordify-tree (car tree)) (keywordify-tree (cdr tree))))))

(defun x-or-car-x (x) (if (atom x) x (car x)))

(defun x-or-cadr-x (x)
  (declare (xargs :guard (or (atom x) (and (consp x) (consp (cdr x))))))
  (if (atom x) x (cadr x)))

(defun designated-string (string-designator)
  (cond
   ((null string-designator) "")
   (t (string string-designator))))

;;;  NB: Acl2 has the advantage of knowning that all terms have been
;;;  translated, which we can't do here do to lack of access to STATE.
;;;  So we define an `assertion' term, along with a free variable finder and a
;;;  substituter for assertion terms.

(defun lambda-function-p (x)
  (and (true-listp x)
       (equal (length x) 3)
       (equal (first x) 'ACL2::LAMBDA)
       (true-listp (second x))))

(mutual-recursion

 (defun assertion-termp (term)
   (cond
    ((atom term) t)
    ((eq (car term) 'QUOTE) t)
    (t (and (or (symbolp (car term))
                (lambda-function-p (car term)))
            (assertion-termp-list (cdr term))))))

 (defun assertion-termp-list (l)
   (cond
    ((atom l) (null l))
    (t (and (assertion-termp (car l))
            (assertion-termp-list (cdr l)))))))

(mutual-recursion

 (defun reason-for-not-assertion-termp (term)
   (cond
    ((atom term) nil)
    ((eq (car term) 'QUOTE) nil)
    (t (if (or (symbolp (car term))
               (lambda-function-p (car term)))
            (reason-for-not-assertion-termp-list (cdr term))
         (msg "the CAR of ~p0 is neither a symbol nor a LAMBDA function."
              term))))) 

 (defun reason-for-not-assertion-termp-list (l)
   (cond
    ((atom l) (or (null l)
                  (msg "it contains an `improper' list terminated by the atom ~
                        ~p0." l)))
    (t (or (reason-for-not-assertion-termp (car l))
           (reason-for-not-assertion-termp-list (cdr l)))))))

(mutual-recursion

 (defun free-vars1 (term ans)
   "A free variable is a symbol that is not a constant, i.e., it excludes T,
    NIL, and *CONST* etc."
   (cond
    ((atom term) (if (and (symbolp term)
                          (not (eq (legal-variable-or-constant-namep term)
                                   'CONSTANT)))
                     (add-to-set-eq term ans)
                   ans))
    ((eq (car term) 'QUOTE) ans)
    (t (free-vars1-lst (cdr term) ans))))

 (defun free-vars1-lst (terms ans)
   (cond
    ((atom terms) ans)
    (t (free-vars1-lst (cdr terms) (free-vars1 (car terms) ans))))))

(defun free-vars (term)
  (free-vars1 term '()))

(mutual-recursion

 (defun subst-expr (new old term)
   (cond
    ((equal term old) new)
    ((atom term) term)
    ((eq (car term) 'QUOTE) term)
    (t (cons (car term) (subst-expr-lst new old (cdr term))))))

 (defun subst-expr-lst (new old args)
   (cond
    ((null args) nil)
    (t (cons (subst-expr new old (car args))
             (subst-expr-lst new old (cdr args)))))))

(defun subst-expr-all (term new-list old-list)
  (cond
   ((atom old-list) term)
   (t (subst-expr-all
       (subst-expr (car new-list) (car old-list) term)
       (cdr new-list) (cdr old-list)))))


;;;****************************************************************************
;;;
;;;   Lemmas
;;;
;;;****************************************************************************

(logic)

(defthm open-mv-nth
  (implies
   (syntaxp (and (consp n) (eq (car n) 'QUOTE)))
   (equal (mv-nth n l)
          (if (zp n)
              (car l)
            (mv-nth (1- n) (cdr l)))))
  :hints
  (("Goal" :in-theory (e/d (mv-nth) (ACL2::MV-NTH-TO-VAL)))))

(in-theory (disable open-mv-nth))

(defun db-fn (key form db)
  (let
    ((pair (assoc key db)))
    (cond
     (pair (cdr pair))
     (t (bomb-from 'DB-FN "Key not present at runtime: ~p0." form)))))

(defun db-slot-fn (slot key form db)
  (let
    ((pair (assoc-equal (cons slot key) db)))
    (cond
     (pair (cdr pair))
     (t (bomb-from 'DB-SLOT-FN "Key not present at runtime: ~p0." form)))))

(defun make-corollary (assertion db)
  "Create the :COROLLARY rule for the assertion."
  (let*
    ((force (db :FORCE))
     (predicate-call (db :PREDICATE-CALL))
     (hyp (if force `(FORCE ,predicate-call) predicate-call)))
    `(IMPLIES ,hyp ,(access ASSERTION assertion :SUBST-ASSERTION))))

(defun make-template (db)
  
  "Using the :SLOT-NAMES, :REPRESENTATION, and :TAG, make a template for
   function generation.  If the structure is tagged, the tag is always added
   as the CAR.  We know that the :TAG is a symbol, and that the
   :REPRSENTATION is of the proper form."

  (db-let (representation slot-names tag)

    ;;  Preliminary template.

    (let ((template
           (case representation
             ((:MV :LIST) slot-names)
             (:DOTTED-LIST (dotify slot-names))
             (:TREE (fold slot-names))
             (t representation))))

      ;;  The final template.

      (if tag (cons tag template) template))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Macro, Function, and Lemma generators.
;;;
;;;    By convention all of these return a list of forms to be spliced into
;;;    the set of events.  They contain comment strings that will be removed
;;;    by the CAPSULE macro.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun guard-declaration (guard verifyp db)

  "If :GUARDS was specified, declare a guard and verify based on
  :VERIFY-GUARDS.  Note that the default is :DEFAULT."

  (db-let (guards verify-guards)

    (if guards
        (list
         `(DECLARE (XARGS :GUARD ,guard
                          ,@(cond
                             ((or (null verifyp) (null verify-guards))
                              '(:VERIFY-GUARDS NIL))
                             ((eq verify-guards t) '(:VERIFY-GUARDS T))))))
      nil)))


;;;  EXTENSIONALITY

#|

;; these functions were moved to symbol-fns

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(defun make-numbered-symbol (witness symbol number)
  (intern-in-package-of-symbol (concatenate 'acl2::string 
                                     (symbol-name symbol)
                                     (coerce (explode-nonnegative-integer number nil) 'acl2::string)) 
                        witness))

(defun number-symbol-list (witness list number)
  (if (consp list)
      (cons (make-numbered-symbol witness (car list) number)
            (number-symbol-list witness (cdr list) number))
    nil))

(defun enkey (symbol)
  (declare (type t symbol))
  (if (symbolp symbol)
      (intern-in-package-of-symbol (symbol-name symbol) :)
    :nil))

(defun enkey-field-names (list)
  (declare (type t list))
  (if (consp list)
      (cons (enkey (car list))
            (enkey-field-names (cdr list)))
    nil))

|#

(defun existential-fields (f f1 f2)
  (if (and (consp f)
           (consp f1)
           (consp f2))
      (cons `(cpath::tag-location ,(enkey (car f)) (equal ,(car f1) ,(car f2)))
            (existential-fields (cdr f) (cdr f1) (cdr f2)))
    nil))

(defun strong-existential-fields (fn f x y)
  (if (consp f)
      (cons `(cpath::tag-location ,(enkey (car f)) (equal (,@fn ,(car f) ,x) 
                                                   (,@fn ,(car f) ,y)))
            (strong-existential-fields fn (cdr f) x y))
    nil))

(defun enlist (list)
  (declare (type t list))
  (if (consp list)
      (cons (list (car list))
            (enlist (cdr list)))
    nil))

(defun extensionality (db)

  (db-let (name inline slot-names keyword-slot-names mix weak-predicate)
          
    (let ((paths  (psort (enlist keyword-slot-names)))
          (fields (field-readers slot-names db)))
      (let ((field1 (number-symbol-list name fields 1))
            (field2 (number-symbol-list name fields 2)))

        (cons

       "
;  The extensionality theorems decompose equality of two structures into
;; equality of their respective fields.
 "
         
        `(
          
          ;; How expensive is this rule??
          
          (defthm ,(join-symbols name name '-extensionality! (if mix '|| '-helper))
            (implies
             (and 
              (,weak-predicate x)
              (,weak-predicate y))
             (iff
              (equal x y)
              (equal (gp-list '(,@paths) x)
                     (gp-list '(,@paths) y)))))
          
          ,@(if mix nil
              `((defthm ,(join-symbols name name '-extensionality!)
                  (implies
                   (and 
                    (,weak-predicate x)
                    (,weak-predicate y))
                   (iff
                    (equal x y)
                    (and ,@(strong-existential-fields nil fields `x `y)))))
                ; :hints (("goal" :in-theory (disable cpath::sp==r))))
                
                (in-theory (disable ,(join-symbols name name '-extensionality! '-helper)))))
          
          ,@(if inline nil
              `(
                (defthm ,(join-symbols name name '-extensionality)
                  (iff
                   (equal (,name ,@field1)
                          (,name ,@field2))
                   (and
                    ,@(existential-fields fields field1 field2)
                    ))
                  :hints (("goal" :in-theory (disable ,weak-predicate ,name))))
                
                (in-theory (disable ,(join-symbols name name '-extensionality!)))
                ))

          )

         )))))

;;;  CONSTRUCTOR




(defun constructor-body (slot-names keyword-slot-names)
  (if (consp slot-names)
      `(sp (list ,(car keyword-slot-names)) ,(car slot-names) 
          ,(constructor-body (cdr slot-names) (cdr keyword-slot-names)))
    'nil))


(defun template-cost (template)
  (cond
   ((atom template) 0)
   (t (+ 1 (template-cost (car template)) (template-cost (cdr template))))))

(defun constructor (db)

  "If :REPRESENTATION is :MV, create an MV macro.  Else create a
   function or macro under control of the :INLINE option.  For tagged
   structures the tag is in the constructor-body as a free variable, so
   we need to bind it."

  (db-let (name acl2-count-lemma constructor-call slot-names representation
                tag doc template inline keyword-slot-names) 

    (cond
     ((eq representation :MV)
      (list
       "
;  The constructor is defined as a macro that expands into an MV form for
;  every slot.
 "
       `(DEFMACRO ,name ,slot-names ,@(if doc (list doc) nil)
          (CONS 'MV (LIST ,@slot-names)))))
      
     (inline
      (list
       "
;  The constructor is defined as a macro that accepts every slot.
 "
       `(DEFMACRO ,name ,slot-names ,@(if doc (list doc) nil)
          (MLAMBDA ,slot-names ,(constructor-body slot-names keyword-slot-names)))))
    
     (t (list
         "
;  The constructor is defined as a function that accepts every slot.
 "
         (if tag
             `(DEFUN ,name ,slot-names ,@(if doc (list doc) nil)
                ,@(guard-declaration T t db)
; perhaps the TAG argument doesn't make sense if we're using records?
                ,(constructor-body slot-names keyword-slot-names)) 
           `(DEFUN ,name ,slot-names ,@(if doc (list doc) nil)
              ,@(guard-declaration T t db)
              ,(constructor-body slot-names keyword-slot-names)))

         )))))

;;;  WEAK-PREDICATE

#| old:
(defun weak-predicate-body (template tree)
  "Traverse the template, creating CONSP and NULL expressions wherever
   needed.  It is necessary for the read/write lemmas that if the template
   contains a NULL entry, that entry must be NULL in every shell.  This
   is initialized with tree = <structure-name> which is the formal parameter
   of the weak predicate."
  (cond
   ((atom template) (cond ((null template) (list `(NULL ,tree)))))
   (t (append (list `(CONSP ,tree))
              (weak-predicate-body (car template) `(CAR ,tree))
              (weak-predicate-body (cdr template) `(CDR ,tree))))))
|#

(defun weak-predicate-body-aux (keyword-slot-names)
  (if (consp keyword-slot-names)
      `(cons (list ,(car keyword-slot-names))
             ,(weak-predicate-body-aux (cdr keyword-slot-names)))
    'nil))

;We changed the weak predicate when we made the conversion to use
;records.  This is kind of gross, but we made it exactly what we
;needed to prove the elim rule.

(defun weak-predicate-body (keyword-slot-names structure-name)
  `(and (wfr ,structure-name)
        (equal (cpath::clrp-list ,(weak-predicate-body-aux keyword-slot-names)
                                ,structure-name)
               nil)))
               
(defun reader-body (slot template tree)
  "Write a call to G to get slot from a structure."
  (declare (xargs :guard (symbolp slot)) (ignore template))
  `(gp (list ,(keywordify slot)) ,tree))

(defun weak-predicate (db)

  "This is the predicate on the `structure' of the structure. If the
   structure is named, then we include a test that the CAR of the structure
   is the correct name.  We also write a lemma that shows when the
   constructor function satisfies this predicate."

  (db-let (weak-predicate weak-predicate-constructor-lemma
                          constructor-call name template tag
                          inline
                          keyword-slot-names)
    
    ;;  Note that an untagged, 0-slot structure is defined to be NIL, and an
    ;;  untagged 1-slot structure is a single object.
    
    (let* ((wp-body (weak-predicate-body keyword-slot-names name))
           (body (cond
                  ((null template) (list `(NULL ,name)))
                  ((atom template) (list `(DECLARE (IGNORE ,name)) T))
                  (tag (list `(AND ,@wp-body (EQ (CAR ,name) ',tag))))
                  (t (list `(AND ,@wp-body))))))
      (list*
       "
;  This predicate defines the `structure' of the structure, and is used as a
;  weak guard on the readers and writers (if defined).
 "

       `(DEFUN ,weak-predicate (,name)
          ,@(guard-declaration T t db)
          
          ,wp-body ;(or t ,name) ;we only mention name to prevent an error about it being irrelevant but not declared so       
          )
       
       (if inline
           nil
         (list

          "
;  The weak-predicate is satisfied by any explicit reference of the
;  constructor.  We also store this information as a :BUILT-IN-CLAUSE
 "
          `(DEFTHM ,weak-predicate-constructor-lemma
             (EQUAL (,weak-predicate ,constructor-call)
                    T)
             :RULE-CLASSES
             ((:REWRITE)
              (:BUILT-IN-CLAUSE
               :COROLLARY
               (,weak-predicate ,constructor-call))))))))))

(defun predicate-body (db)
  "The predicate body is a conjunction of the weak predicate, and all
   assertions about the slots."

  (db-let (weak-predicate weak-predicate-call slot-names assertions)
    `(AND ,weak-predicate-call
          ,@(remove-duplicates-equal
             (append (slot-subst-assertions slot-names db)
                     (map-access-assertion-subst-assertion assertions)))
          T)))

(defun predicate-assertions-explicit (db)

  "The predicate, as the set of assertions for explicit instances of the
   constructor."
  
  (db-let (slot-names assertions weak-predicate constructor-call)
    (let ((assertions
           (remove-duplicates-equal
            (append (slot-assertions slot-names db)
                    (map-access-assertion-assertion assertions)))))

      ;;  Trying not to introduce redundant conjuncts.

      (cond
       (assertions `(AND ,@assertions T))
       (t 'T)))))

(defun predicate (db)
  (db-let (predicate name predicate-call weak-predicate weak-predicate-call
                     constructor-call predicate-weak-predicate-lemma
                     predicate-constructor-lemma inline)

    (list*
     "
;  This is the predicate, which contains the weak predicate and every
;  assertion made about the slots of the structure.  The final T guarantees
;  that all DEFSTRUCTURE predicates are Boolean.
 "
     `(DEFUN ,predicate (,name)
        ,@(guard-declaration T nil db)
        ,(predicate-body db))

         
     (if inline
         nil

       ;;  At times it is excessive to require that we prove the entire type
       ;;  predicate for a structure just to show that the weak predicate is
       ;;  satisfied, but this is the most generally useful rule to have
       ;;  around. 

       (list
        "
;  This lemma shows that the predicate includes the weak predicate, as
;  :REWRITE, :FORWARD-CHAINING, and :BUILT-IN-CLAUSE rules.  Note that the
;  :REWRITE rule is sometimes implicated in thrashing in conjunction with the
;  normalization lemmas.
 "
        `(DEFTHM ,predicate-weak-predicate-lemma
           (IMPLIES
            ,predicate-call
            ,weak-predicate-call)
           :RULE-CLASSES (:FORWARD-CHAINING :REWRITE :BUILT-IN-CLAUSE))
        
        "
;  This lemma rewrites the predicate on an explicit reference of
;  the constructor.
 "
        `(DEFTHM ,predicate-constructor-lemma
           (EQUAL (,predicate ,constructor-call)
                  ,(predicate-assertions-explicit db))))))))
    
(defun keyword-slot-checker (macro-name form args keyword-slot-names)
  "Check keyword argument list for basic syntax and either bomb or return
   NIL."
  (cond
   ((not (keyword-value-listp args))
    (bomb-from macro-name
               "The argument list in the macro invocation ~p0 ~
                does not match the syntax of a keyword argument ~
                list because ~@1."
               form (reason-for-non-keyword-value-listp args)))
   ((not (subsetp (evens args) keyword-slot-names))
    (bomb-from macro-name
               "The argument list in the macro invocation ~p0 is not ~
                 a valid keyword argument list because it contains the ~
                 ~#1~[keyword~/keywords~] ~&1, which ~#1~[is~/are~] ~
                 not the keyword ~#1~[form~/forms~] of any of the ~
                 slot names ~&2." 
               FORM (set-difference-equal (evens args) keyword-slot-names)
               keyword-slot-names))
   (t nil)))


(defun keyword-constructor-fn (form args name keyword-constructor default-alist
                                    keyword-slot-names required-slot-names)
  (cond
   ((keyword-slot-checker keyword-constructor form args keyword-slot-names))
   ((not (subsetp required-slot-names (evens args)))
    (bomb-from keyword-constructor
               "The argument list in the macro invocation ~p0 is not ~
                 valid does not specify a value for the required ~
                 ~#1~[keyword~/keywords~] ~&1. ~
                 Any slot which has no :DEFAULT option at ~
                 DEFSTRUCTURE time must be specified in every ~
                 invocation of the constructor macro." 
               form (set-difference-equal
                     required-slot-names (evens args))
               keyword-slot-names))
   (t `(,name ,@(keyword-constructor-body
                 args keyword-slot-names default-alist)))))

(defun keyword-constructor (db)
  (db-let
   (name keyword-constructor slot-names keyword-slot-names
         required-slot-names)

   (if keyword-constructor
       (list
        "
;  This is the keyword constructor macro.  It will expand into a call of the
;  constructor, with appropriate defaulting.
 "
        `(DEFMACRO ,keyword-constructor (&WHOLE FORM &REST ARGS)
           (KEYWORD-CONSTRUCTOR-FN
            FORM ARGS ',name ',keyword-constructor
            ',(default-alist slot-names db)
            ',keyword-slot-names ',required-slot-names)))
     nil)))
   
(defun readers (db)
  "Define the reader functions"
  (db-let (slot-names acl2-count-lemma)
    (if slot-names
        (append 
         (cons
         "
;  These are the `readers' for the structure.
 "
         (reader-definitions slot-names db))

         (and acl2-count-lemma
             (list
              "
;  This lemma justifies recursion on any slot of the structure.  It is
;  unlikely to be used unless the structure is itself recursive.
  "
          
;This is a different lemma that what we had before the conversion to
;records.  Now it mentions the readers, so it was moved to after the
;readers are defined.
          
          `(DEFTHM ,acl2-count-lemma
             
             (AND ,@(acl2-count-lemma-claims slot-names db))
             :rule-classes (:rewrite :linear))

          
          #|
          `(DEFTHM ,acl2-count-lemma
          (EQUAL (ACL2-COUNT ,constructor-call)
          (+ ,(template-cost template)
          ,@(acl2-countify-slots slot-names))))
          |#
          )))
      nil)))
    

(defun writer-body (slot template var tree)
  "Write a CONS form to put a new slot into a structure, given the slot,
   the structure template, a variable name (a formal parameter) and the
   `tree'."
  (declare (xargs :guard (symbolp slot)))
  (cond
   ((atom template) (cond ((eq slot template) var)))
   (t (let
        ((car-side (writer-body slot (car template) var `(CAR ,tree)))
         (cdr-side (writer-body slot (cdr template) var `(CDR ,tree))))
        (cond
         (car-side `(CONS ,car-side ,(cond
                                      ((null (cdr template)) nil)
                                      (t `(CDR ,tree)))))
         (cdr-side `(CONS (CAR ,tree) ,cdr-side)))))))

(defun writer-macro-fn (bind slot template value name)
  (if bind
      `(LET ((,*binding-variable*
              (CHECK-VARS-NOT-FREE (,*binding-variable*) ,name)))
         ,(writer-body slot template value *binding-variable*))
    (writer-body slot template value name)))

(defun writers (db)
  "Define the writer functions."
  (db-let (slot-names keyword-slot-names read-only)
    (if read-only
        nil
      (cons
       "
;  These are the `writers' for the structure.
 "
       (writer-definitions slot-names keyword-slot-names db)))))

(defun slot-cost (slot template accum)
  "Compute the cost of reading (CAR/CDR) and writing (CONS) a slot."
  (cond
   ((atom template) (cond
                     ((eq slot template) accum)
                     (t nil)))
   (t (or (slot-cost slot (car template) (1+ accum))
          (slot-cost slot (cdr template) (1+ accum))))))

(defun set-cost (slots template)
  (cond
   ((atom slots) 0)
   (t (+ (slot-cost (car slots) template 0)
         (set-cost (cdr slots) template)))))

(defun set-heuristic (keyword-set-slots template)
  (let*
    ((keyword-template (keywordify-tree template))
     (set-cost (set-cost keyword-set-slots keyword-template)))
    (<= set-cost (template-cost keyword-template))))

(defun set-update (args keyword-writer-map struct)
  (cond
   ((atom args) struct)
   (t `(,(cdr (assoc (car args) keyword-writer-map)) ;Writer
        ,(cadr args)                        ;Value
        ,(set-update (cddr args) keyword-writer-map struct)))))

(defun copy-update (name keyword-slot-names args keyword-reader-map struct)
  "If all slots are assigned (equivalent to a constructor call), or the
   updated thing is an atom (variable symbol), then we can simply do the
   copy. Otherwise, bind the struct to a temp and then do the copy."
  (if (or (atom struct)
          (all-slots-assigned-p keyword-slot-names args))
      `(,name ,@(copy-update-fn keyword-slot-names args
                                keyword-reader-map
                                struct nil))
    `(LET ((,*binding-variable* ,struct))
       (,name ,@(copy-update-fn keyword-slot-names args
                                keyword-reader-map
                                *binding-variable* t)))))

(defun inline-update-fn (args template tree check)
  "Write a CONS form to update slots from args, given the structure template
   and tree."
  (cond
   ((atom template) (cond
                     ((null template) (mv nil nil))
                     (t (let* ((keyword-slot (keywordify template))
                               (found (assoc-keyword keyword-slot args))
                               (val (cadr found)))
                          (cond
                           (found
                            (mv t (cond
                                   (check `(CHECK-VARS-NOT-FREE
                                            (,*binding-variable*)
                                            ,val))
                                   (t val))))
                           (t (mv nil tree)))))))
   (t (mv-let (car-found car-result)
        (inline-update-fn args (car template) `(CAR ,tree) check)
        (mv-let (cdr-found cdr-result)
          (inline-update-fn args (cdr template) `(CDR ,tree) check)
          (cond
           ((not (or car-found cdr-found)) (mv nil tree))
           (t (mv
               t
               `(CONS
                 ,(cond
                   (car-found car-result)
                   (t `(CAR ,tree)))
                 ,(cond
                   (cdr-found cdr-result)
                   ((null (cdr template)) nil)
                   (t `(CDR ,tree))))))))))))

(defun inline-update (args template struct keyword-slot-names)
  (let ((bind (and (not (atom struct))
                   (not (all-slots-assigned-p keyword-slot-names args)))))
    (mv-let (found form)
      (inline-update-fn
       args template (if bind *binding-variable* struct) bind)
      (cond
       (bind `(LET ((,*binding-variable* ,struct)) ,form))
       (t form)))))

(defun keyword-updater-fn (form struct args name keyword-updater
                                keyword-slot-names read-only-keyword-slots
                                update-method template keyword-reader-map
                                keyword-writer-map)
  (cond
   ((keyword-slot-checker keyword-updater form args keyword-slot-names))
   ((intersection-eq (evens args) read-only-keyword-slots)
    (bomb-from keyword-updater
               "The argument list in the macro invocation ~p0 is not ~
                valid because it specifies ~#1~[a~/an~] update for the ~
                ~#1~[slot~/slots~] ~&1 which ~#1~[is a~/are~] ~
                :READ-ONLY ~#1~[slot~/slots~]."
               form (intersection-eq (evens args) read-only-keyword-slots)))
   (t

    ;;  Determine the kind of update we're going to do. The :HEURISTIC method
    ;;  always chooses either :SET or :COPY.

    (let*
      ((keyword-set-slots (evens args))
       (method (if (eq update-method :HEURISTIC)
                   (if (set-heuristic keyword-set-slots template)
                       :SET
                     :COPY)
                 update-method)))

      (case method
        (:SET (set-update args keyword-writer-map struct))
        (:COPY (copy-update name keyword-slot-names args
                            keyword-reader-map struct))
        (:INLINE (inline-update args template struct keyword-slot-names))
        (t (bomb-from 'KEYWORD-UPDATER-FN "Illegal method: ~p0."
                      method)))))))

(defun keyword-updater (db)
  (db-let (keyword-updater name keyword-slot-names slot-names
                     update-method template)
    (if keyword-updater
        (list
       "
;  This is the macro that provides for updates of multiple slots of a
;  structure. 
 "
       `(DEFMACRO ,keyword-updater (&WHOLE FORM STRUCT &REST ARGS)
          (KEYWORD-UPDATER-FN
           FORM STRUCT ARGS ',name ',keyword-updater
           ',keyword-slot-names ',(read-only-keyword-slots slot-names db)
           ',update-method ',template ',(keyword-reader-map slot-names db)
           ',(keyword-writer-map slot-names db))))
      nil)))
                            
(defun read-lemma (db)
  (db-let (slot-names read-lemma)
    (if read-lemma
        (list
         "
;  This lemma simplifies reads of an explicit constructor.
 "
         `(DEFTHM ,read-lemma
            (AND ,@(read-lemma-body slot-names db))))
      nil)))

(defun write-lemma (db)
  (db-let (slot-names write-lemma)
    (if write-lemma
        (list
       "
;  This lemma simplifies writes of an explicit constructor.
 "
       `(DEFTHM ,write-lemma
          (AND ,@(write-lemma-body slot-names db))))
      nil)))

;;;  LIFT-IF-LEMMA

#|

The reasons for lifting IF out are as described below, but we always do it
rather than check for the SYNTAXP hyp.  This was important for Alessandro's
work.  Also added IF lifting for the slot writers, in the hope of winning
some simplifications in that way as well ( we do on his examples ).


(defun lift-if-syntaxp (left right constructor)
  ":doc-section lift-if-syntaxp
  Meta heuristic for `lifting' IF through structure accessors.
  ~/~/

The `LIFT-IF' lemma is introduced as a heuristic to speed certain proofs
about specifications involving conditional structure access.  Here is the
idea.  Imagine a generic structure defined by

 (DEFSTRUCTURE FOO A B C).

Now imaging that the term

 (FOO-A (IF test x y))

appears during a proof about a specification involving the structure.  
This will happen because ACL2 does not normally move IF around during
simplification.  Instead, ACL2 simplifies, with IF in place, and then
clausifies out the IFs to produce cases.

Now, if the term above is actually

 (FOO-A (IF test (FOO a b c) (FOO a1 b1 c1))),

i.e., both the left and right branch of the IF are instances of the
constructor, then we can simplify this term to 

 (IF test a a1).

Even though we haven't eliminated the need to clausify away the IF, we have
at least reduced the size of the term, perhaps substantially.  This is
important because if we had clausified away to cases involving

 (FOO-A (FOO a b c)) and (FOO-A (FOO a1 b1 c1))

the prover is obligated to examine all of (FOO a b c) and (FOO a1 b1 c1)
before applying the simple `read lemma' for the structure.  The sizes of
terms can also have a very significant impact on the amount of time spent on
I/O.

If it so happened that a = a1, e.g., this slot is invariant in a
specification, then this would be further simplified to simply

a,

which will potentially result in one less test during clausification.

The heuristic embodied in this lemma is to lift IF through calls of the
accessors if there is some hope that doing so will reduce the size of the
resulting term.  If the left and right hand sides of the IF are both
instances of the constructor, then we know that this will work, thanks to the
`read lemma' for the structure.  We also lift the IFs out if the left or
right hand sides are themselves IF, hoping to win further down.  This
heuristic has been found to result in very significant proof speedups for
certain types of proofs. ~/"

  (declare (xargs :guard t
                  :mode :logic))

  (and (consp left)
       (consp right)
       (symbolp constructor)
       (or (eq (car left) 'IF)
           (eq (car left) constructor))
       (or (eq (car right) 'IF)
           (eq (car right) constructor))))
|#

(defun lift-if-lemma-fn (slots test left right db)
  (append (lift-if-readers slots test left right db)
          (lift-if-writers slots test left right db)))

(defun lift-if-lemma (db)
  (db-let (name lift-if-lemma representation slot-names)
    (let ((test (pack-intern name name "-TEST")) ;Makes forms easer to read
          (left (pack-intern name name "-LEFT")) ;w/o package marks. 
          (right (pack-intern name name "-RIGHT")))
      (if lift-if-lemma
          (list
           "
;  This lemma lifts IF through calls of the slot accessors.
 "
           `(DEFTHM ,lift-if-lemma
              (AND ,@(lift-if-lemma-fn slot-names test left right db))))
        nil))))

;;;  ELIMINATION-LEMMA

(defun elimination-lemma (db)
  (db-let (elimination-lemma slot-names name force
                             weak-predicate-call) 
    (if (and elimination-lemma)
        (list
         "
;  This is the :ELIM lemma for the constructor.
 "
         `(DEFTHM ,elimination-lemma
            (IMPLIES
             ,(if force
                  `(FORCE ,weak-predicate-call)
                weak-predicate-call)
            (EQUAL (,name ,@(map-slots-db slot-names :READER-CALL db))
                   ,name))
            :RULE-CLASSES (:REWRITE :ELIM)))
      nil)))

#|(defun normalization-lemma (db)
  (db-let (name constructor-call normalization-lemma slot-names force
                weak-predicate-call)  

    ;;  Note: In the first conjunct below (the equality conjunct), if both the
    ;;  LHS and RHS are explicit references of the constructor, then we can
    ;;  rewrite w/o hypotheses.  Rather than introducing 2 lemmas, however, we
    ;;  simply introduce the most general one, assuming that one will be able
    ;;  to relieve the weak predicate hypothesis.

    (if normalization-lemma
        (list
         "
;  This lemma normalizes symbolic writes by transforming the symbolic
;  structure into an explicit reference of the constructor.  The first
;  conjunct is a lemma that will normalize equality tests for this structure
;  when one of the objects is an explicit reference of the constructor.
 "
         `(DEFTHM ,normalization-lemma

            (IMPLIES
             ,(if force
                  `(FORCE ,weak-predicate-call)
                weak-predicate-call)
             (AND
              (EQUAL (EQUAL ,constructor-call ,name)
                     (AND ,@(normalize-equal-conjuncts slot-names db)))
              ,@(normalization-conjuncts slot-names slot-names db)))))
      nil)))
      
|#

(defun all-bound-slots (slot-names db)
  (append (map-access-assertion-bound-slots (db :ASSERTIONS))
          (all-bound-slots-fn slot-names db)))

(defun simple-slot-p (slot db)
  (db-let ((slot assertions) slot-names)
    (and (equal (remove-duplicates-equal
                 (map-access-assertion-bound-slots assertions))
                (list (list slot)))
         (not
          (member slot
                  (flatten (all-bound-slots (remove slot slot-names) db)))))))

(defun slot-writers-lemmas (db)
  (db-let (weak-predicate-slot-writers-lemma
           weak-predicate-call weak-predicate
           predicate-slot-writers-lemma predicate
           slot-names)
                                             
    (append
     (if weak-predicate-slot-writers-lemma
         (list
          "
;  This lemma backchains the weak predicate through the slot writers.
  "
          `(DEFTHM ,weak-predicate-slot-writers-lemma
             (IMPLIES
              ,weak-predicate-call
              (AND ,@(weak-predicate-slot-writers-lemma-fn
                      weak-predicate (map-if-slots-db slot-names :WRITER-CALL
                                                   db)))))) 
       nil)
     (if predicate-slot-writers-lemma
         (list
              "
;  This lemma proves the predicate on a slot writer call.  For simple slots
;  whose assertions (if any) only mention the slot itself one need only prove
;  the assertion about the new slot.  For more complex slot assertions, or if
;  the structure as a whole has an assertion, it is necessary to normalize
;  the slot writer call to an explicit instance of the constructor.
  "
              `(DEFTHM ,predicate-slot-writers-lemma
                 (AND ,@(predicate-slot-writers-lemma-fn
                         predicate slot-names slot-names db))))
       nil))))

(defun read-write-lemma (db)
  (db-let (read-write-lemma slot-names force weak-predicate-call)
    (if read-write-lemma
        (list
         "
;  This lemma normalizes symbolic reads of symbolic writes by `pushing'
;  reads though nested writes until either 1) a symbolic write of the read
;  slot is detected, or 2) something unrecognized is found.
 "
         `(DEFTHM ,read-write-lemma
            (AND ,@(read-write-conjuncts slot-names slot-names db))))
      nil)))

(defun write-write-lemma (db)
  (db-let (write-write-lemma template tag)
    (if write-write-lemma
        (let ((template (reverse (flatten (if tag (cdr template) template)))))
          (list
           "
;  This lemma normalizes multiple nested writes of a structure by pushing
;  writes for `deep' slots through writes to `shallow' slots, and reducing
;  redundant writes to the same slot to a single write. 
  "
           `(DEFTHM ,write-write-lemma
              (AND ,@(write-write-conjuncts  template db)))))
      nil)))

(defun all-rule-classes (db)
  (db-let (assertions slot-names)
    (append (map-slot-assertions-for-rule-classes slot-names db)
            (map-assertions-for-rule-classes assertions))))

(defun naked-proofs (db)
  (db-let (assertion-lemma predicate predicate-call 
                           predicate-guard-hints
                           assertion-lemma-hints guards verify-guards)
    (if (or assertion-lemma (and guards verify-guards))
        (append
         (list `(LOCAL (IN-THEORY (ENABLE ,predicate))))
         (and guards verify-guards
              (list
               "
;  The guard verification for the predicate is performed here since it may
;  need the current environment.  If it does not prove then you may need some
;  hints.  Any :PREDICATE-GUARD-HINTS option to DEFSTRUCTURE will be attached
;  to this lemma.
 "
               `(VERIFY-GUARDS ,predicate
                               ,@(and predicate-guard-hints
                                      (list :HINTS predicate-guard-hints)))))
         (and assertion-lemma
              (list
               "
;  This lemma captures all assertions about the structure.  This lemma is not
;  guaranteed to prove.  If it does not prove than you may have to provide
;  some :HINTS.  Any :ASSERTION-LEMMA-HINTS option to DEFSTRUCTURE will be
;  attached to this lemma.  Be sure that you have not specified
;  unsatisfiable assertions. 
 "

               `(DEFTHM ,assertion-lemma
                  (IMPLIES
                   ,predicate-call
                   ,(predicate-body db))
                  :RULE-CLASSES
                  ,(all-rule-classes db)
                  ,@(and assertion-lemma-hints
                         (list :HINTS assertion-lemma-hints))))))
      nil)))
            
;;;  MV-INTRO-MACRO

(defun mv-intro-macro-case-body (readers form n)
  (cond
   ((atom readers) ())
   (t (cons `(,n (,(car readers) ,form))
            (mv-intro-macro-case-body (cdr readers) form (1+ n))))))

(defun mv-intro-macro-fn (name form event-name readers)
  (let*
    ((event-name (if event-name
                     event-name
                   (pack-intern (car form) name "-MV-INTRO-" (car form))))
     (n (car (unique-symbols 1 'MV-INTRO-MACRO-N (flatten form))))
     (mv-nth-form `(MV-NTH ,n ,form)))
     
    `(DEFTHM ,event-name
       (EQUAL ,mv-nth-form
              (CASE ,n
                ,@(MV-intro-macro-case-body readers form 0)
                (T (HIDE ,mv-nth-form))))
       :HINTS
       (("Goal"
         :IN-THEORY '(ZP OPEN-MV-NTH ,@readers)
         :EXPAND (HIDE ,mv-nth-form))))))
         
(defun mv-intro-macro (db)
  (db-let (name slot-names mv-intro-macro)
    (if mv-intro-macro
      (list
       "
;  This macro generates a lemma that will rewrite MV-NTH applied to any form
;  as a call of the appropriate reader for this MV structure.
"
       `(DEFMACRO ,mv-intro-macro (FORM &KEY EVENT-NAME)
          (DECLARE (XARGS :GUARD (AND FORM
                                      (SYMBOL-LISTP FORM)
                                      (SYMBOLP EVENT-NAME))))
          (MV-INTRO-MACRO-FN ',name FORM EVENT-NAME
                          ',(map-slots-db slot-names :READER db))))
      nil)))

#|
(defun r/w-type-prescriptions (db)
  (db-let (slot-names)
    (r/w-type-prescriptions-fn
     (append (map-if-slots-db slot-names :READER db)
             (map-if-slots-db slot-names :WRITER db)))))
|#

(defun definition-theory (db)
  (db-let (name weak-predicate predicate definition-theory slot-names
                representation mix inline) 
    (if inline
        nil
      (list
       "
;  This theory consists of all :DEFINITION runes associated with the
;  constructor, predicates, and slot readers/writers.  Only the
;  :TYPE-PRESCRIPTIONS and :EXECUTABLE-COUNTERPARTS remain ENABLEd.
 "
       `(DEFTHEORY ,definition-theory
          '(

            ;;  Note that for :MV structures the constructor is a macro.

            ,@(if (eq representation :MV)
                  nil
                (list name))
            ,weak-predicate
            ,predicate
            ,@(and (not mix) (map-if-slots-db slot-names :READER db))
            ,@(and (not mix) (map-if-slots-db slot-names :WRITER db))))
       `(IN-THEORY (DISABLE ,definition-theory))))))

(defun lemma-theory (db)
  (db-let (lemma-theory inline)
    (if inline
        nil
      (list
       "
;  This theory lists every lemma generated by this DEFSTRUCTURE.  These are
;  normally to remain ENABLEd.
 "
       `(DEFTHEORY ,lemma-theory
          '(,@(lemma-theory-names *lemma-names* db)))))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Assertion and Rule Checking
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun check-assertion (assertion slot context db)
  "Check the assertion for syntax, and return an ASSERTION record containing
   the assertion, its bound slots, its substitution, and its associated slot."
  (db-let (slot-names)
    (cond

     ;;  If not a LAMBDA, make sure that it is at least a `vanilla' term.

     ((not (assertion-termp assertion))
      (bomb "Assertions are required to satisfy STRUCTURES::ASSERTION-TERMP, ~
             and ~p0 does not because ~@1."
            assertion (reason-for-not-assertion-termp assertion)))

     ;;  This is an assertion term whose free variables are (hopefully!)
     ;;  indicated by FREE-VARS.

     (t (let*
          ((bound-slots (free-vars assertion))
           (err
            (cond
             ((not (subsetp bound-slots slot-names))
              (msg "is not a subset of the slot names ~p0." slot-names))
             ((and slot (not (member slot bound-slots)))
              (msg "does not contain the current slot ~p0." slot)))))
          (if err
              (bomb "The putative assertion ~p0 in the context ~p1 is not ~
                   a valid assertion because the free variable list of the ~
                   assertion (as defined by STRUCTURES::FREE-VARS), ~p2, ~
                   ~@3  If you feel that this message is incorrect, ~
                   then restate your assertion as a LAMBDA function ~
                   and try again." assertion context bound-slots err)

            ;;  Here, the `subst-assertion' is made by substitution of the
            ;;  access forms for the free variables.
          
            (make ASSERTION
                  :assertion assertion
                  :bound-slots bound-slots
                  :subst-assertion
                  (subst-expr-all assertion
                                  (map-slots-db bound-slots :READER-CALL db)
                                  bound-slots)
                  :slot slot
                  :rules NIL)))))))
                

(defun parse-rule (rule default-assertion context slot db)
  "Check rule syntax and return a RULE record."

  (let ((rule-token (if (atom rule) rule (car rule))))
    
    (if (or (not (symbolp rule-token))
            (not (member rule-token *rule-tokens*)))
        
        (bomb "The putative rule descriptor ~p0 in the context ~
               ~p1 is not valid because ~#2~[it~/its CAR~] ~
               is not one of the allowable rule tokens ~v3."
              rule context (if (equal rule rule-token) 0 1) *rule-tokens*)
      
      (cond

       ;;  A symbolic rule inherits everything from the default-assertion.
    
       ((or (atom rule) (null (cdr rule)))
        (make RULE
              :assertion default-assertion
              :rule-class
              `(,rule-token
                :COROLLARY
                ,(make-corollary default-assertion db))))

       ((not (true-listp rule))
        (bomb "The putative atomic rule descriptor ~p0 in the context ~
           ~p1 is not valid because it is not a true list."
              rule context))

       ;;  This is (rule-token assertion . other-rule-stuff).  We parse the
       ;;  assertion and append the other-rule-stuff to make the rule-class.

       (t (let
            ((assertion (check-assertion (second rule) slot rule db)))

            (make RULE
                  :assertion assertion
                  :rule-class
                  (append
                   `(,rule-token
                     :COROLLARY ,(make-corollary assertion db))
                   (rest (rest rule))))))))))

(defun get-string-designator (key options default)
  (designated-string
   (get-option-argument 'DEFSTRUCTURE key options :STRING-DESIGNATOR
                        default default)))

(defun get-symbol (key options default)
  (get-option-argument 'DEFSTRUCTURE key options :SYMBOL default default))

(defun get-representation (options slot-names)
  "The :REPRESENTATION has a special syntax."
  (let ((opt (get-option-entry :REPRESENTATION options))
        (default :LIST))
    (cond
     (opt (cond
           ((consp opt)
            (cond
             ((null (cdr opt)) default)
             (t (if (and (true-listp opt)
                         (null (cddr opt))
                         (or (member (cadr opt) *keyword-representations*)
                             (let ((l (flatten (cadr opt))))
                               (and (subsetp l slot-names)
                                    (subsetp slot-names l)
                                    (equal (length l)
                                           (length slot-names))))))
                    (cadr opt)
                  (bomb "The :REPRESENTATION option descriptor must be either ~
                         :REPRESENTATION, (:REPRESENTATION), ~
                         or (:REPRESENTATION representation), where ~
                         representation is either one of ~v0, or a CONS ~
                         tree which when flattened according to ~
                         STRUCTURES::FLATTEN yields a permutation of the ~
                         slot names ~p1, but ~p2 is not."
                        *keyword-representations* slot-names opt)))))
           (t default)))
     (t default))))

(defun parse-defstructure (name doc-and-slots)
  "Parse the DEFSTRUCTURE arguments, returning the DB"

  (let*
    ((name
      (if (and name (symbolp name))
          name
        (bomb "The <name> argument of DEFSTRUCTURE must be a ~
               non-NIL symbol, but ~p0 is not." name)))

     ;; Since doc-and-slots is an &REST arg, we know it's TRUE-LISTP.

     (doc (if (stringp (car doc-and-slots)) (car doc-and-slots) nil))
     (slots-and-options (if doc (cdr doc-and-slots) doc-and-slots))
     (last-car (car (last slots-and-options)))
     (options? (and (consp last-car) (eq (car last-car) :OPTIONS)))
     (options (if options? (cdr last-car) nil))
     (slots (if options? (butlast slots-and-options 1) slots-and-options))
     
     (option-err
      (get-option-check-syntax 'DEFSTRUCTURE options *options*
                               *duplicate-options* nil))

     (slot-names (map-x-or-car-x slots))

     (check-slot-names
      (or (null slot-names)
          (let
            ((err
              (cond
               ((not (arglistp slot-names))
                (msg "must be a valid argument list as defined by ~
                      ACL2::ARGLISTP, but ~p0 is not." slot-names))
               ((member name slot-names)
                (msg "may not contain the structure name, ~p0, but ~
                      ~p1 does." name slot-names))
               ((duplicates-equal (map-string slot-names))
                (msg "~p0 apparently contains symbols in different packages ~
                      that have the same print name, which is illegal."
                     slot-names)))))
            (if err
                (bomb "The implied list of slot names ~@0" err)
              T)))))

    ;;  Build and return the DB.  First, the user options.

    (extend-db
     ()                                        ;Initialize
     (acons-db
      (:NAME name)
      (:DOC doc)
      (:SLOT-NAMES slot-names)
      (:GUARDS (get-option-as-flag 'DEFSTRUCTURE :GUARDS options))
      (:VERIFY-GUARDS
       (get-option-member 'DEFSTRUCTURE :VERIFY-GUARDS options
                          '(T NIL) :DEFAULT :DEFAULT))
      (:INLINE (get-option-as-flag 'DEFSTRUCTURE :INLINE options))
      (:MIX    (get-option-as-flag 'DEFSTRUCTURE :MIX options))
      (:CONC-NAME
       (get-string-designator
        :CONC-NAME options (concatenate 'STRING (string name) "-")))
      (:SET-CONC-NAME
       (get-string-designator
        :SET-CONC-NAME options (concatenate 'STRING "SET-" (string name) "-")))
      (:KEYWORD-CONSTRUCTOR
       (get-symbol
        :KEYWORD-CONSTRUCTOR options (pack-intern name "MAKE-" name)))
      (:KEYWORD-UPDATER
       (get-symbol :KEYWORD-UPDATER options (pack-intern name "UPDATE-" name)))
      (:PREDICATE
       (get-symbol :PREDICATE options (pack-intern name name "-P")))
      (:WEAK-PREDICATE
       (get-symbol :WEAK-PREDICATE options
                   (pack-intern name "WEAK-" name "-P")))
      (:FORCE
       (get-option-as-flag 'DEFSTRUCTURE :FORCE options))
      (:REPRESENTATION (get-representation options slot-names))
      ;;  Note: The original default was to always generate :SLOT-WRITERS,
      ;;  but this was changed, so the code is all written in terms of a
      ;;  :READ-ONLY flag.
      (:READ-ONLY
       (let ((slot-writers
              (get-option-as-flag 'DEFSTRUCTURE :SLOT-WRITERS options)))
         (cond
          ((and slot-writers (eq (db :REPRESENTATION) :MV))
           (bomb ":MV structures can't have :SLOT-WRITERS."))
          (t (not slot-writers)))))
      (:MV-INTRO-MACRO 
       (if (eq (db :REPRESENTATION) :MV)
           (get-symbol :MV-INTRO-MACRO options
                       (pack-intern name name "-INTRO"))
         (let ((entry (get-option-entry :MV-INTRO-MACRO options)))
           (if (and entry (or (atom entry) (atom (cdr entry)) (cadr entry)))
             (bomb "The :MV-INTRO-MACRO option is illegal unless the ~
                    (:REPRESENTATION :MV) option is chosen.")
             NIL))))
      (:UPDATE-METHOD
       (let* ((default (if (db :READ-ONLY) :COPY (if (db :MIX) :SET :HEURISTIC)))
              (method (get-option-member 'DEFSTRUCTURE :UPDATE-METHOD options 
                                   *update-methods* default default)))
         (if (and (db :READ-ONLY) (not (eq method :COPY)))
             (bomb "The only valid :UPDATE-METHOD for structures without ~
                    :SLOT-WRITERS is :COPY.")
           (cond
            ((db :INLINE) :INLINE)
            (t method)))))
      (:ASSERTION-LEMMA-HINTS
       (get-option-argument 'DEFSTRUCTURE :ASSERTION-LEMMA-HINTS options
                            :FORM nil nil))
      (:PREDICATE-GUARD-HINTS
       (get-option-argument 'DEFSTRUCTURE :PREDICATE-GUARD-HINTS options
                            :FORM nil nil))
      (:PREFIX (get-string-designator :PREFIX options "DEFS-"))

      ;;  Set defaults to possibly be overidden.

      (:TAG name)
      #|(:NORMALIZE T)|#
      (:READ-WRITE T)
      (:WRITE-WRITE t))

     ;;  Override defaults.

     (append-db
      (parse-do-not-options (get-option-entries :DO-NOT options)))

     ;; Still extending we add the forms necessary to complete parsing, and
     ;; parsing the :ASSERT options and the slot descriptors, returning the
     ;; DB. 

     (acons-db
      (:VALUE-VARIABLE (car (unique-symbols 2 (pack-intern name "VALUE")
                                            (cons name slot-names))))
      (:VALUE-VARIABLE1 (cadr (unique-symbols 2 (pack-intern name "VALUE")
                                              (cons name slot-names))))
      (:PREDICATE-CALL `(,(db :PREDICATE) ,name)))
     (append-db
      (reader-names slot-names db)
      (reader-calls slot-names db))
     (acons-db
      (:ASSERTIONS (parse-assert-options
                    (get-option-entries :ASSERT options) nil db)))
     (append-db (parse-slot-options slots db)))))

(defun prepare-for-code-gen (db)

  (db-let (slot-names representation name predicate read-only tag
                      #|normalize|# read-write write-write mv-intro-macro
                      weak-predicate inline mix set-conc-name)
    (cond
     
     ;;  A few error checks.

     ((and (eq representation :MV)
           (< (len slot-names) 2)
           (bomb "An :MV structure must have at least 2 slots in order ~
                  to be valid according to the syntax of Acl2, but ~
                  the current structure has ~#0~[one slot~/no slots~]."
                 slot-names)))

     ((not weak-predicate)
      (bomb "You have apparently tried to suppress the generation of the 
             weak predicate on the structure, which is currently illegal."))

     ((not predicate)
      (bomb "You have apparently tried to suppress the generation of the 
             predicate on the structure, which is currently illegal."))
     
     (t

      (extend-db
       (acons-db
        (:KEYWORD-SLOT-NAMES (keywordify-list slot-names))
        (:REQUIRED-SLOT-NAMES (required-slot-names slot-names db))

        ;;  We force :READ-ONLY if all slots were :READ-ONLY, or the
        ;;  representation is :MV

        (:READ-ONLY (or read-only
                        (equal (read-only-keyword-slots slot-names db)
                               (db :KEYWORD-SLOT-NAMES))
                        (eq representation :MV)))

        ;;  We force :MV records to be untagged.  After settling the :TAG
        ;;  question we can build the template.

        (:TAG (if (eq representation :MV) nil tag))
        (:TEMPLATE (make-template db)))

       (db-let (read-only keyword-updater)
         (extend-db
          (acons-db

           ;;  Define function,macro, and lemma names, and code fragments. We
           ;;  use the convention that if a name is NIL, then it is a flag to
           ;;  the appropriate code generator not to generate that thing.

           (:CONSTRUCTOR-CALL `(,name ,@slot-names))
           (:ACL2-COUNT-LEMMA (if (eq representation :mv)
                                  nil
                                (make-prefix-name "ACL2-COUNT-" name)))

           ;;  Weak Predicate. 

           (:WEAK-PREDICATE-CALL `(,weak-predicate ,name))
           (:WEAK-PREDICATE-CONSTRUCTOR-LEMMA
            (make-prefix-name weak-predicate "-" name))

           ;;  Predicate.

           (:PREDICATE-WEAK-PREDICATE-LEMMA
            (make-prefix-name predicate "-INCLUDES-" weak-predicate))
           
           (:PREDICATE-CONSTRUCTOR-LEMMA (make-prefix-name predicate "-" name))

           ;;  We suppress the keyword-updater if it's an :MV or there
           ;;  aren't any slots. 

           (:KEYWORD-UPDATER (if (or (eq representation :MV) (not slot-names))
                                 nil
                               keyword-updater))

           (:READ-LEMMA (if slot-names (make-prefix-name "READ-" name) nil))
           (:WRITE-LEMMA (if (or read-only (not slot-names))
                             nil
                           (make-prefix-name "WRITE-" name)))

           (:LIFT-IF-LEMMA (if slot-names
                               (make-prefix-name name "-LIFT-IF")
                             nil))

           (:ELIMINATION-LEMMA (if (or mix
                                       (eq representation :MV)
                                       (not slot-names))
                                   nil
                                 (make-prefix-name "ELIMINATE-" name)))
           #|
           (:NORMALIZATION-LEMMA (if (and normalize slot-names (not read-only))
                                     (make-prefix-name "NORMALIZE-" name)
                                   nil))
           |#
           (:WEAK-PREDICATE-SLOT-WRITERS-LEMMA
            (if (and slot-names (not read-only))
                (make-prefix-name weak-predicate "-" set-conc-name)
              nil))
           (:PREDICATE-SLOT-WRITERS-LEMMA
            (if (and slot-names (not read-only))
                (make-prefix-name predicate "-" set-conc-name)
              nil))
           (:READ-WRITE-LEMMA (if (and (not mix)
                                       read-write
                                       (not read-only)
                                       slot-names)
                                  (make-prefix-name "READ-WRITE-" name)
                                nil))
           (:WRITE-WRITE-LEMMA (if (and (not mix)
                                        write-write
                                        (not read-only)
                                        slot-names)
                                   (make-prefix-name "WRITE-WRITE-" name)
                                nil))
           (:ASSERTION-LEMMA (if (and predicate (all-rule-classes db))
                                 (make-prefix-name name "-ASSERTIONS")
                               nil))

           (:DEFINITION-THEORY (make-prefix-name name "-DEFINITION-THEORY"))
           (:LEMMA-THEORY (make-prefix-name name "-LEMMA-THEORY")))

          ;;  In :INLINE mode we simply NULL out all lemma names to suppress
          ;;  their generation.  This could be done more cleanly perhaps,
          ;;  i.e., there was no reason to even generate them above, but
          ;;  this simple and is guaranteed to work.

          (append-db
           (writer-names slot-names db)
           (writer-calls slot-names db)
           (if inline
               (nullify-lemmas *lemma-names*)
             nil)))))))))

;;;
;;;
;;; beginning of defstructure+ stuff
;;;
;;;

#|

(defun harvest-field-names (name base form)
  (if (consp form)
      (let ((line (car form)))
        (if (consp line)
            (if (equal (car line) :options) nil
              (cons (join-symbols name base (car line))
                    (harvest-field-names name base (cdr form))))
          (if (symbolp line)
              (cons (join-symbols name base line)
                    (harvest-field-names name base (cdr form)))
            (harvest-field-names name base (cdr form)))))
    nil))



;bzo
(defthm integerp-+
  (implies
   (and
    (integerp a)
    (integerp b))
   (integerp (+ a b))))

;trying disabled.
(defthmd plus-constant-reduction
  (implies
   (and
    (syntaxp (quotep q))
    (integerp q)
    (integerp n))
   (iff (equal (+ 1 n) q)
        (equal n (1- q)))))

;bzo drop?
(defthmd len-reduction
  (implies
   (and
    (syntaxp (quotep n))
    (integerp n)
    (<= 0 n))
   (iff (equal (len x) n)
        (if (zp n) (not (consp x))
          (and (consp x)
               (equal (len (cdr x)) (1- n)))))))

(defun accessor-predicate (name doc-and-slots)
  (declare (xargs :mode :program))
  (let*
      ((doc (if (stringp (car doc-and-slots)) (car doc-and-slots) nil))
       (slots-and-options (if doc (cdr doc-and-slots) doc-and-slots))
       (last-car (car (last slots-and-options)))
       (options? (and (consp last-car) (eq (car last-car) :OPTIONS)))
       (options (if options? (cdr last-car) nil)))
    (let ((string (structures::get-string-designator
                   :CONC-NAME options (concatenate 'STRING (structures::string name) "-"))))
      (intern-in-package-of-symbol string name))))

(defun add-assertion-types (rst)
  (if (consp rst)
      (let ((entry (car rst)))
        (if (and (consp entry)               ; (field  (:assert (pred field)))
                 (consp (cdr entry))         ;        ((:assert (pred field)))
                 (null  (cddr entry)))
            (let ((assertion (cadr entry)))  ;         (:assert (pred field))
              (let ((assertion
                     (if (and (consp assertion)
                              (equal (car assertion) :assert)
                              (consp (cdr assertion))
                              (null  (cddr assertion)))
                         `(:assert ,(cadr assertion) :rewrite :forward-chaining)
                       assertion)))
                (let ((entry `(,(car entry) ,assertion)))
                  (cons entry (add-assertion-types (cdr rst))))))
          (cons entry (add-assertion-types (cdr rst)))))
    rst))



|#

