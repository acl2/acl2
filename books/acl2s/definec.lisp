#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "defunc" :ttags :all)

(defun map-preds (types tbl atbl ctx)
  (if (endp types)
      nil
    (cons (pred-of-type (car types) tbl atbl ctx)
          (map-preds (rest types) tbl atbl ctx))))

(defun map-intern-type (type pkg)
  (if (keywordp type)
      (intern$ (symbol-name type) pkg)
    type))

(defun map-intern-types (types pkg)
  (if (endp types)
      nil
    (cons (map-intern-type (car types) pkg)
          (map-intern-types (rest types) pkg))))

(defun make-input-contract-aux (args types)
  (cond ((endp args) nil)
        ((equal (car types) 'acl2s::allp)
         (make-input-contract-aux (rest args) (rest types)))
        (t (cons `(,(car types) ,(car args))
                 (make-input-contract-aux (rest args) (rest types))))))
         
(defun make-input-contract (args types)
  (let ((res (make-input-contract-aux args types)))
    (cond ((endp res) t) ; if res=(), no constraints
          ((equal (len res) 1) (first res))
          (t (cons 'and res)))))
     

#|
;; A version of definec without the fc rules

(defmacro definec (name &rest args)
  `(make-event
    (b* ((tbl (table-alist 'defdata::type-metadata-table (w state)))
         (f-args ',(car args))
         (pkg (current-package state))
         (f-type (intern$ ,(symbol-name (second args)) pkg))
         (d-args (evens f-args))
         (d-arg-types (odds f-args))
         (d-arg-preds (map-preds d-arg-types pkg tbl))
	 (f-type-pred (pred-of-type f-type tbl)))
        `(defunc ,',name ,d-args
           :input-contract ,(make-input-contract d-args d-arg-preds)
           :output-contract ,(make-output-contract ',name d-args f-type-pred)
           ,',@(cddr args)))))

Examples

(definec f (x :nat y :nat) :all
  (+ x y))

and 

(definec f (x nat y nat) all
  (+ x y))

both expand into

(DEFUNC F (X X)
  :INPUT-CONTRACT (AND (NATP X) (NATP Y))
  :OUTPUT-CONTRACT T
   (+ X Y))


|#

;; Before latest updates to defunc 

(defun find-bad-d-arg-types (d-arg-types d-arg-preds)
  (cond ((endp d-arg-preds) nil)
        ((null (car d-arg-preds))
         (car d-arg-types))
        (t (find-bad-d-arg-types (cdr d-arg-types)
                                 (cdr d-arg-preds)))))

(defmacro definec (name &rest args)
  `(with-output
    :stack :push :off :all :on (error)
    (make-event
     (b* ((tbl (table-alist 'defdata::type-metadata-table (w state)))
          (atbl (table-alist 'defdata::type-alias-table (w state)))
          (pkg (current-package state))
          (f-args ',(car args))
          (f-type (map-intern-type ',(second args) pkg))
          (d-args (evens f-args))
          (d-arg-types (odds f-args))
          (d-arg-types (map-intern-types d-arg-types pkg))
          (d-arg-preds (map-preds d-arg-types tbl atbl 'definec))
          (f-type-pred (pred-of-type f-type tbl atbl 'definec))
          (ic (make-input-contract d-args d-arg-preds))
          (oc (make-output-contract ',name d-args f-type-pred))
          (defunc `(defunc ,',name ,d-args
                     :input-contract ,ic
                     :output-contract ,oc
                     ,@(cddr ',args)))
          ((when (oddp (len f-args)))
           (er hard 'definec
               "~%The argumets to ~x0 should alternate between variables and types,
but ~x0 has an odd number of arguments: ~x1"
               ',name f-args))
          (bad-type
           (find-bad-d-arg-types d-arg-types d-arg-preds))
          ((when bad-type)
           (er hard 'definec "~%One of the argument types, ~x0, is not a type." bad-type))
          ((unless f-type-pred)
           (er hard 'definec "~%The given return type, ~x0, is not a type." f-type)))
       `(with-output :stack :pop ,defunc)))))

(defmacro definedc (name &rest args)
  `(with-output
    :stack :push :off :all :on (error)
    (make-event
     (b* ((tbl (table-alist 'defdata::type-metadata-table (w state)))
          (atbl (table-alist 'defdata::type-alias-table (w state)))
          (pkg (current-package state))
          (f-args ',(car args))
          (f-type (map-intern-type ',(second args) pkg))
          (d-args (evens f-args))
          (d-arg-types (odds f-args))
          (d-arg-types (map-intern-types d-arg-types pkg))
          (d-arg-preds (map-preds d-arg-types tbl atbl 'definedc))
          (f-type-pred (pred-of-type f-type tbl atbl 'definedc))
          (ic (make-input-contract d-args d-arg-preds))
          (oc (make-output-contract ',name d-args f-type-pred))
          (defundc `(defundc ,',name ,d-args
                      :input-contract ,ic
                      :output-contract ,oc
                      ,@(cddr ',args)))
          ((when (oddp (len f-args)))
           (er hard 'definedc
               "~%The argumets to ~x0 should alternate between variables and types,
but ~x0 has an odd number of arguments: ~x1"
               ',name f-args))
          (bad-type
           (find-bad-d-arg-types d-arg-types d-arg-preds))
          ((when bad-type)
           (er hard 'definedc "~%One of the argument types, ~x0, is not a type." bad-type))
          ((unless f-type-pred)
           (er hard 'definedc "~%The given return type, ~x0, is not a type." f-type)))
       `(with-output :stack :pop ,defundc)))))

#|

Example:

(definec f (x :nat y :nat) :nat
  (+ x y))

and

(definec f (x nat y nat) nat
  (+ x y))

both expand into


(DEFUNC F (X Y)
  :INPUT-CONTRACT (AND (NATP X) (NATP Y))
  :OUTPUT-CONTRACT (NATP (F X Y))
  (+ X Y))

(DEFTHM F-DEFINEC-FC-RULE
  (IMPLIES (FORCE (AND (NATP X) (NATP Y)))
           (NATP (F X Y)))
  :RULE-CLASSES ((:FORWARD-CHAINING :TRIGGER-TERMS ((F X Y)))))

|#

(include-book "xdoc/top" :dir :system)

(defxdoc definec
  :parents (acl2::acl2-sedan acl2::macro-libraries acl2s::defunc)
  :short "Function definitions with contracts @(see acl2s::defunc)"
  :long
  "
<h3>Examples</h3>

@({

  (definec f (x :nat y :nat) :nat
    (+ x y))

  (definec len (a :all) :nat
    (if (atom a)
        0
      (+ 1 (len (rest a)))))

  (definec app (x :tl y :tl) :tl 
    (if (endp x)
        y
      (cons (car x) (app (cdr x) y))))

  (definec square-list (l nat-list) nat-list
    (if (endp l)
        nil
      (app (list (* (car l) (car l)))
           (square-list (cdr l))))
    :verbose t
    :skip-tests t)

})

<h3>Purpose</h3>
<p>
The macro @('definec') is an extension of @('acl2s::defunc')
that makes it more convient to specify simple contracts. 
For example, the expansions of
</p>

@({

  (definec f (x :nat y :nat) :nat
    (+ x y))
})

<p>
and 
</p>

@({

(definec f (x nat y nat) nat
  (+ x y))
})

<p>
are equivalent and include the following events.
</p>

@({

  (defunc f (x y)
    :input-contract (and (natp x) (natp y))
    :output-contract (natp (f x y))
    (+ x y))

  (defthm f-definec-fc-rule
    (implies (force (and (natp x) (natp y)))
             (natp (f x y)))
    :rule-classes ((:forward-chaining :trigger-terms ((f x y)))))

})

<p> Notice that nat was turned into natp. We convert type names into
the corresponding predicates using @('defdata::defdata') and we
support all (the type of the ACL2 universe), tl (the type of
true-lists), int (the type of integers), bool (the type of booleans)
and all other types @('defdata::defdata') knows.  </p>

<p>
When specifying types one can use keywords or regular symbols,
as shown above. It is important to put a space between 
the variable name and the type, e.g., x:nat will lead to errors. 
</p>

<p>
As the examples above show, the paramater types and the return type
are used to generate @('acl2s::defunc') contracts and then the rest of
the arguments are passed to @('acl2s::defunc'), so you can use all the
bells and whistles of @('acl2s::defunc'). 

</p>
"
  )

(defmacro definecd (name &rest args)
  `(encapsulate
    nil
    (definec ,name ,@args)
    (make-event 
     `(in-theory
       (disable
        ,(make-symbl `(,',name -DEFINITION-RULE) (current-package state)))))))

(defmacro definedcd (name &rest args)
  `(encapsulate
    nil
    (definedc ,name ,@args)
    (make-event 
     `(in-theory
       (disable
        ,(make-symbl `(,',name -DEFINITION-RULE) (current-package state)))))))

(defmacro definec-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (definec ,name ,@args)))

(defmacro definecd-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (definecd ,name ,@args)))

(defmacro definedc-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (definedc ,name ,@args)))

(defmacro definedcd-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (definedcd ,name ,@args)))

