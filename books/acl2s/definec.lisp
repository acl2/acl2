#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "defunc" :ttags :all)

(defun pred-of-type (type tbl)
  (cond ((equal type 'tl) 'acl2::true-listp)
        ((equal type 'int) 'acl2::integerp)
        ((equal type 'bool) 'acl2::booleanp)
        (t (let ((res (get-alist :predicate (get-alist type tbl))))
             (or res
                 (er hard 'Definec "~%**Unknown type in definec**: ~x0 is not a known type name.~%" type ))))))

(defun map-preds (types pkg tbl)
  (if (endp types)
      nil
    (cons (pred-of-type (intern$ (symbol-name (car types)) pkg) tbl)
          (map-preds (rest types) pkg tbl))))

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
     
(defun make-output-contract (name args type)
  (cond ((equal type 'acl2s::allp) t)
        (t `(,type ,(cons name args)))))


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

(defmacro definec (name &rest args)
  `(with-output
    :stack :push :off :all
    (make-event
     (b* ((tbl (table-alist 'defdata::type-metadata-table (w state)))
          (pkg (current-package state))
          (f-args ',(car args))
          (f-type (intern$ ,(symbol-name (second args)) pkg))
          (d-args (evens f-args))
          (d-arg-types (odds f-args))
          (d-arg-preds (map-preds d-arg-types pkg tbl))
          (f-type-pred (pred-of-type f-type tbl))
          (ic (make-input-contract d-args d-arg-preds))
          (oc (make-output-contract ',name d-args f-type-pred))
          (defunc `(defunc ,',name ,d-args
                     :input-contract ,ic
                     :output-contract ,oc
                     ,@(cddr ',args))))
         `(with-output :stack :pop ,defunc)))))

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
  (let ((defname (make-symbl `(,name -DEFINITION-RULE))))
    `(progn
       (definec ,name ,@args)
       (in-theory (disable ,defname)))))

(defmacro definec-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (definec ,name ,@args)))

(defmacro definecd-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (definecd ,name ,@args)))
