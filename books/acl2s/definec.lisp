#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "defunc" :ttags :all)

(defun map-preds (types tbl atbl)
  (declare (xargs :guard (and (symbol-listp types) (sym-aalistp tbl)
                              (sym-aalistp atbl))))
  (if (endp types)
      nil
    (cons (pred-of-type (car types) tbl atbl)
          (map-preds (rest types) tbl atbl))))

(defun map-intern-type (type pkg)
  (declare (xargs :guard (and (symbolp type) (pkgp pkg))))
  (if (keywordp type)
      (fix-intern$ (symbol-name type) pkg)
    type))

(defun map-intern-types (types pkg)
  (declare (xargs :guard (and (symbol-listp types) (pkgp pkg))))
  (if (endp types)
      nil
    (cons (map-intern-type (car types) pkg)
          (map-intern-types (rest types) pkg))))

(defun make-input-contract-aux (args types)
  (declare (xargs :guard (and (symbol-listp args) (symbol-listp types))))
  (cond ((endp args) nil)
        ((equal (car types) 'acl2s::allp)
         (make-input-contract-aux (rest args) (rest types)))
        (t (cons `(,(car types) ,(car args))
                 (make-input-contract-aux (rest args) (rest types))))))

(defun make-input-contract (args types)
  (declare (xargs :guard (and (symbol-listp args) (symbol-listp types))))
  (let ((res (make-input-contract-aux args types)))
    (cond ((endp res) t) ; if res=(), no constraints
          ((equal (len res) 1) (first res))
          (t (cons 'and res)))))


#|
;; A version of definec without the fc rules

(defmacro definec (name &rest args)
  `(make-event
    (b* ((tbl (table-alist 'type-metadata-table (w state)))
         (f-args ',(car args))
         (pkg (current-package state))
         (f-type (fix-intern$ ,(symbol-name (second args)) pkg))
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

(defun find-next-type (var l acc)
  (cond ((endp l) acc)
        ((keywordp (car l))
         (find-next-type var (cdr l) (cons (car l) (cons var acc))))
        ((endp acc) (find-next-type var (cdr l) acc))
        (t acc)))

; (find-next-type 'x '(:nat y :int) nil)
; (find-next-type 'x '(:nat :int y :int) nil)
; (find-next-type 'x '(u v :nat :int y :int) nil)

(defun process-typed-args-aux (l acc)
  (cond ((endp l) (rev acc))
        ((keywordp (car l))
         (process-typed-args-aux (cdr l) acc))
        (t (process-typed-args-aux
            (cdr l)
            (append (find-next-type (car l) (cdr l) nil) acc)))))

(defun process-typed-args (l)
  (process-typed-args-aux l nil))

; (process-typed-args nil)
; (process-typed-args '(x :nat y :int))
; (process-typed-args '(x :nat :int y :int))
; (process-typed-args '(x u v :nat :int y z :int))
; (process-typed-args '(x y z))

(defun skip-keywords (l)
  (cond ((endp l) l)
        ((keywordp (car l))
         (skip-keywords (cdr l)))
        (t l)))

(defun proper-argsp (l)
  (or (endp l)
      (and (consp (cdr l))
           (acl2::legal-variablep (first l))
           (if (acl2::keywordp (second l))
               (proper-argsp (skip-keywords (cddr l)))
             (proper-argsp (cdr l))))))

; (check (proper-argsp nil))
; (check (! (proper-argsp '(x))))
; (check (proper-argsp '(x :nat)))
; (check (proper-argsp '(x :nat :int)))
; (check (proper-argsp '(x y :nat :int)))
; (check (! (proper-argsp '(x y :nat :int z))))
; (check (proper-argsp '(x y :nat :int u z :foo)))

(defmacro definec-core (name d? &rest args)
  `(with-output
    :stack :push :off :all :on (error comment)
    (make-event
     (b* ((tbl (table-alist 'type-metadata-table (w state)))
          (atbl (table-alist 'type-alias-table (w state)))
          (pkg (current-package state))
          (name ',name)
          (d? ',d?)
          (args ',args)
          (f-args (car args))
          ((unless (proper-argsp f-args))
           (er hard 'definec
               "~%The arguments to ~x0 are not well formed.
See the documentation for example arguments: ~x1"
               name f-args))
          (f-argsp (process-typed-args f-args))
          (f-type (map-intern-type (second args) pkg))
          (d-args (evens f-argsp))
          (def-args (remove-duplicates d-args))
          (d-arg-types (odds f-argsp))
          (d-arg-types (map-intern-types d-arg-types pkg))
          (d-arg-preds (map-preds d-arg-types tbl atbl))
          (pred (pred-of-type f-type tbl atbl))
          (ic (make-input-contract d-args d-arg-preds))
          (oc (make-contract name def-args pred))
          (defunc `(defunc-core ,name ,d? ,def-args
                     :input-contract ,ic
                     :output-contract ,oc
                     ,@(cddr args)))
          (bad-type
           (find-bad-d-arg-types d-arg-types d-arg-preds))
          ((when bad-type)
           (er hard 'definec "~%One of the argument types, ~x0, is not a type." bad-type))
          ((unless pred)
           (er hard 'definec "~%The given return type, ~x0, is not a known type." f-type)))
       `(with-output :stack :pop ,defunc)))))

(defmacro definec (name &rest args)
  `(definec-core ,name nil ,@args))

(defmacro definedc (name &rest args)
  `(definec-core ,name t ,@args))

#|

Example:

(definec f (x :nat y :nat) :nat
  (+ x y))

expands into


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
  :short "Function definitions with contracts extending @(see defunc)."
  :long
"
<h3>Examples</h3>

@({

  (definec my-len (a :all) :nat
    (if (atom a)
        0
      (+ 1 (my-len (rest a)))))

  ; An alternate, but equivalent, definition of my-len
  (definec my-len (a :all) :nat
    (match a
      (:atom 0)
      ((& . r) (1+ (my-len r)))))

  ; Notice that both x and y are nats
  (definec f (x y :nat) :nat
    (+ x y))

  ; Both x and y are true-lists
  (definec my-app (x y :tl) :tl
    (match x
      (nil y)
      ((f . r) (cons f (my-app r y)))))

  ; All is the universal type
  (definec my-atom (x :all) :bool
    (atom x))

  ; Factorial
  (definec my-fact (x :nat) :pos
    (match x
      ((:or 0 1) 1)
      (& (* x (my-fact (1- x))))))

  ; list-sum
  (definec list-sum (l :rational-list) :rational
    (match l
      (nil 0)
      ((f . r) (+ f (list-sum r)))))

  ; Average: notice that l is a both a rational-list and a cons
  (definec average (l :rational-list :cons) :rational
    (/ (list-sum l) (len l)))

  ; Square a list, with some extra keyword arguments
  (definec square-list (l :nat-list) :nat-list
    (match l
      (nil nil)
      ((f . r) (app (list (* f f)) (square-list r))))
    :verbose t
    :skip-tests t)
})

<h3>Purpose</h3>
<p>
The macro @(see definec) is an extension of @(see defunc)
that makes it more convient to specify simple contracts.
For example, the expansion of
</p>

@({

  (definec f (x y :nat) :nat
    (+ x y))
})

<p>
includes the following events.
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
the corresponding predicates using @(see defdata) and we
support :all (the type of the ACL2 universe), :tl (the type of
true-lists), :int (the type of integers), :bool (the type of booleans)
and all other types @(see defdata) knows.  </p>

<p>
When specifying types one must use keywords,
as shown above. It is important to put a space between
the variable name and the type, e.g., x:nat will lead to errors.
</p>

<p>
As the examples above show, the paramater types and the return type
are used to generate @(see defunc) contracts and then the rest of
the arguments are passed to @(see defunc), so you can use all the
bells and whistles of @(see defunc).

</p>
"
  )

(defmacro definecd (name &rest args)
  `(with-output
    :off :all :on (error) :stack :push
    (encapsulate
     nil
     (with-output
      :stack :pop
      (definec ,name ,@args))
     (make-event
      `(with-output
        :off :all :on (summary) :summary-off (:other-than form)
        (in-theory
         (disable
          ,(make-symbl `(,',name -DEFINITION-RULE) (current-package state)))))))))

(defmacro definedcd (name &rest args)
  `(with-output
    :off :all :on (error) :stack :push
    (encapsulate
     nil
     (with-output
      :stack :pop
      (definedc ,name ,@args))
     (make-event
      `(with-output
        :off :all :on (summary) :summary-off (:other-than form)
        (in-theory
         (disable
          ,(make-symbl `(,',name -DEFINITION-RULE) (current-package state)))))))))

(defmacro definec-no-test (name &rest args)
  `(gen-acl2s-local testing-enabled
                    nil
                    ((definec ,name ,@args))))

(defmacro definecd-no-test (name &rest args)
  `(gen-acl2s-local testing-enabled
                    nil
                    ((definecd ,name ,@args))))

(defmacro definedc-no-test (name &rest args)
  `(gen-acl2s-local testing-enabled
                    nil
                    ((definedc ,name ,@args))))

(defmacro definedcd-no-test (name &rest args)
  `(gen-acl2s-local testing-enabled
                    nil
                    ((definedcd ,name ,@args))))
