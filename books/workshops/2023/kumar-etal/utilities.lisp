(in-package "ACL2S")
(include-book "kestrel/utilities/system/top" :dir :system)

#|

This macro defines a constrained 0-arity function named name, about
which we only know that it has type pred.

It also defines an attachment which is a constant function returning
val.

This allows us to define constants that are treated as arbitrary
constants by the theorem prover, but for which cgen can generate
counterexamples.

|#

(defmacro m-symbl (l)
  `(gen-sym-sym ,l name))

(defmacro define-constant-type (name type)
  `(make-event
    (b* ((tbl (table-alist 'defdata::type-metadata-table (w state)))
         (atbl (table-alist 'defdata::type-alias-table (w state)))
         (pkg (current-package state))
         (unalias-type (type-of-type ',type tbl atbl))
         (pred (pred-of-type ',type tbl atbl))
         (def-name (make-symbl (list ',name '- ',type) pkg))
         (base-val (base-val-of-type unalias-type tbl)))
      `(encapsulate
        ((,',name () t :guard t))
        (local (defun ,',name () ,base-val))
        (defthm ,def-name
          (,pred (,',name))
          :rule-classes
          ((:type-prescription)
           (:forward-chaining :trigger-terms ((,',name)))
           (:rewrite)))))))

; Alias type example
; :trans1 (define-constant-type foo int)
; (define-constant-type foo int)

; Regular type example
; :trans1 (define-constant-type foo integer)
; (define-constant-type foo int)

(defmacro attach-fun-to-const (name val)
  `(make-event
    (b* ((att-name (gen-sym-sym (list ',name '-attached-base) ',name))
         (att-name (acl2::fresh-name-in-world-with-$s att-name nil (w state))))
      `(progn
         (defun ,att-name ()
           (declare (xargs :guard t))
           ,',val)
         (defattach ,',name ,att-name)))))

; :trans1 (attach-fun-to-const foo 10)
; (attach-fun-to-const foo 10)

(defmacro define-attach-constant (name type val)
  `(progn (define-constant-type ,name ,type)
          (attach-fun-to-const ,name ,val)))

; :trans1 (define-attach-constant foo int 10)
; (define-attach-constant foo int 10)

; Example of defining a new attacment
; :trans1 (define-attach-constant foo int 20)
; :trans1 (attach-fun-to-const foo 20)
; (define-attach-constant foo int 20)

(definec fl (x :rational) :integer
  (floor x 1))
