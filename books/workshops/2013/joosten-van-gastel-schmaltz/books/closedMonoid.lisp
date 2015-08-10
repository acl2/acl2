(in-package "ACL2")

(include-book "instance-of-defspec")
; We define different fold operators over the abstract function binary-function


; Alternatively, we can use the first element:
(defun foldr1 (xs)
  (if (endp (cdr xs)) (car xs)
    (binary-function (car xs) (foldr1 (cdr xs)))))
(defun foldr (x xs)
  (if (endp xs) x (binary-function (car xs) (foldr x (cdr xs)))))
(defun foldl (x xs)
  (if (endp xs) x
    (foldl (binary-function x (car xs)) (cdr xs))))

(instance-of-defspec binary cons '((binary-function cons)
                                   (foldr  cons-foldr)
                                   (foldr1 cons-foldr1)
                                   (foldl  cons-foldl)))
#| ; check this out to try the created functions:
(cons-foldr 'a '(b c))
(cons-foldr1 '(a b c))
(cons-foldl 'a '(b c))
|#

; #| ; we have removed these theorems from the article. You may disable them here. The rest will work either way.
; We define some properties that hold on our fold operators
(defthm foldl-nil
  (implies (and (not (consp XS)))
           (equal (foldl X XS) X)))
(defthm foldr-append
  (equal (foldr (foldr x ys) xs)
         (foldr x (append xs ys))))
(defthm foldr1-append
  (implies (consp ys)
           (equal (foldr (foldr1 ys) xs)
                  (foldr1 (append xs ys)))))
(defthm foldl-append
  (equal (foldl (foldl x ys) xs)
         (foldl x (append ys xs))))
; The following theorem states that foldr1 does roughly the same as foldr:
(defthm foldr1-is-foldr
  (equal (foldr1 (append xs (list x)))
                  (foldr x xs)))
; |# ; the article-code continues here

;Suppose the operator binary-function is closed in a domain, (it is called a magma)
(defspec closed-binop ((c-domainp (x) t)
                       (c-binary-function (x y) t))
  (local (defun c-domainp (x) (integerp x)))
  (local (defun c-binary-function (x y) (+ x y)))
  (defthm closed-binop-closed
    (implies (and (c-domainp x) (c-domainp y))
             (c-domainp (c-binary-function x y)))))
(instance-Of-defspec binary c)
; completely redundant at this point, but it is in the article
(instance-of-defspec binary cons '((binary-function cons)))

(defun list-domainp (xs)
  (if (endp xs) t
    (and (c-domainp (car xs)) (list-domainp (cdr xs)))))

(defthm foldr1-closed
  (implies (and (list-domainp xs) (consp xs))
           (c-domainp (c-foldr1 xs))))

; #| ; two theorems not stated in the article. If you remove these, the theorems in the rest of this book will still work.
(defthm c-foldl-closed
  (implies (and (c-domainp x)
                (list-domainp xs))
           (c-domainp (c-foldl x xs))))
(defthm c-foldr-closed
  (implies (and (c-domainp x)
                (list-domainp xs))
           (c-domainp (c-foldr x xs))))
;|#

; If we wish to show that all the fold operators actually yield the same value
; we need to use associativity.
(defspec semigroup ((sg-c-domainp (x) t)
                    (sg-c-binary-function (x y) t))
  (local (defun sg-c-domainp (x) (integerp x)))
  (local (defun sg-c-binary-function (x y) (+ x y)))
  (is-a closed-binop sg semigroup-isa-closed-binop)
  (defthm semigroup-assoc
    (implies (and (sg-c-domainp x)
                  (sg-c-domainp y)
                  (sg-c-domainp z))
             (equal (sg-c-binary-function x (sg-c-binary-function y z))
                    (sg-c-binary-function (sg-c-binary-function x y) z)))))
(instance-Of-defspec closed-binop sg) ; reuse the fold operators (again)

(defthm foldr1-is-foldl
  (implies (and (sg-c-domainp x) (sg-c-domainp y)
                (sg-list-domainp xs))
           (equal (sg-c-foldr1 (cons x xs))
                  (sg-c-foldl x xs))))

(defconst *monoid-renaming*
  '((sg-c-domainp         mon-domainp)      (sg-c-foldr  mon-foldr)
    (sg-c-binary-function mon-binop)        (sg-c-foldr1 mon-foldr1)
    (sg-list-domainp      mon-list-domainp) (sg-c-foldl  mon-foldl) ))

; if there is an identity element, we obtain a monoid
(defspec monoid ((mon-domainp (x) t) (mon-binop (x y) t)
                 (mon-id () t))
  (local (defun mon-domainp (x) (integerp x)))
  (local (defun mon-binop (x y) (+ x y)))
  (local (defun mon-id () 0))
  (defthm id-in-domain (mon-domainp (mon-id)))
  (is-a semigroup mon monoid-isa-semigroup *monoid-renaming*)
  (defthm monoid-id-left
    (implies (and (mon-domainp x))
             (equal (mon-binop x (mon-id))
                    x)))
  (defthm monoid-id-right
    (implies (and (mon-domainp x))
             (equal (mon-binop (mon-id) x)
                    x))))
(instance-Of-defspec semigroup mon *monoid-renaming*)
(defun fold (xs)
  (if (atom xs) (mon-id)
    (mon-foldr1 xs)))

(defthm foldr-eq
  (implies (and (mon-list-domainp xs) (consp xs))
           (equal (mon-foldr (mon-id) xs)
                  (mon-foldr1 xs))))
(defthm foldr1-monoid
  (implies (and (mon-list-domainp xs) (consp xs))
           (equal (mon-foldr1 (cons (mon-id) xs))
                  (mon-foldr1 xs)
                  ))
  :hints (("Goal" :in-theory (disable id-in-domain)))
  )
(defthm foldl-eq
  (implies (and (mon-list-domainp xs) (consp xs))
           (equal (mon-foldr1 xs) (mon-foldl (mon-id) xs)
                  ))
  :hints (("Goal" :in-theory '(mon-foldr1-is-foldl)
                  :use (id-in-domain foldr1-monoid)
                  ))
  )
(defthm fold-eq
  (implies (and (mon-list-domainp xs)
                (consp xs))
           (equal (mon-foldl (mon-id) xs)
                  (fold xs)
                  ))
  :hints (("Goal" :in-theory (disable id-in-domain)))
  )

(defthm identity-is-unique
  (implies (and (mon-domainp x)
                (or (equal (mon-binop x (mon-id)) (mon-id))
                    (equal (mon-binop (mon-id) x) (mon-id))))
           (equal x (mon-id)))
  :rule-classes nil
  )
; to check out all lemmas that apply to mon-foldl, use: (symbol-lemmas mon-foldl)

; some example uses:
(instance-Of-defspec monoid list '((mon-domainp true-listp)
                                   (mon-binop binary-append)
                                   (mon-id (lambda () nil))
                                   ))
; test the resulting fold function: (list-fold `((1 2 3) NIL (6 7) (x (y) z)))
; now suppose we wish to append lists of which the elements satisfy some predicate:
(defspec list-predicate ((predicate (x) t))
  (local (defun predicate (x) x)))
(defun predicate-listp (lst)
  (if (atom lst) (null lst) ; require true-lists
    (and (predicate (car lst)) (predicate-listp (cdr lst)))))

(instance-Of-defspec monoid conditional-list '((mon-domainp predicate-listp)
                                               (mon-binop binary-append)
                                               (mon-id (lambda () nil))
                                               (mon-list-domainp predicate-list-listp)
                                               ))
; let's make an instance where we just handle lists of numbers:
(instance-Of-defspec list-predicate |1| '((predicate (lambda (x) (acl2-numberp x)))))

; we could make an instance that handles lists of 2's, 3's etc, or perhaps pick any item from a given list
(instance-Of-defspec list-predicate members '((predicate (lambda (x) (member-equal x y)))
                                              (predicate-listp (lambda (lst) (subset-equal lst y)))
                                              (predicate-list-listp (lambda (xs) (listof-subsets xs y))) ; required, since otherwise y would become a free variable in the context of monoids
                                              ))#|ACL2s-ToDo-Line|#




#| ; note that we have already made a monoid out of this, so we 'inherit' all theorems, e.g.:
:pe MEMBERS-CONDITIONAL-LIST-FOLD-EQ
|#
