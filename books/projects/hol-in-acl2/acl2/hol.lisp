; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book defines our representation of a hol type as well as a hol value of
; a given hol type.  It then exhibits a set, (v-omega*2), such that every hol
; value belongs to that set.  This implies by set comprehension that the
; collection of all hol values is a set, but we do not take that final step
; here.  Finally (and this could presumably have been done earlier in the
; file), we develop the notion of a hol value/type pair.

(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Hol types, type alists, and values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An hta is an alist associating atomic (in fact, symbol) type names with sets.
; Here is an example.

(defun hta0 () ; example of hta (i.e., hol type alist)
  (declare (xargs :guard t))
  (acons :num (omega)
         (acons :bool (pair t nil)
                nil)))

(defun assoc-hta (name hta)

; This function could have a weaker guard of t, or a stronger guard that also
; requires (symbol-alistp hta) or even (and (alistp hta) (keyword-listp
; (strip-cars hta)).  We may choose later to weaken or strengthen the guard.

  (declare (xargs :guard (symbolp name)))
  (hons-assoc-equal name hta))

(defun hol-typep (type hta groundp)

; This function defines our representation of hol type expressions.  When
; groundp is nil, variables (non-keyword symbols) are allowed; otherwise they
; are not.  Hta is a hol type-alist, mapping keywords to sets.

  (declare (xargs :guard t))
  (cond
   ((keywordp type)
    (and (assoc-hta type hta)
         t))
   ((atom type)
    (and (not groundp)
         (symbolp type)))
   ((true-listp type)
    (case (car type)
      ((:arrow :hash)
       (and (= (length type) 3)
            (and (hol-typep (nth 1 type) hta groundp)
                 (hol-typep (nth 2 type) hta groundp))))
      ((:list :option)
       (and (= (length type) 2)
            (hol-typep (nth 1 type) hta groundp)))
      (otherwise nil)))
   (t nil)))

; We model a list as a function whose domain is a natural number.  That way
; it's more obvious than using cons that the set of all lists from a given set
; is itself a set, without using any sort of collection or replacement (due to
; the way cons bumps up the set-theoretic rank).

(defund hol-type-eval (type hta)

; This function returns the set value of the given ground type with respect to
; hta, an assignment of type names to atomic types.  We complete to a total
; function by returning the empty set, 0, if type is ill-formed with respect to
; hta.

  (declare (xargs :guard (hol-typep type hta t)))
  (cond
   ((not (mbt (hol-typep type hta t)))
    0)
   ((atom type) ; (keywordp type)
    (let ((pair (assoc-hta type hta)))
      (if (consp pair)
          (cdr pair)
        0)))
   (t
    (case (car type)
      (:arrow
       (let ((val1 (hol-type-eval (nth 1 type) hta))
             (val2 (hol-type-eval (nth 2 type) hta)))
         (if (or (equal val1 0)
                 (equal val2 0))
             0
           (fun-space val1 val2))))
      (:hash
       (let ((val1 (hol-type-eval (nth 1 type) hta))
             (val2 (hol-type-eval (nth 2 type) hta)))
         (if (or (equal val1 0)
                 (equal val2 0))
             0
           (prod2 val1 val2))))
      (:list
       (let ((val (hol-type-eval (nth 1 type) hta)))
         (if (equal val 0)
             0
           (finseqs val))))
      (:option
       (let ((val (hol-type-eval (nth 1 type) hta)))
         (if (equal val 0)
             0
           (insert :none
                   (prod2 (singleton :some)
                          val)))))
      (otherwise 0)))))

(defun hol-valuep (x type hta)

; This function recognizes when x is a hol value of the given hol ground type
; with respect to a give association of atomic type names with sets.

  (declare (xargs :guard (hol-typep type hta t)))
  (in x (hol-type-eval type hta)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Hol types and pairs, and matching
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The acronym "hp" stands for "hol-pair", a cons whose cdr is a hol ground type
; and whose car is a hol value of that type.

(defun hpp (p hta)
  (declare (xargs :guard t))
  (and (consp p)
       (hol-typep (cdr p) hta t)
       (hol-valuep (car p) (cdr p) hta)))

(defmacro make-hp (value type)
  `(cons ,value ,type))

(defun hp-listp (x hta)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (hpp (car x) hta)
                (hp-listp (cdr x) hta)))))

(defun weak-hol-typep (type groundp)
  (declare (xargs :guard t))
  (cond ((atom type)
         (or (keywordp type)
             (and (not groundp)
                  (symbolp type))))
        ((true-listp type)
         (case (car type)
           ((:arrow :hash)
            (and (= (length type) 3)
                 (and (weak-hol-typep (nth 1 type) groundp)
                      (weak-hol-typep (nth 2 type) groundp))))
           ((:list :option)
            (and (= (length type) 2)
                 (weak-hol-typep (nth 1 type) groundp)))
           (otherwise nil)))
        (t nil)))

(defun weak-hol-type-alistp (bindings)

; This function recognizes when bindings is an alist mapping variables to
; ground types.

  (declare (xargs :guard t))
  (cond ((atom bindings)
         (null bindings))
        ((consp (car bindings))
         (and (symbolp (caar bindings))
              (not (keywordp (caar bindings)))
              (weak-hol-typep (cdar bindings) t)
              (weak-hol-type-alistp (cdr bindings))))
        (t nil)))

(defun weak-hol-type-listp (x groundp)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (weak-hol-typep (car x) groundp)
                (weak-hol-type-listp (cdr x) groundp)))))

(mutual-recursion

(defun type-match (pat type bindings)

; Pat is a type pattern, that is, a type expression that need not be ground.
; Type-match attempts to extend the given bindings by associating type
; variables with ground types, returning the extended bindings upon success and
; :fail upon failure.

  (declare (xargs :guard (and (weak-hol-typep pat nil)
                              (weak-hol-typep type t)
                              (weak-hol-type-alistp bindings))
                  :verify-guards nil
                  :measure (acl2-count pat)))
  (cond
   ((atom pat)
    (cond ((keywordp pat)
           (cond ((eq pat type) bindings)
                 (t :fail)))
          (t (let ((pair (assoc-hta pat bindings)))
               (cond ((null pair) (acons pat type bindings))
                     ((equal (cdr pair) type) bindings)
                     (t :fail))))))
   ((atom type)
    :fail)
   ((not (eq (car pat) (car type)))
    :fail)
   (t (type-match-lst (cdr pat) (cdr type) bindings))))

(defun type-match-lst (pat-lst type-lst bindings)

; Bindings is an alist.  It keys are symbols that represent types.  Its values
; are type expressions.

  (declare (xargs :guard (and (weak-hol-type-listp pat-lst nil)
                              (weak-hol-type-listp type-lst t)
                              (equal (length pat-lst) (length type-lst))
                              (weak-hol-type-alistp bindings))
                  :measure (acl2-count pat-lst)))
  (cond
   ((atom pat-lst)
    (if (and (null pat-lst)
             (null type-lst))
        bindings
      :fail))
   ((atom type-lst) :fail)
   (t (let ((bindings1 (type-match (car pat-lst) (car type-lst) bindings)))
        (cond ((eq bindings1 :fail)
               :fail)
              (t (type-match-lst (cdr pat-lst) (cdr type-lst) bindings1)))))))
)

(defthm weak-hol-type-alistp-forward-to-symbol-alistp
  (implies (weak-hol-type-alistp bindings)
           (symbol-alistp bindings))
  :rule-classes :forward-chaining)

(defthm weak-hol-typep-impliest-weak-hol-type-listp-cdr
; This speeds up (verify-guards type-match ...) tremendously.
  (implies (and (weak-hol-typep x groundp)
                (not (keywordp x)))
           (weak-hol-type-listp (cdr x) groundp)))

(defthm weak-hol-type-listp-forward-to-true-listp
  (implies (weak-hol-type-listp x groundp)
           (true-listp x))
  :rule-classes :forward-chaining)

(encapsulate
  ()

(local (include-book "tools/flag" :dir :system))

(local (acl2::make-flag type-match))

(local
 (defthm equal-plus-len
   (implies (and (syntaxp (quotep k))
                 (syntaxp (quotep n))
                 (natp n))
            (equal (equal (+ k (len x)) n)
                   (equal (len x) (- n k))))))

(local
 (defthm-flag-type-match
   (defthm weak-hol-type-alist-type-match
     (implies (and (weak-hol-typep pat nil)
                   (weak-hol-typep type t)
                   (weak-hol-type-alistp bindings)
                   (not (equal (type-match pat type bindings)
                               :fail)))
              (weak-hol-type-alistp (type-match pat type bindings)))
     :flag type-match)
   (defthm weak-hol-type-alist-type-match-lst
     (implies (and (weak-hol-type-listp pat-lst nil)
                   (weak-hol-type-listp type-lst t)
                   (equal (length pat-lst) (length type-lst))
                   (weak-hol-type-alistp bindings)
                   (not (equal (type-match-lst pat-lst type-lst bindings)
                               :fail)))
              (weak-hol-type-alistp (type-match-lst pat-lst type-lst
                                                    bindings)))
     :flag type-match-lst)))

(verify-guards type-match
  :hints (("Goal" :expand ((:free (groundp) (weak-hol-typep pat groundp))))))
)

(local (defthm len-strip-cdrs
         (equal (len (strip-cdrs x))
                (len x))))

(defthm hol-typep-forward-to-weak-hol-typep
  (implies (hol-typep x hta groundp)
           (weak-hol-typep x groundp))
  :rule-classes :forward-chaining)

(defun weak-hpp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (weak-hol-typep (cdr x) t)))

(defun hp-value (p)
; Hp-value is a function instead of macro so that it can be disabled.
  (declare (xargs :guard (weak-hpp p)))
  (car p))

(defun hp-type (p)
; Hp-type is a function instead of macro so that it can be disabled.
  (declare (xargs :guard (weak-hpp p)))
  (cdr p))

(defun weak-hp-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (weak-hpp (car x))
                (weak-hp-listp (cdr x))))))

(defthm hp-listp-forward-to-weak-hp-listp

; This is a nice rule but we don't need it for type-match.

  (implies (and (hp-listp obj-lst hta)
                (symbol-alistp hta))
           (weak-hp-listp obj-lst))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Function application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun weak-hpp? (x)

; The value x = nil represents an error.  Otherwise x is intended to be a
; value/type pair.

  (declare (xargs :guard t))
  (or (weak-hpp x)
      (null x)))

(defund hap (f x) ; "hol apply"
  (declare (xargs :guard (and (weak-hpp? f)
                              (weak-hpp? x))))
  (cond
   ((or (null f) (null x))
    nil) ; propagate error from iterated hap calls; see hap*
   (t
    (let ((fval (hp-value f))
          (xval (hp-value x))
          (ftype (hp-type f))
          (xtype (hp-type x)))
      (cond
       ((and (and (consp ftype)
                  (eq (car ftype) :arrow)) ; (arrow a b); x has type a
             (equal xtype (nth 1 ftype)))
        (cons (apply fval xval)
              (nth 2 ftype)))
       (t ; ill-typed function application: error
        nil))))))

(defun hap*-fn (fn arg1 args)
  (declare (xargs :guard (true-listp args)))
  (cond ((endp args)
         `(hap ,fn ,arg1))
        (t (hap*-fn `(hap ,fn ,arg1) (car args) (cdr args)))))

(defmacro hap* (fn arg1 &rest args)

; Example:
; ACL2 !>:trans1 (hap* 'foo 'a 'b 'c)
;  (HAP (HAP (HAP 'FOO 'A) 'B) 'C)
; ACL2 !>

  (hap*-fn fn arg1 args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic support for primitives
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section defines ACL2 functions that operate on hol-pairs (hp objects).
; See the book primitives.lisp for related actual HOL objects with prefix "hol"
; rather than "hp".

; Warning: Keep these in sync with the table hol-arities in terms.lisp.

(defun hp-comma (x y)

; For hol pairs x and y, (hp-comma x y) is (x,y), i.e., the hol pair of
; appropriate type whose value is the cons of the fp-values of x and y.

  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y))))
  (make-hp (cons (hp-value x) (hp-value y))
           (list :hash (hp-type x) (hp-type y))))

(defun hp-none (type)
  (declare (xargs :guard (weak-hol-typep type t)))
  (make-hp :none
           (list :option type)))

(defun hp-some (x)

; For hol pair x, (hp-some x) is the hol pair whose value is of the form
; (:some . x) and whose type is appropriate based on the type of x.

  (declare (xargs :guard (weak-hpp x)))
  (make-hp (cons :some (hp-value x))
           (list :option (hp-type x))))

(defun hp-nil (type)
  (declare (xargs :guard (weak-hol-typep type t)))
  (make-hp 0 ; The empty list is the empty function.
           (list :list type)))

(defun hp-cons (x y)

; For hol pairs x and y, (hp-cons x y) is (x::y), i.e., the hol list of
; appropriate type whose value is the cons of the fp-values of x and y.

; If y:n->s where x \in s, then (x::y):n+1->s by mapping n to x.

  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y))))
  (make-hp (insert (cons (domain (hp-value y)) (hp-value x))
                   (hp-value y))
           (hp-type y)))

(defun hp-num (n)
  (declare (xargs :guard (natp n)))
  (make-hp n :num))

(defun hp-bool (x)
  (declare (xargs :guard (booleanp x)))
  (make-hp x :bool))

(defun hp+ (x y)
  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y)
                              (acl2-numberp (hp-value x))
                              (acl2-numberp (hp-value y)))))
  (make-hp (+ (hp-value x) (hp-value y))
           (hp-type x)))

(defun hp* (x y)
  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y)
                              (acl2-numberp (hp-value x))
                              (acl2-numberp (hp-value y)))))
  (make-hp (* (hp-value x) (hp-value y))
           (hp-type x)))

(defun hp-implies (x y)
  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y))))
  (make-hp (implies (hp-value x) (hp-value y))
           :bool))

(defun hp-and (x y)
  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y))))
  (make-hp (and (hp-value x) (hp-value y) t) ; ensure Boolean
           :bool))

(defun hp-or (x y)
  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y))))
  (make-hp (or (hp-value x) (hp-value y))
           :bool))

(defun hp= (x y)
  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y))))
  (make-hp (equal (hp-value x) (hp-value y))
           :bool))

(defun hp< (x y)
  (declare (xargs :guard (and (weak-hpp x)
                              (weak-hpp y)
                              (rationalp (hp-value x))
                              (rationalp (hp-value y)))))
  (make-hp (< (hp-value x) (hp-value y))
           :bool))

(defun hp-not (p)
  (declare (xargs :guard (weak-hpp p)))
  (make-hp (not (hp-value p))
           :bool))

(defun predicate-typep (typ)
  (declare (xargs :guard t))
  (and (consp typ)
       (eq (car typ) :arrow)
       (eq (cdr typ) :bool)))

(defun hp-forall (p)
  (declare (xargs :guard (and (weak-hpp p)
                              (predicate-typep (hp-type p)))))
  (make-hp (not (in nil (image (hp-value p))))
           :bool))

(defun hp-exists (p)
  (declare (xargs :guard (and (weak-hpp p)
                              (predicate-typep (hp-type p)))))
  (make-hp (in t (image (hp-value p)))
           :bool))

(defun hp-true ()
  (declare (xargs :guard t))
  (make-hp t :bool))

(defun hp-false ()
  (declare (xargs :guard t))
  (make-hp nil :bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; HOL analogues of list car and cdr
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hol-list-typep (x)
  (declare (xargs :guard t))
  (and (weak-hol-typep x t)
       (consp x)
       (eq (car x) :list)))

(defun hol-list-element-type (x)
  (declare (xargs :guard (hol-list-typep x)))
  (cadr x))

(defun hp-list-car (x)

; Returns a weak-hpp if x is a non-empty list, else 0.

  (declare (xargs :guard (and (weak-hpp x)
                              (hol-list-typep (hp-type x)))))
  (let ((fn (hp-value x)))
    (if (and (funp fn)
             (posp (domain fn)))
        (make-hp (apply fn (1- (domain fn)))
                 (hol-list-element-type (hp-type x)))
      0)))

(defun hp-list-cdr (x)
  (declare (xargs :guard (and (weak-hpp x)
                              (hol-list-typep (hp-type x)))))
  (let ((fn (hp-value x))
        (typ (hp-type x)))
    (if (and (funp fn)
             (posp (domain fn)))
        (make-hp (restrict fn (1- (domain fn)))
                 typ)
      (hp-nil (hol-list-element-type typ)))))

(defthmz relation-p-hp-cons
  (implies (relation-p fn)
           (relation-p (union2 fn
                               (pair (cons x1 y1)
                                     (cons x2 y2)))))
  :hints (("Goal"
           :in-theory (disable relation-p-union2)
           :expand ((relation-p (union2 fn
                                        (pair (cons x1 y1)
                                              (cons x2 y2))))))))

(defthmz domain-not-in-domain-lemma
  (implies (and (relation-p fn)
                (in p fn))
           (in (car p) (domain fn)))
  :props (zfc domain$prop)
  :rule-classes nil)

(defthmz domain-not-in-domain
  (implies (and (relation-p fn)
                (in p fn))
           (not (equal (car p) (domain fn))))
  :hints (("Goal"
           :in-theory (disable in-irreflexive IN-IMPLIES-CAR-IN-DOMAIN)
           :use domain-not-in-domain-lemma))
  :props (zfc domain$prop))

(defthmz funp-hp-cons-lemma
  (implies (and (funp fn)
                (natp (domain fn)))
           (let ((fn2 (union2 fn
                              (pair (cons (domain fn) val)
                                    (cons (domain fn) val)))))
             (implies (and (in p1 fn2)
                           (in p2 fn2)
                           (equal (car p1) (car p2)))
                      (equal (equal p1 p2)
                             t))))
  :props (zfc domain$prop))

(defthmz funp-hp-cons
  (implies (and (funp fn)
                (equal dom (domain fn))
                (natp dom))
           (funp (union2 fn
                         (pair (cons dom val)
                               (cons dom val)))))
  :hints (("Goal"
           :expand ((funp (union2 fn
                                  (pair (cons (domain fn) val)
                                        (cons (domain fn) val)))))
           :restrict ((funp-hp-cons-lemma ((fn fn) (val val))))))
  :props (zfc domain$prop))

(defthmz hp-list-car-hp-cons
  (implies (and (force (hol-list-typep (hp-type y)))
                (force (equal (hol-list-element-type (hp-type y))
                              (hp-type x)))
                (force (funp (hp-value y)))
                (force (natp (domain (hp-value y)))))
           (equal (hp-list-car (hp-cons x y))
                  x))
  :hints (("Goal" :in-theory (e/d (n+1-as-union2-reversed)
                                  (ordinal-proper-subset-is-element))))
  :props (zfc domain$prop))

(defthmz hp-list-cdr-hp-cons
  (implies (and (force (hol-list-typep (hp-type y)))
                (force (funp (hp-value y)))
                (force (natp (domain (hp-value y)))))
           (equal (hp-list-cdr (hp-cons x y))
                  y))
  :hints (("Goal" :in-theory (enable n+1-as-union2-reversed)))
  :props (zfc domain$prop restrict$prop))

(defun hp-list-p (x)

; This is a weak predicate.  See also the stronger predicate hp-cons-p, which
; suffices to guarantee the property in hp-cons-hp-list-car-hp-list-cdr.

  (declare (xargs :guard t))
  (and (weak-hpp x)
       (hol-list-typep (hp-type x))))

(defun hp-nil-p (x typ)
  (equal x (hp-nil typ)))

(defthmz hp-list-p-hp-cons
  (implies (and (force (weak-hpp x))
                (force (hp-list-p y)))
           (hp-list-p (hp-cons x y))))

(defthm hp-list-p-hp-nil
  (implies (force (weak-hol-typep type t))
           (hp-list-p (hp-nil type))))

(defun hp-cons-p (x)
  (declare (xargs :guard (weak-hpp x)))
  (and (hol-list-typep (hp-type x))
       (funp (hp-value x))
       (posp (domain (hp-value x)))))

(local (defthm equal-len-hack
         (implies (and (true-listp x)
                       (acl2-numberp n))
                  (equal (equal (+ n (len x)) n)
                         (equal x nil)))))

(defthmz hp-cons-p-cdr
  (implies (and (hp-cons-p x)
                (not (equal (hp-list-cdr x)
                            (hp-nil (hol-list-element-type (hp-type x))))))
           (hp-cons-p (hp-list-cdr x)))
  :hints (("Goal" :expand ((weak-hol-typep (cdr x) t)
                           (weak-hol-typep (caddr x) t))))
  :props (zfc restrict$prop diff$prop domain$prop))

(local
 (defthmz hp-cons-hp-list-car-hp-list-cdr-lemma-1-1-1
   (implies (and (funp fn)
                 (posp (domain fn))
                 (in pair fn))
            (in pair
                (union2 (restrict fn (+ -1 (domain fn)))
                        (pair (cons (+ -1 (domain fn))
                                    (apply fn (+ -1 (domain fn))))
                              (cons (+ -1 (domain fn))
                                    (apply fn (+ -1 (domain fn))))))))
   :hints (("Goal"
            :in-theory (enable subset)
            :cases ((equal (car pair)
                           (1- (domain fn))))))
   :props (zfc domain$prop restrict$prop diff$prop)))

(local
 (defthmz hp-cons-hp-list-car-hp-list-cdr-lemma-1-1
   (implies (and (funp fn)
                 (posp (domain fn)))
            (subset fn
                    (union2 (restrict fn (+ -1 (domain fn)))
                            (pair (cons (+ -1 (domain fn))
                                        (apply fn (+ -1 (domain fn))))
                                  (cons (+ -1 (domain fn))
                                        (apply fn (+ -1 (domain fn))))))))
   :hints (("Goal"
            :in-theory (enable subset)))
   :props (zfc domain$prop restrict$prop diff$prop)))

(local
 (defthmz hp-cons-hp-list-car-hp-list-cdr-lemma-1
   (implies (and (funp fn)
                 (posp (domain fn)))
            (equal (union2 (restrict fn (+ -1 (domain fn)))
                           (pair (cons (+ -1 (domain fn))
                                       (apply fn (+ -1 (domain fn))))
                                 (cons (+ -1 (domain fn))
                                       (apply fn (+ -1 (domain fn))))))
                   fn))
   :hints (("Goal" :in-theory (e/d (extensionality-rewrite)
                                   (subset-x-0))))
   :props (zfc domain$prop restrict$prop diff$prop)))

(defthmz hp-cons-hp-list-car-hp-list-cdr
  (implies (force (hp-cons-p x))
           (equal (hp-cons (hp-list-car x)
                           (hp-list-cdr x))
                  x))
  :hints (("Goal" :in-theory (enable extensionality-rewrite subset)))
  :props (zfc domain$prop restrict$prop diff$prop))

; We leave hp-cons-p enabled to support proofs in ../examples/.
(in-theory (disable hp-cons hp-list-p hp-list-car hp-list-cdr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; HOL analogues of hash car and cdr
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hol-hash-typep (x)
  (declare (xargs :guard t))
  (and (weak-hol-typep x t)
       (consp x)
       (eq (car x) :hash)))

(defun hp-hash-car (x)
  (declare (xargs :guard (and (weak-hpp x)
                              (hol-hash-typep (hp-type x)))))
  (let ((val (hp-value x))
        (typ (hp-type x)))
    (make-hp (ec-call (car val))
             (cadr typ))))

(defun hp-hash-cdr (x)
  (declare (xargs :guard (and (weak-hpp x)
                              (hol-hash-typep (hp-type x)))))
  (let ((val (hp-value x))
        (typ (hp-type x)))
    (make-hp (ec-call (cdr val))
             (caddr typ))))

(defthm hp-hash-car-hp-comma
  (implies (force (weak-hpp x))
           (equal (hp-hash-car (hp-comma x y))
                  x)))

(defthm hp-hash-cdr-hp-comma
  (implies (force (weak-hpp y))
           (equal (hp-hash-cdr (hp-comma x y))
                  y)))

(defun hp-comma-p (x)
  (declare (xargs :guard t))
  (and (weak-hpp x)
       (hol-hash-typep (hp-type x))
       (consp (hp-value x))))

(defthm hp-comma-p-hp-comma
  (implies (and (force (weak-hpp x))
                (force (weak-hpp y)))
           (hp-comma-p (hp-comma x y))))

(defthm hp-comma-hp-hash-car-hp-hash-cdr
  (implies (force (hp-comma-p x))
           (equal (hp-comma (hp-hash-car x)
                            (hp-hash-cdr x))
                  x))
  :hints (("Goal" :expand ((weak-hol-typep (cdr x) t)))))

; We leave hp-comma-p enabled to support proofs in ../examples/.
(in-theory (disable hp-comma hp-hash-car hp-hash-cdr))
