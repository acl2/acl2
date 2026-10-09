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

(include-book "hol-zify") ; no_port

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Hol types, type alists, and values
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; An hta is an alist associating type names, which are keywords, with cons
; pairs of the form (s . arguments), where arguments is a list of distinct
; variables each representing a type.  When arguments is nil, s is the set of
; values corresponding to the type.  But otherwise, s is a set-theoretic
; function, whose curried application to the arguments produces a set.

; An hta (HOL type alist) maps keywords to ordered pairs (cons set arity).
; Note that when an hta contains a type constructor with positive arity, then
; it is not in V_omega, since that type constructor has a domain containing a
; set for each ground type.  But ground types are in V_omega.

(include-book "hta")

(defun assoc-hta (name hta)

; This function could have a weaker guard of t, or a stronger guard that also
; requires (symbol-alistp hta) or even (and (alistp hta) (keyword-listp
; (strip-cars hta)).  We may choose later to weaken or strengthen the guard.

  (declare (xargs :guard (symbolp name)))
  (hons-assoc-equal name hta))

(defun hol-typep-flg (flg x hta)

; This function defines our representation of hol type expressions.  Hta is a
; hol type-alist or nil, wheree nil is suitable if we are only checking that
; the structure of x is reasonable for hol type-alists extending (hta0).  Flg
; is nil if x is a single ground type expression; otherwise x is a list of
; those.

  (declare (xargs :guard t))
  (cond
   (flg (cond ((atom x) (null x))
              (t (and (hol-typep-flg nil (car x) hta)
                      (hol-typep-flg t (cdr x) hta)))))
   ((atom x)
    (and (keywordp x)
         (let ((pair (assoc-hta x (or hta (hta0)))))
           (if pair
               (let ((val (cdr pair)))
                 (and (consp val)
                      (eql (cdr val) 0) ; arity 0

; We consider an hta entry to be invalid when it maps to the empty set, because
; types are supposed to be non-empty.

                      (not (equal (car val) 0))))
             (null hta)))))
   ((keywordp (car x))
    (and (let ((pair (assoc-hta (car x) (or hta (hta0)))))
           (if pair
               (let ((val (cdr pair)))
                 (and (consp val)
                      (posp (cdr val)) ; positive arity
                      (eql (len (cdr x)) (cdr val))))
             (and (null hta)
                  (cdr x))))
         (hol-typep-flg t (cdr x) hta)))
   (t nil)))

(defun hol-typep (type hta)
  (declare (xargs :guard t))
  (hol-typep-flg nil type hta))

(defun hol-type-listp (type hta)
  (declare (xargs :guard t))
  (hol-typep-flg t type hta))

(defun weak-hol-typep (type)
  (declare (xargs :guard t))
  (hol-typep-flg nil type nil))

(defun weak-hol-type-listp (type)
  (declare (xargs :guard t))
  (hol-typep-flg t type nil))

(defun hol-type-eval-flg (flg x hta)

; For flg=nil, this function returns the set value of the given ground type, x,
; with respect to hta, a hol type-alist.  We complete to a total function by
; returning the empty set, 0, if x is ill-formed with respect to hta.  If flg
; is non-nil then x is a list of ground types and we return 0 if any is
; ill-formed, else a list of their values.

  (declare (xargs :guard (if flg
                             (hol-type-listp x hta)
                           (hol-typep x hta))))
  (cond
   (flg (cond ((endp x) nil)
              (t (let ((fst (hol-type-eval-flg nil (car x) hta))
                       (rst (hol-type-eval-flg t (cdr x) hta)))
                   (cond ((or (equal fst 0)
                              (equal rst 0))
                          0)
                         (t (cons fst rst)))))))
   ((not (mbt (hol-typep x hta)))
    0)
   ((keywordp x)
    (let ((pair (assoc-hta x hta)))
      (cond
       (pair
        (assert$
         (consp pair)
         (let ((val (cdr pair)))
           (cond
            ((or (atom val)                 ; ill-formed hta
                 (not (equal (cdr val) 0))) ; not arity 0
             0)
            (t (car val))))))
       (t 0))))
   ((and (true-listp x)
         (consp (cdr x)) ; at least one argument
         (keywordp (car x)))
    (let ((pair (assoc-hta (car x) hta)))
      (cond
       (pair
        (assert$
         (consp pair)
         (let ((val (cdr pair)))
           (cond
            ((and (consp val)
                  (equal (length (cdr x)) (cdr val)))
             (let ((vals (hol-type-eval-flg t (cdr x) hta)))
               (if (equal vals 0)
                   0
                 (apply (car val) vals))))
            (t 0)))))
       (t 0))))
   (t 0)))

(defun hol-type-eval (type hta)
  (declare (xargs :guard (hol-typep type hta)))
  (hol-type-eval-flg nil type hta))

(defun hol-type-eval-lst (lst hta)
  (declare (xargs :guard (hol-type-listp lst hta)))
  (hol-type-eval-flg t lst hta))

(defun hol-valuep (x type hta)

; This function recognizes when x is a hol value of the given hol ground type
; with respect to a give association of atomic type names with sets.

  (declare (xargs :guard (hol-typep type hta)))
  (in x (hol-type-eval type hta)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Hol types and pairs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The acronym "hp" stands for "hol-pair", a cons whose cdr is a hol ground type
; and whose car is a hol value of that type.

(defun hpp (p hta)
  (declare (xargs :guard t))
  (and (consp p)
       (hol-typep (cdr p) hta)
       (hol-valuep (car p) (cdr p) hta)))

(defmacro make-hp (value type)
  `(cons ,value ,type))

(defun hp-listp (x hta)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (hpp (car x) hta)
                (hp-listp (cdr x) hta)))))

; Some of the lemmas below may have been developed in support of the admission
; of the obsolete function type-match and lemmas about it.  But they are
; reasonable lemmas, so we keep them here.

(defthm weak-hol-type-listp-forward-to-true-listp
  (implies (weak-hol-type-listp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defthm weak-hol-typep-impliest-weak-hol-type-listp-cdr
; This sped up (verify-guards type-match ...) tremendously.
  (implies (and (weak-hol-typep x)
                (not (keywordp x)))
           (weak-hol-type-listp (cdr x))))

(local (defthm len-strip-cdrs
         (equal (len (strip-cdrs x))
                (len x))))

; Avoid, for example, attempting to evaluate (omega) on behalf of
; (hol-typep-flg nil :list nil)
(in-theory (disable hta0 (:e hta0) (:e hol-typep-flg)))

(defthmz hol-typep-flg-forward-to-weak-hol-typep-flg
  (implies (and (hol-typep-flg flg x hta)
                (alist-subsetp (hta0) hta))
           (hol-typep-flg flg x nil))
  :rule-classes :forward-chaining)

(defthmz hol-typep-forward-to-weak-hol-typep
  (implies (and (hol-typep x hta)
                (alist-subsetp (hta0) hta))
           (weak-hol-typep x))
  :rule-classes :forward-chaining)

(defthmz hol-type-listp-forward-to-weak-hol-type-listp
  (implies (and (hol-type-listp x hta)
                (alist-subsetp (hta0) hta))
           (weak-hol-type-listp x))
  :rule-classes :forward-chaining)

(defun weak-hpp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (weak-hol-typep (cdr x))))

; Some lemmas that may be useful when hpp and weak-hpp are disabled.

(defthmz hpp-forward-to-weak-hpp
  (implies (and (hpp x hta)
                (alist-subsetp (hta0) hta))
           (weak-hpp x))
  :rule-classes :forward-chaining)

(defthm hpp-forward
  (implies (hpp x hta)
           (and (consp x)
                (hol-typep (cdr x) hta)
                (hol-valuep (car x) (cdr x) hta)))
  :rule-classes :forward-chaining)

; value and type

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
  (hp-listp x nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Function application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun weak-hpp? (x)

; The value x = nil represents an error.  Otherwise x is intended to be a
; value/type pair.

  (declare (xargs :guard t))
  (or (weak-hpp x)
      (null x)))

(defthm hol-typep-flg-t-forward-to-true-listp
  (implies (and (hol-typep-flg flg x hta)
                flg)
           (true-listp x))
  :rule-classes :forward-chaining)

(defthm weak-hol-typep-forward-to-true-listp-or-symbolp
  (implies (weak-hol-typep x)
           (or (true-listp x)
               (symbolp x)))
  :rule-classes :forward-chaining)

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
        (make-hp (apply fval xval)
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
  (declare (xargs :guard (weak-hol-typep type)))
  (make-hp :none
           (list :option type)))

(defun hp-some (x)

; For hol pair x, (hp-some x) is the hol pair whose value is of the form
; (:some . x) and whose type is appropriate based on the type of x.

  (declare (xargs :guard (weak-hpp x)))
  (make-hp (cons :some (hp-value x))
           (list :option (hp-type x))))

(defun hp-nil (type)
  (declare (xargs :guard (weak-hol-typep type)))
  (make-hp 0 ; The empty list is the empty function.
           (list :list type)))

(defun hp-cons (x y)

; For hol pairs x and y, (hp-cons x y) is [x::y], i.e., the hol list of
; appropriate type whose value is the cons of the fp-values of x and y.

; If y:n->s where x \in s, then [x::y]:n+1->s by mapping n to x.

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

(defun function-typep (typ)
  (declare (xargs :guard (weak-hol-typep typ)))
  (and (consp typ)
       (eq (car typ) :arrow)))

(defun hp-dom (typ)
  (declare (xargs :guard (and (zfc)
                              (weak-hol-typep typ)
                              (function-typep typ))))
  (nth 1 typ))

(defun hp-ran (typ)
  (declare (xargs :guard (and (zfc)
                              (weak-hol-typep typ)
                              (function-typep typ))))
  (nth 2 typ))

(defun predicate-typep (typ)
  (declare (xargs :guard (and (zfc)
                              (weak-hol-typep typ))))
  (and (function-typep typ)
       (eq (hp-ran typ) :bool)))

(defun hp-forall (p)
  (declare (xargs :guard (and (zfc)
                              (weak-hpp p)
                              (predicate-typep (hp-type p)))))
  (make-hp (not (in nil (image (hp-value p))))
           :bool))

(defun hp-exists (p)
  (declare (xargs :guard (and (zfc)
                              (weak-hpp p)
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
  (and (weak-hol-typep x)
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
  :hints (("Goal" :in-theory (enable n+1-as-union2-reversed)))
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

(defthmz in-0-v-omega*2
  (in 0 (v-omega*2))
  :props (zfc v$prop v-omega+$prop
              domain$prop prod2$prop inverse$prop))

; Start proof of hol-type-eval-flg-in-v-omega*2.

(defthm hol-type-in-v-omega*2-atom-case
  (implies (and (equal (cddr (hons-assoc-equal x hta))
                       0)
                (htap1 hta))
           (in (cadr (hons-assoc-equal x hta))
               (v-omega*2))))

(defthm member-0-hol-type-eval-flg-t
  (implies (member-equal 0 (hol-type-eval-flg t x hta))
           (equal (hol-type-eval-flg t x hta) 0)))

(defthm hol-type-eval-flg-t-type-prescription
  (or (equal (hol-type-eval-flg t x hta) 0)
      (true-listp (hol-type-eval-flg t x hta)))
  :rule-classes :type-prescription)

(defthm len-hol-type-eval-flg
  (equal (len (hol-type-eval-flg t x hta))
         (if (equal (hol-type-eval-flg t x hta) 0)
             0
           (len x))))

(local
 (defthmz hol-type-in-v-omega*2-lemma
   (implies (and (equal (len (cdr x))
                        (cddr (hons-assoc-equal (car x) hta)))
                 (not (equal (hol-type-eval-flg t (cdr x) hta)
                             0))
                 (in (hol-type-eval-flg t (cdr x) hta)
                     (v-omega*2))
                 (htap1 hta)
                 (< 0 (len (cdr x))))
            (in (apply (cadr (hons-assoc-equal (car x) hta))
                       (hol-type-eval-flg t (cdr x) hta))
                (v-omega*2)))
   :hints (("goal" :use ((:instance
                          hol-constructor-p-necc
                          (constructor (cadr (hons-assoc-equal (car x) hta)))
                          (x (hol-type-eval-flg t (cdr x) hta))
                          (arity (cddr (hons-assoc-equal (car x) hta)))))
            :in-theory (disable hol-constructor-p-necc)))
   :props (hta-prop)))

(defthmz hol-type-eval-flg-in-v-omega*2
  (implies (and (htap1 hta)
                (hol-typep-flg flg x hta))
           (in (hol-type-eval-flg flg x hta)
               (v-omega*2)))
  :props (hta-prop))

(local (defthm hol-type-eval-flg-non-empty-lemma
         (implies (and (equal (len (cdr x))
                              (cddr (hons-assoc-equal (car x) hta)))
                       (htap1 hta)
                       (< 0 (len (cdr x))))
                  (hol-constructor-p (cadr (hons-assoc-equal (car x) hta))
                                     (len (cdr x))))))

(local (defthm not-member-0-hol-type-eval-flg-t
         (implies (not (equal (hol-type-eval-flg t x hta)
                              0))
                  (not (member 0 (hol-type-eval-flg t x hta))))))

(defthmz hol-type-eval-flg-non-empty
  (implies (and (htap hta)
                (hol-typep-flg flg x hta))
           (not (equal (hol-type-eval-flg flg x hta)
                       0)))
  :hints (("Goal" :restrict ((hol-constructor-p-necc
                              ((arity (cddr (hons-assoc-equal (car x) hta))))))))
  :props (hta-prop))

(defthmz hol-type-eval-list
  (implies (and (htap htp)
                (hol-typep x htp)
                (equal (car x) :list))
           (equal (hol-type-eval x htp)
                  (finseqs (hol-type-eval (cadr x) htp))))
  :hints (("Goal" :expand ((hol-typep-flg nil x htp))))
  :props (hta-prop))

(defthmz hp-list-p-hp-cons
  (implies (force (hp-list-p y))
           (hp-list-p (hp-cons x y)))
  :hints (("Goal" :in-theory (enable n+1-as-union2-fold)))
  :props (hta-prop))

(defthmz hp-list-p-hp-nil
  (implies (force (weak-hol-typep type))
           (hp-list-p (hp-nil type)))
  :props (hta-prop))

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
   :hints (("Goal" :in-theory (enable subset)))
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
  :hints (("Goal" :in-theory (e/d (extensionality-rewrite subset)
                                  (subset-x-0))))
  :props (zfc domain$prop restrict$prop diff$prop))

; We leave hp-cons-p enabled to support proofs in ../examples/.
(in-theory (disable hp-cons hp-list-p hp-list-car hp-list-cdr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; HOL analogues of hash car and cdr
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hol-hash-typep (x)
  (declare (xargs :guard t))
  (and (weak-hol-typep x)
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

(defthmz hp-comma-p-hp-comma
  (implies (and (force (weak-hpp x))
                (force (weak-hpp y)))
           (hp-comma-p (hp-comma x y)))
  :props (hta-prop))

(defthm hp-comma-hp-hash-car-hp-hash-cdr
  (implies (force (hp-comma-p x))
           (equal (hp-comma (hp-hash-car x)
                            (hp-hash-cdr x))
                  x)))

; We leave hp-comma-p enabled to support proofs in ../examples/.
(in-theory (disable hp-comma hp-hash-car hp-hash-cdr))
