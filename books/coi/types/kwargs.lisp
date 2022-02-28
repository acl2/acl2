;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "TYPES")
(include-book "type-fty")

(defun remove-list (x y)
  (declare (type (satisfies true-listp) y))
  (if (not (consp x)) y
    (let ((y (remove-equal (car x) y)))
      (remove-list (cdr x) y))))

(def::un extract-keyword-value (key default kvlist)
  (declare (xargs :signature ((keywordp t keyword-value-listp) t keyword-value-listp)))
  (if (not (consp kvlist)) (mv default nil)
    (if (equal key (car kvlist))
        (mv (cadr kvlist) (cddr kvlist))
      (mv-let (val rst) (extract-keyword-value key default (cddr kvlist))
        (mv val (list* (car kvlist) (cadr kvlist) rst))))))

(defun keyword-listp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (and (keywordp (car x))
         (keyword-listp (cdr x)))))

(defthm keyword-listp-implies-true-listp
  (implies
   (keyword-listp x)
   (true-listp x))
  :rule-classes (:forward-chaining))

(def::un keyword-value-list-keys (kvlist)
  (declare (xargs :signature ((keyword-value-listp) keyword-listp)))
  (if (not (consp kvlist)) nil
    (let ((key (car kvlist)))
      (cons key (keyword-value-list-keys (cddr kvlist))))))

(def::und allowed-keys (keys kvlist)
  (declare (xargs :signature ((keyword-listp keyword-value-listp) booleanp)))
  (and (subsetp (keyword-value-list-keys kvlist) keys)
       t))

(def::und allowed-keys-guard (keys rest)
  (declare (xargs :signature ((keyword-listp keyword-value-listp) booleanp)))
  (assert! (allowed-keys keys rest) ("The provided key(s) ~x0 are not included among allowed keys ~x1" (remove-list keys (keyword-value-list-keys rest)) keys) :value t))

(defun kwargs-alistp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (let ((entry (car x)))
      (and (and (consp entry)
                (keywordp (car entry))
                (consp (cdr entry))
                ;;(null (cddr entry)))
                )
           (kwargs-alistp (cdr x))))))

(def::signature append (kwargs-alistp kwargs-alistp) kwargs-alistp)

(def::un keyword-value-list-to-keyword-alist (kvlist)
  (declare (xargs :signature ((keyword-value-listp) kwargs-alistp)))
  (if (not (consp kvlist)) nil
    (cons (list (car kvlist) (cadr kvlist))
          (keyword-value-list-to-keyword-alist (cddr kvlist)))))

(def::un keyword-alist-to-keyword-value-list (kwargs)
  (declare (xargs :signature ((kwargs-alistp) keyword-value-listp)))
  (if (not (consp kwargs)) nil
    (let ((entry (car kwargs)))
      (list*
       (car entry)
       (cadr entry)
       (keyword-alist-to-keyword-value-list (cdr kwargs))))))

(defun key-default-alistp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (let ((entry (car x)))
      (and (and (consp entry)
                (symbolp (car entry))
                (consp (cdr entry))
                ;;(null (cddr entry))
                )
           (key-default-alistp (cdr x))))))

(def::signature append (key-default-alistp key-default-alistp) key-default-alistp)

(defthm kwargs-alistp-implies-symbol-alispt
  (implies
   (kwargs-alistp x)
   (key-default-alistp x))
  :rule-classes (:forward-chaining))

(defthm key-default-alistp-implies-alistp
  (implies
   (key-default-alistp x)
   (alistp x))
  :rule-classes (:forward-chaining))

(def::und enkey (s)
  (declare (xargs :signature ((t) keywordp)
                  :guard (symbolp s)))
  (let ((zed (intern-in-package-of-symbol (symbol-name s) :a)))
    (if (keywordp zed) zed
      :a)))

(def::un enkey-symbol-list (x)
  (declare (xargs :signature ((symbol-listp) keyword-listp)))
  (if (not (consp x)) nil
    (cons (enkey (car x))
          (enkey-symbol-list (cdr x)))))

(def::un alist-keys (alist)
  (declare (xargs :signature ((alistp) true-listp)))
  (if (not (consp alist)) nil
    (let ((entry (car alist)))
      (cons (car entry)
            (alist-keys (cdr alist))))))

(def::signature alist-keys (key-default-alistp) symbol-listp)
(def::signature alist-keys (kwargs-alistp) keyword-listp)

(def::un unassoc-key (key kwargs)
  (declare (xargs :signature ((keywordp kwargs-alistp) kwargs-alistp)))
  (if (not (consp kwargs)) nil
    (let ((entry (car kwargs)))
      (if (equal key (car entry))
          (unassoc-key key (cdr kwargs))
        (cons entry (unassoc-key key (cdr kwargs)))))))

(def::un unassoc-key-list (klist kwargs)
  (declare (xargs :signature ((keyword-listp kwargs-alistp) kwargs-alistp)))
  (if (not (consp klist)) kwargs
    (let ((kwargs (unassoc-key (car klist) kwargs)))
      (unassoc-key-list (cdr klist) kwargs))))

;; ===================================================================
;;
;; We use this only with the &key b*-binder.
;;
(def::un assoc-keyword? (key default kwargs)
  (declare (xargs :signature ((keywordp t kwargs-alistp) t)))
  (if (not (consp kwargs)) default
    (let ((entry (car kwargs)))
      (if (equal key (car entry)) (cadr entry)
        (assoc-keyword? key default (cdr kwargs))))))

(def::un assoc-keyword! (key kwargs)
  (declare (xargs :signature ((keywordp kwargs-alistp) t)))
  (if (not (consp kwargs)) (assert! nil ("key ~x0 not bound in kwargs" key) :value nil)
    (let ((entry (car kwargs)))
      (if (equal key (car entry)) (cadr entry)
        (assoc-keyword! key (cdr kwargs))))))

(defun key-witness-alistp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (and (and (consp entry)
                (symbolp (car entry))
                (consp (cdr entry))
                (quotep (cadr entry))
                (null (cddr entry)))
           (key-witness-alistp (cdr list))))))

(def::un key-default-bindings (opt type-p list value)
  (declare (xargs :signature ((booleanp symbolp key-witness-alistp t) true-listp)))
  (if (not (consp list)) nil
    (let ((entry (car list)))
      (let ((key     (car entry))
            (default (cadr entry)))
        (let ((assoc (if opt `(assoc-keyword? ,(enkey key) ,default ,value)
                       `(assoc-keyword! ,(enkey key) ,value))))
          (cons `(,key (let ((,key ,assoc)) (if (,type-p ,key)
                                                ,key
                                              (assert! nil ("Value ~x0 for key ~x1 does not satisfy ~x2" ,key ',(enkey key) ',type-p) :value ,default))))
                (key-default-bindings opt type-p (cdr list) value)))))))

(def::un key-default-keys (list)
  (declare (xargs :signature ((key-witness-alistp) keyword-listp)))
  (if (not (consp list)) nil
    (let ((entry (car list)))
      (let ((key (car entry)))
        (cons (enkey key)
              (key-default-keys (cdr list)))))))

(defun &opt-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (and (and (consp entry)
                (symbolp (car entry))
                (consp (cdr entry))
                (if (quotep (cadr entry))
                    (null (cddr entry))
                  (key-witness-alistp (cdr entry))))
           (&opt-listp (cdr list))))))

(def::un &opt-bindings (list value)
  (declare (xargs :signature ((&opt-listp t) true-listp)
                  :guard-hints ((and stable-under-simplificationp
                                     '(:expand (&opt-listp list))))))
  (if (not (consp list)) nil
    (let ((entry (car list)))
      (let ((key     (car entry))
            (default (cadr entry)))
        (if (quotep default)
            (cons `(,key (assoc-keyword? ,(enkey key) ,default ,value))
                  (&opt-bindings (cdr list) value))
          (append
           (key-default-bindings t key (cdr entry) value)
           (&opt-bindings (cdr list) value)))))))

(def::un &opt-keys (list)
  (declare (xargs :signature ((&opt-listp) keyword-listp)))
  (if (not (consp list)) nil
    (let ((entry (car list)))
      (let ((key     (car entry))
            (default (cadr entry)))
        (if (quotep default)
            (cons (enkey key) (&opt-keys (cdr list)))
          (append
           (key-default-keys (cdr entry))
           (&opt-keys (cdr list))))))))

(defun &key-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (if (symbolp entry)
          (if (equal entry 'acl2::&opt)
              (&opt-listp (cdr list))
            (&key-listp (cdr list)))
        (and (consp entry)
             (symbolp (car entry))
             (consp (cdr entry))
             (key-witness-alistp (cdr entry))
             (&key-listp (cdr list)))))))

(def::un &key-bindings (list value)
  (declare (xargs :signature ((&key-listp t) true-listp)))
  (if (not (consp list)) nil
    (let ((entry (car list)))
      (if (symbolp entry)
          (if (equal entry 'acl2::&opt)
              (&opt-bindings (cdr list) value)
            (cons `(,entry (assoc-keyword! ,(enkey entry) ,value))
                  (&key-bindings (cdr list) value)))
        (append
         (key-default-bindings nil (car entry) (cdr entry) value)
         (&key-bindings (cdr list) value))))))

(def::un &key-keys (list)
  (declare (xargs :signature ((&key-listp) keyword-listp)))
  (if (not (consp list)) nil
    (let ((entry (car list)))
      (if (consp entry)
          (append
           (key-default-keys (cdr entry))
           (&key-keys (cdr list)))
        (if (equal entry 'acl2::&opt)
            (&opt-keys (cdr list))
          (cons (enkey entry) (&key-keys (cdr list))))))))

(defun &xxx-listp (list)
  (declare (type t list))
  (and (consp list)
       (or (and (equal (car list) 'acl2::&key)
                (&key-listp (cdr list)))
           (and (equal (car list) 'acl2::&opt)
                (&opt-listp (cdr list))))))

(defun &rest-listp (args)
  (declare (type t args))
  (and (consp args)
       (symbolp (car args))
       (&xxx-listp (cdr args))))

;; &rest x &key a (symbolp (b 'nil)) c &opt (a 'nil) (b 'fred)

;; Sadly we cannot really do the type checking thing
;; the way I wanted. ie: deduce type-p and type-fix
;; from a type-spec (because we don't have a type-spec)
;;
;; What we can do, however, is require the user to
;; provide a default value that does satisfy the type.
;;
;; The challenge is how to mix this with op
;; 
;;
;; (symbolp 'x (a nil) b)
;; (symbolp (a 'nil) (b 0))

(def::und &xxx-bindings (list value)
  (declare (xargs :signature ((&xxx-listp t) true-listp)))
  (let ((key (car list)))
    (if (equal key 'acl2::&key)
        (&key-bindings (cdr list) value)
      (&opt-bindings (cdr list) value))))

(def::und &xxx-keys (list)
  (declare (xargs :signature ((&xxx-listp) keyword-listp)))
  (let ((key (car list)))
    (if (equal key 'acl2::&key)
        (&key-keys (cdr list))
      (&opt-keys (cdr list)))))

(def::und &rest-bindings (list value)
  (declare (xargs :signature ((&rest-listp t) true-listp)))
  (let* ((var (car list))
         (bindings (&xxx-bindings (cdr list) value))
         (keys     (&xxx-keys     (cdr list))))
    `(,@bindings
      (,var (unassoc-key-list ',keys ,value)))))

(defmacro acl2::patbind-&opt (args value rst)
  (declare (type (satisfies &opt-listp) args)
           (type (satisfies consp) value))
  `(let ,(&opt-bindings args (car value))
     ,rst))

(defmacro acl2::patbind-&key (args value rst)
  (declare (type (satisfies &key-listp) args)
           (type (satisfies consp) value))
  `(let ,(&key-bindings args (car value))
     ,rst))

(defmacro acl2::patbind-&rest (args value rst)
  (declare (type (satisfies &rest-listp) args)
           (type (satisfies consp) value))
  `(let ,(&rest-bindings args (car value))
     ,rst))

;; ===================================================================

(def::un key-default-alistp-to-kwargs-alistp (alist)
  (declare (xargs :signature ((key-default-alistp) kwargs-alistp)))
  (if (not (consp alist)) nil
    (let ((entry (car alist)))
      (let ((key   (enkey (car entry)))
            (value (cdr entry)))
        (acons key value (key-default-alistp-to-kwargs-alistp (cdr alist)))))))

(defun add-type-p (x)
  (declare (type t x))
  (or (equal x nil)
      (equal x :drop)
      (equal x t)))
;;
;; You have a new key.  You can just add it or not.
;;
;;                                 | assoc | not assoc | I'd like to come up with a new name for 'add' so we could say:
;;                                 +-------+-----------+
;; add = :drop : ignore new keys   |  add  |   ignore  | :ignore
;; add = nil   : error on new keys |  add  |   error   | :error
;; add = t     : add new keys      |  add  |    add    | nil
;;                                 +-------+-----------+
;;
(def::und update-defaults (kwargs defaults add ctx)
  (declare (xargs :signature ((kwargs-alistp kwargs-alistp add-type-p symbolp) kwargs-alistp)))
  (if (not (consp kwargs)) defaults
    (let ((entry (car kwargs)))
      (let ((key   (car entry))
            (value (cdr entry)))
        (if (and (not (assoc key defaults)) (not (equal add t)))
            (prog2$
             (assert! add ("The set of allowed keys ~x0 does not include ~x1" (alist-keys defaults) key) :context ctx)
             (update-defaults (cdr kwargs) defaults add ctx))
          (let ((defaults (unassoc-key key defaults)))
            (let ((defaults (acons key value defaults)))
              (update-defaults (cdr kwargs) defaults add ctx))))))))

(def::und kwargs-fn (defaults kvlist add)
  (declare (xargs :signature ((key-default-alistp keyword-value-listp add-type-p) kwargs-alistp)))
  (let ((kwargs   (keyword-value-list-to-keyword-alist kvlist))
        (defaults (key-default-alistp-to-kwargs-alistp defaults)))
    (update-defaults kwargs defaults add 'kwargs)))

;; kwargs should be used in the macro definition.
;; It will map the kvlist over the defaults and return a kwargs.
(defmacro kwargs (defaults kvlist &key (add 'nil))
  `(kwargs-fn ,defaults ,kvlist ,add))

(def::und keep-fn (defaults kwargs kvlist)
  (declare (xargs :signature ((key-default-alistp kwargs-alistp keyword-value-listp) kwargs-alistp)))
  (let ((defaults  (key-default-alistp-to-kwargs-alistp defaults))
        (newkwargs (keyword-value-list-to-keyword-alist kvlist)))
    ;; Update defaults with any associated values in kwargs
    (let ((defaults (update-defaults kwargs defaults :drop 'keep)))
      ;; Update the result with any kv args
      (update-defaults newkwargs defaults nil 'keep))))

;; keep will update the defaults with the relevenat bindings in kwargs
(defmacro keep (defaults kwargs &rest kvlist)
  `(keep-fn ,defaults ,kwargs (list ,@kvlist)))

(def::und update-fn (kwargs kvlist add ctx)
  (declare (xargs :signature ((kwargs-alistp keyword-value-listp add-type-p symbolp) kwargs-alistp)))
  (let ((newkwargs (keyword-value-list-to-keyword-alist kvlist)))
    (update-defaults newkwargs kwargs add ctx)))

;; Update updating bindings already bound in kwargs.
(defmacro update (kwargs &rest kvlist)
  ;; Since we are 'updating' we require the keys to be in kwargs
  `(update-fn ,kwargs (list ,@kvlist) nil 'update))

;; Extend the bindings in kwargs
(defmacro extend (kwargs &rest kvlist)
  ;; Expand kwargs with kvlist
  `(update-fn ,kwargs (list ,@kvlist) t 'update))

(def::und kvlist-fn (kwargs kvlist)
  (declare (xargs :signature ((kwargs-alistp keyword-value-listp) keyword-value-listp)))
  ;; We allow kvlist to expand the domain 
  (let ((kwargs (update-fn kwargs kvlist t 'kvlist)))
    (keyword-alist-to-keyword-value-list kwargs)))

;; kwlist will flatten kwargs for use in a subsequent macro call,
;; updating the keys bound in kvlist.
(defmacro kvlist (kwargs &rest kvlist)
  `(kvlist-fn ,kwargs (list ,@kvlist)))

;; ===================================================================

(defun check-keywords (default kwargs)
  (declare (type (satisfies key-default-alistp) default)
           (type (satisfies kwargs-alistp) kwargs))
  (let ((xkeys (enkey-symbol-list (alist-keys default)))
        (ykeys (alist-keys kwargs)))
    (let ((diff (remove-list xkeys ykeys)))
      (if diff
          (assert! nil ("Surplus keys ~x0" diff) :value kwargs)
        (let ((diff (remove-list ykeys xkeys)))
          (if diff
              (assert! nil ("Missing keys ~x0" diff) :value kwargs)
            kwargs))))))

(defthm check-keywords-identity
  (equal (check-keywords default kwargs)
         kwargs))

(in-theory (disable check-keywords))

;; ===================================================================

(def::und type-predicate-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `((define-predicate   t)
    (type-name        nil)
    (guard            nil)
    (non-executable   nil)
    (doc              nil)
    (body             nil)
    (and              nil)
    (or               nil)
    (disable-type-p     t)
    (define-in-theory nil)
    ))

(def::und type-property-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `(
    (prove-properties      t   "Prove the standard properties")
    (negative-rules        nil "Rewrite rules to establish the negation of the predicate")
    (positive-rules        t   "Rewrite rules to establish the positive of the predicate")
    (rewrite               nil "Enable rewriting to establish elements of a conjunct")
    (type-prescription     nil "Enable type-prescription rules to establish elements of a conjunct [not recommended]")
    (forward-chain         t   "Permit the use of forward-chaining")
    (forward-chain-or      nil "Forward chain disjunctions")
    (forward-chain-and     t   "Forward chain conjunctions")
    (forward-chain-body    nil "Trigger on conjuncts to forward chain the predicate")
    (forward-chain-cases   t   "Forward chain the individual cases of an 'or' hypothesis")
    (tau-system            nil "Employ tau reasoning for rewrite-like rules [not recommended]")
    (prove-in-theory       nil "Theory in which to prove these properties")
    ))

(def::und def-type-property-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  (type-property-keywords))

(def::und type-fix-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `((args            '(x))
    (type-p           nil)
    (fix              nil)
    (fix!             nil)
    (type-witness     nil)
    (open-fix-default nil)
    (prefer-guarded   nil)
    (non-executable   nil)
    (disable-fix      t)
    (fix-signature    t)
    (fix-in-theory    nil)
    ))

(def::und type-equiv-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `((type-p               nil   "The type predicate name")
    (fix                  nil   "The (preferred) type fixer name")
    (equiv                nil   "The type equivalence name")
    (guarded              nil   "Generate a guarded equivalence relation")
    (equality             equal "The eqivalence to use to compare the fixing functions")
    (reduce-equiv         nil   "Reduce equiv to equal when arguments satisfy type-p")
    (equal-fix-rule-class :forward-chaining
                                "Rule class(es) to use for the equal fix rules nil/:all/:rewrite/:forward-chaining")
    (equiv-in-theory      nil   "Theory in which to prove the equivalence relation properties")
    ))

(def::und def-type-equiv-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  (type-equiv-keywords))

(def::und type-refinement-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `(
    (refines                 nil   "List of type names refined by the new type")
    (extends                 nil   "List of type names extended by the new type")
    (xequiv                  equal "Equivalence relation")
    ;;
    ;; We should probably denote this as "predicate refinement"
    ;;
    (refines-type-in-theory  nil   "Theory in which to prove type refinement")
    (refines-equiv-in-theory nil   "Theory in which to prove equivalence refinement")
    (type-refinement-lemma   nil   "Generate type refinement lemmas")
    ))

(def::und def-type-refinement-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  (append (type-property-keywords)
          (type-refinement-keywords)))

(def::und type-list-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `(
    (list-name  nil "Generic list type name")
    (listp      nil "List type predicate")
    (list-fix   nil "List type fixing function (potentially guarded)")
    (list-fix!  nil "List type fixing function (unguarded)")
    (list-equiv nil "List type equivalence relation")
    ;; I think this may be standard ..
    ;;(refine-list-equiv t "Prove that new list refines (true-)list-equiv")
    ))

(def::und def-type-list-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  (append (type-list-keywords) (type-refinement-keywords)))
   
(def::und def-type-predicate-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `(,@(type-predicate-keywords)
    ,@(type-property-keywords)
    ,@(type-refinement-keywords)
    ))

(def::und def-type-fix-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  (type-fix-keywords))

(def::und def-type-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `(,@(type-predicate-keywords)
    ,@(type-property-keywords)
    ,@(type-fix-keywords)
    (fix-constants t "Generate fixing rules for constants")
    ,@(type-equiv-keywords)
    ,@(type-list-keywords)
    (type-list    nil "Type name for a list of type-p")
    (list-extends nil "List of type names extended by listp")
    (list-refines nil "List of type names refined by listp")
    ,@(type-refinement-keywords)
    ))

(def::un def-type-str-refinement-keywords ()
  (declare (xargs :signature (() key-default-alistp)))
  `((fields  nil )
    (refines nil )
    (root    nil )
    ,@(type-fix-keywords)
    ))

