; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "generic-union")

;; The generated events include these books locally, to admit the tree-level
;; definition. Including them here as well makes them dependencies of every
;; book which uses the macro.
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/data/treeset/hash" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/lookup"))
(local (include-book "internal/split"))
(local (include-book "map"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defunion
  :parents (treemap)
  :short "Define a union of @(see treemap)s which combines the values of
          shared keys."
  :long
  (xdoc::topstring
    (xdoc::p
      "The union binds every key of either map. A key bound in only one map
       keeps its value, and a key bound in both is bound to the combination
       of its two values. The definition and its theorems are instances of
       the generic union in @('generic-union.lisp'), so nothing is proved
       anew for each use.")
    (xdoc::p
      "Time complexity: @($O(m\\log(n/m))$), where @($m \\leq n$) are the
       sizes of the two maps, plus the cost of each combination.")
    (xdoc::section
      "General form"
      (xdoc::codeblock
        "(defunion name"
        "  :combine       combine        ; required"
        "  :val-pred      val-pred       ; optional"
        "  :val-set-pred  val-set-pred   ; optional"
        "  :combine-hints hints          ; optional"
        "  :parents       parents        ; optional"
        "  :short         short          ; optional"
        "  :long          long)          ; optional")
      (xdoc::desc
        "@(':combine')"
        (xdoc::p
          "A function symbol of three arguments, or a closed @('lambda')
           expression of three formals. It is called on the key, the value
           in the first map, and the value in the second map. A @('lambda')
           is defined as the enabled function @('<name>-combine'). The
           generated functions have no guard on the values, so the
           combination must be guard-verified for arbitrary values (e.g., by
           fixing them)."))
      (xdoc::desc
        "@(':val-pred') and @(':val-set-pred')"
        (xdoc::p
          "A predicate on values, and its check over a @(see
           acl2::treeset). They are given together or not at all. The set
           check must be defined as @(tsee treeset::set-all-genericp) is,
           with @(':val-pred') in place of @('treeset::genericp'). When they
           are given, the combination must preserve @(':val-pred'), and the
           union of maps whose values satisfy it is generated."))
      (xdoc::desc
        "@(':combine-hints')"
        (xdoc::p
          "Hints for the proof that the combination preserves
           @(':val-pred'). Only allowed with @(':val-pred')."))
      (xdoc::desc
        "@(':parents'), @(':short'), @(':long')"
        (xdoc::p
          "Documentation for the generated union.")))
    (xdoc::section
      "Generated events"
      (xdoc::ul
        (xdoc::li
          "@('<name>-combine'), when @(':combine') is a @('lambda').")
        (xdoc::li
          "@('tree-<name>'), the union on the implementation trees.")
        (xdoc::li
          "@('<name>'), the union on @(see treemap)s, which is inlined.")
        (xdoc::li
          "Theorems about @('<name>'): its return type, congruences,
           @(tsee emptyp), @(tsee keys), and @(tsee lookup) of it, its value
           with an empty argument, and, with @(':val-set-pred'), the value
           type of the union.")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defunion-sym ((prefix stringp)
                      (name symbolp)
                      (suffix stringp))
  :mode :program
  (intern-in-package-of-symbol
    (concatenate 'string prefix (symbol-name name) suffix)
    name))

(define defunion-combine-p (combine)
  :mode :program
  (or (and (symbolp combine)
           combine)
      (and (true-listp combine)
           (eq (first combine) 'lambda)
           (symbol-listp (second combine))
           (equal (len (second combine)) 3)
           (consp (cddr combine)))))

;; Each theorem is the generic theorem instantiated. The obligations are the
;; definitions of the two functions and, for a typed union, the preservation of
;; the value predicate, which is proved first as the closure lemma. The context
;; is the substitution, the two function names, and the closure lemma, if any.
(define defunion-hints (thm
                        context
                        extra-subst
                        extra-enable)
  :mode :program
  (b* (((list subst tree-name fn closure) context))
    `(("Goal" :by (:functional-instance ,thm ,@subst ,@extra-subst))
      '(:in-theory (enable ,tree-name ,fn ,@extra-enable)
        ,@(and closure `(:use ,closure))))))

;;;;;;;;;;;;;;;;;;;;

(define defunion-fn (name
                     combine
                     val-pred
                     val-set-pred
                     combine-hints
                     parents
                     short
                     long)
  :mode :program
  (b* (((unless (and (symbolp name) name))
        (er hard? 'defunion "The name must be a symbol, but is ~x0." name))
       ((unless (defunion-combine-p combine))
        (er hard? 'defunion
            "The :combine argument must be a function symbol or a lambda ~
             expression of three formals, but is ~x0." combine))
       ((unless (and (symbolp val-pred)
                     (symbolp val-set-pred)
                     (iff val-pred val-set-pred)))
        (er hard? 'defunion
            "The :val-pred and :val-set-pred arguments must be symbols, ~
             given together or not at all, but are ~x0 and ~x1."
            val-pred val-set-pred))
       ((when (and combine-hints (not val-pred)))
        (er hard? 'defunion
            "The :combine-hints argument is only allowed with :val-pred."))
       ;; A lambda is defined as an enabled function. The theorems then
       ;; mention it by name, as their functional instances do, where the
       ;; lambda itself would be beta-reduced in the instances.
       (combine-fn (if (symbolp combine)
                       combine
                     (defunion-sym "" name "-COMBINE")))
       (tree-name (defunion-sym "TREE-" name ""))
       (fn (defunion-sym "" name "$INLINE"))
       (closure (defunion-sym "" name "-COMBINE-PRESERVES-VAL-PRED"))
       (when-emptyp-of-arg1 (defunion-sym "" name "-WHEN-EMPTYP-OF-ARG1"))
       (when-emptyp-of-arg2 (defunion-sym "" name "-WHEN-EMPTYP-OF-ARG2"))
       (subst `((generic-union ,fn)
                (tree-generic-union ,tree-name)
                (generic-combine ,combine-fn)
                (treeset::genericp ,(or val-pred '(lambda (v) t)))))
       (context (list subst tree-name fn (and val-pred closure)))
       (xdoc (append (and parents `(:parents ,parents))
                     (and short `(:short ,short))
                     (and long `(:long ,long)))))
    `(encapsulate ()
       (local (include-book "kestrel/utilities/ordinals" :dir :system))
       (local (include-book "kestrel/data/treeset/hash" :dir :system))
       (local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
       (local
         (include-book "kestrel/data/treemap/internal/lookup" :dir :system))
       (local (include-book "kestrel/data/treemap/internal/split" :dir :system))
       (local (include-book "kestrel/data/treemap/map" :dir :system))

       ,@(and (not (symbolp combine))
              `((define ,combine-fn ,(second combine)
                  ,@(cddr combine)
                  :enabled t)))

       ,@(and val-pred
              `((local
                  (defthm ,closure
                    (implies (and (,val-pred x)
                                  (,val-pred y))
                             (,val-pred (,combine-fn key x y)))
                    :rule-classes nil
                    ,@(and combine-hints `(:hints ,combine-hints))))))

       (define ,tree-name
         ((x treep)
          (y treep))
         :returns (tree treep)
         (cond ((tree-empty-p x)
                (tree-fix y))
               ((tree-empty-p y)
                (tree-fix x))
               ((heap<-with-tree-element (tree->head x) (tree->head y))
                (mv-let (assoc left right)
                        (tree-split (tree-element->key (tree->head y)) x)
                  (let ((head
                          (if assoc
                              (tree-element
                                (tree-element->hash (tree->head y))
                                (tree-element->key (tree->head y))
                                (,combine-fn
                                  (tree-element->key (tree->head y))
                                  (cdr assoc)
                                  (tree-element->val (tree->head y))))
                            (tree->head y))))
                    (tree-node head
                               (,tree-name left (tree->left y))
                               (,tree-name right (tree->right y))))))
               (t
                (mv-let (assoc left right)
                        (tree-split (tree-element->key (tree->head x)) y)
                  (let ((head
                          (if assoc
                              (tree-element
                                (tree-element->hash (tree->head x))
                                (tree-element->key (tree->head x))
                                (,combine-fn
                                  (tree-element->key (tree->head x))
                                  (tree-element->val (tree->head x))
                                  (cdr assoc)))
                            (tree->head x))))
                    (tree-node head
                               (,tree-name (tree->left x) left)
                               (,tree-name (tree->right x) right))))))
         :measure (+ (acl2-count x)
                     (acl2-count y))
         :verify-guards :after-returns
         :guard-hints (("Goal" :in-theory (enable tree-element
                                                  tree-element-p))))

       (define ,name
         ((x mapp)
          (y mapp))
         (declare (xargs :type-prescription :none))
         ,@xdoc
         :returns (map mapp
                       :hints ,(defunion-hints 'mapp-of-generic-union
                                               context nil nil))
         (,tree-name (fix x) (fix y))
         :inline t
         :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

       (defruled ,(defunion-sym "" name "-TYPE-PRESCRIPTION")
         (or (consp (,name x y))
             (equal (,name x y) nil))
         :rule-classes :type-prescription
         :hints ,(defunion-hints 'generic-union-type-prescription
                                 context nil nil))

       (add-to-ruleset break-abstraction
                       '(,(defunion-sym "" name "-TYPE-PRESCRIPTION")))

       (defrule ,(defunion-sym "" name "-WHEN-EQUIV-OF-ARG1-CONGRUENCE")
         (implies (equiv x0 x1)
                  (equal (,name x0 y)
                         (,name x1 y)))
         :rule-classes :congruence
         :hints ,(defunion-hints 'generic-union-when-equiv-of-arg1-congruence
                                 context nil nil))

       (defrule ,(defunion-sym "" name "-WHEN-EQUIV-OF-ARG2-CONGRUENCE")
         (implies (equiv y0 y1)
                  (equal (,name x y0)
                         (,name x y1)))
         :rule-classes :congruence
         :hints ,(defunion-hints 'generic-union-when-equiv-of-arg2-congruence
                                 context nil nil))

       (defrule ,(defunion-sym "EMPTYP-OF-" name "")
         (equal (emptyp (,name x y))
                (and (emptyp x)
                     (emptyp y)))
         :hints ,(defunion-hints 'emptyp-of-generic-union
                                 context nil nil))

       (defrule ,(defunion-sym "KEYS-OF-" name "")
         (equal (keys (,name x y))
                (treeset::union (keys x)
                                (keys y)))
         :hints ,(defunion-hints 'keys-of-generic-union
                                 context nil nil))

       (defrule ,(defunion-sym "LOOKUP-OF-" name "")
         (equal (lookup key (,name x y) :default default)
                (if (treeset::in key (keys x))
                    (if (treeset::in key (keys y))
                        (,combine-fn key
                                     (lookup key x)
                                     (lookup key y))
                      (lookup key x :default default))
                  (lookup key y :default default)))
         :hints ,(defunion-hints 'lookup-of-generic-union
                                 context nil nil))

       (defruled ,when-emptyp-of-arg1
         (implies (emptyp x)
                  (equal (,name x y)
                         (fix y)))
         :hints ,(defunion-hints 'generic-union-when-emptyp-of-arg1
                                 context nil nil))

       (defrule ,(defunion-sym "" name "-WHEN-EMPTYP-OF-ARG1-CHEAP")
         (implies (emptyp x)
                  (equal (,name x y)
                         (fix y)))
         :rule-classes ((:rewrite :backchain-limit-lst (0)))
         :by ,when-emptyp-of-arg1)

       (defrule ,(defunion-sym "" name "-OF-EMPTY")
         (equal (,name (empty) y)
                (fix y))
         :enable ,when-emptyp-of-arg1)

       (defruled ,when-emptyp-of-arg2
         (implies (emptyp y)
                  (equal (,name x y)
                         (fix x)))
         :hints ,(defunion-hints 'generic-union-when-emptyp-of-arg2
                                 context nil nil))

       (defrule ,(defunion-sym "" name "-WHEN-EMPTYP-OF-ARG2-CHEAP")
         (implies (emptyp y)
                  (equal (,name x y)
                         (fix x)))
         :rule-classes ((:rewrite :backchain-limit-lst (0)))
         :by ,when-emptyp-of-arg2)

       (defrule ,(defunion-sym "" name "-OF-ARG1-AND-EMPTY")
         (equal (,name x (empty))
                (fix x))
         :enable ,when-emptyp-of-arg2)

       ,@(and val-set-pred
              `((defrule ,(defunion-sym (concatenate 'string
                                                     (symbol-name val-set-pred)
                                                     "-OF-VALUES-OF-")
                                        name
                                        "")
                  (implies (and (,val-set-pred (values x))
                                (,val-set-pred (values y)))
                           (,val-set-pred (values (,name x y))))
                  :hints ,(defunion-hints
                            'set-all-genericp-of-values-of-generic-union
                            context
                            `((treeset::set-all-genericp ,val-set-pred))
                            `(,val-set-pred))))))))

;;;;;;;;;;;;;;;;;;;;

(defmacro defunion (name
                    &key
                    combine
                    val-pred
                    val-set-pred
                    combine-hints
                    parents
                    short
                    long)
  (defunion-fn name
               combine
               val-pred
               val-set-pred
               combine-hints
               parents
               short
               long))
