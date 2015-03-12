
(in-package "FTY")

(include-book "deftypes")
(include-book "tools/templates" :dir :system)

(defun my-intern (string sym)
  (intern-in-package-of-symbol
   string
   (if (equal (symbol-package-name sym) "COMMON-LISP")
       'acl2::asdfo
     sym)))
(program)

(defun search-deftypes-types (type-name types)
  (if (atom types)
      nil
    (or (with-flextype-bindings (x (car types))
          (and (eq type-name x.name) x))
        (search-deftypes-types type-name (cdr types)))))

(defun search-deftypes-table (type-name table)
  ;; Returns (mv flextypes-obj type-obj) where type-obj describes either a sum,
  ;; list, or alist type, and flextypes-obj contains the type-obj and any other
  ;; types created in its mutual-recursion.
  (if (atom table)
      (mv nil nil)
    (let ((type (search-deftypes-types type-name (flextypes->types (cdar table)))))
      (if type
          (mv (cdar table) ;; info for whole deftypes form
              type) ;; info for this type
        (search-deftypes-table type-name (cdr table))))))

;; (search-deftypes-table 'vl::vl-expr (table-alist 'flextypes-table (w state)))

  
(def-primitive-aggregate visitorspec
  (name       ;; Base name of the visitor.  Functions will be named <name>-<type>.
   formals    ;; Formals, with special case (varname :object) signifies the current object.
   returns    ;; Returns, with special case (retname :update) signifies updated object.
   accum-vars ;; Alist mapping accumulator formals to returns.
   join-vars  ;; Alist mapping return vars to alternate vars, used in join bindings
   type-fns   ;; Alist mapping field types to visitor function names, :skip to skip.
   field-fns  ;; Alist mapping field names to visitor function names or :skip,
              ;; overriding type-fns.
   prod-fns   ;; Alist mapping product names to alists mapping field names to
              ;; visitor functions or :skip, overriding field-fns.
   initial    ;; Bindings for non-update return values when there are no fields.
   join       ;; Bindings for non-update return values in terms of their current values
              ;; and the joinvar.
   xvar       ;; The varname from the formals.
   fnname-template ;; Symbol, template using substring <TYPE> to
                   ;; describe how to generate visitor function names
   renames    ;; alist mapping type names to non-default visitor function names
   wrld))

(defun visitor-return-binder-aux (returns fldname firstp x)
  (if (atom returns)
      nil
    (b* (((visitorspec x))
         ((mv name type)
          (if (consp (car returns))
              (b* (((list name type) (car returns)))
                (mv name type))
            (mv (car returns) nil)))
         (accum (rassoc-eq name x.accum-vars))
         (name (if (eq type :update)
                   fldname
                 (if accum
                     (car accum)
                   (if firstp
                       name
                     (cdr (assoc name x.join-vars)))))))
      (cons name
            (visitor-return-binder-aux (cdr returns) fldname firstp x)))))

(defun visitor-return-binder (returns fldname firstp x)
  (b* ((returns (if (and (consp returns)
                         (eq (car returns) 'mv))
                    (cdr returns)
                  (list returns)))
       (lst (visitor-return-binder-aux returns fldname firstp x)))
    (if (eql (len returns) 1)
        (car lst)
      (cons 'mv lst))))
          
(defun visitor-name (x type)
  (b* (((visitorspec x))
       (look (assoc type x.renames)))
    (if look
        (cadr look)
      (if x.fnname-template
          (acl2::tmpl-sym-sublis `(("<TYPE>"    . ,(symbol-name type)))
                                 x.fnname-template x.name)
        (acl2::tmpl-sym-sublis `(("<TYPE>"    . ,(symbol-name type))
                                 ("<VISITOR>"    . ,(symbol-name x.name)))
                               '<VISITOR>-<TYPE> x.name)))))

(defun visitor-normalize-fixtype (type wrld)
  (b* (((visitorspec x))
       (fty (find-fixtype-for-pred type (get-fixtypes-alist wrld))))
    (if fty
        (fixtype->name fty)
      type)))



       

(defun visitor-field-fn (fldname fldtype prod x)
  (b* (((visitorspec x))
       (fldtype (visitor-normalize-fixtype fldtype x.wrld))
       (prod-fns (and prod (cdr (assoc prod x.prod-fns))))
       (prod-fld (and fldname (assoc fldname prod-fns)))
       ((when prod-fld) (if (eq (cdr prod-fld) :skip)
                            nil
                          (cdr prod-fld)))
       (fld      (assoc fldname x.field-fns))
       ((when fld)      (if (eq (cdr fld) :skip)
                            nil
                          (cdr fld)))
       (type     (assoc fldtype x.type-fns))
       ((when type)     (if (eq (cdr type) :skip)
                            nil
                          (cdr type))))
    nil))
       


(defun visitor-prod-field-joins (fields x prodname firstp)
  (b* (((visitorspec x) x)
       ((when (atom fields))
        (if firstp
            ;; no fields -- return the initial values
            (mv nil x.initial)
          (mv nil nil)))
       ((flexprod-field fld) (car fields))
       (fnname    (visitor-field-fn fld.name fld.type prodname x))
       ((unless fnname)
        (visitor-prod-field-joins (cdr fields) x prodname firstp))
       ((mv rest-changes rest-bindings)
        (visitor-prod-field-joins (cdr fields) x prodname nil)))
    (mv `(,(intern$ (symbol-name fld.name) "KEYWORD")
          ,fld.name
          . ,rest-changes)
        `((,(visitor-return-binder x.returns fld.name firstp x)
           (,fnname . ,(subst (my-intern
                               (concatenate 'string (symbol-name x.xvar) "."
                                            (symbol-name fld.name))
                               x.xvar)
                              x.xvar
                              (strip-cars x.formals))))
          ,@(and (not firstp) x.join)
          . ,rest-bindings))))
         

(defun visitor-return-values-aux (returns update x)
  (if (atom returns)
      nil
    (b* (((visitorspec x))
         ((mv name type)
          (if (consp (car returns))
              (b* (((list name type) (car returns)))
                (mv name type))
            (mv (car returns) nil)))
         (accum (rassoc-eq name x.accum-vars)))
      (cons (if (eq type :update)
                update
              (if accum
                  (car accum)
                name))
            (visitor-return-values-aux (cdr returns) update x)))))

(defun visitor-return-values (returns update x)
  (b* ((returns (if (and (consp returns)
                         (eq (car returns) 'mv))
                    (cdr returns)
                  (list returns)))
       (lst (visitor-return-values-aux returns update x)))
    (if (eql (len returns) 1)
        (car lst)
      (cons 'mv lst))))
  


(defun visitor-prod-body (prod x)
  (b* (((flexprod prod))
       ((visitorspec x))
       ((mv changer-args bindings)
        (visitor-prod-field-joins prod.fields x prod.type-name t)))
    `(b* (,@bindings)
       ,(visitor-return-values
         x.returns
         `(,(std::da-changer-name prod.type-name)
           ,x.xvar ,@changer-args)
         x))))

(defun visitor-prod-def (type x mrec)
  (b* (((flexsum type))
       ((visitorspec x))
       ((flexprod prod) (car type.prods))
       (name (visitor-name x type.name)))
    `(define ,name ,(subst type.pred :object x.formals)
       ,@(and type.count `(:measure (,type.count ,x.xvar)))
       :returns ,(subst type.pred :update x.returns)
       :verify-guards nil
       (b* (((,prod.ctor-name ,x.xvar) (,type.fix ,x.xvar)))
         ,(visitor-prod-body prod x))
       ///
       ,@(and (not mrec) `((verify-guards ,name))))))

(defun visitor-prod-bodies (prods x)
  (if (atom prods)
      nil
    (b* (((flexprod prod) (car prods)))
      `(,prod.kind
        ,(visitor-prod-body prod x)
        . ,(visitor-prod-bodies (cdr prods) x)))))
      
 

(defun visitor-sum-def (type x mrec)
  (b* (((flexsum type))
       ((when (eql (len type.prods) 1))
        (visitor-prod-def type x mrec))
       ((visitorspec x))
       (name (visitor-name x type.name)))
    `(define ,name ,(subst type.pred :object x.formals)
       ,@(and type.count `(:measure (,type.count ,x.xvar)))
       :returns ,(subst type.pred :update x.returns)
       :verify-guards nil
       (,type.case ,x.xvar
         . ,(visitor-prod-bodies type.prods x))
       ///
       ,@(and (not mrec) `((verify-guards ,name))))))
                        



(defun visitor-list-def (type x mrec)
  (b* (((flexlist type))
       ((visitorspec x))
       (name (visitor-name x type.name))
       (elt-fnname (visitor-field-fn nil type.elt-type nil x))
       ((unless elt-fnname)
        (er hard? 'defvisitor "Nothing to do for list type ~x0 -- use :skip." type.name)))
    `(define ,name ,(subst type.pred :object x.formals)
       ,@(if type.count
             `(:measure (,type.count ,x.xvar))
           `(:measure (len ,x.xvar)))
       :returns ,(subst type.pred :update x.returns)
       :verify-guards nil
       (b* (((when (atom ,x.xvar))
             (b* (,@x.initial)
               ,(visitor-return-values x.returns
                                       (if type.true-listp nil x.xvar)
                                       x)))
            (,(visitor-return-binder x.returns 'car t x)
             (,elt-fnname . ,(subst `(car ,x.xvar)
                                x.xvar
                                (strip-cars x.formals))))
            (,(visitor-return-binder x.returns 'cdr nil x)
             (,name . ,(subst `(cdr ,x.xvar)
                              x.xvar
                              (strip-cars x.formals))))
            ,@x.join)
         ,(visitor-return-values
           x.returns `(cons car cdr) x))
       ///
       ,@(and (not mrec) `((verify-guards ,name))))))

(defun visitor-alist-def (type x mrec)
  (b* (((flexalist type))
       ((visitorspec x))
       (name (visitor-name x type.name))
       (key-fnname (visitor-field-fn nil type.key-type nil x))
       (val-fnname (visitor-field-fn nil type.val-type nil x))
       ((unless (or key-fnname val-fnname))
        (er hard? 'defvisitor "Nothing to do for alist type ~x0 -- use :skip." type.name)))
    `(define ,name ,(subst type.pred :object x.formals)
       ,@(if type.count
             `(:measure (,type.count ,x.xvar))
           `(:measure (len (,type.fix ,x.xvar))))
       :returns ,(subst type.pred :update x.returns)
       :verify-guards nil
       (b* ((,x.xvar (,type.fix ,x.xvar))
            ((when (atom ,x.xvar))
             (b* (,@x.initial)
               ,(visitor-return-values x.returns
                                       (if type.true-listp nil x.xvar)
                                       x)))
            ,@(and key-fnname
                   `((,(visitor-return-binder x.returns 'key t x)
                      (,key-fnname . ,(subst `(caar ,x.xvar)
                                             x.xvar
                                             (strip-cars x.formals))))))
            ,@(and val-fnname
                   `((,(visitor-return-binder x.returns 'val (not key-fnname) x)
                      (,val-fnname . ,(subst `(cdar ,x.xvar)
                                             x.xvar
                                             (strip-cars x.formals))))
                     ,@(and key-fnname x.join)))
            (,(visitor-return-binder x.returns 'cdr nil x)
             (,name . ,(subst `(cdr ,x.xvar)
                              x.xvar
                              (strip-cars x.formals))))
            ,@x.join)
         ,(visitor-return-values
           x.returns
           `(cons (cons ,(if key-fnname 'key `(caar ,x.xvar))
                        ,(if val-fnname 'val `(cdar ,x.xvar)))
                  cdr)
           x))
       ///
       ,@(and (not mrec) `((verify-guards ,name))))))


(defun visitor-def (type x mrec)
  (with-flextype-bindings type
    (visitor-*-def type x mrec)))


(defun visitor-omit-bound-types (types type-fns)
  ;; If the type is bound to :skip, then we're not defining a visitor for that
  ;; type.  If it's bound to a function name, then that function should be
  ;; defined by hand (separately or in the mutual recursion).
  (if (atom types)
      nil
    (b* ((name (with-flextype-bindings (x (car types)) x.name))
         (look (assoc name type-fns)))
      (if (cdr look)
          (visitor-omit-bound-types (cdr types) type-fns)
        (cons (car types) (visitor-omit-bound-types (cdr types) type-fns))))))


(defun visitor-mutual-aux (types x)
  (if (atom types)
      nil
    (cons (visitor-def (car types) x t)
          (visitor-mutual-aux (cdr types) x))))

(defun visitor-mutual (type-name types x other-fns)
  (b* (((visitorspec x)))
  `(defines ,(visitor-name x type-name)
     ,@other-fns
     ,@(visitor-mutual-aux types x)
     ///
     (verify-guards ,(visitor-name x
                                   (with-flextype-bindings (type (car types))
                                     type.name))))))

(defun visitor-add-type-fns (types x)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (type (car types))
            (cons type.name
                  (visitor-name x type.name)))
          (visitor-add-type-fns (cdr types) x))))


;; (defun visitor-define (x type-name type-table other-fns)
;;   (b* ((fty (cdr (assoc type-name type-table)))
;;        ((flextypes fty))
;;        ((visitorspec x))
;;        (types (visitor-omit-bound-types fty.types x.type-fns))
;;        (new-type-fns (append (visitor-add-type-fns types x.name) x.type-fns))
;;        (x (change-visitorspec x :type-fns new-type-fns))
;;        ((when (and (eql (len types) 1)
;;                    (atom other-fns)))
;;         (visitor-single (car types) x)))
;;     (visitor-mutual type-name types x other-fns)))


(defun visitor-parse-return (x)
  ;; Produces (mv return accums initials joins joinvars) based on parsing of retarg
  ;; for return variable name.  Also returns modified x.
  ;; The three possibilities we'll deal with are:
  ;;    (retname :update)
  ;; --- signifies the updated version of the object; we basically leave this be.

  ;;    (retname (:join jointerm :tmp-var joinvar :initial initial) type-stuff)
  ;; --- signifies that this is a joined variable; we add appropriate stuff to
  ;; the initials/joins/joinvars and strip the joinspec out.

  ;;    (retname (:acc formal [:fix fixterm]) type-stuff)
  ;; --- signifies that this is a returned accumulator; we add its pairing to
  ;; accums and strip the accspec out.

  (b* (((when (atom x))
        (er hard? 'defvisitor-template
            "Bad return entry ~x0" x)
        (mv x nil nil nil nil))
       ((list* name retarg rest) x)
       ((when (eq retarg :update))
        (mv x nil nil nil nil))
       ((when (atom retarg))
        (er hard? 'defvisitor-template
            "Bad return entry ~x0" x)
        (mv x nil nil nil nil)))
    (case (car retarg)
      (:join (case-match retarg
               ((':join jointerm ':tmp-var joinvar ':initial initial)
                (mv (cons name rest)
                    nil
                    (list (list name initial))
                    (list (list name jointerm))
                    (list (cons name joinvar))))
               (& (prog2$
                   (er hard? 'defvisitor-template
                       "Bad return entry ~x0" x)
                   (mv x nil nil nil nil)))))
      (:acc  (case-match retarg
               ((':acc formal)
                (mv (cons name rest)
                    (list (cons formal name))
                    nil nil nil))
               ((':acc formal ':fix term)
                (mv (cons name rest)
                    (list (cons formal name))
                    (list (list formal term))
                     nil nil))
               (& (prog2$
                   (er hard? 'defvisitor-template
                       "Bad return entry ~x0" x)
                   (mv x nil nil nil nil)))))
      (otherwise
       (prog2$
        (er hard? 'defvisitor-template
            "Bad return entry ~x0" x)
        (mv x nil nil nil nil))))))

(defun visitor-parse-returns-aux (returns)
  ;; returns: (mv stripped-returns accums initials joins joinvars)
  (b* (((when (atom returns))
        (mv nil nil nil nil nil))
       ((mv rest accums initials joins joinvars)
        (visitor-parse-returns-aux (cdr returns)))
       ((mv return1 accums1 initials1 joins1 joinvars1)
        (visitor-parse-return (car returns))))
    (mv (cons return1 rest)
        (append accums1 accums)
        (append initials1 initials)
        (append joins1 joins)
        (append joinvars1 joinvars))))

(defun visitor-parse-returns (returns)
  (b* ((returns (if (and (consp returns)
                         (eq (car returns) 'mv))
                    (cdr returns)
                  (list returns)))
       ((mv rets accums initials joins joinvars)
        (visitor-parse-returns-aux returns)))
    (mv (if (eql (len returns) 1)
            (car rets)
          (cons 'mv rets))
        accums initials joins joinvars)))

(defun visitor-xvar-from-formals (formals)
  (if (atom formals)
      (er hard? 'defvisitor-template
          "No input was designated the :object of the visitor")
    (if (and (consp (car formals))
             (eq (cadar formals) :object))
        (caar formals)
      (visitor-xvar-from-formals (cdr formals)))))

(defun visitor-symbol/fn-doubletonlist-p (x)
  (if (atom x)
      (eq x nil)
    (case-match x
      (((name fn) . rest)
       (and name fn
            (symbolp name)
            (or (symbolp fn)
                (and (consp fn) (eq (car fn) 'lambda)))
            (visitor-symbol/fn-doubletonlist-p rest)))
      (& nil))))

(defun visitor-symbol/fn-doubletonlist-alist-p (x)
  (if (atom x)
      (eq x nil)
    (case-match x
      (((name . alist) . rest)
       (and name (symbolp name)
            (visitor-symbol/fn-doubletonlist-p alist)
            (visitor-symbol/fn-doubletonlist-alist-p rest)))
      (& nil))))

(defun visitor-doubletonlist-to-alist (x)
  (if (atom x)
      nil
    (cons (cons (caar x) (cadar x))
          (visitor-doubletonlist-to-alist (cdr x)))))

(defun visitor-doubletonlist-alist-to-alist (x)
  (if (atom x)
      nil
    (cons (cons (caar x)
                (visitor-doubletonlist-to-alist (cdar x)))
          (visitor-doubletonlist-alist-to-alist (cdr x)))))

(defun visitor-normalize-type-fns (type-fns wrld)
  (if (atom type-fns)
      nil
    (cons (cons (visitor-normalize-fixtype (caar type-fns) wrld)
                (cdar type-fns))
          (visitor-normalize-type-fns (cdr type-fns) wrld))))
        
(defconst *defvisitor-template-keys*
  '(:returns :type-fns :field-fns :prod-fns :parents :short :long
    :fnname-template))

(defun visitor-process-fnspecs (kwd-alist wrld)
  (b* ((type-fns (cdr (assoc :type-fns kwd-alist)))
       (- (or (visitor-symbol/fn-doubletonlist-p type-fns)
              (er hard? 'visitor "Bad type-fns -- see ~x0"
                  'visitor-symbol/fn-doubletonlist-p)))
       (type-fns (visitor-normalize-type-fns
                  (visitor-doubletonlist-to-alist type-fns) wrld))

       (field-fns (cdr (assoc :field-fns kwd-alist)))
       (- (or (visitor-symbol/fn-doubletonlist-p field-fns)
              (er hard? 'visitor "Bad field-fns -- see ~x0"
                  'visitor-symbol/fn-doubletonlist-p)))
       (field-fns (visitor-doubletonlist-to-alist field-fns))

       (prod-fns (cdr (assoc :prod-fns kwd-alist)))
       (- (or (visitor-symbol/fn-doubletonlist-alist-p prod-fns)
              (er hard? 'visitor "Bad prod-fns -- see ~x0"
                  'visitor-symbol/fn-doubletonlist-alist-p)))
       (prod-fns (visitor-doubletonlist-alist-to-alist prod-fns)))
    (mv type-fns field-fns prod-fns)))


(defun visitor-check-fnname-template (x)
  (or (not x)
      (and (symbolp x)
           (search "<TYPE>" (symbol-name x)))
      (er hard? 'defvisitor-template
          "fnname-template should be a symbol whose name contains the ~
           substring <TYPE>")))

(defun defvisitor-template-main (name args wrld)
  (b* (((mv kwd-alist rest)
        (extract-keywords 'defvisitor-template *defvisitor-template-keys* args nil))
       ((unless (eql (len rest) 1))
        (er hard? 'defvisitor-template
            "The only non-keyword argument after the name should be the formals."))
       (formals (car rest))
       (returns (cdr (assoc :returns kwd-alist)))
       
       ((mv type-fns field-fns prod-fns)
        (visitor-process-fnspecs kwd-alist wrld))

       ((mv stripped-returns accums initials joins joinvars)
        (visitor-parse-returns returns))

       (fnname-template (cdr (assoc :fnname-template kwd-alist)))
       (- (visitor-check-fnname-template fnname-template))
       (x (make-visitorspec
           :name name
           :formals formals
           :returns stripped-returns
           :accum-vars accums
           :join-vars joinvars
           :type-fns type-fns
           :field-fns field-fns
           :prod-fns prod-fns
           :initial initials
           :join joins
           :fnname-template fnname-template
           :xvar (visitor-xvar-from-formals formals))))
    x))

(defun defvisitor-template-fn (name args)
  `(table visitor-templates ',name
          (defvisitor-template-main ',name ',args world)))

(defmacro defvisitor-template (name &rest args)
  (defvisitor-template-fn name args))



(defconst *defvisitor-keys*
  '(:type :template :type-fns :field-fns :prod-fns
    :fnname-template :renames
    :parents :short :long))


(defun defvisitor-fn (args wrld)
  (b* (((mv name args)
        (if (and (symbolp (car args))
                 (not (keywordp (car args))))
            (mv (car args) (cdr args))
          (mv nil args)))
       ((mv pre-/// post-///) (std::split-/// 'defvisitor args))
       ((mv kwd-alist mrec-fns)
        (extract-keywords 'defvisitor *defvisitor-keys* pre-/// nil))
       (template (cdr (assoc :template kwd-alist)))
       (type (cdr (assoc :type kwd-alist)))
       ((unless (and template type))
        (er hard? 'defvisitor ":type and :template arguments are mandatory"))

       (x1 (cdr (assoc template (table-alist 'visitor-templates wrld))))
       ((unless x1)
        (er hard? 'defvisitor "Template ~x0 wasn't defined" template))
       ((mv type-fns field-fns prod-fns)
        (visitor-process-fnspecs kwd-alist wrld))

       ((visitorspec x1))
       (x1.type-fns (append type-fns x1.type-fns))
       (x1.field-fns (append field-fns x1.field-fns))
       (x1.prod-fns (append prod-fns x1.prod-fns))

       (fty (cdr (assoc type (table-alist 'flextypes-table wrld))))
       ((unless fty)
        (er hard? 'defvisitor "Type ~x0 not found" type))
       ((flextypes fty))
       (types (visitor-omit-bound-types fty.types x1.type-fns))

       (fnname-template (or (cdr (assoc :fnname-template kwd-alist))
                            x1.fnname-template))
       (- (visitor-check-fnname-template fnname-template))
       (renames (cdr (assoc :renames kwd-alist)))
       (x1-with-renaming (change-visitorspec x1 :fnname-template fnname-template
                                             :renames renames))
       (new-type-fns (append (visitor-add-type-fns types x1-with-renaming)
                             x1.type-fns))

       ;; this will be the visitorspec that we store in the table afterward; we
       ;; assume the renamings are temporary.
       (x (change-visitorspec x1 :type-fns new-type-fns
                              :field-fns x1.field-fns
                              :prod-fns x1.prod-fns))

       (local-x
        (change-visitorspec x :wrld wrld
                            :fnname-template fnname-template
                            :renames renames))
       (event-name (or name (visitor-name local-x type)))
       (def (if (and (eql (len types) 1)
                     (atom mrec-fns))
                (visitor-def (car types) local-x nil)
              (visitor-mutual type types local-x mrec-fns))))
    `(defsection-progn ,event-name
       ,(append def post-///)
       (table visitor-templates ',template ',x))))

(defmacro defvisitor (&rest args)
  `(make-event
    (defvisitor-fn ',args (w state))))






