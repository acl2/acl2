; FTY type support library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

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
   measure    ;; measure template
   fixequivs  ;; prove congruences
   prepwork   ;; template for prepwork, where <type> is substituted
   reversep   ;; reverse order in which fields are processed
   wrapper    ;; wrapper around the body of a function, using :body and <type>
              ;; in template substitutions
   macrop     ;; indicates that this has a macro wrapper
   defines-args ;; extra keyword args to defines
   define-args  ;; extra keyword args to define
   order      ;; topological order ranking for defvisitors under multi
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
         (name (if (or (eq type :update)
                       (eq (car type) :update))
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

(defun visitor-macroname (x type)
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
          
(defun visitor-fnname (x type)
  (b* (((visitorspec x))
       (macroname (visitor-macroname x type)))
    (if x.macrop
        (intern-in-package-of-symbol
         (concatenate 'string (symbol-name macroname) "-FN")
         macroname)
      macroname)))



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
       

(defun visitor-formal-names (formals)
  (strip-cars (std::remove-macro-args 'visitor formals nil)))


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
                              (visitor-formal-names x.formals))))
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
      (cons (if (or (eq type :update)
                    (equal type '(:update)))
                update
              (if (eq (car type) :update)
                  (subst update :update (cadr type))
                (if accum
                    (car accum)
                  name)))
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


(defun visitor-return-decls-aux (returns type-pred type-fix)
  (b* (((when (atom returns)) nil)
       ((list* name rettype rest) (car returns))
       (rest-returns (visitor-return-decls-aux (cdr returns) type-pred type-fix))
       ((when (eq rettype :update))
        (cons (list* name type-pred rest) rest-returns))
       ((when (eq (car rettype) :update))
        (b* ((look (assoc-keyword :type rettype))
             ((unless look)
              (cons (list* name type-pred rest) rest-returns)))
          (cons (list* name (sublis `((:type . ,type-pred)
                                      (:fix . ,type-fix))
                                    (cadr look))
                       rest)
                rest-returns))))
    (cons (cons name rest) rest-returns)))

(defun visitor-return-decls (returns type-name type-pred type-fix)
  (b* ((returns (if (and (consp returns)
                         (eq (car returns) 'mv))
                    (cdr returns)
                  (list returns)))
       (returns (acl2::template-subst-top
                 returns
                 ;; BOZO bad hack
                 (acl2::make-tmplsubst
                  :strs `(("<TYPE>" ,(symbol-name type-name) . ,type-name)))))
       (lst (visitor-return-decls-aux returns type-pred type-fix)))
    (if (eql (len returns) 1)
        (car lst)
      (cons 'mv lst))))
              
    


(defun visitor-prod-subbody (prod x)
  (b* (((flexprod prod))
       ((visitorspec x))
       ((mv changer-args bindings)
        (visitor-prod-field-joins (if x.reversep (reverse prod.fields) prod.fields)
                                  x prod.type-name t)))
    `(b* (,@bindings)
       ,(visitor-return-values
         x.returns
         `(,(std::da-changer-name prod.ctor-name)
           ,x.xvar ,@changer-args)
         x))))


(defun visitor-measure (x default)
  (b* (((visitorspec x)))
    (if x.measure
        (subst x.order :order (subst default :count x.measure))
      default)))

(defun visitor-prod-body (type x)
  (b* (((flexsum type))
       ((visitorspec x))
       ((flexprod prod) (car type.prods)))
    `(b* (((,prod.ctor-name ,x.xvar) (,type.fix ,x.xvar)))
       ,(visitor-prod-subbody prod x))))


(defun visitor-prod-bodies (prods x)
  (if (atom prods)
      nil
    (b* (((flexprod prod) (car prods)))
      `(,prod.kind
        ,(visitor-prod-subbody prod x)
        . ,(visitor-prod-bodies (cdr prods) x)))))
      
 

(defun visitor-sum-body (type x)
  (b* (((flexsum type))
       ((when (eql (len type.prods) 1))
        (visitor-prod-body type x))
       ((visitorspec x)))
    `(,type.case ,x.xvar
       . ,(visitor-prod-bodies type.prods x))))

(defun visitor-sum-measure (type x mrec)
  (b* (((flexsum type))
       ((visitorspec x)))
    (and (or mrec type.recp)
         `(:measure ,(visitor-measure x (if type.count
                                            `(,type.count ,x.xvar)
                                          0))))))
                        


(defun visitor-list-measure (type x mrec)
  (declare (ignorable mrec))
  (b* (((flexlist type))
       ((visitorspec x)))
    `(:measure ,(visitor-measure x (if type.count
                                       `(,type.count ,x.xvar)
                                     `(len ,x.xvar))))))
  


(defun visitor-list-body (type x)
  (b* (((flexlist type))
       ((visitorspec x))
       (name (visitor-fnname x type.name))
       (elt-fnname (visitor-field-fn :elt type.elt-type type.name x))
       (formal-names (visitor-formal-names x.formals))
       ((unless elt-fnname)
        (er hard? 'defvisitor "Nothing to do for list type ~x0 -- use :skip." type.name)))
    `(b* (((when (atom ,x.xvar))
           (b* (,@x.initial)
             ,(visitor-return-values x.returns
                                     (if type.true-listp nil x.xvar)
                                     x)))
          ,@(if x.reversep
                `((,(visitor-return-binder x.returns 'cdr t x)
                   (,name . ,(subst `(cdr ,x.xvar)
                                    x.xvar
                                    formal-names)))
                  (,(visitor-return-binder x.returns 'car nil x)
                   (,elt-fnname . ,(subst `(car ,x.xvar)
                                          x.xvar
                                          formal-names))))
              `((,(visitor-return-binder x.returns 'car t x)
                 (,elt-fnname . ,(subst `(car ,x.xvar)
                                        x.xvar
                                        formal-names)))
                (,(visitor-return-binder x.returns 'cdr nil x)
                 (,name . ,(subst `(cdr ,x.xvar)
                                  x.xvar
                                  formal-names)))))
          ,@x.join)
       ,(visitor-return-values
         x.returns `(cons car cdr) x))))

(defun visitor-alist-measure (type x mrec)
  (declare (ignorable mrec))
  (b* (((flexalist type))
       ((visitorspec x)))
    `(:measure ,(visitor-measure x (if type.count
                                       `(,type.count ,x.xvar)
                                     `(len (,type.fix ,x.xvar)))))))



(defun visitor-alist-body (type x)
  (b* (((flexalist type))
       ((visitorspec x))
       (name (visitor-fnname x type.name))
       (key-fnname (visitor-field-fn :key type.key-type type.name x))
       (val-fnname (visitor-field-fn :val type.val-type type.name x))
       (formal-names (visitor-formal-names x.formals))
       ((unless (or key-fnname val-fnname))
        (er hard? 'defvisitor "Nothing to do for alist type ~x0 -- use :skip." type.name)))
    `(b* ((,x.xvar (,type.fix ,x.xvar))
          ((when (atom ,x.xvar))
           (b* (,@x.initial)
             ,(visitor-return-values x.returns
                                     (if type.true-listp nil x.xvar)
                                     x)))
          ,@(if x.reversep
                `((,(visitor-return-binder x.returns 'cdr t x)
                   (,name . ,(subst `(cdr ,x.xvar)
                                    x.xvar
                                    formal-names)))
                  
                  
                  ,@(and val-fnname
                         `((,(visitor-return-binder x.returns 'val nil x)
                            (,val-fnname . ,(subst `(cdar ,x.xvar)
                                                   x.xvar
                                                   formal-names)))
                           ,@x.join))

                  ,@(and key-fnname
                         `((,(visitor-return-binder x.returns 'key nil x)
                            (,key-fnname . ,(subst `(caar ,x.xvar)
                                                   x.xvar
                                                   formal-names)))
                           ,@x.join)))

              `(,@(and key-fnname
                       `((,(visitor-return-binder x.returns 'key t x)
                          (,key-fnname . ,(subst `(caar ,x.xvar)
                                                 x.xvar
                                                 formal-names)))))
                  ,@(and val-fnname
                         `((,(visitor-return-binder x.returns 'val (not key-fnname) x)
                            (,val-fnname . ,(subst `(cdar ,x.xvar)
                                                   x.xvar
                                                   formal-names)))
                           ,@(and key-fnname x.join)))
                  (,(visitor-return-binder x.returns 'cdr nil x)
                   (,name . ,(subst `(cdr ,x.xvar)
                                    x.xvar
                                    formal-names)))
                  ,@x.join)))
       ,(visitor-return-values
         x.returns
         `(cons (cons ,(if key-fnname 'key `(caar ,x.xvar))
                      ,(if val-fnname 'val `(cdar ,x.xvar)))
                cdr)
         x))))


(defun visitor-def (type x mrec)
  (b* ((body (with-flextype-bindings type
               (visitor-*-body type x)))
       (measure-args (with-flextype-bindings type
                       (visitor-*-measure type x mrec)))
       ((visitorspec x))
       (type.name (with-flextype-bindings type type.name))
       (type.pred (with-flextype-bindings type type.pred))
       (type.fix  (with-flextype-bindings type type.fix))
       (name (visitor-macroname x type.name))
       (fnname (visitor-fnname x type.name))
       (formals (acl2::template-subst-top
                 x.formals
                 (acl2::make-tmplsubst
                  :strs `(("<TYPE>" ,(symbol-name type.name) . ,type.name))
                  :atoms `((:object . ,type.pred))))))
    `(define ,name ,formals
       :returns ,(visitor-return-decls x.returns type.name type.pred type.fix)
       :verify-guards nil
       :hooks nil
       ,@measure-args
       ,@x.define-args
       ,(acl2::template-subst-top
         x.wrapper
         (acl2::make-tmplsubst
          :atoms `((:body . ,body))
          :strs `(("<TYPE>" ,(symbol-name type.name) . ,type.name))))
       ///
       ,@(and (not mrec) `(,@(and x.fixequivs
                                  `((deffixequiv ,name)))
                             (local (in-theory (disable ,name)))
                             (verify-guards ,fnname)
                             )))))
    


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
  `(defines ,(visitor-macroname x type-name)
     ;; [Jared] no longer necessary since we now always use DEFUN
     ;; :locally-enable nil
     ,@x.defines-args
     ,@other-fns
     ,@(visitor-mutual-aux types x)
     ///
     (verify-guards ,(visitor-fnname x
                                   (with-flextype-bindings (type (car types))
                                     type.name)))
     ,@(and x.fixequivs
            `((deffixequiv-mutual ,(visitor-macroname x type-name)))))))


(defun visitor-multi-aux (types-templates)
  (if (atom types-templates)
      nil
    (b* (((cons types template) (car types-templates)))
      (append (visitor-mutual-aux types template)
              (visitor-multi-aux (cdr types-templates))))))

(def-primitive-aggregate visitormulti
  (name
   defines-args
   other-fns
   fixequivs))

(defun visitor-multi (multicfg  types-templates)
  (b* (((visitormulti multicfg)))
    `(defines ,multicfg.name
       ;; [Jared] no longer necessary since we now always use DEFUN
       ;; :locally-enable nil
       ,@multicfg.defines-args
       ,@multicfg.other-fns
       ,@(visitor-multi-aux types-templates)
       ///
       (verify-guards ,(visitor-fnname (cdar types-templates)
                                       (with-flextype-bindings (type (car (caar types-templates)))
                                         type.name)))
       ,@(and multicfg.fixequivs
              `((deffixequiv-mutual ,multicfg.name))))))

(defun visitor-add-type-fns (types x)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (type (car types))
            (cons type.name
                  (visitor-fnname x type.name)))
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
  ;; Produces (mv accums initials joins joinvars) based on parsing of retarg
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

  (b* (((when (or (atom x) (atom (cdr x))))
        (er hard? 'defvisitor-template
            "Bad return entry ~x0" x)
        (mv nil nil nil nil))
       ((list name retarg) x)
       ((when (eq retarg :update))
        (mv nil nil nil nil))
       ((when (atom retarg))
        (er hard? 'defvisitor-template
            "Bad return entry ~x0" x)
        (mv nil nil nil nil)))
    (case (car retarg)
      (:join (b* (((mv kwd-alist rest-args)
                   (extract-keywords 'visitor-join-return
                                     '(:join :tmp-var :initial)
                                     retarg nil))
                  ((acl2::assocs (initial :initial)
                                 (join    :join)
                                 (tmp-var :tmp-var))
                   kwd-alist)
                  ((when (or rest-args
                             (not tmp-var)
                             (not (symbolp tmp-var))))
                   (prog2$
                    (er hard? 'defvisitor-template
                        "Bad return entry ~x0" x)
                    (mv nil nil nil nil))))
               (mv nil
                    (list (list name initial))
                    (list (list name join))
                    (list (cons name tmp-var)))))
      (:acc  (b* (((mv kwd-alist rest-args)
                   (extract-keywords 'visitor-acc-return
                                     '(:acc :fix)
                                     retarg nil))
                  (formal (cdr (assoc :acc kwd-alist)))
                  (fixp (assoc :fix kwd-alist))
                  (fix (cdr fixp))
                  ((when rest-args)
                   (prog2$
                    (er hard? 'defvisitor-template
                        "Bad return entry ~x0" x)
                    (mv nil nil nil nil))))
               (mv (list (cons formal name))
                   (and fixp (list (list formal fix)))
                   nil nil)))
      (:update  (b* (((mv ?kwd-alist rest-args)
                      (extract-keywords 'visitor-acc-return
                                        '(:update :type)
                                        retarg nil))
                     ((when rest-args)
                      (prog2$
                       (er hard? 'defvisitor-template
                           "Bad return entry ~x0" x)
                       (mv nil nil nil nil))))
                  (mv nil nil nil nil)))
      (otherwise
       (prog2$
        (er hard? 'defvisitor-template
            "Bad return entry ~x0" x)
        (mv nil nil nil nil))))))

(defun visitor-parse-returns-aux (returns)
  ;; returns: (mv stripped-returns accums initials joins joinvars)
  (b* (((when (atom returns))
        (mv nil nil nil nil nil))
       ((mv rest accums initials joins joinvars)
        (visitor-parse-returns-aux (cdr returns)))
       (return1 (car returns))
       ((mv accums1 initials1 joins1 joinvars1)
        (visitor-parse-return return1)))
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
    :fnname-template :renames :fixequivs :reversep :wrapper))

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
       (macrop (not (equal (std::remove-macro-args 'defvisitor-template formals nil) formals)))
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
           :xvar (visitor-xvar-from-formals formals)
           :fixequivs (std::getarg :fixequivs t kwd-alist)
           :prepwork (std::getarg :prepwork nil kwd-alist)
           :reversep (std::getarg :reversep nil kwd-alist)
           :wrapper (std::getarg :wrapper :body kwd-alist)
           :renames (std::getarg :renames nil kwd-alist)
           :macrop macrop)))
    x))

(defun defvisitor-template-fn (name args)
  `(with-output :off :all :on (error)
     (progn (table visitor-templates ',name
                   (defvisitor-template-main ',name ',args world))
            (with-output :stack :pop
              (value-triple ',name)))))

(defmacro defvisitor-template (name &rest args)
  (defvisitor-template-fn name args))

(defun visitor-include-types (types include-types)
  (if (atom types)
      nil
    (if (with-flextype-bindings (type (car types))
          (member type.name include-types))
        (cons (car types)
              (visitor-include-types (cdr types) include-types))
      (visitor-include-types (cdr types) include-types))))

(defun visitor-omit-types (types omit-types)
  (if (atom types)
      nil
    (if (with-flextype-bindings (type (car types))
          (member type.name omit-types))
        (visitor-omit-types (cdr types) omit-types)
      (cons (car types)
            (visitor-omit-types (cdr types) omit-types)))))
              



(defconst *defvisitor-keys*
  '(:type :template :type-fns :field-fns :prod-fns
    :fnname-template :renames :omit-types :include-types
    :measure
    :defines-args
    :define-args
    :order
    :parents :short :long))

(defun process-defvisitor (kwd-alist wrld)
  ;; returns (mv local-template store-template types)
  (b* ((template (cdr (assoc :template kwd-alist)))
       (type (cdr (assoc :type kwd-alist)))
       ((unless (and template type))
        (er hard? 'defvisitor ":type and :template arguments are mandatory")
        (mv nil nil nil))

       (x1 (cdr (assoc template (table-alist 'visitor-templates wrld))))
       ((unless x1)
        (er hard? 'defvisitor "Template ~x0 wasn't defined" template)
        (mv nil nil nil))
       ((mv type-fns field-fns prod-fns)
        (visitor-process-fnspecs kwd-alist wrld))

       ((visitorspec x1))
       (x1.type-fns (append type-fns x1.type-fns))
       (x1.field-fns (append field-fns x1.field-fns))
       (x1.prod-fns (append prod-fns x1.prod-fns))

       (fty (cdr (assoc type (table-alist 'flextypes-table wrld))))
       ((unless fty)
        (er hard? 'defvisitor "Type ~x0 not found" type)
        (mv nil nil nil))
       ((flextypes fty))

       (omit-types (cdr (assoc :omit-types kwd-alist)))
       (include-types (cdr (assoc :include-types kwd-alist)))
       ((when (and omit-types include-types))
        (er hard? 'defvisitor ":omit-types and :include-types are mutually exclusive")
        (mv nil nil nil))
       (types (cond (include-types
                     (visitor-include-types fty.types include-types))
                    (omit-types
                     (visitor-omit-types fty.types omit-types))
                    (t fty.types)))

       (fnname-template (or (cdr (assoc :fnname-template kwd-alist))
                            x1.fnname-template))
       (- (visitor-check-fnname-template fnname-template))
       (renames (append (cdr (assoc :renames kwd-alist)) x1.renames))
       (x1-with-renaming (change-visitorspec x1 :fnname-template fnname-template
                                             :renames renames))
       (unbound-types (visitor-omit-bound-types types x1.type-fns))
       (new-type-fns (append (visitor-add-type-fns unbound-types x1-with-renaming)
                             x1.type-fns))

       ;; this will be the visitorspec that we store in the table afterward; we
       ;; assume the renamings are temporary.
       (store-template (change-visitorspec x1 :type-fns new-type-fns
                                           :field-fns x1.field-fns
                                           :prod-fns x1.prod-fns))

       (local-template
        (change-visitorspec store-template
                            :wrld wrld
                            :fnname-template fnname-template
                            :renames renames
                            :defines-args (cdr (assoc :defines-args kwd-alist))
                            :define-args (cdr (assoc :define-args kwd-alist))
                            :measure (cdr (assoc :measure kwd-alist))
                            :order (cdr (assoc :order kwd-alist)))))
    (mv local-template store-template types)))



(defun defvisitor-fn (args wrld)
  (b* (((mv name args)
        (if (and (symbolp (car args))
                 (not (keywordp (car args))))
            (mv (car args) (cdr args))
          (mv nil args)))
       ((mv pre-/// post-///) (std::split-/// 'defvisitor args))
       ((mv kwd-alist mrec-fns)
        (extract-keywords 'defvisitor *defvisitor-keys* pre-/// nil))

       ((mv local-x store-x types)
        (process-defvisitor kwd-alist wrld))

       (template (cdr (assoc :template kwd-alist)))
       (type (cdr (assoc :type kwd-alist)))

       (event-name (or name (visitor-macroname local-x type)))
       (def (if (and (eql (len types) 1)
                     (atom mrec-fns))
                (visitor-def (car types) local-x nil)
              (visitor-mutual type types local-x mrec-fns))))
    `(defsection-progn ,event-name
       ,(append def post-///)
       (with-output :off :all :on (error)
         (table visitor-templates ',template ',store-x)))))

(defmacro defvisitor (&rest args)
  `(with-output :off (event)
     (make-event
      (defvisitor-fn ',args (w state)))))










(defconst *defvisitors-keys*
  '(:template    ;; visitor template to use
    :types       ;; Types targeted for toplevel functions
    :dep-types   ;; Get dependencies of these types
    :measure     ;; alt form of measure, applied to all the defvisitor forms
    :debug
    :order-base  ;; integer to start numbering
    ))



;; We're given the leaf functions (prod-fns, field-fns, type-fns) and the
;; top-level types that we want to visit.  Steps to determining the proper
;; sequence of defvisitor forms:

;; 1. Create a graph mapping types to member types, starting from the top-level
;; types and going down to the leaves that have predefined functions for them.
;; While doing this, accumulate a list of types that are encountered that have
;; a member in the type/prod/field-fns.  Call these types the leaf types.

;; 2. Reverse the graph.  Starting from the leaf types, mark all reachable
;; types in the reverse graph.  These are the types that need visitor functions
;; defined.

;; 3. Check the top-level types and produce an error if any weren't marked.

;; 4. Operating on the restricted graph containing only the marked types,
;; constrict the graph to be on the flextype objects for the marked types.

;; 5. Topologically sort the flextype graph.
;; 6. For each flextype in topological
;; order, issue a defvisitor form to create the appropriate
;; visitors.




;; Step 1.
(defun visitor-membertype-collect-member-types (type x wrld)
  ;; returns (mv subtypes is-leaf)
  (b* (((visitorspec x))
       (type (visitor-normalize-fixtype type wrld))
       (type-entry (assoc type x.type-fns))
       ((when type-entry)
        ;; Leaf type or skipped.
        (mv nil (and (cdr type-entry)
                     (not (eq (cdr type-entry) :skip)))))
       ;; Otherwise, check whether it's a fixtype; if so, it's a subtype (but not a leaf-type).
       ((mv fty ?ftype) (search-deftypes-table type (table-alist 'flextypes-table wrld)))
       ((when fty)
        (mv (list type) nil)))
    (mv nil nil)))

(defun visitor-field-collect-member-types (field x prod-entry wrld)
  ;; returns (mv subtypes is-leaf-type-p)
  (b* (((flexprod-field field))
       ((visitorspec x))
       (field-entry (or (assoc field.name prod-entry)
                        (assoc field.name x.field-fns)))
       ((when field-entry)
        (b* ((fn (cdr field-entry)))
          ;; We don't add a subtype or leaftype for this, but if it's a
          ;; non-skip entry we make this sum/product a leaftype.
          (mv nil (and fn (not (eq fn :skip))))))
       ((mv subtypes is-leaf)
        (visitor-membertype-collect-member-types field.type x wrld)))
    (mv subtypes is-leaf)))

(defun visitor-fields-collect-member-types (fields x prod-entry wrld)
  ;; returns (mv subtypes is-leaf-type-p)
  (b* (((when (atom fields)) (mv nil nil))
       ((mv subtypes1 is-leaf-type-p1)
        (visitor-field-collect-member-types (car fields) x prod-entry wrld))
       ((mv subtypes2 is-leaf-type-p2)
        (visitor-fields-collect-member-types (cdr fields) x prod-entry wrld)))
    (mv (union-eq subtypes1 subtypes2)
        (or is-leaf-type-p1 is-leaf-type-p2))))


(defun visitor-prods-collect-member-types (prods x wrld)
  (b* (((when (atom prods)) (mv nil nil))
       ((visitorspec x))
       ((flexprod prod1) (car prods))
       (prod-entry (cdr (assoc prod1.type-name x.prod-fns)))
       ((mv subtypes1 is-leaf-type1)
        (visitor-fields-collect-member-types prod1.fields x prod-entry wrld))
       ((mv subtypes2 is-leaf-type2)
        (visitor-prods-collect-member-types (cdr prods) x wrld)))
    (mv (union-eq subtypes1 subtypes2)
        (or is-leaf-type1 is-leaf-type2))))

(defun visitor-sumtype-collect-member-types (type x wrld)
  (b* (((flexsum type)))
    (visitor-prods-collect-member-types type.prods x wrld)))

(defun visitor-listtype-collect-member-types (type x wrld)
  (b* (((flexlist type)))
    (visitor-membertype-collect-member-types type.elt-type x wrld)))

(defun visitor-alisttype-collect-member-types (type x wrld)
  (b* (((flexalist type))
       ((mv subtypes1 is-leaf1)
        (visitor-membertype-collect-member-types type.key-type x wrld))
       ((mv subtypes2 is-leaf2)
        (visitor-membertype-collect-member-types type.val-type x wrld)))
    (mv (union-eq subtypes1 subtypes2)
        (or is-leaf1 is-leaf2))))
       

(defun visitor-type-collect-member-types (typename
                                          x    ;; visitorspec object
                                          wrld)
  (b* (((mv ?fty type-obj)
        (search-deftypes-table typename (table-alist 'flextypes-table wrld)))
       ((unless type-obj)
        (cw "WARNING: Expected to find deftypes table entry for ~x0 but didn't~%" typename)
        (mv nil nil)))
    (case (tag type-obj)
      (:sum (visitor-sumtype-collect-member-types type-obj x wrld))
      (:list (visitor-listtype-collect-member-types type-obj x wrld))
      (:alist (visitor-alisttype-collect-member-types type-obj x wrld))
      (otherwise (mv nil nil)))))


(mutual-recursion
 (defun visitor-type-make-type-graph (typename
                                      x           ;; visitorspec template
                                      wrld
                                      type-graph  ;; accumulator, fast alist
                                      leaf-types) ;; list of leaf types
   (b* (((when (hons-get typename type-graph))
         ;; already seen
         (mv type-graph leaf-types))
        ((mv subtypes is-leaf) (visitor-type-collect-member-types typename x wrld))
        (leaf-types (if is-leaf (cons typename leaf-types) leaf-types))
        (type-graph (hons-acons typename subtypes type-graph)))
     (visitor-types-make-type-graph subtypes x wrld type-graph leaf-types)))

 (defun visitor-types-make-type-graph (types x wrld type-graph leaf-types)
   (b* (((when (atom types)) (mv type-graph leaf-types))
        ((mv type-graph leaf-types)
         (visitor-type-make-type-graph (car types) x wrld type-graph leaf-types)))
     (visitor-types-make-type-graph (cdr types) x wrld type-graph leaf-types))))

(defun visitor-reverse-graph-putlist (froms to revgraph)
  (if (atom froms)
      revgraph
    (visitor-reverse-graph-putlist
     (cdr froms) to
     (hons-acons (car froms)
                 (cons to (cdr (hons-get (car froms) revgraph)))
                 revgraph))))

(defun visitor-reverse-graph-aux (graph)
  (if (atom graph)
      nil
    (let ((revgraph (visitor-reverse-graph-aux (cdr graph))))
      (visitor-reverse-graph-putlist (cdar graph) (caar graph) revgraph))))

(defun visitor-reverse-graph (graph)
  (fast-alist-clean (visitor-reverse-graph-aux graph)))


(mutual-recursion
 (defun visitor-mark-type-rec (type rev-graph marks)
   ;; If already marked, we're done.
   (b* (((when (hons-get type marks)) marks)
        (marks (hons-acons type t marks))
        (parents (cdr (hons-get type rev-graph))))
     (visitor-mark-types-rec parents rev-graph marks)))
 (defun visitor-mark-types-rec (types rev-graph marks)
   (if (atom types)
       marks
     (visitor-mark-types-rec
      (cdr types) rev-graph 
      (visitor-mark-type-rec (car types) rev-graph marks)))))

(defun visitor-check-top-types (types marks)
  (if (atom types)
      nil
    (if (cdr (hons-get (car types) marks))
        (visitor-check-top-types (cdr types) marks)
      (er hard? 'defvisitors
          "Type ~x0 doesn't have any descendants that need visiting." (car types)))))


(defun visitor-types-filter-marked (types marks)
  (if (atom types)
      nil
    (if (cdr (hons-get (car types) marks))
        (cons (car types)
              (visitor-types-filter-marked (cdr types) marks))
      (visitor-types-filter-marked (cdr types) marks))))


(defun visitor-members-to-ftys (memb-types deftypes-table)
  (b* (((when (atom memb-types)) nil)
       ((mv fty ?ftype) (search-deftypes-table (car memb-types) deftypes-table))
       ((unless fty)
        (cw "Warning: didn't find ~x0 in deftypes table~%" (car memb-types)))
       ((flextypes fty)))
    (add-to-set-eq fty.name
                   (visitor-members-to-ftys (cdr memb-types) deftypes-table))))



(defun visitor-to-fty-graph (type-graph marks deftypes-table fty-graph)
  (b* (((when (atom type-graph)) (fast-alist-clean fty-graph))
       ((cons type memb-types) (car type-graph))
       ((unless (cdr (hons-get type marks)))
        (visitor-to-fty-graph (cdr type-graph) marks deftypes-table fty-graph))
       ((mv fty ?ftype) (search-deftypes-table type deftypes-table))
       ((unless fty)
        (cw "Warning: didn't find ~x0 in deftypes table" type)
        (visitor-to-fty-graph (cdr type-graph) marks deftypes-table fty-graph))
       ((flextypes fty))
       (memb-ftys (visitor-members-to-ftys
                   (visitor-types-filter-marked memb-types marks)
                   deftypes-table))
       (prev-ftys (cdr (hons-get fty.name fty-graph)))
       (fty-graph (hons-acons fty.name (union-eq memb-ftys prev-ftys) fty-graph)))
    (visitor-to-fty-graph (cdr type-graph) marks deftypes-table fty-graph)))


(mutual-recursion
 (defun visitor-toposort-type (type fty-graph seen postorder)
   (b* (((when (hons-get type seen)) (mv seen postorder))
        (seen (hons-acons type t seen))
        ((mv seen postorder)
         (visitor-toposort-types (cdr (hons-get type fty-graph))
                                 fty-graph seen postorder)))
     (mv seen (cons type postorder))))
 (defun visitor-toposort-types (types fty-graph seen postorder)
   (b* (((when (atom types)) (mv seen postorder))
        ((mv seen postorder) (visitor-toposort-type (car types) fty-graph seen postorder)))
     (visitor-toposort-types (cdr types) fty-graph seen postorder))))


(defun visitor-type-to-fty (type deftypes-table)
  (b* (((mv fty ?ftype) (search-deftypes-table type deftypes-table))
       ((unless fty)
        (er hard? 'defvisitors "Didn't find ~x0 in deftypes table" type))
       ((flextypes fty)))
    fty.name))

(defun visitor-types-to-ftys (types deftypes-table)
  (if (atom types)
      nil
    (cons (visitor-type-to-fty (car types) deftypes-table)
          (visitor-types-to-ftys (cdr types) deftypes-table))))



(defun flextypelist-names (x)
  (if (atom x)
      nil
    (cons (with-flextype-bindings (y (car x))
            y.name)
          (flextypelist-names (cdr x)))))

(defun visitor-fty-defvisitor-form (fty-name order marks template-name deftypes-table kwd-alist)
  (b* ((fty (cdr (assoc fty-name deftypes-table)))
       ((unless fty)
        (er hard? 'defvisitors "Didn't find ~x0 in the deftypes table~%" fty-name))
       (measure-look (assoc :measure kwd-alist)))
    `(defvisitor :template ,template-name :type ,fty-name
       :include-types ,(visitor-types-filter-marked
                        (flextypelist-names (flextypes->types fty))
                        marks)
       :order ,order
       ,@(and measure-look `(:measure ,(cdr measure-look))))))

(defun visitor-defvisitor-forms (toposort order marks template-name deftypes-table kwd-alist)
  (if (atom toposort)
      nil
    (cons (visitor-fty-defvisitor-form (car toposort) order marks template-name deftypes-table
                                       kwd-alist)
          (visitor-defvisitor-forms (cdr toposort) (+ 1 order) marks template-name deftypes-table kwd-alist))))

(defun process-defvisitors (kwd-alist wrld)
  ;; Returns defvisitor-forms
  (b* ((template (cdr (assoc :template kwd-alist)))
       (types (append (cdr (assoc :types kwd-alist))
                      (cdr (assoc :dep-types kwd-alist))))
       (types (if (and types (atom types))
                  (list types)
                types))
       ((unless (and template (symbolp template)
                     types (symbol-listp types)))
        (er hard? 'defvisitors ":types and :template arguments are mandatory ~
                               and must be a symbol-list and symbol, ~
                               respectively"))
       (x1 (cdr (assoc template (table-alist 'visitor-templates wrld))))
       ((unless x1)
        (er hard? 'defvisitors "Template ~x0 wasn't defined" template))


       (deftypes-table (table-alist 'flextypes-table wrld))

       ;; Step 1.
       ((mv type-graph leaf-types)
        (visitor-types-make-type-graph types x1 wrld nil nil))

       ;; 2.
       (rev-graph (visitor-reverse-graph type-graph))
       (marks (visitor-mark-types-rec leaf-types rev-graph nil))


       ;; 3.
       (- (visitor-check-top-types types marks))

       ;; 4.
       (fty-graph (visitor-to-fty-graph type-graph marks deftypes-table nil))

       (dep-ftys (visitor-types-to-ftys (cdr (assoc :dep-types kwd-alist)) deftypes-table))
       ;; 5.
       ((mv seen-al rev-toposort) (visitor-toposort-types
                                   (set-difference-eq (strip-cars fty-graph) dep-ftys)
                                   fty-graph nil nil))
       (- (fast-alist-free seen-al))

       ;; 6. 
       (forms (visitor-defvisitor-forms (reverse rev-toposort)
                                        (or (cdr (assoc :order-base kwd-alist)) 0)
                                        marks template deftypes-table
                                        kwd-alist)))
    
    (and (cdr (assoc :debug kwd-alist))
         (progn$
          (cw "type graph: ~x0~%" type-graph)
          (cw "leaf types: ~x0~%" leaf-types)
          (cw "rev-graph:  ~x0~%" rev-graph)
          (cw "marks:      ~x0~%" marks)
          (cw "fty-graph:  ~x0~%" fty-graph)
          (cw "toposort:  ~x0~%" rev-toposort)))
    forms))



(defun defvisitors-fn (args wrld)
  (b* (((mv name args)
        (if (and (symbolp (car args))
                 (not (keywordp (car args))))
            (mv (car args) (cdr args))
          (mv nil args)))
       ((mv pre-/// post-///) (std::split-/// 'defvisitors args))
       ((mv kwd-alist mrec-fns)
        (extract-keywords 'defvisitors *defvisitors-keys* pre-/// nil))
       ((when mrec-fns)
        (er hard? 'defvisitors "Extra mutually-recursive functions aren't ~
                                allowed in defvisitors unless inside ~
                                defvisitor-multi."))
       (forms (process-defvisitors kwd-alist wrld)))

    `(defsection-progn ,name
       ,@forms
       . ,post-///)))




(defmacro defvisitors (&rest args)
  `(make-event
    (defvisitors-fn ',args (w state))))





(defconst *defvisitor-multi-keys*
  '(:defines-args :fixequivs))

(defconst *defvisitor-inside-multi-keys*
  (set-difference-eq *defvisitor-keys* *defvisitor-multi-keys*))

(defun process-defvisitor-multi (args wrld)
  ;; returns (mv types-templates other-fns ///-events table-stores)
  (b* (((when (atom args)) (mv nil nil nil nil))

       ((mv args other-fns1 ///-events1)
        (if (and (consp (car args))
                 (eq (caar args) 'defvisitors))
            (b* (((mv pre-/// post-///) (std::split-/// 'defvisitors (cdar args)))
                 ((mv kwd-alist mrec-fns)
                  (extract-keywords 'defvisitors *defvisitors-keys* pre-/// nil))
                 (kwd-alist (if (assoc :measure kwd-alist)
                                kwd-alist
                              (cons (cons :measure :count) kwd-alist)))
                 (defvisitor-forms (process-defvisitors kwd-alist wrld)))
              (mv (append defvisitor-forms (cdr args)) mrec-fns post-///))
          (mv args nil nil)))

       ((unless (consp (car args)))
        (er hard? 'defvisitor-multi "Bad arg: ~x0" (car args))
        (mv nil nil nil nil))

       ((when (eq (caar args) 'define))
        (b* (((mv types-templates other-fns ///-events table-stores)
              (process-defvisitor-multi (cdr args) wrld)))
          (mv types-templates (cons (car args) other-fns) ///-events table-stores)))

       ((unless (eq (caar args) 'defvisitor))
        (er hard? 'defvisitor-multi "Bad arg: ~x0" (car args))
        (mv nil nil nil nil))
       ;; defvisitor.  
       ((mv pre-/// post-///) (std::split-/// 'defvisitor (cdar args)))
       ((mv kwd-alist other-fns2)
        (extract-keywords 'defvisitor *defvisitor-inside-multi-keys* pre-/// nil))
       ((mv local-template store-template types)
        (process-defvisitor kwd-alist wrld))

       (wrld (putprop 'visitor-templates
                      'table-alist
                      (cons (cons (visitorspec->name store-template) store-template)
                            (table-alist 'visitor-templates wrld))
                      wrld))

       ((mv types-templates other-fns ///-events table-stores)
        (process-defvisitor-multi (cdr args) wrld))



       (types-templates (cons (cons types local-template) types-templates))
       (other-fns (append other-fns1 other-fns2 other-fns))
       (///-events (append ///-events1 post-/// ///-events))
       (table-stores (cons `(with-output :off :all :on (error)
                              (table visitor-templates
                                     ',(cdr (assoc :template kwd-alist))
                                     ',store-template))
                           table-stores)))
    (mv types-templates other-fns ///-events table-stores)))



(defun defvisitor-multi-fn (args wrld)
  (b* (((cons name args) args)
       ((unless (and (symbolp name)
                     (not (keywordp name))))
        (er hard? 'defvisitor-multi
            "Defvisitor-multi requires a name for the form as the first argument"))

       ((mv pre-/// post-///) (std::split-/// 'defvisitor args))
       ((mv kwd-alist args)
        (extract-keywords 'defvisitor-multi *defvisitor-multi-keys* pre-/// nil))

       ((mv types-templates other-fns ///-events table-stores)
        (process-defvisitor-multi args wrld))

       (multicfg (make-visitormulti :defines-args (cdr (assoc :defines-args kwd-alist))
                                    :fixequivs (getarg :fixequivs t kwd-alist)
                                    :name name
                                    :other-fns other-fns))
       
       (def (visitor-multi multicfg types-templates)))
    `(defsection-progn ,name
       ,(append def ///-events post-///)
       . ,table-stores)))


(defmacro defvisitor-multi (&rest args)
  `(with-output :off (event)
     (make-event
      (defvisitor-multi-fn ',args (w state)))))








(defun update-type-visitor-fn (visitor type fn world)
  (b* (((visitorspec x)
        (cdr (assoc visitor
                    (table-alist 'visitor-templates world)))))
    (change-visitorspec
     x :type-fns (cons (cons (visitor-normalize-fixtype type world) fn) x.type-fns))))


(defmacro update-type-visitor (visitor type fn)
  `(table visitor-templates
          ',visitor
          (update-type-visitor-fn ',visitor ',type ',fn world)))


(defxdoc defvisitor-template
  :parents (defvisitors)
  :short "Create a template that says how to make visitor functions."
  :long "<p>This is used in combination with @(see defvisitors) and @(see
defvisitor) to automatically generate \"visitor\" functions, i.e. functions
that traverse a data structure and do something at specified locations in it.
E.g., they can be used to transform all fields of a certain type, or to collect
some information about all occurrences of a certain product field, etc.  The
types that these visitors may traverse are those defined by @(see deftypes) and
related macros @(see defprod), @(see deftagsum), @(see deflist), @(see
defalist), @(see defoption), @(see deftranssum), and @(see defflexsum).</p>

<p>Visitor templates can be used by @(see defvisitor), @(see defvisitors), and
@(see defvisitor-multi) to automatically generate immense amounts of
boilerplate code for traversing complicated datatypes, especially when the
operation you want to do only really has to do with a few fields or component
types.</p>

<p>Here is a simple example from visitor-tests.lisp, annotated:</p>

@({
 (defvisitor-template

   ;; Name of the template.  This gets referred to later when this template is
   ;; used by defvisitor/defvisitors.
   collect-strings

   ;; Formals, similar to the formals in std::define.  Here :object stands for
   ;; the type predicate of whatever kind of object we're currently visiting; we'll
   ;; typically instantiate this template with several different :object types.
   ((x :object))

   ;; Return specifiers.  These are also like in std::define, but after each return name
   ;; is a description of how the return value gets constructed.  The names here are
   ;; a \"join\" value, which means they get constructed by combining,
   ;; pairwise, the corresponding values returned by sub-calls.  In this case, the
   ;; value (names1) returned from the most recent subcall is appended onto the
   ;; previous value (names).  The initial value is nil, i.e. this is what a
   ;; visitor function returns when run on an empty list or an object with no fields.
   :returns (names (:join (append names1 names)
                    :tmp-var names1
                    :initial nil)
                   string-listp)
   
   ;; Now we describe what is a base case and what we return in base cases.
   ;; This says, for any string field x, just produce (list x).  (The value
   ;; bound in the alist is a lambda or function that gets applied to the
   ;; formals, in this case just x.)
   :type-fns ((string list))
   
   ;; Describes how the functions we produce should be named.  Here, <type> gets
   ;; replaced by the type of object each separate visitor function operates on.
   :fnname-template collect-strings-in-<type>)
})

<p>Besides join values, there are two other kinds of visitor return values:
accumulators and updaters.  The following example shows how to use an
accumulator:</p>

@({
 (defvisitor-template collect-names-acc   ;; template name
     ;; formals:
     ((x :object)
      (names string-listp)) ;; accumulator formal

     ;; Names the return value and declares it to be an accumulator, which
     ;; corresponds to the formal NAMES.  The :fix is optional but is needed if
     ;; the return type of your accumulator output is unconditional.
     :returns  (names-out (:acc names :fix (string-list-fix names))
                          string-listp) 

     ;; Base case specification.  This says that when visiting a
     ;; simple-tree-leaf product, use the function CONS as the visitor for the
     ;; NAME field.  That is, instead of recurring on name, use (cons x names),
     ;; i.e., add the name to the accumulator.
     :prod-fns ((simple-tree-leaf  (name cons))))
 })

<p>This shows how to use an updater return value:</p>

@({
  (defvisitor-template incr-val  ((x :object)
                                  (incr-amount natp))

    ;; In an :update return value, the type is implicitly the same as :object.
    ;; It can optionally be specified differently.  This means that new-x gets
    ;; created by updating all the fields that we recurred on (or that were base
    ;; cases) with the corresponding results.
    :returns (new-x :update)

    ;; This says that when we visit a simple-tree-leaf, we replace its value field with
    ;; the field's previous value plus (lnfix incr-amount).  (We could just use
    ;; + here instead of the lambda, but this would violate the fixing convention for
    ;; incr-amount.)
    :prod-fns ((simple-tree-leaf  (value (lambda (x incr-amount) (+ x (lnfix incr-amount)))))))
 })

<p>The general form of a @('defvisitor-template') call is:</p>
@({
 (defvisitor-template template-name formals ... keyword-args)
 })

<p>where the accepted keywords are as follows:</p>

<ul>

<li>@(':returns'), required, describing the values returned by each visitor
function and how they are constructed from recursive calls.  The argument to
@(':returns') is either a single return tuple or several return tuples inside
an @('(mv ...)'), and each return tuple is similar to a @(see std::define)
returnspec except that it has an extra form after the return name and before
the rest of the arguments, describing how it is constructed -- either a
@(':join'), @(':acc'), or @(':update') form, as in the examples above.</li>

<li>@(':type-fns') specify base cases for fields of certain types.  The
argument is a list of pairs @('(type function)'), where the function applied to
the visitor formals gives the visitor values for fields of that type.
Alternatively, function may be @(':skip'), meaning that we don't recur on
fields of this type. (This is the default for field types that were not defined
by @(see deftypes).)  The @(':type-fns') entry is only used if there is no
applicable entry in @(':field-fns') or @(':prod-fns'), below.</li>

<li>@(':prod-fns') specify base cases for certain fields of certain products.
The argument is a list of entries @('(prod-name (field-name1
function1) (field-name2 function2) ...)'), where the functions work the same
way as in @(':type-fns').  @(':prod-fns') entries override @(':type-fns') and
@(':field-fns') entries.</li>

<li>@(':field-fns') specify base cases for fields with certain names.  The
argument is a list of pairs @('(field-name function)'), where function is as in
the @(':type-fns').  This is similar to using @(':prod-fns'), but applies to
fields of the given name inside any product.  @(':field-fns') entries override
@(':type-fns') entries, but @(':prod-fns') entries override both.</li>

<li>@(':fnname-template') describes how the generated functions should be
named. The argument is a symbol containing the substring @('<TYPE>'), and
function names are generated by replacing this with the name of the type.</li>

<li>@(':renames') allows you to specify function names that differ from the
ones described by the @(':fnname-template').  The argument is a list of pairs
@('(type function-name)').</li>

<li>@(':fixequivs') -- true by default, says whether to prove
congruence (deffixequiv) theorems about the generated functions.</li>

<li>@(':reversep') -- false by default, says whether to reverse the order in
which fields are processed.</li>

<li>@(':wrapper') -- @(':body') by default; gives a form in which to wrap the
generated body of each function, where @(':body') is replaced by that generated
body.  Advanced use.</li>

</ul>

<p>See also @('defvisitor'), @('defvisitors'), and @('defvisitor-multi').</p>")

(defxdoc defvisitor
  :parents (defvisitors)
  :short "Generate visitor functions for one type or one mutually-recursive clique of types."
  :long "<p>Defvisitor first requires that you have a visitor template defined
using @(see defvisitor-template).  The defvisitor form then instantiates that
template to create a visitor function for a type, or for each type in a
mutually-recursive clique of types.  See also @(see defvisitors), which
generates several defvisitor forms in order to traverse several types, and
@(see defvisitor-multi), which combines defvisitor and defvisitors forms into a
mutual recursion.</p>

<p>For example, the following visitor template was described in @(see
defvisitor-template):</p>

@({
 (defvisitor-template collect-strings ((x :object))
   :returns (names (:join (append names1 names)
                    :tmp-var names1
                    :initial nil)
                   string-listp)
   :type-fns ((string list))
   :fnname-template collect-strings-in-<type>)
})

<p>If we have a type defined as follows:</p>
@({
 (deftagsum simple-tree
   ;; Some simple kind of structure
   (:leaf ((name  stringp)
           (value natp)
           (cost  integerp)))
   (:branch ((left   simple-tree)
             (right  simple-tree)
             (hint   booleanp)
             (family stringp)
             (size   natp))))
 })
<p>then to create a visitor for the simple-tree type, we can do:</p>

@({
 (defvisitor collect-strings-in-simple-tree-definition
             ;; optional event name, for tags etc

   ;; type or mutually-recursive clique of types to visit
   :type simple-tree

   ;; template to instantiate
   :template collect-strings)
 })

<p>This creates (essentially) the following function definition:</p>

@({
  (define collect-strings-in-simple-tree ((x simple-tree-p))
    :returns (names string-listp)
    :measure (simple-tree-count x)
    (simple-tree-case x
      :leaf   (b* ((names (list x.name)))
                 names)
      :branch (b* ((names (collect-strings-in-simple-tree x.left))
                   (names1 (collect-strings-in-simple-tree x.right))
                   (names (append names1 names))
                   (names1 (list x.family))
                   (names (append names1 names)))
                 names)))
 })

<p>Additionally, defvisitor modifies the collect-strings template so that
future instantiations of the template will, by default, use
@('collect-strings-in-simple-tree') when visiting a simple-tree object.  (The
pair @('(simple-tree collect-strings-in-simple-tree)') is added to the
@(':type-fns') of the template; see @(see defvisitor-template).)</p>


<p>If we instead have a mutually-recursive clique of types, like the following:</p>

@({
 (deftypes mrec-tree
   (deftagsum mrec-tree-node
      (:leaf ((name stringp)
              (value natp)
              (cost integerp)))
      (:branch ((children mrec-treelist)
                (family stringp)
                (size natp))))
   (deflist mrec-treelist :elt-type mrec-tree-node))
 })

<p>then we can create a mutual recursion of visitors for these types as follows:</p>

@({
 (defvisitor collect-mrec-tree-strings
    :type mrec-tree   ;; the deftypes form name, not one of the type names
    :template collect-strings)
 })

<p>This creates a definition like this:</p>

@({
  (defines collect-strings-in-mrec-tree
    (define collect-strings-in-mrec-tree-node ((x mrec-tree-node-p))
       :returns (names string-listp)
       :measure (mrec-tree-node-count x)
       (mrec-tree-node-case x
         :leaf ...    ;; similar to the simple-tree above
         :branch ...))
    (define collect-strings-in-mrec-treelist ((x mrec-treelist-p))
       :returns (names string-listp)
       :measure (mrec-treelist-count x)
       (if (atom x)
           nil
         (b* ((names (collect-strings-in-mrec-tree-node (car x)))
              (names1 (collect-strings-in-mrec-treelist (cdr x)))
              (names (append names1 names)))
           names))))
 })

<p>The general form of defvisitor is:</p>

@({
 (defvisitor [ event-name ]
    :type type-name
    :template template-name
    other-keyword-args
    mrec-defines
    ///
    post-events)
 })

<p>One or more additional define forms may be nested inside a defvisitor form;
this means they will be added to the mutual-recursion with the generated
visitor functions.  This can be used to specialize the visitor's behavior on
some field so that when visiting that field the function is called, which then
calls other visitor functions from the clique.</p>

<p>The available keyword arguments (other than @(':type') and @(':template'))
are as follows:</p>

<ul>

<li>@(':type-fns'), @(':field-fns'), @(':prod-fns') -- these add additional
entries to the corresponding arguments of the template; see @(see
defvisitor-template).  When the defvisitor event finishes, these entries are
left in the updated template.</li>

<li>@(':fnname-template'), @(':renames') -- these override the corresponding
arguments of the template, but only for the current defvisitor; i.e., they are
not stored in the updated template.</li>

<li>@(':omit-types'), @(':include-types') -- when defining visitors for a
mutually-recursive clique of types, @(':omit-types') may be used to skip
creation of a visitor for some of the types, or @(':include-types') may be used
to only create visitors for the listed types.</li>

<li>@(':measure') -- Template for generating the measure for the functions;
defaults to @(':count').  In the template, @(':count') is replaced by the count
function for each type visited, and @(':order') is replaced by the current
order value (see below).  E.g., @('(two-nats-measure :count 0)') is often a
useful measure template, and @('(two-nats-measure :order :count)') is sometimes
useful inside @(see defvisitor-multi).</li>

<li>@(':defines-args'), @('define-args') -- Extra keyword arguments provided to
@('defines') or @(':define') respectively; @('defines-args') is only applicable
when there is a mutual recursion.</li>

<li>@(':order') specifies the order value for this clique, which is useful when
combining multiple defvisitor cliques into a single mutual recursion with @(see
defvisitor-multi).</li>
</ul>")


(defxdoc defvisitors
  :parents (fty)
  :short "Generate visitor functions across types using a visitor template."
  :long "<p>To use defvisitors, first see @(see defvisitor-template) and @(see
defvisitor).  Defvisitors automates the generation of several defvisitor forms
that create a system of visitor functions that works on a nest of types.</p>

<p>For example, suppose we have the following types:</p>

@({
  (defprod employee
     ((name stringp)
      (salary natp)
      (title stringp)))

  (deflist employees :elt-type employee)

  (defprod group
    ((lead employee)
     (members employees)
     (budget natp)
     (name stringp)
     (responsibilities string-listp)))

  (defprod division
    ((head employee)
     (operations  group)
     (engineering group)
     (sales       group)
     (service     group)
     (black-ops   group)))
 })

<p>Suppose we want to total up the salaries of all the employees in a division,
including the division head, group leads, and group members.  A visitor
template for this operation might look like this:</p>

@({
  (defvisitor-template salary-total ((x :object))
    :returns (total (:join (+ total1 total)
                     :tmp-var total1
                     :initial 0)
                    natp :rule-classes :type-prescription
                    \"The total salary of all employees\")
    :type-fns ((employee employee->salary)))
 })

<p>Now we need visitor functions for the employees, group, and division types, so we can do:</p>

@({
  (defvisitor :type employees :template salary-total)
  (defvisitor :type group     :template salary-total)
  (defvisitor :type division  :template salary-total)
 })

<p>However, we can automate this more by using defvisitors instead of
defvisitor.  This doesn't seem worthwhile to get rid of just three defvisitor
forms, but oftentimes the type hierarchy is much more specialized than this,
and changes frequently.  Using defvisitors can prevent the need to modify the
code if you add a type to the hierarchy.  To invoke it:</p>

@({
 (defvisitors division-salary-total ;; optional event name
   :types (division)
   :template salary-total)
 })

<p>This searches over the field types of the @('division') type and creates a
graph of the types that need to be visited, then arranges them in dependency
order and creates the necessary defvisitor forms.</p>

<p>The options for @('defvisitors') are somewhat more limited than for
@('defvisitor').  The available keyword arguments are as follows:</p>

<ul>

<li>@(':template') -- the name of the visitor template to instantiate.</li>

<li>@(':types'), @(':dep-types') -- controls the top-level types to visit.
Those listed in @('dep-types') are not themselves visited, but their children
are.  Note that these are type names, NOT deftypes names as in @(see
defvisitor).  (For a single type, the type name and deftypes name is likely the
same, but for a mutually-recursive clique of types, the deftypes name refers to
the whole clique.)</li>

<li>@(':measure') -- measure form to use for each @('defvisitor') form; this is
mostly only useful in the context of a @('defvisitor-multi') form.</li>

<li>@(':order-base') -- starting index from which the order indices assigned to
the deftypes forms are generated; also mostly only useful in the context of a
@('defvisitor-multi') form.  Defvisitors assigns a different order index to
each defvisitor form it submits, with earlier forms having lower indices.  When
the measure is properly formulated in terms of the order, this allows them to
be used together in a mutual recursion.</li>

<li>@(':debug') -- print some information about the graph traversals.</li>

</ul>")

(defxdoc defvisitor-multi
  :parents (defvisitors)
  :short "Put defvisitor, defvisitors, and define forms togeher into a single mutual recursion."
  :long "<p>In a few cases it is useful to have visitors for several types (or
perhaps several different kinds of visitors) together in a mutual recursion.
Here is an example showing how this can work.</p>

@({
  ;; We have sum of product terms.  Each literal in the sum of products is
  ;; either a constant or a variable, which refers to another sum of products
  ;; term via a lookup table.
  (deftagsum literal
    (:constant ((value natp)))
    (:variable ((name symbolp))))

  (defprod product
    ((first  literal-p)
     (second literal-p)
     (third  literal-p)))

  (defprod sum
    ((left  product-p)
     (right product-p)))

  ;; Lookup table mapping each variable to a sum-of-products.
  (defalist sop-env :key-type symbolp :val-type sum-p)

  ;; Suppose we have a lookup table and we want to collect all the dependencies
  ;; of some expression -- i.e., when we get to a variable we want to collect
  ;; it, then look up its formula and collect its dependencies too.  If the
  ;; table doesn't have some strict dependency order, then we might not
  ;; terminate, so we'll use a recursion limit.

  (defvisitor-template collect-deps ((x :object)
                                     (env sop-env-p)
                                     (rec-limit natp))
    :returns (deps (:join (append deps1 deps)
                    :tmp-var deps1 :initial nil)
                    symbol-listp)

    ;; We'll call the function to apply to variable names
    ;; collect-and-recur-on-var.  Note that this hasn't been defined yet -- it
    ;; needs to be mutually recursive with the other functions in the clique.
    :prod-fns ((variable (name collect-and-recur-on-var)))

    :fnname-template <type>-collect-deps)

  ;; A defvisitor-multi form binds together some defvisitor and defvisitors
  ;; forms into a mutual recursion with some other functions.  Here, we'll just have
  ;; the one defvisitors form inside.
  (defvisitor-multi sum-collect-deps

     (defvisitors :template collect-deps :types (sum)
       ;; Normally this defvisitors form would create a visitor for a literal,
       ;; then product, then sum.  Inside a defvisitor-multi, it instead puts
       ;; all of those definitions into one mutual recursion.

       ;; We have to do something special with the measure.  Defvisitors
       ;; assigns an order to each of the types so that calling from one
       ;; visitor to another can generally reduce the measure.  Therefore, we
       ;; only need to decrease the rec-limit when calling from a lower-level
       ;; type to a higher-level one -- e.g. when we reach a variable and will
       ;; recur on a sum.
       :measure (two-nats-measure rec-limit :order)

       ;; Since our lowest-level visitor (literal-collect-deps) is going to
       ;; call an intermediate function (collect-and-recur-on-var) which then
       ;; calls our highest-level visitor (sum-collect-deps), it's convenient
       ;; to set the order of the lowest-level to 1 so that
       ;; collect-and-recur-on-var can use 0 as the order in its measure.
       :order-base 1)

     ;; This function goes in the mutual recursion with the others.
     (define collect-and-recur-on-var ((x symbolp)
                                       (env sop-env-p)
                                       (rec-limit natp))
        :returns (deps symbol-listp)
        :measure (two-nats-measure rec-limit 0)
        (b* ((x (mbe :logic (symbol-fix x) :exec x))
             (lookup (hons-get x (sop-env-fix env)))
             ((unless lookup) (list x))
             ((when (zp rec-limit))
              (cw \"Recursion limit ran out on ~x0~%\" x)
              (list x)))
          (cons x (sum-collect-deps (cdr lookup) env (- rec-limit 1))))))

})

<p>A @('defvisitor-multi') form's syntax is as follows:</p>
@({
  (defvisitor-multi event-name
     defvisitor-defvisitors-define-forms
     keyword-args
     ///
     post-events)
 })

<p>The only keyword arguments currently accepted are @(':defines-args') and
@(':fixequivs'), which are described in @(see defvisitor).  All the usual
arguments to defvisitor and defvisitors are accepted, except for these two.  An
additional difference from non-nested forms is that the nested defvisitor and
defvisitors forms may not have an event name as the first argument.</p>")




