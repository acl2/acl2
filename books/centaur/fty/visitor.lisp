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
(program)

(define my-intern (string sym)
  (intern-in-package-of-symbol string
                               (if (equal (symbol-package-name sym) "COMMON-LISP")
                                   (pkg-witness "ACL2")
                                 sym)))

(def-primitive-aggregate visitorspec
  (name               ;; Base name of the visitor.  Functions will be named <name>-<type>.
   formals            ;; Formals, with special case (varname :object) signifies the current object.
   returns            ;; Returns, with special case (retname :update) signifies updated object.
   accum-vars         ;; Alist mapping accumulator formals to returns.
   join-vars          ;; Alist mapping return vars to alternate vars, used in join bindings
   type-fns           ;; Alist mapping field types to visitor function names, :skip to skip.
   field-fns          ;; Alist mapping field names to visitor function names or :skip,
                      ;; overriding type-fns.
   prod-fns           ;; Alist mapping product names to alists mapping field names to
                      ;; visitor functions or :skip, overriding field-fns.
   initial            ;; Bindings for non-update return values when there are no fields.
   join               ;; Bindings for non-update return values in terms of their current values
                      ;; and the joinvar.
   xvar               ;; The varname from the formals.
   fnname-template    ;; Symbol, template using substring <TYPE> to
                      ;; describe how to generate visitor function names
   renames            ;; alist mapping type names to non-default visitor function names
   measure            ;; measure template
   fixequivs          ;; prove congruences
   prepwork           ;; template for prepwork, where <type> is substituted
   reversep           ;; reverse order in which fields are processed
   wrapper            ;; wrapper around the body of a function, using :body and <type>
                      ;; in template substitutions
   macrop             ;; indicates that this has a macro wrapper
   defines-args       ;; extra keyword args to defines
   define-args        ;; extra keyword args to define
   order              ;; topological order ranking for defvisitors under multi
   wrld))

(define visitor-return-binder-aux (returns fldname firstp x)
  (b* (((when (atom returns))
        nil)
       ((visitorspec x))
       ((mv name type)
        (if (consp (car returns))
            (b* (((list name type) (car returns)))
              (mv name type))
          (mv (car returns) nil)))
       (accum (rassoc-eq name x.accum-vars))
       (name (cond ((or (eq type :update)
                        (eq (car type) :update))
                    fldname)
                   (accum  (car accum))
                   (firstp name)
                   (t      (cdr (assoc name x.join-vars))))))
    (cons name
          (visitor-return-binder-aux (cdr returns) fldname firstp x))))

(define visitor-return-binder (returns fldname firstp x)
  (b* ((returns (if (and (consp returns)
                         (eq (car returns) 'mv))
                    (cdr returns)
                  (list returns)))
       (lst (visitor-return-binder-aux returns fldname firstp x))
       ((when (eql (len returns) 1))
        (car lst)))
    (cons 'mv lst)))

(define visitor-macroname (x type)
  (b* (((visitorspec x))
       (look (assoc type x.renames))
       ((when look)
        (cadr look))
       ((when x.fnname-template)
        (acl2::tmpl-sym-sublis `(("<TYPE>"    . ,(symbol-name type)))
                               x.fnname-template x.name)))
    (acl2::tmpl-sym-sublis `(("<TYPE>"    . ,(symbol-name type))
                             ("<VISITOR>"    . ,(symbol-name x.name)))
                           '<VISITOR>-<TYPE> x.name)))

(define visitor-fnname (x type)
  (b* (((visitorspec x))
       (macroname (visitor-macroname x type))
       ((when x.macrop)
        (intern-in-package-of-symbol
         (concatenate 'string (symbol-name macroname) "-FN")
         macroname)))
    macroname))

(define visitor-normalize-fixtype (type wrld)
  (b* ((fty (find-fixtype-for-pred type (get-fixtypes-alist wrld)))
       ((when fty)
        (fixtype->name fty)))
    type))

(define visitor-field-fn (fldname fldtype prod x)
  (b* (((visitorspec x))
       (fldtype  (visitor-normalize-fixtype fldtype x.wrld))
       (prod-fns (and prod (cdr (assoc prod x.prod-fns))))
       (prod-fld (and fldname (assoc fldname prod-fns)))
       ((when prod-fld)
        (if (eq (cdr prod-fld) :skip)
            nil
          (cdr prod-fld)))
       (fld (assoc fldname x.field-fns))
       ((when fld)
        (if (eq (cdr fld) :skip)
            nil
          (cdr fld)))
       (type (assoc fldtype x.type-fns))
       ((when type)
        (if (eq (cdr type) :skip)
            nil
          (cdr type))))
    nil))

(define strip-cars-of-pairs (x)
  (if (atom x)
      nil
    (cons (if (consp (car x)) (caar x) (car x))
          (strip-cars-of-pairs (cdr x)))))

(define visitor-formal-names (formals)
  (strip-cars-of-pairs (std::remove-macro-args 'visitor formals nil)))


(define visitor-prod-field-joins (fields x prodname firstp)
  :returns (mv changes    ;; keyword-value pairs for change macro
               bindings)  ;; bindings to append into b*
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


(define visitor-return-values-aux (returns update x)
  (b* (((when (atom returns))
        nil)
       ((visitorspec x))
       ((mv name type)
        (if (consp (car returns))
            (b* (((list name type) (car returns)))
              (mv name type))
          (mv (car returns) nil)))
       (accum (rassoc-eq name x.accum-vars))
       (ret1 (cond ((or (eq type :update)
                        (equal type '(:update)))
                    update)
                   ((eq (car type) :update)
                    (subst update :update (cadr type)))
                   (accum
                    (car accum))
                   (t name))))
    (cons ret1
          (visitor-return-values-aux (cdr returns) update x))))

(define visitor-return-values (returns update x)
  (b* ((returns (if (and (consp returns)
                         (eq (car returns) 'mv))
                    (cdr returns)
                  (list returns)))
       (lst (visitor-return-values-aux returns update x))
       ((when (eql (len returns) 1))
        (car lst)))
    (cons 'mv lst)))

(define visitor-return-decls-aux (returns type-pred type-fix)
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

(define visitor-return-decls (returns type-name type-pred type-fix)
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




(define visitor-prod-subbody (prod x)
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


(define visitor-measure (x default type-name)
  (b* (((visitorspec x)))
    (if x.measure
        (acl2::template-subst
         x.measure
         :str-alist `(("<TYPE>" ,(symbol-name type-name) . ,type-name))
         :atom-alist `((:order . ,x.order)
                       (:count . ,default)))
      default)))

(define visitor-prod-body (type x)
  (b* (((flexsum type))
       ((visitorspec x))
       ((flexprod prod) (car type.prods)))
    `(b* (((,prod.ctor-name ,x.xvar) (,type.fix ,x.xvar)))
       ,(visitor-prod-subbody prod x))))


(define visitor-prod-bodies (prods x)
  (b* (((when (atom prods))
        nil)
       ((flexprod prod) (car prods)))
    `(,prod.kind
      ,(visitor-prod-subbody prod x)
      . ,(visitor-prod-bodies (cdr prods) x))))



(define visitor-sum-body (type x)
  (b* (((flexsum type))
       ((when (eql (len type.prods) 1))
        (visitor-prod-body type x))
       ((visitorspec x)))
    `(,type.case ,x.xvar
       . ,(visitor-prod-bodies type.prods x))))

(define visitor-sum-measure (type x mrec)
  (b* (((flexsum type))
       ((visitorspec x)))
    (and (or mrec type.recp)
         `(:measure ,(visitor-measure x (if type.count
                                            `(,type.count ,x.xvar)
                                          0)
                                      type.name)))))



(define flextranssum-memberlist->typenames (members)
  (if (atom members)
      nil
    (cons (flextranssum-member->name (car members))
          (flextranssum-memberlist->typenames (cdr members)))))

(define visitor-transsum-updates (member x)
  ;; modeled after visitor-prod-field-joins
  :returns (mv updated-member
               bindings)  ;; bindings to append into b*
  (b* (((visitorspec x) x)
       ((flextranssum-member member))
       (typefn-lookup (assoc member.name x.type-fns))
       ((when (or (not typefn-lookup)
                  (eq (cdr typefn-lookup) :skip)))
        ;; Nothing to do, return the unchanged object and initial values
        (mv x.xvar x.initial))
       (fnname      (cdr typefn-lookup))
       (update-name
        ;; bozo my kingdom for gensym
        (my-intern (cat (symbol-name x.xvar) "." (symbol-name member.name)) x.xvar)))
    (mv update-name
        `((,(visitor-return-binder x.returns update-name t x)
           (,fnname . ,(visitor-formal-names x.formals)))))))

(define visitor-transsum-member-body (member x)
  ;; modeled after visitor-prod-subbody
  (b* (((visitorspec x))
       ((mv new-value bindings) (visitor-transsum-updates member x)))
    `(b* (,@bindings)
       ,(visitor-return-values
         x.returns
         new-value
         x))))

(define visitor-transsum-member-bodies (members x)
  (cond ((atom members)
         nil)
        ((atom (cdr members))
         (list (list 'otherwise (visitor-transsum-member-body (car members) x))))
        (t
         (b* (((flextranssum-member member) (car members)))
           (cons `(,member.tags ,(visitor-transsum-member-body (car members) x))
                 (visitor-transsum-member-bodies (cdr members) x))))))

(define visitor-transsum-body (type x)
  (b* (((flextranssum type))
       ((visitorspec x)))
    `(let ((,x.xvar (,type.fix ,x.xvar)))
       (case (tag ,x.xvar)
         . ,(visitor-transsum-member-bodies type.members x)))))

(define visitor-transsum-measure (type x mrec)
  (declare (ignorable type mrec))
  (b* ((default
         ;; Not really sure what to use as a default measure, but maybe
         ;; 0 makes sense since that's the default for a normal sum.
         0)
       (typename (flextranssum->name type)))
    `(:measure ,(visitor-measure x default typename))))




(define visitor-list-measure (type x mrec)
  (declare (ignorable mrec))
  (b* (((flexlist type))
       ((visitorspec x)))
    `(:measure ,(visitor-measure x (if type.count
                                       `(,type.count ,x.xvar)
                                     `(len ,x.xvar))
                                 type.name))))



(define visitor-list-body (type x)
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
         x.returns `(cons-with-hint car cdr ,x.xvar) x))))

(define visitor-alist-measure (type x mrec)
  (declare (ignorable mrec))
  (b* (((flexalist type))
       ((visitorspec x)))
    `(:measure ,(visitor-measure x (if type.count
                                       `(,type.count ,x.xvar)
                                     `(len (,type.fix ,x.xvar)))
                                 type.name))))



(define visitor-alist-body (type x)
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
         `(cons-with-hint (cons-with-hint ,(if key-fnname 'key `(caar ,x.xvar))
                                          ,(if val-fnname 'val `(cdar ,x.xvar))
                                          (car ,x.xvar))
                          cdr
                          ,x.xvar)
         x))))

(define visitor-set-measure (type x mrec)
  (declare (ignorable mrec))
  (b* (((flexset type))
       ((visitorspec x)))
    `(:measure ,(visitor-measure x (if type.count
                                       `(,type.count ,x.xvar)
                                     `(len ,x.xvar))
                                 type.name))))

(define visitor-set-body (type x)
  (b* (((flexset type))
       ((visitorspec x))
       (name (visitor-fnname x type.name))
       (elt-fnname (visitor-field-fn :elt type.elt-type type.name x))
       (formal-names (visitor-formal-names x.formals))
       ((unless elt-fnname)
        (er hard? 'defvisitor "Nothing to do for set type ~x0 -- use :skip." type.name)))
    `(b* (((when (atom ,x.xvar))
           (b* (,@x.initial)
             ,(visitor-return-values x.returns
                                     nil
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
         x.returns `(cons-with-hint car cdr ,x.xvar) x))))

(define visitor-def (type x mrec)
  (b* ((body (with-flextype-bindings type
               (visitor-*-body type x)))
       (measure-args (with-flextype-bindings type
                       (visitor-*-measure type x mrec)))
       ((visitorspec x))
       (type.name (with-flextype-bindings type type.name))
       (type.pred (with-flextype-bindings type type.pred))
       (type.fix  (with-flextype-bindings type type.fix))
       (name (visitor-macroname x type.name))
       ((when (eq name :skip)) nil)
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



(define visitor-omit-bound-types (types type-fns)
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


(define visitor-mutual-aux (types x)
  (if (atom types)
      nil
    (b* ((def (visitor-def (car types) x t))
         (rest (visitor-mutual-aux (cdr types) x)))
      (if def
          (cons def rest)
        rest))))

(define visitor-mutual (type-name types x other-fns)
  (b* (((visitorspec x))
       (defs (visitor-mutual-aux types x))
       ((when (and (not other-fns) (not defs))) nil))
  `(defines ,(visitor-macroname x type-name)
     ;; [Jared] no longer necessary since we now always use DEFINE
     ;; :locally-enable nil
     ,@x.defines-args
     ,@other-fns
     ,@defs
     ///
     (verify-guards ,(visitor-fnname x
                                   (with-flextype-bindings (type (car types))
                                     type.name)))
     ,@(and x.fixequivs
            `((deffixequiv-mutual ,(visitor-macroname x type-name)))))))


(define visitor-multi-aux (types-templates)
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

(define visitor-multi (multicfg  types-templates)
  (b* (((visitormulti multicfg))
       (defs (visitor-multi-aux types-templates))
       ((when (and (not multicfg.other-fns) (not defs))) nil))
    `(defines ,multicfg.name
       ;; [Jared] no longer necessary since we now always use DEFINE
       ;; :locally-enable nil
       ,@multicfg.defines-args
       ,@multicfg.other-fns
       ,@defs
       ///
       (verify-guards ,(visitor-fnname (cdar types-templates)
                                       (with-flextype-bindings (type (car (caar types-templates)))
                                         type.name)))
       ,@(and multicfg.fixequivs
              `((deffixequiv-mutual ,multicfg.name))))))

(define visitor-add-type-fns (types x)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (type (car types))
            (cons type.name
                  (visitor-fnname x type.name)))
          (visitor-add-type-fns (cdr types) x))))


;; (define visitor-define (x type-name type-table other-fns)
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


(define visitor-parse-return (x)
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

(define visitor-parse-returns-aux (returns)
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

(define visitor-parse-returns (returns)
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


(define visitor-symbol/fn-doubletonlist-p (x)
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

(define visitor-symbol/fn-doubletonlist-alist-p (x)
  (if (atom x)
      (eq x nil)
    (case-match x
      (((name . alist) . rest)
       (and name (symbolp name)
            (visitor-symbol/fn-doubletonlist-p alist)
            (visitor-symbol/fn-doubletonlist-alist-p rest)))
      (& nil))))

(define visitor-doubletonlist-to-alist (x)
  (if (atom x)
      nil
    (cons (cons (caar x) (cadar x))
          (visitor-doubletonlist-to-alist (cdr x)))))

(define visitor-doubletonlist-alist-to-alist (x)
  (if (atom x)
      nil
    (cons (cons (caar x)
                (visitor-doubletonlist-to-alist (cdar x)))
          (visitor-doubletonlist-alist-to-alist (cdr x)))))

(define visitor-normalize-type-fns (type-fns wrld)
  (if (atom type-fns)
      nil
    (cons (cons (visitor-normalize-fixtype (caar type-fns) wrld)
                (cdar type-fns))
          (visitor-normalize-type-fns (cdr type-fns) wrld))))

(defconst *defvisitor-template-keys*
  '(:returns
    :type-fns
    :field-fns
    :prod-fns
    :parents
    :short
    :long
    :fnname-template
    :renames
    :fixequivs
    :reversep
    :wrapper))

(define visitor-process-fnspecs (kwd-alist wrld)
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

(define visitor-check-fnname-template (name x)
  (or (not x)
      (and (symbolp x)
           (search "<TYPE>" (symbol-name x)))
      (raise "~x0: fnname-template should be a symbol whose name contains the ~
               substring <TYPE>, but found ~x1."
               name x)))

(define visitor-xvar-from-formals (name formals)
  (cond ((atom formals)
         (raise "~x0: No input was designated the :object of the visitor."
                name))
        ((and (consp (car formals))
              (eq (cadar formals) :object))
         (caar formals))
        (t
         (visitor-xvar-from-formals name (cdr formals)))))

(define defvisitor-template-main (name args wrld)
  (b* (((mv kwd-alist rest) (extract-keywords name *defvisitor-template-keys* args nil))
       ((unless (eql (len rest) 1))
        (raise "~x0: the only non-keyword argument after the name should be ~
                the formals." name))
       (formals (car rest))
       (returns (cdr (assoc :returns kwd-alist)))

       ((mv type-fns field-fns prod-fns)
        (visitor-process-fnspecs kwd-alist wrld))

       ((mv stripped-returns accums initials joins joinvars)
        (visitor-parse-returns returns))

       (fnname-template (cdr (assoc :fnname-template kwd-alist)))
       (- (visitor-check-fnname-template name fnname-template))
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
           :xvar (visitor-xvar-from-formals name formals)
           :fixequivs (std::getarg :fixequivs t kwd-alist)
           :prepwork (std::getarg :prepwork nil kwd-alist)
           :reversep (std::getarg :reversep nil kwd-alist)
           :wrapper (std::getarg :wrapper :body kwd-alist)
           :renames (std::getarg :renames nil kwd-alist)
           :macrop macrop)))
    x))

(define defvisitor-template-fn (name args)
  `(with-output :off :all :on (error)
     (progn (table visitor-templates ',name
                   (defvisitor-template-main ',name ',args world))
            (with-output :stack :pop
              (value-triple ',name)))))

(defmacro defvisitor-template (name &rest args)
  (defvisitor-template-fn name args))

(define visitor-include-types (types include-types)
  (cond ((atom types)
         nil)
        ((with-flextype-bindings (type (car types))
           (member type.name include-types))
         (cons (car types)
               (visitor-include-types (cdr types) include-types)))
        (t
         (visitor-include-types (cdr types) include-types))))

(define visitor-omit-types (types omit-types)
  (cond ((atom types)
         nil)
        ((with-flextype-bindings (type (car types))
           (member type.name omit-types))
         (visitor-omit-types (cdr types) omit-types))
        (t
         (cons (car types)
               (visitor-omit-types (cdr types) omit-types)))))




(defconst *defvisitor-keys*
  '(:type
    :template
    :type-fns
    :field-fns
    :prod-fns
    :fnname-template
    :renames
    :omit-types
    :include-types
    :measure
    :defines-args
    :define-args
    :order
    :parents
    :short
    :long))

(define process-defvisitor (name kwd-alist wrld)
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
       (- (visitor-check-fnname-template name fnname-template))
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



(define defvisitor-fn (args wrld)
  (b* (((mv name args)
        (if (and (symbolp (car args))
                 (not (keywordp (car args))))
            (mv (car args) (cdr args))
          (mv nil args)))
       ((mv pre-/// post-///) (std::split-/// 'defvisitor args))
       ((mv kwd-alist mrec-fns)
        (extract-keywords 'defvisitor *defvisitor-keys* pre-/// nil))

       ((mv local-x store-x types)
        (process-defvisitor name kwd-alist wrld))

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
;;
;; General priority ordering of things:
;;
;;   if myprod has fielda (type atype):
;;     - if myprod has an entry in prod-fns and fielda has an entry there, do what it says
;;     - otherwise if fielda has an entry in field-fns do what it says
;;     - otherwise if atype has an entry in type-fns do what it says
;;     - otherwise maybe call our generated visitor for atype, or ignore it
;;
;; Determining what needs to be visited.
;;
;; Vocabulary:  "Visiting" a type means: we need to generate a function for this type.
;;
;; We consider each top-level type and find out everything that needs to be
;; visited to support it.  (If it turns out that a top-level type doesn't need
;; to be visited, abort with an error.)
;;
;; Here is how to mark-types, starting with some type foo, to find out whether
;; foo needs to be visited, and which other transitive member types within foo,
;; need to be visited:
;;
;;    Definition. The (possibly named) members of foo are
;;      - For a product, its (field name, field type) pairs
;;      - For a list, only just its element type (no field name)
;;      - For an alist, its key-type and val-types (no field names)
;;      - For a sum, its possible types (no field names)
;;
;;    Consider in turn each member of foo, memname : memtype
;;
;;      Let action be:
;;        - if foo is a product:
;;           - if prod-fns[foo][memname] exists, then prod-fns[foo][memname]
;;           - if field-fns[memname] exists, then field-fns[memname]
;;        - if type-fns[memtype] exists, then type-fns[memtype].
;;        - otherwise NONE
;;
;;     If action is SKIP: do nothing
;;     else if action is NONE:
;;               marktypes(memtype)               // because its members may need visiting
;;               mark foo if memtype is marked    // propagates visiting upwards
;;     else mark foo.                             // foo is a "leaf type" that must be visited
;;
;; Note that the above will mark a type, foo, even in the case where
;; type-fns[foo] is provided by the user.  We often make use of this in order
;; to customize the behavior for a type: the defvisitor form can generate a
;; default function that visits all of the type's members, and then our wrapper
;; can fix up whatever is wrong with that.
;;
;; Implementation of this idea:
;;
;; 1. Create a graph mapping types to member types, starting from the top-level
;;    types and going down to the leaves that have predefined functions for
;;    them.  While doing this, accumulate a list of types that are encountered
;;    that have a (non-skip) member in the type/prod/field-fns.  This is like
;;    the algorithm above, except that we only get the leaf types in this step.
;;
;; 2. Reverse the graph.  Starting from the leaf types, mark all reachable
;;    types in the reverse graph.  These are the types that need visitor
;;    functions defined.  This marks the same types that are marked by the
;;    algorithm above.
;;
;; ---- End of "visiting" ----
;;
;; 3. Check the top-level types and produce an error if any weren't marked.
;;
;; 4. Operating on the restricted graph containing only the marked types,
;;    constrict the graph to be on the flextype objects for the marked types.
;;
;; 5. Topologically sort the flextype graph.
;;
;; 6. For each flextype in topological order, issue a defvisitor form to create
;;    the appropriate visitors.




;; Step 1.  Create graph mapping types to member types ------------------------


;; visitor-field-collect-member-types and
;; visitor-membertype-collect-member-types are like finding the ACTION above.
;; Instead of returning the action, we return the list of types to recur on
;; (either one or none), and the leaf-p flag (which applies to the containing
;; type, not the member type).
(define visitor-membertype-collect-member-types (type x wrld)
  :returns (mv subtypes is-leaf-p)
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

(define visitor-field-collect-member-types (field x prod-entry wrld)
  :returns (mv subtypes is-leaf-p)
  (b* (((flexprod-field field))
       ((visitorspec x))
       (field-entry (or (assoc field.name prod-entry)
                        (assoc field.name x.field-fns)))
       ((when field-entry)
        (b* ((fn (cdr field-entry)))
          ;; We don't add a subtype or leaftype for this, but if it's a
          ;; non-skip entry we make this sum/product a leaftype.
          (mv nil (and fn (not (eq fn :skip))))))
       ;; See how to determine ACTION above.  Here there is no :field-fns or
       ;; :prod-fns override, so just fall through to looking at the field's
       ;; type.
       ((mv subtypes is-leaf)
        (visitor-membertype-collect-member-types field.type x wrld)))
    (mv subtypes is-leaf)))

(define visitor-fields-collect-member-types (fields x prod-entry wrld)
  :returns (mv subtypes is-leaf-p)
  (b* (((when (atom fields)) (mv nil nil))
       ((mv subtypes1 is-leaf-type-p1)
        (visitor-field-collect-member-types (car fields) x prod-entry wrld))
       ((mv subtypes2 is-leaf-type-p2)
        (visitor-fields-collect-member-types (cdr fields) x prod-entry wrld)))
    (mv (union-eq subtypes1 subtypes2)
        (or is-leaf-type-p1 is-leaf-type-p2))))

(define visitor-prods-collect-member-types (prods x wrld)
  :returns (mv subtypes is-leaf-p)
  (b* (((when (atom prods))
        (mv nil nil))
       ((visitorspec x))
       ((flexprod prod1) (car prods))
       (prod-entry (cdr (assoc prod1.type-name x.prod-fns)))
       ((mv subtypes1 is-leaf-type1) (visitor-fields-collect-member-types prod1.fields x prod-entry wrld))
       ((mv subtypes2 is-leaf-type2) (visitor-prods-collect-member-types (cdr prods) x wrld)))
    (mv (union-eq subtypes1 subtypes2)
        (or is-leaf-type1 is-leaf-type2))))

(define visitor-sumtype-collect-member-types (type x wrld)
  :returns (mv subtypes is-leaf-p)
  (b* (((flexsum type)))
    (visitor-prods-collect-member-types type.prods x wrld)))

(define visitor-listtype-collect-member-types (type x wrld)
  :returns (mv subtypes is-leaf-p)
  (b* (((flexlist type)))
    (visitor-membertype-collect-member-types type.elt-type x wrld)))

(define visitor-alisttype-collect-member-types (type x wrld)
  :returns (mv subtypes is-leaf-p)
  (b* (((flexalist type))
       ((mv subtypes1 is-leaf1) (visitor-membertype-collect-member-types type.key-type x wrld))
       ((mv subtypes2 is-leaf2) (visitor-membertype-collect-member-types type.val-type x wrld)))
    (mv (union-eq subtypes1 subtypes2)
        (or is-leaf1 is-leaf2))))

(define visitor-transsum-members-without-actions (typenames x)
  ;; Which member types of a transsum should we recur through when we are marking
  ;; types to be visited?  Only the ones where the action is NONE.
  (b* (((when (atom typenames))
        nil)
       ((visitorspec x))
       (type-entry (assoc (car typenames) x.type-fns))
       ((when (cdr type-entry))
        ;; The action is not NONE.
        (visitor-transsum-members-without-actions (cdr typenames) x)))
    (cons (car typenames)
          (visitor-transsum-members-without-actions (cdr typenames) x))))

(define visitor-transsum-is-leaf (typenames x)
  ;; When should the transsum be considered a leaf?  When it has any member that
  ;; has an action that is not SKIP and not NONE.
  (b* (((when (atom typenames)) nil)
       ((visitorspec x))
       (type (car typenames))
       (type-entry (assoc type x.type-fns))
       ((when (and (cdr type-entry)
                   (not (eq (cdr type-entry) :skip))))
        t))
    (visitor-transsum-is-leaf (cdr typenames) x)))

(define visitor-transsumtype-collect-member-types (type x wrld)
  :returns (mv subtypes is-leaf-p)
  (declare (ignorable x wrld))
  (b* (((flextranssum type))
       (all-subtypes (flextranssum-memberlist->typenames type.members))
       (new-subtypes (visitor-transsum-members-without-actions all-subtypes x))
       (is-leaf-p    (visitor-transsum-is-leaf all-subtypes x)))
    (mv new-subtypes is-leaf-p)))

(define visitor-type-collect-member-types ((typename)
                                           (x "The visitorspec object.")
                                           wrld)
  (b* (((mv ?fty type-obj)
        (search-deftypes-table typename (table-alist 'flextypes-table wrld)))
       ((unless type-obj)
        (cw "WARNING: Expected to find deftypes table entry for ~x0 but didn't~%" typename)
        (mv nil nil)))
    (case (tag type-obj)
      ;; bozo should be using with-flextype-bindings eh?
      (:sum      (visitor-sumtype-collect-member-types type-obj x wrld))
      (:list     (visitor-listtype-collect-member-types type-obj x wrld))
      (:alist    (visitor-alisttype-collect-member-types type-obj x wrld))
      (:transsum (visitor-transsumtype-collect-member-types type-obj x wrld))
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

(define visitor-reverse-graph-putlist (froms to revgraph)
  (b* (((when (atom froms))
        revgraph)
       (old-val (cdr (hons-get (car froms) revgraph)))
       (new-val (cons to old-val))
       (revgraph (hons-acons (car froms) new-val revgraph)))
    (visitor-reverse-graph-putlist (cdr froms) to revgraph)))

(define visitor-reverse-graph-aux (graph)
  (b* (((when (atom graph))
        nil)
       (revgraph (visitor-reverse-graph-aux (cdr graph))))
    (visitor-reverse-graph-putlist (cdar graph) (caar graph) revgraph)))

(define visitor-reverse-graph (graph)
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

(define visitor-check-top-types (types marks)
  (cond ((atom types)
         nil)
        ((cdr (hons-get (car types) marks))
         (visitor-check-top-types (cdr types) marks))
        (t
         (raise "Type ~x0 doesn't have any descendants that need visiting."
                (car types)))))

(define visitor-types-filter-marked (types marks)
  (cond ((atom types)
         nil)
        ((cdr (hons-get (car types) marks))
         (cons (car types)
               (visitor-types-filter-marked (cdr types) marks)))
        (t
         (visitor-types-filter-marked (cdr types) marks))))


(define visitor-members-to-ftys (memb-types deftypes-table)
  (b* (((when (atom memb-types)) nil)
       ((mv fty ?ftype) (search-deftypes-table (car memb-types) deftypes-table))
       ((unless fty)
        (cw "Warning: didn't find ~x0 in deftypes table~%" (car memb-types)))
       ((flextypes fty)))
    (add-to-set-eq fty.name
                   (visitor-members-to-ftys (cdr memb-types) deftypes-table))))

(define visitor-to-fty-graph (type-graph marks deftypes-table fty-graph)
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

(define visitor-type-to-fty (type deftypes-table)
  (b* (((mv fty ?ftype) (search-deftypes-table type deftypes-table))
       ((unless fty)
        (raise "Didn't find ~x0 in deftypes table" type))
       ((flextypes fty)))
    fty.name))

(define visitor-types-to-ftys (types deftypes-table)
  (if (atom types)
      nil
    (cons (visitor-type-to-fty (car types) deftypes-table)
          (visitor-types-to-ftys (cdr types) deftypes-table))))

(define visitor-fty-defvisitor-form (fty-name order marks template-name deftypes-table kwd-alist)
  (b* ((fty (cdr (assoc fty-name deftypes-table)))
       ((unless fty)
        (raise  "Didn't find ~x0 in the deftypes table~%" fty-name))
       (measure-look (assoc :measure kwd-alist)))
    `(defvisitor :template ,template-name :type ,fty-name
       :include-types ,(visitor-types-filter-marked
                        (flextypelist-names (flextypes->types fty))
                        marks)
       :order ,order
       ,@(and measure-look `(:measure ,(cdr measure-look))))))

(define visitor-defvisitor-forms (toposort order marks template-name deftypes-table kwd-alist)
  (if (atom toposort)
      nil
    (cons (visitor-fty-defvisitor-form (car toposort) order marks template-name deftypes-table kwd-alist)
          (visitor-defvisitor-forms (cdr toposort) (+ 1 order) marks template-name deftypes-table kwd-alist))))

(define process-defvisitors (kwd-alist wrld)
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



(define defvisitors-fn (args wrld)
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

(define process-defvisitor-multi (args wrld)
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
        (process-defvisitor 'bozo-fixme-name-for-process-defvisitor-multi
                            kwd-alist wrld))

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



(define defvisitor-multi-fn (args wrld)
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


;; [Jared] this doesn't seem to be used anywhere?

;; (define update-type-visitor-fn (visitor type fn world)
;;   (b* (((visitorspec x)
;;         (cdr (assoc visitor
;;                     (table-alist 'visitor-templates world)))))
;;     (change-visitorspec
;;      x :type-fns (cons (cons (visitor-normalize-fixtype type world) fn) x.type-fns))))

;; (defmacro update-type-visitor (visitor type fn)
;;   `(table visitor-templates
;;           ',visitor
;;           (update-type-visitor-fn ',visitor ',type ',fn world)))

