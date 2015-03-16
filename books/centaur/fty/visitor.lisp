; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(defun visitor-return-decls (returns type-pred type-fix)
  (b* ((returns (if (and (consp returns)
                         (eq (car returns) 'mv))
                    (cdr returns)
                  (list returns)))
       (lst (visitor-return-decls-aux returns type-pred type-fix)))
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
         `(,(std::da-changer-name prod.ctor-name)
           ,x.xvar ,@changer-args)
         x))))


(defun visitor-measure (x default)
  (b* (((visitorspec x)))
    (if x.measure
        (subst default :count x.measure)
      default)))

(defun visitor-prod-def (type x mrec)
  (b* (((flexsum type))
       ((visitorspec x))
       ((flexprod prod) (car type.prods))
       (name (visitor-name x type.name)))
    `(define ,name ,(subst type.pred :object x.formals)
       ,@(and mrec
              `(:measure ,(visitor-measure x `(,type.count ,x.xvar))))
       :returns ,(visitor-return-decls x.returns type.pred type.fix)
       :verify-guards nil
       :hooks nil
       (b* (((,prod.ctor-name ,x.xvar) (,type.fix ,x.xvar)))
         ,(visitor-prod-body prod x))
       ///
       ,@(and (not mrec) `(,@(and x.fixequivs
                                  `((deffixequiv ,name)))
                             (local (in-theory (disable ,name)))
                             (verify-guards ,name))))))

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
       ,@(and (or mrec type.recp)
              `(:measure ,(visitor-measure x `(,type.count ,x.xvar))))
       :returns ,(visitor-return-decls x.returns type.pred type.fix)
       :verify-guards nil
       :hooks nil
       (,type.case ,x.xvar
         . ,(visitor-prod-bodies type.prods x))
       ///
       ,@(and (not mrec) `(,@(and x.fixequivs
                                  `((deffixequiv ,name)))
                             (local (in-theory (disable ,name)))
                             (verify-guards ,name)
                             )))))
                        



(defun visitor-list-def (type x mrec)
  (b* (((flexlist type))
       ((visitorspec x))
       (name (visitor-name x type.name))
       (elt-fnname (visitor-field-fn nil type.elt-type nil x))
       ((unless elt-fnname)
        (er hard? 'defvisitor "Nothing to do for list type ~x0 -- use :skip." type.name)))
    `(define ,name ,(subst type.pred :object x.formals)
       :measure ,(visitor-measure x (if type.count
                                        `(,type.count ,x.xvar)
                                      `(len ,x.xvar)))
       :returns ,(visitor-return-decls x.returns type.pred type.fix)
       :verify-guards nil
       :hooks nil
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
       ,@(and (not mrec) `(,@(and x.fixequivs
                                  `((deffixequiv ,name)))
                             (local (in-theory (disable ,name)))
                             (verify-guards ,name))))))



(defun visitor-alist-def (type x mrec)
  (b* (((flexalist type))
       ((visitorspec x))
       (name (visitor-name x type.name))
       (key-fnname (visitor-field-fn nil type.key-type nil x))
       (val-fnname (visitor-field-fn nil type.val-type nil x))
       ((unless (or key-fnname val-fnname))
        (er hard? 'defvisitor "Nothing to do for alist type ~x0 -- use :skip." type.name)))
    `(define ,name ,(subst type.pred :object x.formals)
       :measure ,(visitor-measure x (if type.count
                                        `(,type.count ,x.xvar)
                                      `(len (,type.fix ,x.xvar))))
       :returns ,(visitor-return-decls x.returns type.pred type.fix)
       :verify-guards nil
       :hooks nil
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
       ,@(and (not mrec) `(,@(and x.fixequivs
                                  `((deffixequiv ,name)))
                             (local (in-theory (disable ,name)))
                             (verify-guards ,name))))))


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
     :locally-enable nil
     ,@other-fns
     ,@(visitor-mutual-aux types x)
     ///
     (verify-guards ,(visitor-name x
                                   (with-flextype-bindings (type (car types))
                                     type.name)))
     ,@(and x.fixequivs
            `((deffixequiv-mutual ,(visitor-name x type-name)))))))

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
                   (and fixp (list (cons formal fix)))
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
    :fnname-template :fixequivs))

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
           :xvar (visitor-xvar-from-formals formals)
           :fixequivs (std::getarg :fixequivs t kwd-alist))))
    x))

(defun defvisitor-template-fn (name args)
  `(table visitor-templates ',name
          (defvisitor-template-main ',name ',args world)))

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
              



(defconst *defvisitor-for-deftype-keys*
  '(:type :template :type-fns :field-fns :prod-fns
    :fnname-template :renames :omit-types :include-types
    :measure
    :parents :short :long))


(defun defvisitor-for-deftype-fn (args wrld)
  (b* (((mv name args)
        (if (and (symbolp (car args))
                 (not (keywordp (car args))))
            (mv (car args) (cdr args))
          (mv nil args)))
       ((mv pre-/// post-///) (std::split-/// 'defvisitor-for-deftype args))
       ((mv kwd-alist mrec-fns)
        (extract-keywords 'defvisitor-for-deftype *defvisitor-for-deftype-keys* pre-/// nil))
       (template (cdr (assoc :template kwd-alist)))
       (type (cdr (assoc :type kwd-alist)))
       ((unless (and template type))
        (er hard? 'defvisitor-for-deftype ":type and :template arguments are mandatory"))

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

       (omit-types (cdr (assoc :omit-types kwd-alist)))
       (include-types (cdr (assoc :include-types kwd-alist)))
       ((when (and omit-types include-types))
        (er hard? 'defvisitor ":omit-types and :include-types are mutually exclusive"))
       (types (cond (include-types
                     (visitor-include-types fty.types include-types))
                    (omit-types
                     (visitor-omit-types fty.types omit-types))
                    (t fty.types)))

       (fnname-template (or (cdr (assoc :fnname-template kwd-alist))
                            x1.fnname-template))
       (- (visitor-check-fnname-template fnname-template))
       (renames (cdr (assoc :renames kwd-alist)))
       (x1-with-renaming (change-visitorspec x1 :fnname-template fnname-template
                                             :renames renames))
       (unbound-types (visitor-omit-bound-types types x1.type-fns))
       (new-type-fns (append (visitor-add-type-fns unbound-types x1-with-renaming)
                             x1.type-fns))

       ;; this will be the visitorspec that we store in the table afterward; we
       ;; assume the renamings are temporary.
       (x (change-visitorspec x1 :type-fns new-type-fns
                              :field-fns x1.field-fns
                              :prod-fns x1.prod-fns))

       (local-x
        (change-visitorspec x :wrld wrld
                            :fnname-template fnname-template
                            :renames renames
                            :measure (cdr (assoc :measure kwd-alist))))
       (event-name (or name (visitor-name local-x type)))
       (def (if (and (eql (len types) 1)
                     (atom mrec-fns))
                (visitor-def (car types) local-x nil)
              (visitor-mutual type types local-x mrec-fns))))
    `(defsection-progn ,event-name
       ,(append def post-///)
       (table visitor-templates ',template ',x))))

(defmacro defvisitor-for-deftype (&rest args)
  `(make-event
    (defvisitor-for-deftype-fn ',args (w state))))



(defconst *defvisitor-keys*
  '(:template    ;; visitor template to use
    :types       ;; Types targeted for toplevel functions
    :fnname-template :renames       ;; Override default function names
    ))



;; We're given the leaf functions (prod-fns, field-fns, type-fns) and the
;; top-level types that we want to visit.  Steps to determining the proper
;; sequence of defvisitor-for-deftype forms:

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
;; order, issue a defvisitor-for-deftype form to create the appropriate
;; visitors.




;; Step 1.
(defun visitor-membertype-collect-member-types (type x wrld)
  ;; returns (mv subtypes is-leaf)
  (b* (((visitorspec x))
       (type (visitor-normalize-fixtype type wrld))
       (type-entry (assoc type x.type-fns))
       ((when (and type-entry
                   (cdr type-entry)
                   (not (eq (cdr type-entry) :skip))))
        ;; Leaf type.
        (mv nil t))
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
      (er hard? 'defvisitor
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
       (fty-graph (if memb-ftys
                      (if prev-ftys
                          (hons-acons fty.name (union-eq memb-ftys prev-ftys) fty-graph)
                        (hons-acons fty.name memb-ftys fty-graph))
                    fty-graph)))
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


(defun flextypelist-names (x)
  (if (atom x)
      nil
    (cons (with-flextype-bindings (y (car x))
            y.name)
          (flextypelist-names (cdr x)))))

(defun visitor-fty-defvisitor-form (fty-name marks template-name deftypes-table)
  (b* ((fty (cdr (assoc fty-name deftypes-table)))
       ((unless fty)
        (er hard? 'defvisitor "Didn't find ~x0 in the deftypes table~%" fty-name)))
    `(defvisitor-for-deftype :template ,template-name :type ,fty-name
       :include-types ,(visitor-types-filter-marked
                        (flextypelist-names (flextypes->types fty))
                        marks))))

(defun visitor-defvisitor-forms (toposort marks template-name deftypes-table)
  (if (atom toposort)
      nil
    (cons (visitor-fty-defvisitor-form (car toposort) marks template-name deftypes-table)
          (visitor-defvisitor-forms (cdr toposort) marks template-name deftypes-table))))


(defun defvisitor-fn (args wrld)
  (b* (((mv name args)
        (if (and (symbolp (car args))
                 (not (keywordp (car args))))
            (mv (car args) (cdr args))
          (mv nil args)))
       ((mv pre-/// post-///) (std::split-/// 'defvisitor args))
       ((mv kwd-alist mrec-fns)
        (extract-keywords 'defvisitor *defvisitor-keys* pre-/// nil))
       ((when mrec-fns)
        (er hard? 'defvisitor "Extra mutually-recursive functions aren't ~
                               allowed in defvisitor, just in ~
                               defvisitor-for-deftypes."))
       (template (cdr (assoc :template kwd-alist)))
       (types (cdr (assoc :types kwd-alist)))
       (types (if (and types (atom types))
                  (list types)
                types))
       ((unless (and template (symbolp template)
                     types (symbol-listp types)))
        (er hard? 'defvisitor ":types and :template arguments are mandatory ~
                               and must be a symbol-list and symbol, ~
                               respectively"))
       (x1 (cdr (assoc template (table-alist 'visitor-templates wrld))))
       ((unless x1)
        (er hard? 'defvisitor "Template ~x0 wasn't defined" template))


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

       ;; 5.
       ((mv seen-al rev-toposort) (visitor-toposort-types (strip-cars fty-graph)
                                                          fty-graph nil nil))
       (- (fast-alist-free seen-al))

       ;; 6. 
       (forms (visitor-defvisitor-forms (reverse rev-toposort) marks template deftypes-table)))
    (cw "type graph: ~x0~%" type-graph)
    (cw "leaf types: ~x0~%" leaf-types)
    (cw "rev-graph:  ~x0~%" rev-graph)
    (cw "marks:      ~x0~%" marks)
    (cw "fty-graph:  ~x0~%" fty-graph)
    (cw "toposort:  ~x0~%" rev-toposort)

    `(defsection-progn ,name
       ,@forms
       . ,post-///)))




(defmacro defvisitor (&rest args)
  `(make-event
    (defvisitor-fn ',args (w state))))





(defun update-type-visitor-fn (visitor type fn world)
  (b* (((fty::visitorspec x)
        (cdr (assoc visitor
                    (table-alist 'fty::visitor-templates world)))))
    (fty::change-visitorspec
     x :type-fns (cons (cons (visitor-normalize-fixtype type world) fn) x.type-fns))))


(defmacro update-type-visitor (visitor type fn)
  `(table fty::visitor-templates
          ',visitor
          (update-type-visitor-fn ',visitor ',type ',fn world)))



