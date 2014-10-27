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
; Original author: Jared Davis <jared@centtech.com> (VL package)
;                   Sol Swords <sswords@centtech.com> (this book)

(in-package "VL")

(include-book "expr-tools")
(include-book "../parsetree")
(local (std::add-default-post-define-hook :fix))
(local (defun types-mk-strsubst-alists (types)
         (if (atom types)
             nil
           (let ((name (symbol-name (car types))))
             (cons `(("__TYPE__" ,name . vl-package)
                     ("__ELTS__" ,(if (member (char name (1- (length name))) '(#\S #\s))
                                      (str::cat name "ES")
                                    (str::cat name "S")) . vl-package))
                   (types-mk-strsubst-alists (cdr types)))))))

(local (defun project-over-types-rec (template strsubst-alists)
         (declare (xargs :mode :program))
         (if (atom strsubst-alists)
             nil
           (cons (b* (((mv & val)
                       (acl2::template-subst-rec nil nil nil (car strsubst-alists)
                                                 template 'vl-package)))
                   val)
                 (project-over-types-rec template (cdr strsubst-alists))))))

(local (defun append-over-types-rec (template strsubst-alists)
         (declare (xargs :mode :program))
         (if (atom strsubst-alists)
             nil
           (append (b* (((mv & val)
                         (acl2::template-subst-rec nil nil nil (car strsubst-alists)
                                                   template 'vl-package)))
                     val)
                   (append-over-types-rec template (cdr strsubst-alists))))))

(local (defun project-over-types (template)
         (declare (xargs :mode :program))
         (project-over-types-rec template (types-mk-strsubst-alists *vl-modelement-typenames*))))

(local (defun append-over-types (template)
         (declare (xargs :mode :program))
         (append-over-types-rec template (types-mk-strsubst-alists *vl-modelement-typenames*))))


(make-event
 `(define vl-module->genblob ((x vl-module-p))
    :returns (genblob vl-genblob-p)
    (b* (((vl-module x)))
      (make-vl-genblob
       ,@(append-over-types-rec
          '(:__elts__ x.__elts__)
          (types-mk-strsubst-alists
           '(import port portdecl vardecl paramdecl fundecl taskdecl assign modinst gateinst always initial)))
       :generates x.generates))))

(make-event
 `(define vl-genblob->module ((x vl-genblob-p)
                                            (orig vl-module-p))
    :returns (new-mod vl-module-p)
    (b* (((vl-genblob x)))
      (change-vl-module orig
                        ,@(append-over-types-rec
                           '(:__elts__ x.__elts__)
                           (types-mk-strsubst-alists
                            '(import port portdecl vardecl
                                     paramdecl fundecl taskdecl
                                     assign modinst gateinst
                                     always initial)))))))


(make-event
 `(define vl-genblob->elems-aux  ((orig-elements vl-genelementlist-p)
                                                ,@(project-over-types
                                                   '(__elts__ vl-__type__list-p))
                                                (generates vl-genelementlist-p)
                                                (acc vl-genelementlist-p))
    :measure (len orig-elements)
    :returns (final-acc vl-genelementlist-p)
    :prepwork ((local (in-theory (disable acl2::true-listp-append
                                          acl2::consp-of-append
                                          acl2::subsetp-append1
                                          append
                                          consp-when-member-equal-of-cons-listp
                                          acl2::append-when-not-consp
                                          ,@(project-over-types
                                             'vl-__type__list-p-of-append)))))
    :hooks nil
    (b* (((when (atom orig-elements))
          (revappend-without-guard
           (vl-genelementlist-fix acc)
           (append-without-guard
            (vl-modelementlist->genelements
             (append-without-guard
              ,@(project-over-types '__elts__)))
            (vl-genelementlist-fix generates)))))
      (vl-genelement-case (x (car orig-elements))
        :vl-genbase
        (case (tag x.item)
          ,@(project-over-types
             `(:vl-__type__ (b* (((mv acc __elts__)
                                  (if (consp __elts__)
                                      (mv (cons (make-vl-genbase :item (vl-__type__-fix (car __elts__))) acc)
                                          (cdr __elts__))
                                    (mv acc __elts__))))
                              (vl-genblob->elems-aux
                               (cdr orig-elements)
                               ,@(project-over-types '__elts__)
                               generates
                               acc)))))
        :otherwise (b* (((mv acc generates)
                         (if (consp generates)
                             (mv (cons (car generates) acc)
                                 (cdr generates))
                           (mv acc generates))))
                     (vl-genblob->elems-aux
                      (cdr orig-elements)
                      ,@(project-over-types '__elts__)
                      generates
                      acc))))))

(make-event
 `(define vl-genblob->elems
    ((x vl-genblob-p "the current genblob of elements")
     (orig-elements vl-genelementlist-p
                    "the original elements, used to determine the ordering of the
                     current elements will be sorted"))
    :returns (new-elements vl-genelementlist-p "flattened list of elements from genblob")
    (b* (((vl-genblob x))) 
      (vl-genblob->elems-aux
       (vl-genelementlist-fix orig-elements)
       ,@(project-over-types 'x.__elts__)
       x.generates nil))))





(make-event
 `(defthm vl-genelementlist-count-of-vl-sort-genelements-aux 
    (b* (((mv ,@(project-over-types '?__elts__1) generates1)
          (vl-sort-genelements-aux
           x ,@(project-over-types '__elts__) generates)))
      (<= (vl-genelementlist-count generates1)
          (+ -1 (vl-genelementlist-count x)
             (vl-genelementlist-count generates))))
    :hints(("Goal" :induct (vl-sort-genelements-aux
                            x ,@(project-over-types '__elts__) generates)
            :in-theory (e/d ((:i vl-sort-genelements-aux)
                             vl-genelementlist-count) 
                            (not))
            :expand ((vl-sort-genelements-aux
                      x ,@(project-over-types '__elts__) generates))))
    :rule-classes :linear))

(defthm vl-genelementlist-count-of-vl-sort-genelements
  (<= (vl-genelementlist-count (vl-genblob->generates (vl-sort-genelements x)))
      (vl-genelementlist-count x))
  :hints(("Goal" :in-theory (enable vl-sort-genelements)))
  :rule-classes :linear)


(defines vl-genblob-count
  (define vl-genblob-count ((x vl-genblob-p))
    :measure (two-nats-measure (vl-genelementlist-count (vl-genblob->generates x)) 10)
    :returns (count posp :rule-classes :type-prescription)
    (+ 1 (vl-genblob-generates-count (vl-genblob->generates x)))
    ///
    (more-returns
     (count :name vl-genblob-count-greater-than-generates
            (< (vl-genblob-generates-count (vl-genblob->generates x))
               count)
            :rule-classes :linear)))

  (define vl-genblob-generates-count ((x vl-genelementlist-p))
    :measure (two-nats-measure (vl-genelementlist-count x) 5)
    :returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        1
      (+ 1 (vl-genblob-generate-count (car x))
         (vl-genblob-generates-count (cdr x))))
    ///
    (more-returns
     (count :name vl-genblob-generates-count-greater-than-first
            (implies (consp x)
                     (< (vl-genblob-generate-count (car x))
                        count))
            :rule-classes :linear)
     (count :name vl-genblob-generates-count-gte-rest
            (<= (vl-genblob-generates-count (cdr x))
                count)
            :rule-classes :linear)
     (count :name vl-genblob-generates-count-greater-than-rest
            (implies (consp x)
                     (< (vl-genblob-generates-count (cdr x))
                        count))
            :rule-classes :linear)))

  (define vl-genblob-generate-count ((x vl-genelement-p))
    :measure (two-nats-measure (vl-genelement-count x) 10)
    :returns (count posp :rule-classes :type-prescription)
    (vl-genelement-case x
      :vl-genblock (+ 2 (vl-genblob-elementlist-count x.elems))
      :vl-genarray (+ 2 (vl-genblob-genarrayblocklist-count x.blocks))
      :otherwise 1)
    ///
    (more-returns
     (count :name vl-genblob-generate-count-greater-than-genblock-elems
            (implies (equal (vl-genelement-kind x) :vl-genblock)
                     (< (vl-genblob-elementlist-count (vl-genblock->elems x))
                        count))
            :rule-classes :linear)
     (count :name vl-genblob-generate-count-greater-than-genblockarray-blocks
            (implies (equal (vl-genelement-kind x) :vl-genarray)
                     (< (vl-genblob-genarrayblocklist-count (vl-genarray->blocks x))
                        count))
            :rule-classes :linear)))

  (define vl-genblob-elementlist-count ((x vl-genelementlist-p))
    :measure (two-nats-measure (vl-genelementlist-count x) 15)
    :returns (count posp :rule-classes :type-prescription)
    (+ 1 (vl-genblob-count (vl-sort-genelements x)))
    ///
    (more-returns
     (count :name vl-genblob-elementlist-count-greater-than-genblob-count
            (< (vl-genblob-count (vl-sort-genelements x))
               count)
            :rule-classes :linear)))

  (define vl-genblob-genarrayblocklist-count ((x vl-genarrayblocklist-p))
    :measure (two-nats-measure (vl-genarrayblocklist-count x) 10)
    :returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        1
      (+ 1 (vl-genblob-genarrayblock-count (car x))
         (vl-genblob-genarrayblocklist-count (cdr x))))
    ///
    (more-returns
     (count :name vl-genblob-genarrayblocklist-count-greater-than-first
            (implies (consp x)
                     (< (vl-genblob-genarrayblock-count (car x))
                        count))
            :rule-classes :linear)
     (count :name vl-genblob-genarrayblocklist-count-gte-rest
            (<= (vl-genblob-genarrayblocklist-count (cdr x))
                count)
            :rule-classes :linear)
     (count :name vl-genblob-genarrayblocklist-count-greater-than-rest
            (implies (consp x)
                     (< (vl-genblob-genarrayblocklist-count (cdr x))
                        count))
            :rule-classes :linear)))

  (define vl-genblob-genarrayblock-count ((x vl-genarrayblock-p))
    :measure (two-nats-measure (vl-genarrayblock-count x) 15)
    :returns (count posp :rule-classes :type-prescription)
    (+ 1 (vl-genblob-elementlist-count (vl-genarrayblock->elems x)))
    ///
    (more-returns
     (count :name vl-genblob-genarrayblock-count-greater-than-elems
            (< (vl-genblob-elementlist-count (vl-genarrayblock->elems x))
               count)
            :rule-classes :linear))))
      

;; Example def-genblob-transform:

;; (def-genblob-transform my-transform (;; implicitly,
;;                                      ;; (x vl-genblob-p)
;;                                      (ss vl-scopestack-p)
;;                                      (warnings vl-warninglist-p))
;;   :returns (mv (okp booleanp :rule-classes :type-prescription)
;;                (warnings vl-warninglist-p)
;;                ;; implicitly,
;;                ;; (new-x vl-genblob-p)
;;                )
;;   :apply-to-generates my-transform-on-generates
;;   (b* (((vl-genblob x))
;;        (ss (vl-scopstack-push (vl-genblob-fix x) ss))
;;        ((mv okp1 warnings new-assigns) (vl-transform-assigns x.assigns ss warnings))
;;        ((mv okp2 warnings new-generates) (my-transform-on-generates x.generates ss warnings))
;;        (res (change-vl-genblob x :assigns new-assigns :generates new-generates)))
;;     (mv (and okp1 okp2) warnings res))
;;   :combine-bindings ((okp (and okp1 okp2)))
;;   :empty-list-bindings ((okp t))
;;   :bad-generate-bindings ((okp nil)))

(program)
(set-state-ok t)
(defun formals->fixes (names formals fty-table)
  (declare (xargs :mode :program))
  (b* (((when (atom names)) nil)
       (first (fty::find-formal-by-name (car names) formals))
       (type (fty::fixequiv-type-from-guard (std::formal->guard first)))
       (fixtype (fty::find-fixtype-for-pred type fty-table)))
    (if fixtype
        (cons `(,(car names) (,(fty::fixtype->fix fixtype) ,(car names)))
              (formals->fixes (cdr names) formals fty-table))
      (formals->fixes (cdr names) formals fty-table))))
       

(defun assigns-for-getargs (args alist)
  (if (atom args)
      nil
    (cons (b* (((mv sym default) (if (consp (car args))
                                     (mv (caar args) (cadar args))
                                   (mv (car args) nil)))
               ((mv basesym ?ign) (acl2::decode-varname-for-patbind sym)))
            `(,sym (std::getarg ,(intern$ (symbol-name basesym) "KEYWORD") ,default ,alist)))
          (assigns-for-getargs (cdr args) alist))))

(acl2::def-b*-binder getargs
  :short "@(see b*) binder for getargs on a keyword alist."
  :long "<p>Usage:</p>
@({
    (b* (((getargs a
                   (b b-default-term)
                   c
                   d)
          alst))
      form)
})

<p>is equivalent to</p>

@({
    (b* ((a (getarg :a nil alst))
         (b (getarg :b b-default-term alst))
         (c (getarg :c nil alst)))
      form)
})"

  :body
  (mv-let (pre-bindings name rest)
    (if (and (consp (car acl2::forms))
             (not (eq (caar acl2::forms) 'quote)))
        (mv `((?tmp-for-getargs ,(car acl2::forms)))
            'tmp-for-getargs
            `(check-vars-not-free (tmp-for-getargs)
                            ,acl2::rest-expr))
      (mv nil (car acl2::forms) acl2::rest-expr))
    `(b* (,@pre-bindings
          . ,(assigns-for-getargs args name))
       ,rest)))
  
(defconst *def-genblob-transform-keywords*
  '(:apply-to-generates
    :returns
    :combine-bindings
    :empty-list-bindings
    :genblock-bindings
    :return-from-genblock-bindings
    :genarray-bindings
    :return-from-genarray-bindings
    :genarrayblock-bindings
    :return-from-genarrayblock-bindings
    :elementlist-bindings
    :bad-generate-bindings
    :verify-guards
    :guard-hints))

(defun kwd-alist->filtered-key-args (kwd-alist omit-names)
  (if (atom kwd-alist)
      nil
    (if (member (caar kwd-alist) omit-names)
        (kwd-alist->filtered-key-args (cdr kwd-alist) omit-names)
      (cons (caar kwd-alist)
            (cons (cdar kwd-alist)
                  (kwd-alist->filtered-key-args (cdr kwd-alist) omit-names))))))

(defun suffix-syms (names suffix std::mksym-package-symbol)
  (if (atom names)
      nil
    (cons (std::mksym (car names) suffix)
          (suffix-syms (cdr names) suffix std::mksym-package-symbol))))

(defun maybe-mv-fn (args)
  (if (eql (len args) 1)
      (car args)
    (cons 'mv args)))

(defmacro maybe-mv (&rest args)
  (maybe-mv-fn args))

(acl2::def-b*-binder maybe-mv
  :body
  `(b* ((,(if (eql (len acl2::args) 1)
              (car acl2::args)
            (cons 'mv acl2::args))
         ,@acl2::forms))
     ,acl2::rest-expr))


(defun def-genblob-transform-fn (name    ;; name of main function
                                 args
                                 state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((__function__ 'def-genblob-transform)
       (std::mksym-package-symbol name)
       (wrld (w state))
       ((unless (symbolp name))
        (raise "Expected a symbol for the name of the main function, not ~x0" name))
       ((mv main-stuff rest-events) (std::split-/// name args))
       ((mv kwd-alist normal-defun-stuff)
        (std::extract-keywords name (append *def-genblob-transform-keywords* std::*define-keywords*)
                          main-stuff nil))
       (raw-formals            (car normal-defun-stuff))
       (traditional-decls/docs (butlast (cdr normal-defun-stuff) 1))
       (body                   (car (last normal-defun-stuff)))
       
       ((getargs (apply-to-generates (std::mksym name '-generates))
                 returns
                 combine-bindings
                 empty-list-bindings
                 genblock-bindings
                 return-from-genblock-bindings
                 genarray-bindings
                 return-from-genarray-bindings
                 genarrayblock-bindings
                 return-from-genarrayblock-bindings
                 elementlist-bindings
                 return-from-elementlist-bindings
                 bad-generate-bindings
                 (verify-guards t)
                 guard-hints)
        kwd-alist)
       
       (define-keys (kwd-alist->filtered-key-args
                     kwd-alist *def-genblob-transform-keywords*))

       (formal-infos (std::parse-formals name raw-formals nil wrld))
       (formal-names (std::formallist->names formal-infos))
       (return-infos (std::parse-returnspecs-aux name returns wrld))
       (return-names (std::returnspeclist->names return-infos))
       ((when (member 'x formal-names))
        (raise "X shouldn't be among the formals -- it's implicit."))
       ((when (or (member 'x return-names)
                  (member 'new-x return-names)))
        (raise "X or NEW-X shouldn't be among the returns -- it's implicit."))
       (accumulators (intersection-eq return-names formal-names))
       ;; return names need to come first so that we preserve their order and
       ;; the return-names-ordered check doesn't fail

       (?extra-formals (set-difference-eq formal-names accumulators))
       (extra-returns (set-difference-eq return-names accumulators))

       (apply-to-elementlist (std::mksym name '-elementlist))
       (apply-to-generate    (std::mksym name '-generate))
       (apply-to-genarrayblock     (std::mksym name '-genarrayblock))
       (apply-to-genarrayblocklist (std::mksym name '-genarrayblocklist))

       (return-names-ordered (append extra-returns accumulators))

       ((unless (equal return-names-ordered return-names))
        (raise "Return names must be ordered so that all non-accumulators precede all accumulators"))

       (return-names1 (append (suffix-syms extra-returns '|1| std::mksym-package-symbol) accumulators))
       (return-names2 (append (suffix-syms extra-returns '|2| std::mksym-package-symbol) accumulators))
       (acc-fix-bindings (formals->fixes accumulators formal-infos (fty::get-fixtypes-alist wrld))))
    `(defines ,name
       
       (define ,name ((x vl-genblob-p)
                      . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  (new-x vl-genblob-p)))
         :measure (vl-genblob-count x)
         :verify-guards nil
         ,@define-keys
         ,@traditional-decls/docs
         ,body)

       (define ,apply-to-generates ((x vl-genelementlist-p)
                                    . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  (new-x vl-genelementlist-p)))
         :measure (vl-genblob-generates-count x)
         (b* (((when (atom x))
               (b* (,@acc-fix-bindings
                    ,@empty-list-bindings)
                 (maybe-mv ,@return-names nil)))
              ((maybe-mv ,@return-names1 first)
               (,apply-to-generate (car x) . ,formal-names))
              ((maybe-mv ,@return-names2 rest)
               (,apply-to-generates (cdr x) . ,formal-names))
              . ,combine-bindings)
           (maybe-mv ,@return-names (cons first rest))))

       (define ,apply-to-generate ((x vl-genelement-p)
                                   . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  (new-x vl-genelement-p)))
         :measure (vl-genblob-generate-count x)
         (vl-genelement-case x
           :vl-genblock (b* (,@genblock-bindings
                             ((maybe-mv ,@return-names new-elems)
                              (,apply-to-elementlist x.elems . ,formal-names))
                             ,@return-from-genblock-bindings)
                          (maybe-mv ,@return-names (change-vl-genblock x :elems new-elems)))
           :vl-genarray (b* (,@genarray-bindings
                             ((maybe-mv ,@return-names new-blocks)
                              (,apply-to-genarrayblocklist x.blocks . ,formal-names))
                             ,@return-from-genarray-bindings)
                          (maybe-mv ,@return-names (change-vl-genarray x :blocks new-blocks)))
           :otherwise (b* (,@acc-fix-bindings
                           ,@bad-generate-bindings)
                        (maybe-mv ,@return-names (vl-genelement-fix x)))))

       (define ,apply-to-elementlist ((x vl-genelementlist-p)
                                      . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  (new-x vl-genelementlist-p)))
         :measure (vl-genblob-elementlist-count x)
         (b* (,@elementlist-bindings
              ((maybe-mv ,@return-names new-blob)
               (,name (vl-sort-genelements x) . ,formal-names))
              ,@return-from-elementlist-bindings)
           (maybe-mv ,@return-names (vl-genblob->elems new-blob x))))

       (define ,apply-to-genarrayblocklist ((x vl-genarrayblocklist-p)
                                            . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  (new-x vl-genarrayblocklist-p)))
         :measure (vl-genblob-genarrayblocklist-count x)
         (b* (((when (atom x))
               (b* (,@acc-fix-bindings
                    ,@empty-list-bindings)
                 (maybe-mv ,@return-names nil)))
              ((maybe-mv ,@return-names1 first) (,apply-to-genarrayblock (car x) . ,formal-names))
              ((maybe-mv ,@return-names2 rest) (,apply-to-genarrayblocklist (cdr x) . ,formal-names))
              . ,combine-bindings)
           (maybe-mv ,@return-names (cons first rest))))

       (define ,apply-to-genarrayblock ((x vl-genarrayblock-p)
                                        . ,raw-formals)
         :returns ,(maybe-mv-fn `(,@returns
                                  (new-x vl-genarrayblock-p)))
         :measure (vl-genblob-genarrayblock-count x)
         (b* (((vl-genarrayblock x))
              ,@genarrayblock-bindings
              ((maybe-mv ,@return-names new-elems) (,apply-to-elementlist x.elems . ,formal-names))
              ,@return-from-genarrayblock-bindings)
           (maybe-mv ,@return-names (change-vl-genarrayblock x :elems new-elems))))
       ///
       (local (in-theory (disable ,apply-to-genarrayblock
                                ,apply-to-genarrayblocklist
                                ,apply-to-elementlist
                                ,apply-to-generate
                                ,apply-to-generates
                                ,name)))
       ,@(and verify-guards `((verify-guards ,name :hints ,guard-hints)))
       (deffixequiv-mutual ,name
         :hints ((and stable-under-simplificationp
                      (flag::expand-calls-computed-hint
                       clause '(,apply-to-genarrayblock
                                ,apply-to-genarrayblocklist
                                ,apply-to-elementlist
                                ,apply-to-generate
                                ,apply-to-generates
                                ,name)))))
       ,@rest-events)))

(defmacro def-genblob-transform (name &rest args)
  `(make-event
    (def-genblob-transform-fn ',name ',args state)))


