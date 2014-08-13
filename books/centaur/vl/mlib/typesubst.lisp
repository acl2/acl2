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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "context")
(include-book "expr-tools")
(include-book "stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc type-substitution
  :parents (mlib)
  :short "Routines for replacing named datatypes with their definitions."

  :long "<p>These functions are used by the @(see unparameterization) transform
to carry out substitutions for type parameters.  For instance, when we
encounter a module instance like:</p>

@({
    myalu #(.bustype(logic [63:0])) alu1 (...);
})

<p>We need a way to substitute the type @('logic [63:0]') everywhere for
@('bustype') throughout the submodule.</p>

<p>The main data structure here is a @(see vl-typesigma-p), which is an alist
that binds the names of datatypes (to be replaced) to the replacement
datatypes.  These generally <b>should be fast alists</b>.</p>

<p>We implement functions for applying these subtitutions throughout a parse
tree.  These functions are not particularly aware of namespace issues, so care
should be taken to ensure that, e.g., functions declarations aren't shadowing
the names of the types being substituted.</p>

<p>Our type substitution functions may fail in certain degenerate cases, for
instance, if you have an @('enum') such as</p>

@({
     enum foo_t { red, white, blue };
})

<p>then it is perfectly valid to replace @('foo_t') with @('integer'), but it
is not okay to replace @('foo_t') with, say, a tagged @('union').</p>")

(local (xdoc::set-default-parents type-substitution))

(fty::defalist vl-typesigma
  :key-type stringp
  :val-type vl-datatype-p
  :count vl-typesigma-count)

(defalist vl-typesigma-p (x)
  :short "An alist mapping strings to datatypes.  Should be fast alists."
  :key (stringp x)
  :val (vl-datatype-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :already-definedp t)



(defthm vl-typesigma-count-of-cdr-strong
  (implies (and (vl-typesigma-p x)
                (consp x))
           (< (vl-typesigma-count (cdr x))
              (vl-typesigma-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-typesigma-count))))

(defmacro def-vl-typesubst (name &key type body takes-elem verbosep)
  `(define ,name
     :short ,(cat "Substitute types into a @(see " (symbol-name type) ").")
     ((x        ,type)
      (sigma    vl-typesigma-p)
      ,@(and takes-elem '((elem vl-modelement-p)))
      (warnings vl-warninglist-p))
     :returns (mv (successp booleanp :rule-classes :type-prescription)
                  (warnings vl-warninglist-p)
                  (new-x    ,type))
     :verbosep ,verbosep
     (declare (ignorable x sigma ,@(and takes-elem '(elem))))
     (b* ((warnings (vl-warninglist-fix warnings))
          (sigma    (vl-typesigma-fix sigma))
          ,@(and takes-elem
                 `((?elem    (vl-modelement-fix elem)))))
       ,body)))

(defmacro def-vl-typesubst-list (name &key type element takes-elem)
  `(define ,name
     :short ,(cat "Substitute types into a @(see " (symbol-name type) ").")
     ((x        ,type)
      (sigma    vl-typesigma-p)
      ,@(and takes-elem '((elem vl-modelement-p)))
      (warnings vl-warninglist-p))
     :returns (mv (successp booleanp :rule-classes :type-prescription)
                  (warnings vl-warninglist-p)
                  (new-x    (and (,type new-x)
                                 (equal (len new-x) (len x))
                                 (iff new-x (consp x))
                                 (equal (consp new-x) (consp x)))))
     (b* (((when (atom x))
           (mv t (ok) nil))
          ((mv okp1 warnings car) (,element (car x) sigma ,@(and takes-elem '(elem)) warnings))
          ((mv okp2 warnings cdr) (,name (cdr x) sigma ,@(and takes-elem '(elem)) warnings)))
       (mv (and okp1 okp2)
           warnings
           (cons car cdr)))))

(def-vl-typesubst vl-enumbasetype-typesubst
  :takes-elem t
  :type vl-enumbasetype-p
  :body
  (b* ((x (vl-enumbasetype-fix x))
       ((vl-enumbasetype x) x)

       ((unless (stringp x.kind))
        ;; Fixed type like :vl-byte, nothing to do
        (mv t warnings x))

       (look (hons-get x.kind sigma))
       ((unless look)
        ;; User-defined type like foo_t, but it's not a type that we're trying to
        ;; substitute for right now, so there's nothing to do.
        (mv t warnings x))

       (new-type (cdr look))
       ((when x.dim)
        (mv nil
            (fatal :type :vl-typesubst-fail
                   :msg "~a0: can't replace enum base type, ~s1, because it ~
                         is an array."
                   :args (list elem x.kind))
            x))

       ((unless (eq (vl-datatype-kind new-type) :vl-coretype))
        ;; BOZO maybe should also permit other simple user-defined types, like bar_t.
        (mv nil
            (fatal :type :vl-typesubst-fail
                   :msg "~a0: can't replace enum base type, ~s1, with ~a1."
                   :args (list elem x.kind new-type))
            x))

       ((vl-coretype new-type) new-type)
       ((unless (vl-enumbasekind-p new-type.name))
        (mv nil
            (fatal :type :vl-typesubst-fail
                   :msg "~a0: can't replace enum base type, ~s1, with ~a1; this
                         isn't a valid type for enumerations."
                   :args (list elem x.kind new-type))
            x))

       ((unless (or (atom new-type.dims)
                    (atom (cdr new-type.dims))))
        (mv nil
            (fatal :type :vl-typesubst-fail
                   :msg "~a0: can't replace enum base type, ~s1, with ~a1; too
                         many array dimensions."
                   :args (list elem x.kind new-type))
            x))

       (x-prime (make-vl-enumbasetype :kind new-type.name
                                      :signedp new-type.signedp
                                      :dim (if (atom new-type.dims)
                                               nil
                                             (car new-type.dims)))))

    (mv t warnings x-prime)))

(defines vl-datatype-typesubst
  :verify-guards nil

  (define vl-datatype-typesubst
    :short "Substitute types into a @(see vl-datatype-p)."
    ((x        vl-datatype-p)
     (sigma    vl-typesigma-p)
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-datatype-p))
    :measure (vl-datatype-count x)
    (b* ((warnings (vl-warninglist-fix warnings))
         (sigma    (vl-typesigma-fix sigma))
         (elem     (vl-modelement-fix elem))
         (x        (vl-datatype-fix x)))
      (vl-datatype-case x
        (:vl-coretype
         ;; These are just basic types like int, byte, etc., nothing here can
         ;; be substituted, nothing to do.
         (mv t warnings x))

        (:vl-struct
         (b* (((mv okp warnings members)
               (vl-structmemberlist-typesubst x.members sigma elem warnings))
              ((unless okp)
               (mv nil warnings x)))
           (mv t warnings (change-vl-struct x :members members))))

        (:vl-union
         (b* (((mv okp warnings members)
               (vl-structmemberlist-typesubst x.members sigma elem warnings))
              ((unless okp)
               (mv nil warnings x)))
           (mv t warnings (change-vl-union x :members members))))

        (:vl-enum
         (b* (((mv okp warnings basetype)
               (vl-enumbasetype-typesubst x.basetype sigma elem warnings))
              ((unless okp)
               (mv nil warnings x)))
           (mv t warnings (change-vl-enum x :basetype basetype))))

        (:vl-usertype
         (b* (((unless (vl-idexpr-p x.kind))
               ;; Fine, not something we're trying to substitute for.
               (mv t warnings x))

              (name (vl-idexpr->name x.kind))
              (look (hons-get name sigma))
              ((unless look)
               ;; User-defined type like foo_t, but it's not a type that we're
               ;; trying to substitute for right now, so nothing to do.
               (mv t warnings x))
              (new-type (cdr look))
              ((when (consp x.dims))
               (mv nil
                   (fatal :type :vl-typesubst-fail
                          :msg  "~a0: can't substitute type ~a1 into array of ~s2."
                          :args (list elem new-type name))
                   x)))
           ;; Otherwise, found something like foo_t and we have a replacement
           ;; for it.  This seems fine.
           (mv t warnings new-type))))))

  (define vl-structmemberlist-typesubst
    :short "Substitute types into a @(see vl-structmemberlist-p)."
    ((x        vl-structmemberlist-p)
     (sigma    vl-typesigma-p)
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x))
          (mv t (ok) nil))
         ((mv okp1 warnings car) (vl-structmember-typesubst (car x) sigma elem warnings))
         ((mv okp2 warnings cdr) (vl-structmemberlist-typesubst (cdr x) sigma elem warnings)))
      (mv (and okp1 okp2) warnings (cons car cdr))))

  (define vl-structmember-typesubst
    :short "Substitute types into a @(see vl-structmember-p)."
    ((x        vl-structmember-p)
     (sigma    vl-typesigma-p)
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-structmember-p))
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x) x)
         ((mv okp warnings type) (vl-datatype-typesubst x.type sigma elem warnings))
         (new-x (change-vl-structmember x :type type)))
      (mv okp warnings new-x)))
  ///
  (verify-guards vl-datatype-typesubst)
  (deffixequiv-mutual vl-datatype-typesubst))

(def-vl-typesubst vl-maybe-datatype-typesubst
  :takes-elem t
  :type vl-maybe-datatype-p
  :body
  (if x
      (vl-datatype-typesubst x sigma elem warnings)
    (mv t (ok) nil)))


(def-vl-typesubst vl-paramvalue-typesubst
  :takes-elem t
  :type vl-paramvalue-p
  :body
  (b* ((x (vl-paramvalue-fix x))
       ((when (vl-paramvalue-expr-p x))
        (mv t warnings x)))
    (vl-datatype-typesubst x sigma elem warnings)))

(def-vl-typesubst vl-maybe-paramvalue-typesubst
  :takes-elem t
  :type vl-maybe-paramvalue-p
  :body
  (if x
      (vl-paramvalue-typesubst x sigma elem warnings)
    (mv t warnings x)))

(def-vl-typesubst-list vl-paramvaluelist-typesubst
  :takes-elem t
  :type vl-paramvaluelist-p
  :element vl-paramvalue-typesubst)

(def-vl-typesubst vl-namedparamvalue-typesubst
  :takes-elem t
  :type vl-namedparamvalue-p
  :body
  (b* (((vl-namedparamvalue x) x)
       ((mv okp warnings new-value)
        (vl-maybe-paramvalue-typesubst x.value sigma elem warnings))
       (new-x (change-vl-namedparamvalue x :value new-value)))
    (mv okp warnings new-x)))

(def-vl-typesubst-list vl-namedparamvaluelist-typesubst
  :takes-elem t
  :type vl-namedparamvaluelist-p
  :element vl-namedparamvalue-typesubst)

(def-vl-typesubst vl-paramargs-typesubst
  :takes-elem t
  :type vl-paramargs-p
  :body
  (vl-paramargs-case x
    (:vl-paramargs-named
     (b* (((mv okp warnings new-args)
           (vl-namedparamvaluelist-typesubst x.args sigma elem warnings))
          (new-x (change-vl-paramargs-named x :args new-args)))
       (mv okp warnings new-x)))
    (:vl-paramargs-plain
     (b* (((mv okp warnings new-args)
           (vl-paramvaluelist-typesubst x.args sigma elem warnings))
          (new-x (change-vl-paramargs-plain x :args new-args)))
       (mv okp warnings new-x)))))

(def-vl-typesubst vl-modinst-typesubst
  :type vl-modinst-p
  :body
  (b* (((vl-modinst x) (vl-modinst-fix x))
       ((mv okp warnings paramargs)
        (vl-paramargs-typesubst x.paramargs sigma x warnings))
       (new-x
        (change-vl-modinst x
                           ;; BOZO eventually more of these fields may have
                           ;; types
                           :paramargs paramargs)))
    (mv okp warnings new-x)))

(def-vl-typesubst-list vl-modinstlist-typesubst
  :type vl-modinstlist-p
  :element vl-modinst-typesubst)




(def-vl-typesubst vl-vardecl-typesubst
  :type vl-vardecl-p
  :body
  (b* (((vl-vardecl x) (vl-vardecl-fix x))
       ((mv okp warnings vartype)
        (vl-datatype-typesubst x.vartype sigma x warnings))
       (new-x (change-vl-vardecl x :vartype vartype)))
    (mv okp warnings new-x)))

(def-vl-typesubst-list vl-vardecllist-typesubst
  :type vl-vardecllist-p
  :element vl-vardecl-typesubst)

(def-vl-typesubst vl-paramtype-typesubst
  :takes-elem t
  :type vl-paramtype-p
  :body
  (b* ((x (vl-paramtype-fix x)))
    (vl-paramtype-case x
      (:vl-implicitvalueparam
       ;; No types here
       (mv t (ok) x))

      (:vl-explicitvalueparam
       (b* (((mv okp warnings type) (vl-datatype-typesubst x.type sigma elem warnings))
            (new-x (change-vl-explicitvalueparam x :type type)))
         (mv okp warnings new-x)))

      (:vl-typeparam
       (b* (((mv okp warnings default) (vl-maybe-datatype-typesubst x.default sigma elem warnings))
            (new-x (change-vl-typeparam x :default default)))
         (mv okp warnings new-x))))))

(def-vl-typesubst vl-paramdecl-typesubst
  :type vl-paramdecl-p
  :body
  (b* (((vl-paramdecl x) (vl-paramdecl-fix x))
       ((mv okp warnings type) (vl-paramtype-typesubst x.type sigma x warnings))
       (new-x (change-vl-paramdecl x :type type)))
    (mv okp warnings new-x)))

(def-vl-typesubst-list vl-paramdecllist-typesubst
  :type vl-paramdecllist-p
  :element vl-paramdecl-typesubst)

(def-vl-typesubst vl-blockitem-typesubst
  :type vl-blockitem-p
  :body
  (b* ((x (vl-blockitem-fix x)))
    (case (tag x)
      (:vl-vardecl (vl-vardecl-typesubst x sigma warnings))
      (otherwise   (vl-paramdecl-typesubst x sigma warnings)))))

(def-vl-typesubst-list vl-blockitemlist-typesubst
  :type vl-blockitemlist-p
  :element vl-blockitem-typesubst)


(defines vl-stmt-typesubst
  :verify-guards nil

  (define vl-stmt-typesubst
    :short "Substitute types into a @(see vl-stmt-p)."
    ((x        vl-stmt-p)
     (sigma    vl-typesigma-p)
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    vl-stmt-p))
    :measure (vl-stmt-count x)
    (b* ((warnings (vl-warninglist-fix warnings))
         (sigma    (vl-typesigma-fix sigma))
         (elem     (vl-modelement-fix elem))
         (x        (vl-stmt-fix x))

         ((when (vl-atomicstmt-p x))
          ;; BOZO eventually some of the atomic statements may have datatypes
          (mv t warnings x))

         ((mv okp1 warnings decls)
          (vl-blockitemlist-typesubst (vl-compoundstmt->decls x) sigma warnings))
         ((mv okp2 warnings stmts)
          (vl-stmtlist-typesubst (vl-compoundstmt->stmts x) sigma elem warnings))
         ;; BOZO eventually exprs/ctrl might also have datatypes
         (okp (and okp1 okp2))
         (new-x
          (change-vl-compoundstmt x
                                  :stmts stmts
                                  :decls decls)))
      (mv okp warnings new-x)))

  (define vl-stmtlist-typesubst
    :short "Substitute types into a @(see vl-stmtlist-p)."
    ((x        vl-stmtlist-p)
     (sigma    vl-typesigma-p)
     (elem     vl-modelement-p)
     (warnings vl-warninglist-p))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-x    (and (vl-stmtlist-p new-x)
                                (equal (len new-x) (len x)))))
    :measure (vl-stmtlist-count x)
    (b* (((when (atom x))
          (mv t (ok) nil))
         ((mv okp1 warnings car) (vl-stmt-typesubst (car x) sigma elem warnings))
         ((mv okp2 warnings cdr) (vl-stmtlist-typesubst (cdr x) sigma elem warnings)))
      (mv (and okp1 okp2) warnings (cons car cdr))))

  ///
  (verify-guards vl-stmt-typesubst)
  (deffixequiv-mutual vl-stmt-typesubst))


(def-vl-typesubst vl-initial-typesubst
  :type vl-initial-p
  :body
  (b* (((vl-initial x) (vl-initial-fix x))
       ((mv okp warnings stmt) (vl-stmt-typesubst x.stmt sigma x warnings))
       (new-x (change-vl-initial x :stmt stmt)))
    (mv okp warnings new-x)))

(def-vl-typesubst-list vl-initiallist-typesubst
  :type vl-initiallist-p
  :element vl-initial-typesubst)


(def-vl-typesubst vl-always-typesubst
  :type vl-always-p
  :body
  (b* (((vl-always x) (vl-always-fix x))
       ((mv okp warnings stmt) (vl-stmt-typesubst x.stmt sigma x warnings))
       (new-x (change-vl-always x :stmt stmt)))
    (mv okp warnings new-x)))

(def-vl-typesubst-list vl-alwayslist-typesubst
  :type vl-alwayslist-p
  :element vl-always-typesubst)


(def-vl-typesubst vl-fundecl-typesubst
  :type vl-fundecl-p
  :body
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       ;; BOZO eventually fundecls may have other datatypes, e.g., in their ports
       ((mv okp warnings body) (vl-stmt-typesubst x.body sigma x warnings))
       (new-x (change-vl-fundecl x :body body)))
    (mv okp warnings new-x)))

(def-vl-typesubst-list vl-fundecllist-typesubst
  :type vl-fundecllist-p
  :element vl-fundecl-typesubst)


(def-vl-typesubst vl-taskdecl-typesubst
  :type vl-taskdecl-p
  :body
  (b* (((vl-taskdecl x) (vl-taskdecl-fix x))
       ;; BOZO eventually taskdecls may have other datatypes, e.g., in their ports
       ((mv okp warnings body) (vl-stmt-typesubst x.body sigma x warnings))
       (new-x (change-vl-taskdecl x :body body)))
    (mv okp warnings new-x)))

(def-vl-typesubst-list vl-taskdecllist-typesubst
  :type vl-taskdecllist-p
  :element vl-taskdecl-typesubst)



(define vl-module-typesubst
  :short "Carry out type substitution throughout a module."
  ((x     vl-module-p)
   (sigma vl-typesigma-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription
                         "Says whether all type substitutions were carried out
                          successfully.")
               (new-x vl-module-p
                      "On success, a rewritten version of @('x') with types
                       substituted as appropriated.  On failure, a copy of
                       @('x') without any changes except that new fatal
                       warnings have been added."))

  (b* (((vl-module x) x)
       (warnings x.warnings)

       ((mv okp1 warnings vardecls)   (vl-vardecllist-typesubst   x.vardecls   sigma warnings))
       ((mv okp2 warnings paramdecls) (vl-paramdecllist-typesubst x.paramdecls sigma warnings))
       ((mv okp3 warnings fundecls)   (vl-fundecllist-typesubst   x.fundecls   sigma warnings))
       ((mv okp4 warnings taskdecls)  (vl-taskdecllist-typesubst  x.taskdecls  sigma warnings))
       ((mv okp5 warnings modinsts)   (vl-modinstlist-typesubst   x.modinsts   sigma warnings))
       ((mv okp6 warnings alwayses)   (vl-alwayslist-typesubst    x.alwayses   sigma warnings))
       ((mv okp7 warnings initials)   (vl-initiallist-typesubst   x.initials   sigma warnings))

       ;; BOZO eventually more things may have datatypes:
       ;;  - params
       ;;  - ports
       ;;  - portdecls
       ;;  - netdecls
       ;;  - assigns
       ;;  - gateinsts

       (okp (and okp1 okp2 okp3 okp4 okp5 okp6 okp7))
       ((unless okp)
        (mv nil (change-vl-module x :warnings warnings)))

       (new-x (change-vl-module x
                                :vardecls   vardecls
                                :paramdecls paramdecls
                                :fundecls   fundecls
                                :taskdecls  taskdecls
                                :modinsts   modinsts
                                :alwayses   alwayses
                                :initials   initials)))
    (mv t new-x)))
