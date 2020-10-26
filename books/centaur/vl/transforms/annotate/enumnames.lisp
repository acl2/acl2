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
; Original author:  Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "../../parsetree")
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/find")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :System))
(local (std::add-default-post-define-hook :fix))

;; BOZO We can run into a problem with shadowcheck due to constructs like this:

;; module foo ();

;;   localparam width = 4;

;;   typedef enum logic [width-1:0] {
;;       a = 1;
;;       b = 2;
;;       c = 3;
;;   } my_enum_type;

;; endmodule

;; because currently we put all the localparams derived from the enum at the
;; beginning of the module, rather than in program order.

;; We could fix this by either inserting them in program order or else doing
;; this after shadowcheck.  Probably the only necessary fix to shadowcheck
;; would be to track the names introduced by the enum.

(defxdoc enum-names
  :parents (annotate)
  :short "Making sense of the names defined by enum types."

  :long "<p>Enum types are unique among datatypes in that using one has a side
effect of declaring some names with assigned values.  We deal with these early
on, as part of @(see annotate), by declaring these names as parameters.  For
example:</p>

@({
    typedef enum logic [3:0] { red=1, blue, green, yellow[4:0]=5, orange[3:5] };
})

<p>results in the following parameter declarations:</p>

@({
    localparam logic [3:0] red = 1;
    localparam logic [3:0] blue = red + 1;
    localparam logic [3:0] green = blue + 1;
    localparam logic [3:0] yellow4 = 5;
    localparam logic [3:0] yellow3 = 6;
    localparam logic [3:0] yellow2 = 7;
    localparam logic [3:0] yellow1 = 8;
    localparam logic [3:0] yellow0 = 9;
    localparam logic [3:0] orange3 = 10;
    localparam logic [3:0] orange4 = 11;
    localparam logic [3:0] orange5 = 12;
})

<p>We require the range indices (e.g. for @('yellow[4:0]'), @('orange[3:5]') to
be constants (syntactically), which ncverilog does as well.  VCS is somewhat
more forgiving, but still doesn't allow arbitrary constant expressions; i.e.,
it seems you can't call a function in there.</p>

<p>The above example illustrates how we create parameters for the names
declared in an enum type.  This transformation then applies this to every enum
found in the datatype of a variable, parameter, or typedef declaration.</p>")

(local (xdoc::set-default-parents enum-names))

(define vl-enumname-range-declarations
  :short "For example: given a ranged enum item like @('foo[3:0]'), we create
          the parameters for @('foo3'), @('foo2'), @('foo1'), and @('foo0')."
  ((name     stringp)
   (top      integerp)
   (bottom   integerp)
   (nextval  vl-expr-p
             "We use an expression, instead of a constant, so that we can
              support enums where the values being assigned to an enum item
              depend on other parameters.  For example:
                   @('enum { foo = myparam, bar, baz }').")
   (basetype vl-datatype-p)
   (atts     vl-atts-p)
   (loc      vl-location-p))
  :returns (mv (params      vl-paramdecllist-p)
               (new-nextval vl-expr-p))
  :measure (abs (- (ifix top) (ifix bottom)))
  (b* ((top (lifix top))
       (bottom (lifix bottom))
       (name1 (str::cat name (if (< top 0) "-" "") (str::natstr (abs top))))
       (first (make-vl-paramdecl
               :name name1
               :localp t
               :type
               (make-vl-explicitvalueparam
                :type basetype
                :default (vl-expr-fix nextval))
               :atts atts
               :loc loc))
       (nextval (make-vl-binary :op :vl-binary-plus
                                :left (vl-idexpr name1)
                                :right (vl-make-index 1)))
       ((when (eql top bottom))
        (mv (list first) nextval))
       ((mv decls nextval) (vl-enumname-range-declarations
                            name
                            (if (< top bottom) (1+ top) (1- top))
                            bottom nextval basetype atts loc)))
    (mv (cons first decls) nextval)))

(define vl-enumname-declarations ((x        vl-enumitem-p)
                                  (nextval  vl-expr-p)
                                  (basetype vl-datatype-p)
                                  (atts     vl-atts-p)
                                  (loc      vl-location-p))
  :returns (mv (warnings vl-warninglist-p)
               (params vl-paramdecllist-p)
               (new-nextval vl-expr-p))
  (b* (((vl-enumitem x))
       (nextval (vl-expr-fix nextval))
       (warnings nil)
       (val (or x.value nextval))
       ((unless x.range)
        (b* ((decl (make-vl-paramdecl :name x.name
                                      :localp t
                                      :type
                                      (make-vl-explicitvalueparam :type basetype
                                                                  :default val)
                                      :atts atts
                                      :loc loc))
             (nextval (make-vl-binary :op :vl-binary-plus
                                      :left (vl-idexpr x.name)
                                      :right (vl-make-index 1))))
          (mv (ok) (list decl) nextval)))

       ((unless (vl-range-resolved-p x.range))
        (mv (warn :type :vl-enum-declarations-fail
                  :msg "Non-constant range on enum item ~s0"
                  :args (list x.name))
            nil
            nextval))
       ((vl-range x.range))
       ((mv decls nextval)
        (vl-enumname-range-declarations x.name
                                        (vl-resolved->val x.range.msb)
                                        (vl-resolved->val x.range.lsb)
                                        val basetype atts loc)))
    (mv (ok) decls nextval)))

(define vl-enumitemlist-enumname-declarations ((x        vl-enumitemlist-p)
                                               (lastval  vl-expr-p)
                                               (basetype vl-datatype-p)
                                               (atts     vl-atts-p)
                                               (loc      vl-location-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv warnings decls nextval)
        (vl-enumname-declarations (car x) lastval basetype atts loc))
       ((mv warnings-rest decls-rest)
        (vl-enumitemlist-enumname-declarations (cdr x) nextval basetype atts loc)))
    (mv (append-without-guard warnings warnings-rest)
        (append-without-guard decls decls-rest))))


(fty::defmap vl-datatype-map :key-type vl-datatype :val-type vl-datatype :true-listp t)

(defines vl-datatype-enumname-declarations
  (define vl-datatype-enumname-declarations ((x           vl-datatype-p)
                                             (typedefname maybe-stringp)
                                             (loc         vl-location-p)
                                             (seen        vl-datatype-map-p))
    :returns (mv (new-x vl-datatype-p)
                 (warnings vl-warninglist-p)
                 (paramdecls vl-paramdecllist-p)
                 (seen-out vl-datatype-map-p))
    :measure (vl-datatype-count x)
    :verify-guards nil
    (b* ((seen (vl-datatype-map-fix seen)))
      (vl-datatype-case x
        :vl-enum (b* ((look (hons-get (vl-datatype-fix x) seen))
                      ((when look)
                       (mv (cdr look) nil nil seen))
                      (warnings nil)
                      (typedefname (maybe-string-fix typedefname))
                      ;; For debugging, mark each declaration that we introduce
                      ;; with a VL_ENUMITEM attribute that, if possible, will say
                      ;; the name of the typedef that declares the enum.
                      (atts (list (cons "VL_ENUMITEM"
                                        (and typedefname
                                             (make-vl-literal :val (make-vl-string :value typedefname))))))
                      ((wmv warnings decls :ctx (vl-datatype-fix x))
                       (vl-enumitemlist-enumname-declarations x.items (vl-make-index 0) x.basetype
                                                              atts loc))
                      (ans (change-vl-enum x :values (vl-make-idexpr-list (vl-paramdecllist->names decls)))))
                   (mv ans
                       warnings decls
                       (hons-acons (vl-datatype-fix x) ans seen)))
        :vl-struct (b* (((mv new-membs warnings paramdecls seen)
                         (vl-structmemberlist-enumname-declarations x.members typedefname loc seen)))
                     (mv (change-vl-struct x :members new-membs) warnings paramdecls seen))
        :vl-union (b* (((mv new-membs warnings paramdecls seen)
                        (vl-structmemberlist-enumname-declarations x.members typedefname loc seen)))
                    (mv (change-vl-union x :members new-membs) warnings paramdecls seen))
        :otherwise (mv (vl-datatype-fix x) nil nil seen))))
  (define vl-structmemberlist-enumname-declarations ((x vl-structmemberlist-p)
                                                     (typedefname maybe-stringp)
                                                     (loc vl-location-p)
                                                     (seen        vl-datatype-map-p))
    :returns (mv (new-x vl-structmemberlist-p)
                 (warnings vl-warninglist-p)
                 (paramdecls vl-paramdecllist-p)
                 (seen-out vl-datatype-map-p))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x)) (mv nil nil nil (vl-datatype-map-fix seen)))
         ((mv new-type warnings1 decls1 seen)
          (vl-datatype-enumname-declarations (vl-structmember->type (car x)) typedefname loc seen))
         ((mv new-rest warnings-rest decls-rest seen)
          (vl-structmemberlist-enumname-declarations (cdr x) typedefname loc seen)))
      (mv (cons (change-vl-structmember (car x) :type new-type) new-rest)
          (append-without-guard warnings1 warnings-rest)
          (append-without-guard decls1 decls-rest)
          seen)))
  ///
  (deffixequiv-mutual vl-datatype-enumname-declarations)
  (verify-guards vl-datatype-enumname-declarations))

(define vl-paramdecl-enumname-declarations ((x vl-paramdecl-p)
                                            (seen vl-datatype-map-p))
  :returns (mv (new-x vl-paramdecl-p)
               (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p)
               (seen-out vl-datatype-map-p))
  (b* (((vl-paramdecl x))
       ((mv new-type warnings paramdecls seen)
        (vl-paramtype-case x.type
          ;; Note: Not sure how this should work for type parameters.  Presumably
          ;; it shouldn't hurt to make the declarations, even if it's going to get
          ;; overridden?
          :vl-typeparam
          (b* (((mv type warnings paramdecls seen)
                (if x.type.default
                    (vl-datatype-enumname-declarations x.type.default nil x.loc seen)
                  (mv nil nil nil (vl-datatype-map-fix seen)))))
            (mv (change-vl-typeparam x.type :default type)
                warnings paramdecls seen))
          :vl-explicitvalueparam
          (b* (((mv type warnings paramdecls seen)
                (vl-datatype-enumname-declarations x.type.type nil x.loc seen)))
            (mv (change-vl-explicitvalueparam x.type :type type) warnings paramdecls seen))
          :otherwise (mv x.type nil nil (vl-datatype-map-fix seen)))))
    (mv (change-vl-paramdecl x :type new-type) warnings paramdecls seen)))

(define vl-vardecl-enumname-declarations ((x vl-vardecl-p)
                                          (seen vl-datatype-map-p))
  :returns (mv (new-x vl-vardecl-p)
               (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p)
               (seen-out vl-datatype-map-p))
  (b* (((vl-vardecl x))
       ((mv new-type warnings paramdecls seen)
        (vl-datatype-enumname-declarations x.type nil x.loc seen)))
    (mv (change-vl-vardecl x :type new-type) warnings paramdecls seen)))

(define vl-typedef-enumname-declarations ((x vl-typedef-p)
                                          (seen vl-datatype-map-p))
  :returns (mv (new-x vl-typedef-p)
               (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p)
               (seen-out vl-datatype-map-p))
  (b* (((vl-typedef x))
       ((mv new-type warnings paramdecls seen)
        (vl-datatype-enumname-declarations x.type x.name x.minloc seen)))
    (mv (change-vl-typedef x :type new-type) warnings paramdecls seen)))

;; BOZO Do we need to also cover function/task decls, portdecls, etc?


(define vl-paramdecllist-enumname-declarations ((x vl-paramdecllist-p)
                                                (seen vl-datatype-map-p))
  :returns (mv (new-x vl-paramdecllist-p)
               (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p)
               (seen-out vl-datatype-map-p))
  (b* (((when (atom x)) (mv nil nil nil (vl-datatype-map-fix seen)))
       ((mv new-x1 warnings1 decls1 seen) (vl-paramdecl-enumname-declarations (car x) seen))
       ((mv new-x2 warnings2 decls2 seen) (vl-paramdecllist-enumname-declarations (cdr x) seen)))
    (mv (cons new-x1 new-x2)
        (append-without-guard warnings1 warnings2)
        (append-without-guard decls1 decls2)
        seen)))

(define vl-vardecllist-enumname-declarations ((x vl-vardecllist-p)
                                              (seen vl-datatype-map-p))
  :returns (mv (new-x vl-vardecllist-p)
               (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p)
               (seen-out vl-datatype-map-p))
  (b* (((when (atom x)) (mv nil nil nil (vl-datatype-map-fix seen)))
       ((mv new-x1 warnings1 decls1 seen) (vl-vardecl-enumname-declarations (car x) seen))
       ((mv new-x2 warnings2 decls2 seen) (vl-vardecllist-enumname-declarations (cdr x) seen)))
    (mv (cons new-x1 new-x2)
        (append-without-guard warnings1 warnings2)
        (append-without-guard decls1 decls2)
        seen)))

(define vl-typedeflist-enumname-declarations ((x vl-typedeflist-p)
                                              (seen vl-datatype-map-p))
  :returns (mv (new-x vl-typedeflist-p)
               (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p)
               (seen-out vl-datatype-map-p))
  (b* (((when (atom x)) (mv nil nil nil (vl-datatype-map-fix seen)))
       ((mv new-x1 warnings1 decls1 seen) (vl-typedef-enumname-declarations (car x) seen))
       ((mv new-x2 warnings2 decls2 seen) (vl-typedeflist-enumname-declarations (cdr x) seen)))
    (mv (cons new-x1 new-x2)
        (append-without-guard warnings1 warnings2)
        (append-without-guard decls1 decls2)
        seen)))


(defines vl-genelementlist-enumname-declarations
  :verify-guards nil

  (define vl-genelementlist-enumname-declarations ((x vl-genelementlist-p)
                                                   (seen vl-datatype-map-p))
    :returns (mv (warnings  vl-warninglist-p)
                 (new-x     vl-genelementlist-p)
                 (seen-out vl-datatype-map-p))
    :measure (two-nats-measure (vl-genelementlist-count x) 0)
    (b* (((when (atom x))
          (mv nil nil (vl-datatype-map-fix seen)))
         ((mv warnings first seen)  (vl-genelement-enumname-declarations (car x) seen))
         ((wmv warnings rest seen) (vl-genelementlist-enumname-declarations (cdr x) seen)))
      (mv warnings
          (append first rest)
          seen)))

  (define vl-genblock-enumname-declarations ((x vl-genblock-p))
    :returns (mv (warnings  vl-warninglist-p)
                 (new-x     vl-genblock-p))
    :measure (two-nats-measure (vl-genblock-count x) 0)
    (b* (((vl-genblock x))
         ((mv warnings new-elems seen) (vl-genelementlist-enumname-declarations x.elems nil))
         (- (fast-alist-free seen))
         (new-x (change-vl-genblock x :elems new-elems)))
      (mv warnings new-x)))

  (define vl-genelement-enumname-declarations ((x vl-genelement-p)
                                               (seen vl-datatype-map-p))
    :returns (mv (warnings  vl-warninglist-p)
                 (new-elems     vl-genelementlist-p)
                 (seen-out vl-datatype-map-p))
    :measure (two-nats-measure (vl-genelement-count x) 0)
    (vl-genelement-case x
      :vl-genbase
      (b* (((mv new-item warnings decls seen)
            (case (tag x.item)
              (:vl-paramdecl (vl-paramdecl-enumname-declarations x.item seen))
              (:vl-typedef   (vl-typedef-enumname-declarations x.item seen))
              (:vl-vardecl   (vl-vardecl-enumname-declarations x.item seen))
              (otherwise     (mv x.item nil nil (vl-datatype-map-fix seen)))))
           ;; Remove duplicate decls because when we find something like:
          ;;    enum { FOO, BAR } a, b;
          ;; the declaration for "a" will try to introduce paramdecls for FOO
          ;; and BAR, and so will the declaration for "b".  This will look like
          ;; a name clash unless we remove the duplicates.
          ;;
          ;; Don't use mergesort to remove the dupes, because we want earlier
          ;; declarations to come first, in case later declarations refer to
          ;; them.
           (decls (remove-duplicates-equal (list-fix decls)))
           (new-elems (cons (change-vl-genbase x :item new-item)
                        (vl-modelementlist->genelements decls))))
        (mv warnings new-elems seen))
      :vl-genbegin
      (b* (((mv warnings new-block) (vl-genblock-enumname-declarations x.block))
           (new-x                   (change-vl-genbegin x :block new-block)))
        (mv warnings (list new-x) (vl-datatype-map-fix seen)))
      :vl-genif
      (b* (((mv warnings then)  (vl-genblock-enumname-declarations x.then))
           ((wmv warnings else) (vl-genblock-enumname-declarations x.else))
           (new-x               (change-vl-genif x :then then :else else)))
        (mv warnings (list new-x) (vl-datatype-map-fix seen)))
      :vl-gencase
      (b* (((mv warnings cases)    (vl-gencaselist-enumname-declarations x.cases))
           ((wmv warnings default) (vl-genblock-enumname-declarations x.default))
           (new-x                  (change-vl-gencase x :cases cases :default default)))
        (mv warnings (list new-x) (vl-datatype-map-fix seen)))
      :vl-genloop
      (b* (((mv warnings body) (vl-genblock-enumname-declarations x.body))
           (new-x              (change-vl-genloop x :body body)))
        (mv warnings (list new-x) (vl-datatype-map-fix seen)))
      :vl-genarray
      (b* (((mv warnings blocks) (vl-genblocklist-enumname-declarations x.blocks))
           (new-x                (change-vl-genarray x :blocks blocks)))
        (mv warnings (list new-x) (vl-datatype-map-fix seen)))))

  (define vl-gencaselist-enumname-declarations ((x vl-gencaselist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-gencaselist-p))
    :measure (two-nats-measure (vl-gencaselist-count x) 0)
    (b* ((x (vl-gencaselist-fix x))
         ((when (atom x)) (mv nil nil))
         ((mv warnings1 case1) (vl-genblock-enumname-declarations (cdar x)))
         ((mv warnings2 rest)  (vl-gencaselist-enumname-declarations (cdr x))))
      (mv (append-without-guard warnings1 warnings2)
          (cons (cons (caar x) case1) rest))))

  (define vl-genblocklist-enumname-declarations ((x vl-genblocklist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-genblocklist-p))
    :measure (two-nats-measure (vl-genblocklist-count x) 0)
    (b* (((when (atom x)) (mv nil nil))
         ((mv  warnings first) (vl-genblock-enumname-declarations (car x)))
         ((wmv warnings rest)  (vl-genblocklist-enumname-declarations (cdr x))))
      (mv warnings (cons first rest))))
  ///
  (verify-guards vl-genelementlist-enumname-declarations)
  (deffixequiv-mutual vl-genelementlist-enumname-declarations))


(define vl-module-add-enumname-declarations ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       ((unless x.parse-temps) x)
       ((mv warnings items seen)
        (vl-genelementlist-enumname-declarations (vl-parse-temps->loaditems x.parse-temps) nil))
       (- (fast-alist-free seen)))
    ;; BOZO Enums first used in ports and paramports don't work yet
    (change-vl-module x
                      :parse-temps (change-vl-parse-temps x.parse-temps :loaditems items)
                      :warnings (append-without-guard warnings x.warnings))))

(defprojection vl-modulelist-add-enumname-declarations ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-add-enumname-declarations x))

(define vl-interface-add-enumname-declarations ((x vl-interface-p))
  :returns (new-x vl-interface-p)
  (b* (((vl-interface x) (vl-interface-fix x))
       ((unless x.parse-temps) x)
       ((mv warnings items seen)
        (vl-genelementlist-enumname-declarations (vl-parse-temps->loaditems x.parse-temps) nil))
       (- (fast-alist-free seen)))
    ;; BOZO Enums first used in ports and paramports don't work yet
    (change-vl-interface x
                         :parse-temps (change-vl-parse-temps x.parse-temps :loaditems items)
                         :warnings (append-without-guard warnings x.warnings))))

(defprojection vl-interfacelist-add-enumname-declarations ((x vl-interfacelist-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-add-enumname-declarations x))

(define vl-package-add-enumname-declarations ((x vl-package-p))
  :returns (new-x vl-package-p)
  (b* (((vl-package x) (vl-package-fix x))
       (seen nil)
       ((mv typedefs warnings1 decls1 seen) (vl-typedeflist-enumname-declarations x.typedefs seen))
       ((mv vardecls warnings2 decls2 seen) (vl-vardecllist-enumname-declarations x.vardecls seen))
       ((mv paramdecls warnings3 decls3 seen) (vl-paramdecllist-enumname-declarations x.paramdecls seen))
       (- (fast-alist-free seen))
       (decls (remove-duplicates-equal (append-without-guard decls1 decls2 (list-fix decls3)))))
    (change-vl-package
     x
     :typedefs typedefs
     :vardecls vardecls
     :paramdecls (append decls paramdecls)
     :warnings (append-without-guard warnings1 warnings2 warnings3 x.warnings))))

(defprojection vl-packagelist-add-enumname-declarations ((x vl-packagelist-p))
  :returns (new-x vl-packagelist-p)
  (vl-package-add-enumname-declarations x))


(define vl-design-add-enumname-declarations ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (seen nil)
       ((mv typedefs warnings1 decls1 seen)   (vl-typedeflist-enumname-declarations x.typedefs seen))
       ((mv vardecls warnings2 decls2 seen)   (vl-vardecllist-enumname-declarations x.vardecls seen))
       ((mv paramdecls warnings3 decls3 seen) (vl-paramdecllist-enumname-declarations x.paramdecls seen))
       (- (fast-alist-free seen))
       (decls (remove-duplicates-equal (append-without-guard decls1 decls2 (list-fix decls3)))))
    (change-vl-design x
                      :paramdecls (append decls paramdecls)
                      :typedefs   typedefs
                      :vardecls   vardecls
                      :mods       (vl-modulelist-add-enumname-declarations x.mods)
                      :interfaces (vl-interfacelist-add-enumname-declarations x.interfaces)
                      :packages   (vl-packagelist-add-enumname-declarations x.packages)
                      :warnings   (append-without-guard warnings1 warnings2 warnings3 x.warnings))))




