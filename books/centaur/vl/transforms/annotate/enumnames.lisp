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
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "centaur/misc/arith-equivs" :dir :System))
(local (std::add-default-post-define-hook :fix))

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
   (top      natp)
   (bottom   natp)
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
  :measure (abs (- (nfix top) (nfix bottom)))
  (b* ((top (lnfix top))
       (bottom (lnfix bottom))
       (name1 (str::cat name (str::natstr top)))
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


(defines vl-datatype-enumname-declarations
  (define vl-datatype-enumname-declarations ((x           vl-datatype-p)
                                             (typedefname maybe-stringp)
                                             (loc         vl-location-p))
    :returns (mv (warnings vl-warninglist-p)
                 (paramdecls vl-paramdecllist-p))
    :measure (vl-datatype-count x)
    :guard-debug t
    (vl-datatype-case x
      :vl-enum (b* ((warnings    nil)
                    (typedefname (maybe-string-fix typedefname))
                    ;; For debugging, mark each declaration that we introduce
                    ;; with a VL_ENUMITEM attribute that, if possible, will say
                    ;; the name of the typedef that declares the enum.
                    (atts (list (cons "VL_ENUMITEM"
                                      (and typedefname
                                           (make-vl-literal :val (make-vl-string :value typedefname))))))
                    ((wmv warnings decls :ctx (vl-datatype-fix x))
                     (vl-enumitemlist-enumname-declarations x.items (vl-make-index 0) x.basetype
                                                            atts loc)))
                 (mv warnings decls))
      :vl-struct (vl-structmemberlist-enumname-declarations x.members typedefname loc)
      :vl-union (vl-structmemberlist-enumname-declarations x.members typedefname loc)
      :otherwise (mv nil nil)))
  (define vl-structmemberlist-enumname-declarations ((x vl-structmemberlist-p)
                                                     (typedefname maybe-stringp)
                                                     (loc vl-location-p))
    :returns (mv (warnings vl-warninglist-p)
                 (paramdecls vl-paramdecllist-p))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x)) (mv nil nil))
         ((mv warnings1 decls1)
          (vl-datatype-enumname-declarations (vl-structmember->type (car x)) typedefname loc))
         ((mv warnings-rest decls-rest)
          (vl-structmemberlist-enumname-declarations (cdr x) typedefname loc)))
      (mv (append-without-guard warnings1 warnings-rest)
          (append-without-guard decls1 decls-rest))))
  ///
  (deffixequiv-mutual vl-datatype-enumname-declarations))

(define vl-paramdecl-enumname-declarations ((x vl-paramdecl-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((vl-paramdecl x)))
    (vl-paramtype-case x.type
      ;; Note: Not sure how this should work for type parameters.  Presumably
      ;; it shouldn't hurt to make the declarations, even if it's going to get
      ;; overridden?
      :vl-typeparam (if x.type.default
                        (vl-datatype-enumname-declarations x.type.default nil x.loc)
                      (mv nil nil))
      :vl-explicitvalueparam (vl-datatype-enumname-declarations x.type.type nil x.loc)
      :otherwise (mv nil nil))))

(define vl-vardecl-enumname-declarations ((x vl-vardecl-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((vl-vardecl x)))
    (vl-datatype-enumname-declarations x.type nil x.loc)))

(define vl-typedef-enumname-declarations ((x vl-typedef-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((vl-typedef x)))
    (vl-datatype-enumname-declarations x.type x.name x.minloc)))

;; BOZO Do we need to also cover function/task decls, portdecls, etc?


(define vl-paramdecllist-enumname-declarations ((x vl-paramdecllist-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv warnings1 decls1) (vl-paramdecl-enumname-declarations (car x)))
       ((mv warnings2 decls2) (vl-paramdecllist-enumname-declarations (cdr x))))
    (mv (append-without-guard warnings1 warnings2)
        (append-without-guard decls1 decls2))))

(define vl-vardecllist-enumname-declarations ((x vl-vardecllist-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv warnings1 decls1) (vl-vardecl-enumname-declarations (car x)))
       ((mv warnings2 decls2) (vl-vardecllist-enumname-declarations (cdr x))))
    (mv (append-without-guard warnings1 warnings2)
        (append-without-guard decls1 decls2))))

(define vl-typedeflist-enumname-declarations ((x vl-typedeflist-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv warnings1 decls1) (vl-typedef-enumname-declarations (car x)))
       ((mv warnings2 decls2) (vl-typedeflist-enumname-declarations (cdr x))))
    (mv (append-without-guard warnings1 warnings2)
        (append-without-guard decls1 decls2))))


(defines vl-genelementlist-enumname-declarations
  :verify-guards nil

  (define vl-genelementlist-enumname-declarations ((x vl-genelementlist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-genelementlist-p))
    :measure (two-nats-measure (vl-genelementlist-count x) 0)
    (b* (((when (atom x))
          (mv nil nil))
         ((mv warnings elems1) (vl-genelement-enumname-declarations (car x)))
         ((wmv warnings rest)  (vl-genelementlist-enumname-declarations (cdr x))))
      (mv warnings
          (append-without-guard elems1 rest))))

  (define vl-genblock-enumname-declarations ((x vl-genblock-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-genblock-p))
    :measure (two-nats-measure (vl-genblock-count x) 0)
    (b* (((vl-genblock x))
         ((mv warnings new-elems) (vl-genelementlist-enumname-declarations x.elems))
         (new-x                   (change-vl-genblock x :elems new-elems)))
      (mv warnings new-x)))

  (define vl-genelement-enumname-declarations ((x vl-genelement-p))
    :returns (mv (warnings     vl-warninglist-p)
                 (replacements vl-genelementlist-p
                               "List of elements that should replace @('x').
                                Even though we start with a single element, we
                                need to return a list since we sometimes need
                                to add parameter declarations."))
    :measure (two-nats-measure (vl-genelement-count x) 0)
    (vl-genelement-case x
      :vl-genbase
      (b* (((mv warnings decls)
            (case (tag x.item)
              (:vl-paramdecl (vl-paramdecl-enumname-declarations x.item))
              (:vl-typedef   (vl-typedef-enumname-declarations x.item))
              (:vl-vardecl   (vl-vardecl-enumname-declarations x.item))
              (otherwise     (mv nil nil)))))
        (mv warnings (append (vl-modelementlist->genelements decls)
                             (list (vl-genelement-fix x)))))
      :vl-genbegin
      (b* (((mv warnings new-block) (vl-genblock-enumname-declarations x.block))
           (new-x                   (change-vl-genbegin x :block new-block)))
        (mv warnings (list new-x)))
      :vl-genif
      (b* (((mv warnings then)  (vl-genblock-enumname-declarations x.then))
           ((wmv warnings else) (vl-genblock-enumname-declarations x.else))
           (new-x               (change-vl-genif x :then then :else else)))
        (mv warnings (list new-x)))
      :vl-gencase
      (b* (((mv warnings cases)    (vl-gencaselist-enumname-declarations x.cases))
           ((wmv warnings default) (vl-genblock-enumname-declarations x.default))
           (new-x                  (change-vl-gencase x :cases cases :default default)))
        (mv warnings (list new-x)))
      :vl-genloop
      (b* (((mv warnings body) (vl-genblock-enumname-declarations x.body))
           (new-x              (change-vl-genloop x :body body)))
        (mv warnings (list new-x)))
      :vl-genarray
      (b* (((mv warnings blocks) (vl-genblocklist-enumname-declarations x.blocks))
           (new-x                (change-vl-genarray x :blocks blocks)))
        (mv warnings (list new-x)))))

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
       ((mv warnings items)
        (vl-genelementlist-enumname-declarations (vl-parse-temps->loaditems x.parse-temps))))
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
       ((mv warnings items)
        (vl-genelementlist-enumname-declarations (vl-parse-temps->loaditems x.parse-temps))))
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
       ((mv warnings1 decls1) (vl-typedeflist-enumname-declarations x.typedefs))
       ((mv warnings2 decls2) (vl-vardecllist-enumname-declarations x.vardecls))
       ((mv warnings3 decls3) (vl-paramdecllist-enumname-declarations x.paramdecls)))
    (change-vl-package
     x
     :paramdecls (append-without-guard decls1 decls2 decls3 x.paramdecls)
     :warnings (append-without-guard warnings1 warnings2 warnings3 x.warnings))))

(defprojection vl-packagelist-add-enumname-declarations ((x vl-packagelist-p))
  :returns (new-x vl-packagelist-p)
  (vl-package-add-enumname-declarations x))


(define vl-design-add-enumname-declarations ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       ((mv warnings1 decls1) (vl-typedeflist-enumname-declarations x.typedefs))
       ((mv warnings2 decls2) (vl-vardecllist-enumname-declarations x.vardecls))
       ((mv warnings3 decls3) (vl-paramdecllist-enumname-declarations x.paramdecls)))
    (change-vl-design x
                      :paramdecls (append-without-guard decls1 decls2 decls3 x.paramdecls)
                      :mods       (vl-modulelist-add-enumname-declarations x.mods)
                      :interfaces (vl-interfacelist-add-enumname-declarations x.interfaces)
                      :packages   (vl-packagelist-add-enumname-declarations x.packages)
                      :warnings   (append-without-guard warnings1 warnings2 warnings3 x.warnings))))




