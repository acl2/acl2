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
on by declaring these names as parameters.  For example:</p>

@({
 typedef enum logic [3:0] { red=1, blue, green, yellow[4:0]=5, orange[3:5] };
 })

<p>results in the following parameter declarations:</p>

@({
 parameter logic [3:0] red = 1;
 parameter logic [3:0] blue = red + 1;
 parameter logic [3:0] green = blue + 1;
 parameter logic [3:0] yellow4 = 5;
 parameter logic [3:0] yellow3 = 6;
 parameter logic [3:0] yellow2 = 7;
 parameter logic [3:0] yellow1 = 8;
 parameter logic [3:0] yellow0 = 9;
 parameter logic [3:0] orange3 = 10;
 parameter logic [3:0] orange4 = 11;
 parameter logic [3:0] orange5 = 12;

 })

<p>We require the range indices (e.g. for @('yellow[4:0]'), @('orange[3:5]') to
be constants (syntactically), which ncverilog does as well.  VCS is somewhat
more forgiving, but still doesn't allow arbitrary constant expressions; i.e.,
it seems you can't call a function in there.</p>

<p>The above example illustrates how we create parameters for the names
declared in an enum type.  This transformation then applies this to every enum
found in the datatype of a variable, parameter, or typedef declaration.</p>")

(define vl-enumname-range-declarations ((name stringp)
                                        (top natp)
                                        (bottom natp)
                                        (nextval vl-expr-p)
                                        (basetype vl-datatype-p)
                                        (loc vl-location-p))
  :returns (mv (params vl-paramdecllist-p)
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
               :loc loc))
       (nextval (make-vl-binary :op :vl-binary-plus
                                :left (vl-idexpr name1)
                                :right (vl-make-index 1)))
       ((when (eql top bottom))
        (mv (list first) nextval))
       ((mv decls nextval)
        (vl-enumname-range-declarations
         name
         (if (< top bottom) (1+ top) (1- top))
         bottom
         nextval
         basetype loc)))
    (mv (cons first decls) nextval)))


(define vl-enumname-declarations ((x vl-enumitem-p)
                                  (nextval vl-expr-p)
                                  (basetype vl-datatype-p)
                                  (loc vl-location-p))
  :returns (mv (warnings vl-warninglist-p)
               (params vl-paramdecllist-p)
               (new-nextval vl-expr-p))
  (b* (((vl-enumitem x))
       (warnings nil)
       (val (or x.value (vl-expr-fix nextval)))
       (nextval (make-vl-binary :op :vl-binary-plus
                                :left (vl-idexpr x.name)
                                :right (vl-make-index 1)))
       ((unless x.range)
        (mv (ok)
            (list (make-vl-paramdecl
                   :name x.name
                   :localp t
                   :type
                   (make-vl-explicitvalueparam
                    :type basetype
                    :default val)
                   :loc loc))
            nextval))
       ((unless (vl-range-resolved-p x.range))
        (mv (warn :type :vl-enum-declarations-fail
                  :msg "Non-constant range on enum item ~s0"
                  :args (list x.name))
            nil
            nextval))
       ((vl-range x.range))
       ((mv decls nextval)
        (vl-enumname-range-declarations
         x.name
         (vl-resolved->val x.range.msb)
         (vl-resolved->val x.range.lsb)
         nextval basetype loc)))
    (mv (ok) decls nextval)))

(define vl-enumitemlist-enumname-declarations ((x vl-enumitemlist-p)
                                               (lastval vl-expr-p)
                                               (basetype vl-datatype-p)
                                               (loc vl-location-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv warnings decls nextval)
        (vl-enumname-declarations (car x) lastval basetype loc))
       ((mv warnings-rest decls-rest)
        (vl-enumitemlist-enumname-declarations (cdr x) nextval basetype loc)))
    (mv (append-without-guard warnings warnings-rest)
        (append-without-guard decls decls-rest))))


(defines vl-datatype-enumname-declarations
  (define vl-datatype-enumname-declarations ((x vl-datatype-p)
                                             (loc vl-location-p))
    :returns (mv (warnings vl-warninglist-p)
                 (paramdecls vl-paramdecllist-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      :vl-enum (b* ((warnings nil)
                    ((wmv warnings decls :ctx (vl-datatype-fix x))
                     (vl-enumitemlist-enumname-declarations
                      x.items (vl-make-index 0) x.basetype loc)))
                 (mv warnings decls))
      :vl-struct (vl-structmemberlist-enumname-declarations x.members loc)
      :vl-union (vl-structmemberlist-enumname-declarations x.members loc)
      :otherwise (mv nil nil)))
  (define vl-structmemberlist-enumname-declarations ((x vl-structmemberlist-p)
                                                     (loc vl-location-p))
    :returns (mv (warnings vl-warninglist-p)
                 (paramdecls vl-paramdecllist-p))
    :measure (vl-structmemberlist-count x)
    (b* (((when (atom x)) (mv nil nil))
         ((mv warnings1 decls1)
          (vl-datatype-enumname-declarations (vl-structmember->type (car x))
                                                 loc))
         ((mv warnings-rest decls-rest)
          (vl-structmemberlist-enumname-declarations (cdr x) loc)))
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
                        (vl-datatype-enumname-declarations x.type.default x.loc)
                      (mv nil nil))
      :vl-explicitvalueparam (vl-datatype-enumname-declarations x.type.type x.loc)
      :otherwise (mv nil nil))))

(define vl-vardecl-enumname-declarations ((x vl-vardecl-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((vl-vardecl x)))
    (vl-datatype-enumname-declarations x.type x.loc)))

(define vl-typedef-enumname-declarations ((x vl-typedef-p))
  :returns (mv (warnings vl-warninglist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((vl-typedef x)))
    (vl-datatype-enumname-declarations x.type x.minloc)))

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
  (define vl-genelement-enumname-declarations ((x vl-genelement-p))
    ;; This is called on each individual genelement in a list.  It is NOT the
    ;; thing to call on the genelement that is an if branch, loop body, etc.
    :returns (mv (warnings vl-warninglist-p)
                 (elts vl-genelementlist-p))
    :measure (two-nats-measure (vl-genelement-count x)
                               (if (vl-genelement-case x :vl-genbase) 0 1))
    (vl-genelement-case x
      :vl-genbase
      (b* (((mv warnings decls)
            (case (tag x.item)
              (:vl-paramdecl (vl-paramdecl-enumname-declarations x.item))
              (:vl-typedef (vl-typedef-enumname-declarations x.item))
              (:vl-vardecl (vl-vardecl-enumname-declarations x.item))
              (t (mv nil nil)))))
        (mv warnings (append (vl-modelementlist->genelements decls)
                             (list (vl-genelement-fix x)))))
      :otherwise
      (b* (((mv warnings elt) (vl-genelementblock-enumname-declarations x)))
        (mv warnings (list elt)))))

  (define vl-genelementblock-enumname-declarations ((x vl-genelement-p))
    :returns (mv (warnings vl-warninglist-p)
                 (elem vl-genelement-p))
    :measure (two-nats-measure (vl-genelement-count x)
                               (if (vl-genelement-case x :vl-genbase) 1 0))
    (vl-genelement-case x
      :vl-genbase
      (b* (((mv warnings elems)
            (vl-genelement-enumname-declarations x)))
        (mv warnings
            (make-vl-genblock :elems elems :loc (vl-modelement->loc x.item))))
      
      :vl-genif
      (b* (((mv warnings then) (vl-genelementblock-enumname-declarations x.then))
           ((wmv warnings else) (vl-genelementblock-enumname-declarations x.else)))
        (mv warnings
            (change-vl-genif
             x
             :then then :else else )))
      :vl-gencase
      (b* (((mv warnings cases) (vl-gencaselist-enumname-declarations x.cases))
           ((wmv warnings default) (vl-genelementblock-enumname-declarations x.default)))
        (mv warnings
            (change-vl-gencase
              x
              :cases cases
              :default default)))
      :vl-genloop
      (b* (((mv warnings body) (vl-genelementblock-enumname-declarations x.body)))
        (mv warnings
            (change-vl-genloop
             x
             :body body)))
      :vl-genblock
      (b* (((mv warnings elems) (vl-genelementlist-enumname-declarations x.elems))) 
        (mv warnings
            (change-vl-genblock
             x
             :elems elems)))
      :vl-genarray
      (b* (((mv warnings blocks) (vl-genarrayblocklist-enumname-declarations x.blocks)))
        (mv warnings
            (change-vl-genarray
             x
             :blocks blocks)))))

  (define vl-gencaselist-enumname-declarations ((x vl-gencaselist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (elts vl-gencaselist-p))
    :measure (two-nats-measure (vl-gencaselist-count x) 1)
    (b* ((x (vl-gencaselist-fix x))
         ((when (atom x)) (mv nil nil))
         ((mv warnings1 case1) (vl-genelementblock-enumname-declarations (cdar x)))
         ((mv warnings2 rest) (vl-gencaselist-enumname-declarations (cdr x))))
      (mv (append-without-guard warnings1 warnings2)
          (cons (cons (caar x) case1) rest))))

  (define vl-genarrayblocklist-enumname-declarations ((x vl-genarrayblocklist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (blocks vl-genarrayblocklist-p))
    :measure (two-nats-measure (vl-genarrayblocklist-count x) 1)
    (b* (((when (atom x)) (mv nil nil))
         ((mv warnings1 elems1) (vl-genelementlist-enumname-declarations
                                 (vl-genarrayblock->elems (car x))))
         ((mv warnings2 rest) (vl-genarrayblocklist-enumname-declarations (cdr x))))
      (mv (append-without-guard warnings1 warnings2)
          (cons (change-vl-genarrayblock (car x) :elems elems1) rest))))

  (define vl-genelementlist-enumname-declarations ((x vl-genelementlist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (elems vl-genelementlist-p))
    :measure (two-nats-measure (vl-genelementlist-count x) 0)
    (b* (((when (atom x)) (mv nil nil))
         ((mv warnings1 elems1) (vl-genelement-enumname-declarations (car x)))
         ((mv warnings2 rest) (vl-genelementlist-enumname-declarations (cdr x))))
      (mv (append-without-guard warnings1 warnings2)
          (append-without-guard elems1 rest))))
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
    (change-vl-module x :parse-temps (change-vl-parse-temps x.parse-temps
                                                            :loaditems items)
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
    (change-vl-interface x :parse-temps (change-vl-parse-temps x.parse-temps
                                                            :loaditems items)
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
    (change-vl-design x :paramdecls (append-without-guard
                                     decls1 decls2 decls3 x.paramdecls)
                      :mods (vl-modulelist-add-enumname-declarations x.mods)
                      :interfaces (vl-interfacelist-add-enumname-declarations x.interfaces)
                      :packages (vl-packagelist-add-enumname-declarations x.packages)
                      :warnings
                      (append-without-guard warnings1 warnings2 warnings3 x.warnings))))



    
