; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Stephen Westfold
;          Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "expression-values-and-environments")
(include-book "variable-substitution-operations")

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/basic/fix" :dir :system))
(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/basic/rfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ values-to-abstract-syntax
  :parents (dynamic-semantics)
  :short "Mapping of values to ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "Evaluation turns ASTs into (ispace, type, and expression) values.
     Although our values are defined as separate data types from ASTs,
     they are essentially like irreducible ASTs;
     indeed, [thesis], [arxiv], and [esop] define the Remora dynamic semantics
     in terms of reduction rules over ASTs.")
   (xdoc::p
    "Here we define conversions from values to ASTs,
     which have different practical uses in our Remora development.
     Not all values can be converted to ASTS,
     because not all float values can be represented as float literals.
     But this may change once Remora has syntax for infinities and NaNs,
     and once our model of floats does not use all ACL2 rationals."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-value-to-ispace ((ival ispace-valuep))
  :returns (ispace ispacep)
  :short "Convert an ispace value to an ispace."
  (ispace-value-case
   ival
   :dim (ispace-dim (dim-const ival.val))
   :shape (ispace-shape (shape-dims (dim-const-list ival.val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-value-list-to-ispaces ((x ispace-value-listp))
  :returns (ispaces ispace-listp)
  :short "Lift @(tsee ispace-value-to-ispace) to lists."
  (ispace-value-to-ispace x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-var-ispace-value-map-to-substs ((map
                                                ispace-var-ispace-value-mapp))
  :returns (mv (dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp))
  :short "Convert (i) a map from ispace variables to ispace values
          to (ii) dimension and shape substitutions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The entries that associate dimension values to dimension variables
     yield the dimension substitution,
     and the entries that associate shape values to shape variables
     yield the shape substitution;
     the variables are turned into their names,
     and the values are converted to dimension and shape ASTs.
     Entries with mismatched sorts should never occur,
     but currently we do not have that invariant available."))
  (b* (((when (omap::emptyp (ispace-var-ispace-value-map-fix map)))
        (mv nil nil))
       ((mv key val) (omap::head map))
       ((mv dim-subst shape-subst)
        (ispace-var-ispace-value-map-to-substs (omap::tail map))))
    (ispace-var-case
     key
     :dim (ispace-value-case
           val
           :dim (mv (omap::update key.name (dim-const val.val) dim-subst)
                    shape-subst)
           :shape (prog2$
                   (raise "Internal error: ~
                           ~x0 and ~x1 have different sorts."
                          key val)
                   (mv nil nil)))
     :shape (ispace-value-case
             val
             :dim (prog2$
                   (raise "Internal error: ~
                                 ~x0 and ~x1 have different sorts."
                          key val)
                   (mv nil nil))
             :shape (mv dim-subst
                        (omap::update key.name
                                      (shape-dims (dim-const-list val.val))
                                      shape-subst)))))
  :no-function nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type-values-to-types
  :short "Convert type values to types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-value-to-type ((tval type-valuep))
    :returns (type typep)
    :parents (values-to-abstract-syntax type-values-to-types)
    :short "Convert a type value to a type."
    :long
    (xdoc::topstring
     (xdoc::p
      "Universal, product, and sum type values are closures:
       we substitute the bindings of the captured dynamic environment
       into the body (see @(tsee type-subst-type-denv)),
       and we rebuild the (universal, product, or sum) type
       with the parameters and the resulting body."))
    (type-value-case
     tval
     :base (type-base tval.type)
     :array (make-type-array
             :elem (type-value-to-type tval.elem)
             :ispace (ispace-shape (shape-dims (dim-const-list tval.dims))))
     :fun (make-type-fun :in (type-value-list-to-type-list tval.in)
                         :out (type-value-to-type tval.out))
     :forall (make-type-forall
              :params tval.params
              :body (type-subst-type-denv tval.body tval.denv))
     :pi (make-type-pi
          :params tval.params
          :body (type-subst-type-denv tval.body tval.denv))
     :sigma (make-type-sigma
             :params tval.params
             :body (type-subst-type-denv tval.body tval.denv)))
    :measure (type-value-count tval))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-value-list-to-type-list ((tvals type-value-listp))
    :returns (types type-listp)
    :parents (values-to-abstract-syntax type-values-to-types)
    :short "Convert a list of type values to a list of types."
    (if (endp tvals)
        nil
      (cons (type-value-to-type (car tvals))
            (type-value-list-to-type-list (cdr tvals))))
    :measure (type-value-list-count tvals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-var-type-value-map-to-substs ((map type-var-type-value-mapp))
    :returns (mv (atom-subst string-type-mapp)
                 (array-subst string-type-mapp))
    :parents (values-to-abstract-syntax type-values-to-types)
    :short "Convert (i) a map from type variables to type values
            to (ii) atom and array type substitutions."
    :long
    (xdoc::topstring
     (xdoc::p
      "The entries for atom-kinded type variables
       yield the first substitution,
       and the entries for array-kinded type variables
       yield the second substitution;
       the variables are mapped to their names,
       and the type values are converted to types.")
     (xdoc::p
      "This is mutually recursive with @(tsee type-value-to-type)
       because it has to turn the type values in the environment to types,
       and those may recursively be closures."))
    (b* (((when (omap::emptyp (type-var-type-value-map-fix map))) (mv nil nil))
         ((mv key val) (omap::head map))
         ((mv atom-subst array-subst)
          (type-var-type-value-map-to-substs (omap::tail map)))
         (type (type-value-to-type val)))
      (type-var-case key
                     :atom (mv (omap::update key.name type atom-subst)
                               array-subst)
                     :array (mv atom-subst
                                (omap::update key.name type array-subst))))
    :measure (type-var-type-value-map-count map))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-subst-type-denv ((type typep) (denv type-denvp))
    :returns (new-type typep)
    :parents (values-to-abstract-syntax type-values-to-types)
    :short "Substitute the bindings of a type dynamic environment in a type."
    :long
    (xdoc::topstring
     (xdoc::p
      "The ispace bindings are substituted as dimensions and shapes,
       and the type bindings are substituted as types
       converted from the type values.
       This is used to convert type value closures to types:
       since the environment of a closure has bindings for
       the free variables of the closure's body,
       the resulting type has no free variables
       other than the closure's parameters.")
     (xdoc::p
      "We use the substitution operations without alpha renaming:
       the dimensions and shapes that we substitute are constants,
       and the types that we substitute are converted from type values,
       and thus have no free variables
       (given the invariant on closure environments mentioned above);
       so no variable capture is possible,
       and alpha renaming would never actually apply."))
    (b* (((mv dim-subst shape-subst)
          (ispace-var-ispace-value-map-to-substs
           (ispace-denv->ispaces (type-denv->ienv denv))))
         ((mv atom-subst array-subst)
          (type-var-type-value-map-to-substs (type-denv->types denv)))
         (type (type-subst-ispace-vars type dim-subst shape-subst)))
      (type-subst-type-vars type atom-subst array-subst))
    :measure (type-denv-count denv))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual type-values-to-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-value-option-to-type-option ((tval? type-value-optionp))
  :returns (type? type-optionp)
  :short "Convert an optional type value to an optional type."
  (type-value-option-case tval?
                          :some (type-value-to-type tval?.val)
                          :none nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var+typevalue-to-var+type? ((vt var+typevalue-p))
  :returns (var+type? var+type?-p)
  :short "Convert a variable with a type value
          to a variable with an (optional) type."
  (make-var+type? :var (var+typevalue->var vt)
                  :type? (type-value-to-type (var+typevalue->type vt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection var+typevalue-list-to-var+type?s ((x var+typevalue-listp))
  :returns (var+type?s var+type?-listp)
  :short "Lift @(tsee var+typevalue-to-var+type?) to lists."
  (var+typevalue-to-var+type? x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-to-int-lit ((i integerp))
  :returns (ilit int-litp)
  :short "Represent an integer as an integer literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the minimum number of digits,
     with a minus sign for negative integers."))
  (b* ((i (lifix i)))
    (make-int-lit :sign? (if (< i 0) (sign-minus) nil)
                  :digits (str::nat-to-dec-chars (abs i))))
  :guard-hints (("Goal" :in-theory (enable abs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define count-factor ((p integerp) (n posp))
  :guard (<= 2 p)
  :returns (mv (count natp :rule-classes (:rewrite :type-prescription))
               (rest posp :rule-classes (:rewrite :type-prescription)))
  :short "Count the multiplicity of a factor in a positive integer,
          returning also the integer with that factor removed."
  (b* ((p (lifix p))
       (n (lposfix n))
       ((unless (mbt (<= 2 p))) (mv 0 1))
       (q (/ n p))
       ((unless (posp q)) (mv 0 n))
       ((mv count rest) (count-factor p q)))
    (mv (1+ count) rest))
  :measure (nfix n)
  :hints (("Goal" :in-theory (enable pos-fix)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable (tau-system))))
  :prepwork
  ((defrulel inverse-below-one
     (implies (and (integerp p) (<= 2 p))
              (< (/ p) 1))
     :rule-classes :linear
     :hints (("Goal" :nonlinearp t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pad-zeros-left ((digits str::dec-digit-char-listp) (len natp))
  :returns (new-digits str::dec-digit-char-listp)
  :short "Pad a list of digits with leading zeros up to a given length."
  (append (repeat (nfix (- (lnfix len) (len digits))) #\0)
          (str::dec-digit-char-list-fix digits))
  :prepwork
  ((defrulel dec-digit-char-listp-of-repeat-of-zero-char
     (str::dec-digit-char-listp (repeat n #\0))
     :induct t
     :enable repeat))

  ///

  (defret consp-of-pad-zeros-left
    (implies (or (consp digits) (< 0 (nfix len)))
             (consp new-digits))
    :hints (("Goal" :in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rational-to-float-lit ((r rationalp))
  :returns (mv (err booleanp) (flit float-litp))
  :short "Represent a rational as a float literal, if possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "A rational has an exact float literal representation iff
     its denominator has no prime factors other than 2 and 5,
     i.e. iff its decimal expansion terminates.
     In that case we return the literal @('<whole>.<frac>'),
     with a minus sign for negative rationals
     and with the minimum number of fractional digits (at least one);
     otherwise we fail."))
  (b* ((r (rfix r))
       (neg (< r 0))
       (a (abs r))
       ((mv c2 rest) (count-factor 2 (denominator a)))
       ((mv c5 rest) (count-factor 5 rest))
       (dummy (make-float-lit :sign? nil
                              :whole-digits '(#\0)
                              :frac-digits '(#\0)
                              :expo? nil))
       ((unless (eql rest 1)) (mv t dummy))
       (k (max c2 c5))
       (w (floor a 1))
       (f (* (- a w) (expt 10 k)))
       ;; The following checks on W and F never fail;
       ;; they just simplify guard proofs.
       ;; TODO: eliminate these
       ((unless (and (natp w) (natp f))) (mv t dummy)))
    (mv nil
        (make-float-lit :sign? (if neg (sign-minus) nil)
                        :whole-digits (str::nat-to-dec-chars w)
                        :frac-digits (pad-zeros-left (str::nat-to-dec-chars f)
                                                     (max k 1))
                        :expo? nil)))
  :guard-hints (("Goal" :in-theory (enable abs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-value-to-float-lit ((fval float-valuep))
  :returns (mv (err booleanp) (flit float-litp))
  :short "Represent a float value as a float literal, if possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "Negative zero is @('-0.0');
     rationals are handled by @(tsee rational-to-float-lit);
     infinities and not-a-number have no literal representation."))
  (float-value-case
   fval
   :ratio (rational-to-float-lit fval.ratio)
   :neg0 (mv nil (make-float-lit :sign? (sign-minus)
                                 :whole-digits '(#\0)
                                 :frac-digits '(#\0)
                                 :expo? nil))
   :otherwise (mv t (make-float-lit :sign? nil
                                    :whole-digits '(#\0)
                                    :frac-digits '(#\0)
                                    :expo? nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base-value-to-base-lit ((bval base-valuep))
  :returns (mv (err booleanp) (blit base-litp))
  :short "Represent a base value as a base literal, if possible."
  (base-value-case
   bval
   :bool (mv nil (base-lit-bool bval.val))
   :int (mv nil (base-lit-int (int-to-int-lit (int-value->int bval.val))))
   :float (b* (((mv err flit) (float-value-to-float-lit bval.val)))
            (mv err (base-lit-float flit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-name-lookup ((pval primop-valuep) (map string-expr-value-mapp))
  :returns (mv (err booleanp) (name stringp))
  :short "Find the name associated to a primitive operation value in a map."
  (b* (((when (omap::emptyp (string-expr-value-map-fix map))) (mv t ""))
       ((mv key val) (omap::head map))
       ((when (equal val (expr-value-primop pval))) (mv nil (str-fix key))))
    (primop-name-lookup pval (omap::tail map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-name ((pval primop-valuep))
  :returns (mv (err booleanp) (name stringp))
  :short "Name of the variable that denotes a primitive operation value."
  :long
  (xdoc::topstring
   (xdoc::p
    "For an instantiated stage of a polymorphic primitive operation,
     this is the name of the variable that denotes
     the uninstantiated operation."))
  (primop-name-lookup (primop-value-uninstantiated pval) (primop-values)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-to-expr ((pval primop-valuep))
  :returns (mv (err booleanp) (expr exprp))
  :short "Convert a primitive operation value to an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "An uninstantiated primitive operation value,
     which includes every monomorphic primitive operation,
     becomes the variable that denotes the operation.
     A partially instantiated primitive operation value becomes
     a type application of that variable
     to the type converted from the type value in the stage.
     A totally instantiated primitive operation value becomes
     an ispace application of that type application
     to the dimension and the shape in the stage.
     As we add more polymorphic primitive operations,
     we will need to generalize this."))
  (b* (((mv err name) (primop-value-name pval))
       (opvar (expr-var name))
       ((when err) (mv t opvar)))
    (primop-value-case
     pval
     :head-t (mv nil
                 (make-expr-tapp
                  :fun opvar
                  :args (list (type-value-to-type pval.tval))))
     :head-t-d-s (mv nil
                     (make-expr-iapp
                      :fun (make-expr-tapp
                            :fun opvar
                            :args (list (type-value-to-type pval.tval)))
                      :args (list (ispace-dim (dim-const pval.d))
                                  (ispace-shape
                                   (shape-dims (dim-const-list pval.s))))))
     :tail-t (mv nil
                 (make-expr-tapp
                  :fun opvar
                  :args (list (type-value-to-type pval.tval))))
     :tail-t-d-s (mv nil
                     (make-expr-iapp
                      :fun (make-expr-tapp
                            :fun opvar
                            :args (list (type-value-to-type pval.tval)))
                      :args (list (ispace-dim (dim-const pval.d))
                                  (ispace-shape
                                   (shape-dims (dim-const-list pval.s))))))
     :length-t (mv nil
                   (make-expr-tapp
                    :fun opvar
                    :args (list (type-value-to-type pval.tval))))
     :length-t-d-s (mv nil
                       (make-expr-iapp
                        :fun (make-expr-tapp
                              :fun opvar
                              :args (list (type-value-to-type pval.tval)))
                        :args (list (ispace-dim (dim-const pval.d))
                                    (ispace-shape
                                     (shape-dims (dim-const-list pval.s))))))
     :otherwise (mv nil opvar))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expr-values-to-exprs
  :short "Convert expression values to expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Base values become literal atoms;
     primitive operation values become the variables that denote the operations,
     wrapped in type and ispace applications
     if the operations are partially or totally instantiated
     (see @(tsee primop-value-to-expr));
     lambda values become lambda abstraction atoms
     (with the parameter and result type values converted to types);
     boxes become box atoms;
     non-empty vectors become bracket expressions;
     and empty vectors become empty array expressions.
     Conversion fails only for float values with no literal syntax
     (see @(tsee float-value-to-float-lit))."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-value-to-expr ((val expr-valuep))
    :returns (mv (err booleanp) (expr exprp))
    :parents (values-to-abstract-syntax expr-values-to-exprs)
    :short "Convert an expression value to an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This needs to be extended to handle closures."))
    (expr-value-case
     val
     :base (b* (((mv err blit) (base-value-to-base-lit val.val)))
             (mv err (expr-atom (atom-base blit))))
     :primop (primop-value-to-expr val.val)
     :lambda (mv nil
                 (expr-atom
                  (make-atom-lambda
                   :params (var+typevalue-list-to-var+type?s val.params)
                   :body val.body
                   :type? (type-value-option-to-type-option val.type?))))
     :tlambda (mv nil (expr-atom (atom-tlambda val.params val.body)))
     :ilambda (mv nil (expr-atom (atom-ilambda val.params val.body)))
     :box (b* (((mv err array) (expr-value-to-expr val.array)))
            (mv err
                (expr-atom
                 (make-atom-box
                  :ispaces (ispace-value-list-to-ispaces val.ispaces)
                  :array array
                  :type (type-value-to-type val.type)))))
     :vector (b* (((mv err exprs) (expr-value-list-to-exprs val.elems)))
               (mv err (expr-bracket exprs)))
     :vector-empty (mv nil
                       (expr-array-empty (cons 0 val.dims)
                                         (type-value-to-type val.elem))))
    :measure (expr-value-count val))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define expr-value-list-to-exprs ((vals expr-value-listp))
    :returns (mv (err booleanp) (exprs expr-listp))
    :parents (values-to-abstract-syntax expr-values-to-exprs)
    :short "Convert a list of expression values to a list of expressions."
    (b* (((when (endp vals)) (mv nil nil))
         ((mv err expr) (expr-value-to-expr (car vals)))
         ((when err) (mv t nil))
         ((mv err exprs) (expr-value-list-to-exprs (cdr vals))))
      (mv err (cons expr exprs)))
    :measure (expr-value-list-count vals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual expr-values-to-exprs))
