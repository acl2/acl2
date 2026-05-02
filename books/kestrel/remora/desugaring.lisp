; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-core")
(include-book "abstract-syntax-structural-operations")
(include-book "character-literal-codes")

(include-book "kestrel/fty/deffold-map" :dir :system)

(acl2::controlled-configuration)

(local (in-theory (enable* abstract-syntax-corep-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ desugaring
  :parents (abstract-syntax)
  :short "Abstract syntax desugaring."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a desugaring transformation from all ASTs to the core ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-lit-desugar ((clit char-litp))
  :returns (ilit int-litp)
  :short "Desugar a character literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Character literals are only used in string literals,
     which desugar to array expressions
     whose atoms are integers that are the codes of the character literals.
     So here we desugar a character literal to an integer literal:
     we obtain the code of the character literal
     and we represent it with the minimum number of digits without sign."))
  (make-int-lit :sign? nil
                :digits (str::nat-to-dec-chars (char-lit-code clit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection char-lit-list-desugar ((x char-lit-listp))
  :returns (ilits int-lit-listp)
  :short "Lift @(tsee char-lit-desugar)."
  (char-lit-desugar x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map desugar
  :short "Desugar ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A shape with a list of zero or more dimensions
     is turned into a concatenation of single-dimension shapes.")
   (xdoc::p
    "A shape splice is turned into a concatenation.")
   (xdoc::p
    "A bracket type is turned into an array type
     whose shape is the concatenation of the shapes.")
   (xdoc::p
    "A string is turned into an arary expression
     with the length of the string as its single dimension
     and with the characters, converted to integers, as atoms.")
   (xdoc::p
    "A combined application is turned into its constituent applications,
     also based on whether type and ispace arguments are present or not."))
  :types (shapes
          ispace
          ispace-list
          ispace-list-option
          types
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :override
  ((shape :dims (shape-append (shape-dim-list shape.dims)))
   (shape :splice (shape-append (shape-list-desugar shape.shapes)))
   (type :bracket (make-type-array :elem (type-desugar type.elem)
                                   :shape (shape-append
                                           (shape-list-desugar type.shapes))))
   (expr :string (make-expr-array
                  :dims (list (len expr.chars))
                  :atoms (atom-base-list
                          (base-lit-int-list
                           (char-lit-list-desugar expr.chars)))))
   (expr :capp (b* ((fun (expr-desugar expr.fun))
                    (fun-targs
                     (type-list-option-case
                      expr.targs
                      :some (make-expr-tapp
                             :fun fun
                             :args (type-list-desugar expr.targs.val))
                      :none fun))
                    (fun-targs-iargs
                     (ispace-list-option-case
                      expr.iargs
                      :some (make-expr-iapp
                             :fun fun-targs
                             :args (ispace-list-desugar expr.iargs.val))
                      :none fun-targs))
                    (fun-targs-iargs-args
                     (make-expr-app
                      :fun fun-targs-iargs
                      :args (expr-list-desugar expr.args))))
                 fun-targs-iargs-args))
   (expr :bracket (prog2$ (hard-error 'desugar "TODO" nil)
                          (expr-var "irrelevant")))
   (expr :let (prog2$ (hard-error 'desugar "TODO" nil)
                      (expr-var "irrelevant")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection corep-of-desugar
  :short "Desugaring always returns core ASTs."

  (defret-mutual shapes-corep-of-shapes-desugar
    (defret shape-corep-of-shape-desugar
      (shape-corep fty::result)
      :fn shape-desugar)
    (defret shape-list-corep-of-shape-list-desugar
      (shape-list-corep fty::result)
      :fn shape-list-desugar)
    :mutual-recursion shapes-desugar
    :hints (("Goal" :in-theory (enable shape-desugar shape-list-desugar))))

  (defret ispace-corep-of-ispace-desugar
    (ispace-corep fty::result)
    :fn ispace-desugar
    :hints (("Goal" :in-theory (enable ispace-desugar))))

  (defret ispace-list-corep-of-ispace-list-desugar
    (ispace-list-corep fty::result)
    :fn ispace-list-desugar
    :hints (("Goal" :induct t :in-theory (enable ispace-list-desugar))))

  (defret ispace-list-option-corep-of-ispace-list-option-desugar
    (ispace-list-option-corep fty::result)
    :fn ispace-list-option-desugar
    :hints (("Goal" :in-theory (enable ispace-list-option-desugar))))

  (defret-mutual types-corep-of-types-desugar
    (defret type-corep-of-type-desugar
      (type-corep fty::result)
      :fn type-desugar)
    (defret type-list-corep-of-type-list-desugar
      (type-list-corep fty::result)
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints (("Goal" :in-theory (enable type-desugar type-list-desugar))))

  (defret var+type-corep-of-var+type-desugar
    (var+type-corep fty::result)
    :fn var+type-desugar
    :hints (("Goal" :in-theory (enable var+type-desugar))))

  (defret var+type-list-corep-of-var+type-list-desugar
    (var+type-list-corep fty::result)
    :fn var+type-list-desugar
    :hints (("Goal" :induct t :in-theory (enable var+type-list-desugar))))

  (defret-mutual exprs/atoms/binds-corep-of-exprs/atoms/binds-desugar
    (defret expr-corep-of-expr-desugar
      (expr-corep fty::result)
      :fn expr-desugar)
    (defret expr-list-corep-of-expr-list-desugar
      (expr-list-corep fty::result)
      :fn expr-list-desugar)
    (defret atom-corep-of-atom-desugar
      (atom-corep fty::result)
      :fn atom-desugar)
    (defret atom-list-corep-of-atom-desugar
      (atom-list-corep fty::result)
      :fn atom-list-desugar)
    :skip-others t
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable expr-desugar
                                       expr-list-desugar
                                       atom-desugar
                                       atom-list-desugar))))

  (defret prog-corep-of-prog-desugar
    (prog-corep fty::result)
    :fn prog-desugar
    :hints (("Goal" :in-theory (enable prog-desugar)))))
