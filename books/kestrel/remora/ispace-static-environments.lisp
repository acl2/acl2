; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "variable-substitution-operations")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-static-environments
  :parents (static-environments)
  :short "Ispace static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see static-environments) first."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ispace-senv
  :short "Fixtype of ispace static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "An ispace static environment is
     a map from the ispace variables in scope to optional ispaces.
     This corresponds to @($\\Theta$);
     since our ispace variables include their own sort,
     the keys suffice to capture the sorts,
     as opposed to a map from variables to sorts.
     The optional ispace associated to a variable:
     is absent when the variable is bound by an abstraction,
     i.e. it does not stand for any specific ispace;
     it is present when the variable is bound by a @('let')
     to a specific ispace, which is then its definition."))
  ((ispaces ispace-var-ispace-option-map))
  :pred ispace-senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-ispace-senv ()
  :returns (ienv ispace-senvp)
  :short "Initial ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, ispace static environment.
     It is empty."))
  (ispace-senv nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-add-var ((var ispace-varp) (ienv ispace-senvp))
  :returns (new-ienv ispace-senvp)
  :short "Add an ispace variable to the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with an absent associated ispace,
     because it does not stand for any specific ispace;
     this is the case for variables bound by abstractions.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-ispace-senv ienv
                      :ispaces (omap::update (ispace-var-fix var)
                                             nil
                                             (ispace-senv->ispaces ienv))))

;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-add-vars ((vars ispace-var-listp) (ienv ispace-senvp))
  :returns (new-ienv ispace-senvp)
  :short "Add zero or more ispace variables to the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee ispace-senv-add-var),
     which this function repeats for each variable."))
  (b* (((when (endp vars)) (ispace-senv-fix ienv))
       (ienv (ispace-senv-add-var (car vars) ienv)))
    (ispace-senv-add-vars (cdr vars) ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-add-def ((var ispace-varp)
                             (ispace ispacep)
                             (ienv ispace-senvp))
  :returns (new-ienv ispace-senvp)
  :short "Add an ispace variable with its ispace definition
          to the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with a present associated ispace,
     namely its definition;
     this is the case for variables bound by @('let')s.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-ispace-senv ienv
                      :ispaces (omap::update (ispace-var-fix var)
                                             (ispace-fix ispace)
                                             (ispace-senv->ispaces ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-ispace-subst ((map ispace-var-ispace-option-mapp))
  :returns (subst stringdimmap+stringshapemap-p)
  :short "Turn a map from ispace variables to optional ispaces
          into the ispace variable substitution
          determined by the definitions in the map."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to turn
     the map in an ispace static environment
     into a dimension substitution and a shape substitution,
     consisting of the variables that have a definition
     (i.e. a present optional ispace);
     variables without an ispace do not contribute.
     A dimension variable maps to the dimension of its (dimension) ispace,
     and a shape variable maps to the shape of its (shape) ispace.")
   (xdoc::p
    "It should never be the case that the map violates sorts,
     i.e. associates a dimension variable to a shape ispace
     or a shape variable to a dimension ispace.
     But we do not have that static invariant yet,
     so we defensively throw an error if that happens."))
  (b* (((when (omap::emptyp (ispace-var-ispace-option-map-fix map)))
        (make-stringdimmap+stringshapemap :dim-map nil :shape-map nil))
       ((mv var ispace?) (omap::head map))
       ((stringdimmap+stringshapemap subst-rest)
        (ispace-senv-ispace-subst (omap::tail map))))
    (ispace-option-case
     ispace?
     :none subst-rest
     :some
     (ispace-var-case
      var
      :dim (ispace-case
            ispace?.val
            :dim (change-stringdimmap+stringshapemap
                  subst-rest
                  :dim-map (omap::update var.name
                                         ispace?.val.dim
                                         subst-rest.dim-map))
            :shape (prog2$ (raise "Internal error: ~
                                   dimension variable ~x0 ~
                                   is associated with ~
                                   shape ispace ~x1."
                                  var ispace?.val)
                           subst-rest))
      :shape (ispace-case
              ispace?.val
              :dim (prog2$ (raise "Internal error: ~
                                   shape variable ~x0 ~
                                   is associated with ~
                                   dimension ispace ~x1."
                                  var ispace?.val)
                           subst-rest)
              :shape (change-stringdimmap+stringshapemap
                      subst-rest
                      :shape-map (omap::update var.name
                                               ispace?.val.shape
                                               subst-rest.shape-map))))))
  :no-function nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-expand-shape ((shape shapep) (ienv ispace-senvp))
  :returns (new-shape shapep)
  :short "Expand a shape using the ispace definitions
          in the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined ispace variable in the shape
     with its definition (see @(tsee ispace-senv-ispace-subst)).
     Since shapes contain no binders, this substitution cannot capture."))
  (b* (((stringdimmap+stringshapemap subst)
        (ispace-senv-ispace-subst (ispace-senv->ispaces ienv))))
    (shape-subst-ispace-vars shape subst.dim-map subst.shape-map)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-expand-ispace ((ispace ispacep) (ienv ispace-senvp))
  :returns (new-ispace ispacep)
  :short "Expand an ispace using the ispace definitions
          in the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined ispace variable in the ispace
     with its definition (see @(tsee ispace-senv-ispace-subst)).
     Since ispaces contain no binders, this substitution cannot capture."))
  (b* (((stringdimmap+stringshapemap subst)
        (ispace-senv-ispace-subst (ispace-senv->ispaces ienv))))
    (ispace-subst-ispace-vars ispace subst.dim-map subst.shape-map)))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-senv-expand-ispace-list ((x ispace-listp)
                                                    (ienv ispace-senvp))
  :returns (new-ispaces ispace-listp)
  :short "Lift @(tsee ispace-senv-expand-ispace) to lists of ispaces."
  (ispace-senv-expand-ispace x ienv))
