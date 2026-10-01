; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/c/syntax/validation-annotations" :dir :system)
(include-book "kestrel/c/syntax/validator" :dir :system)
(include-book "std/util/deffixer" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ code-env
  :parents (c-transformation-json-rpc)
  :short "The environment of named code ensembles
          kept by the JSON-RPC interface."
  :long
  (xdoc::topstring
   (xdoc::p
    "The JSON-RPC server keeps a single environment
     that maps names, chosen by the clients, to annotated code ensembles.
     Methods that read files add code ensembles to the environment,
     transformation methods read code ensembles from it and add new ones,
     and other methods write out, list, or drop them.
     The environment persists across requests and connections.")
   (xdoc::p
    "The environment is a @(see acl2::stobj)
     with a single hash table field, @('ensembles'),
     whose keys are the names.
     Its values are typed in the logic,
     so a code ensemble read from the environment is known to be annotated,
     without checking it again at run time.
     Dropping a name (via @('ensembles-rem'))
     makes its code ensemble available for garbage collection.")
   (xdoc::p
    "Looking up an unbound name yields @('nil'),
     so the values are optional annotated code ensembles
     (see @(tsee ann-code-ensemble-option)).
     The methods only store actual code ensembles,
     so a name is bound exactly when its value is not @('nil')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ann-code-ensemblep (x)
  :returns (yes/no booleanp)
  :short "Recognizer for @(tsee ann-code-ensemble)."
  (and (code-ensemblep x)
       (code-ensemble-annop x))
  ///

  (defrule code-ensemblep-when-ann-code-ensemblep
    (implies (ann-code-ensemblep x)
             (code-ensemblep x))
    :enable ann-code-ensemblep)

  (defrule code-ensemble-annop-when-ann-code-ensemblep
    (implies (ann-code-ensemblep x)
             (code-ensemble-annop x))
    :enable ann-code-ensemblep)

  (defrule ann-code-ensemblep-when-code-ensemble-annop
    (implies (and (code-ensemblep x)
                  (code-ensemble-annop (double-rewrite x)))
             (ann-code-ensemblep x))
    :enable ann-code-ensemblep))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ann-code-ensemble
  :short "An irrelevant annotated code ensemble."
  :type ann-code-ensemblep
  :body (c$::make-code-ensemble
         :trans-units (c$::make-trans-ensemble
                       :units nil
                       :resolved-includes nil
                       :info (c$::make-trans-ensemble-vinfo
                              :externals nil
                              :completions nil))
         :ienv (c$::irr-ienv)))

;;;;;;;;;;;;;;;;;;;;

(std::deffixer ann-code-ensemble-fix
  :short "Fixer for @(tsee ann-code-ensemble)."
  :pred ann-code-ensemblep
  :body-fix (irr-ann-code-ensemble))

;;;;;;;;;;;;;;;;;;;;

(fty::deffixtype ann-code-ensemble
  :pred ann-code-ensemblep
  :fix ann-code-ensemble-fix
  :equiv ann-code-ensemble-equiv
  :define t)

(defxdoc+ ann-code-ensemble
  :short "Fixtype of annotated code ensembles."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the code ensembles
     that satisfy @(tsee code-ensemble-annop),
     i.e. that are annotated with validation information.
     The transformations require such code ensembles.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption ann-code-ensemble-option
  ann-code-ensemble
  :short "Fixtype of optional annotated code ensembles."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the values in the environment.
     It includes @('nil') because that is the value of an unbound name."))
  :pred ann-code-ensemble-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define revalidate-code-ensemble ((code code-ensemblep))
  :returns (mv (er? maybe-msgp)
               (code$ ann-code-ensemblep
                      :hints (("Goal"
                               :in-theory
                               (enable* revalidate-code-ensemble
                                        c$::abstract-syntax-annop-rules)))))
  :short "Validate a transformed code ensemble,
          obtaining an annotated code ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
    "Most transformations do not re-validate their output,
     which is thus not annotated, or not fully,
     e.g. because it contains new constructs.
     Before such an output is stored in the environment,
     it is validated again, with the same implementation environment.
     This also refreshes any annotations that the transformation
     may have made out of date."))
  (b* (((reterr) (irr-ann-code-ensemble))
       ((code-ensemble code) code)
       ((unless (c$::trans-ensemble-unambp code.trans-units))
        (retmsg$ "Internal error: the transformed code is ambiguous."))
       ((erp trans-units)
        (c$::valid-trans-ensemble code.trans-units code.ienv nil))
       ;; TODO: remove once it is proved that validation produces
       ;; an annotated term.
       ((unless (c$::trans-ensemble-annop trans-units))
        (retmsg$ "Internal error: the transformed code is invalid.")))
    (retok (change-code-ensemble code :trans-units trans-units))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj code-env
  (ensembles :type (hash-table equal nil (satisfies ann-code-ensemble-optionp))
             :initially nil))

(defruledl ann-code-ensemble-optionp-of-cdr-of-hons-assoc-equal-when-ensemblesp
  (implies (ensemblesp alist)
           (ann-code-ensemble-optionp (cdr (hons-assoc-equal key alist))))
  :induct t
  :enable (ensemblesp hons-assoc-equal))

(defrule ann-code-ensemble-optionp-of-ensembles-get
  (implies (code-envp code-env)
           (ann-code-ensemble-optionp (ensembles-get key code-env)))
  :enable ann-code-ensemble-optionp-of-cdr-of-hons-assoc-equal-when-ensemblesp)

(in-theory (disable ensembles-get))
