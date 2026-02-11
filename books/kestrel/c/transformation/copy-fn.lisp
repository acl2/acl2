; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")
(include-book "../syntax/validation-information")
(include-book "utilities/rename-fn")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ copy-fn
  :parents (transformation-tools)
  :short "A C-to-C transformation to copy a function."
  :long
  (xdoc::topstring
    (xdoc::p
      "This transformation introduces a new function which is the duplicate of
      another.")
    (xdoc::p
      "For instance, consider the following C code:")
    (xdoc::codeblock
      "int fibonacci(int x) {"
      "  if (x <= 1) {"
      "    return x;"
      "  }"
      "  return fibonacci(x - 1) + fibonacci(x - 2);"
      "}")
    (xdoc::p
      "Copying @('fibonacci') and creating a new function @('fib') yields the
       following:")
    (xdoc::codeblock
      "int fibonacci(int x) {"
      "  if (x <= 1) {"
      "    return x;"
      "  }"
      "  return fibonacci(x - 1) + fibonacci(x - 2);"
      "}"
      "int fib(int x) {"
      "  if (x <= 1) {"
      "    return x;"
      "  }"
      "  return fib(x - 1) + fib(x - 2);"
      "}")
    (xdoc::p
      "This transformation is not likely to be useful in isolation. Most often
       it is an initial step before applying different transformations to the
       two duplicates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-fundef
  ((fundef fundefp)
   (target-fn identp)
   (new-fn identp))
  :guard (fundef-annop fundef)
  :short "Transform a function definition."
  :returns (fundef? fundef-optionp)
  (b* (((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor)
       ((fundef-info info) fundef.info))
    (dirdeclor-case
      fundef.declor.direct
      :function-params
      (if (equal target-fn
                 (c$::dirdeclor->ident fundef.declor.direct.declor))
          ;; Return
          (make-fundef
            :extension fundef.extension
            :specs fundef.specs
            :declor (make-declor
                      :pointers fundef.declor.pointers
                      :direct (make-dirdeclor-function-params
                               :declor (dirdeclor-ident new-fn)
                               :params fundef.declor.direct.params
                               :ellipsis fundef.declor.direct.ellipsis))
            :declons fundef.declons
            :body (make-comp-stmt
                   :labels (comp-stmt->labels fundef.body)
                   :items (block-item-list-rename-fn
                            (comp-stmt->items fundef.body)
                            info.uid
                            new-fn))
            :info fundef.info)
        nil)
      :otherwise nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-ext-declon
  ((extdecl ext-declonp)
   (target-fn identp)
   (new-fn identp))
  :guard (ext-declon-annop extdecl)
  :short "Transform an external declaration."
  :returns (mv (found booleanp)
               (extdecls ext-declon-listp))
  (ext-declon-case
   extdecl
   :fundef (b* ((fundef?
                 (copy-fn-fundef
                   extdecl.fundef
                   target-fn
                   new-fn)))
             (if fundef?
                 (mv t (list (ext-declon-fix extdecl) (ext-declon-fundef fundef?)))
               (mv nil (list (ext-declon-fix extdecl)))))
   :declon (mv nil (list (ext-declon-fix extdecl)))
   :empty (mv nil (list (ext-declon-fix extdecl)))
   :asm (mv nil (list (ext-declon-fix extdecl)))))

(define copy-fn-ext-declon-list
  ((extdecls ext-declon-listp)
   (target-fn identp)
   (new-fn identp))
  :guard (ext-declon-list-annop extdecls)
  :short "Transform a list of external declarations."
  :returns (new-extdecls ext-declon-listp)
  (b* (((when (endp extdecls))
        nil)
       ((mv found new-extdecls)
        (copy-fn-ext-declon (first extdecls) target-fn new-fn)))
    (append new-extdecls
            (if found
                (ext-declon-list-fix (rest extdecls))
              (copy-fn-ext-declon-list (rest extdecls) target-fn new-fn))))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-transunit
  ((tunit transunitp)
   (target-fn identp)
   (new-fn identp))
  :guard (transunit-annop tunit)
  :short "Transform a translation unit."
  :returns (new-tunit transunitp)
  (b* (((transunit tunit) tunit)
       ((when tunit.includes)
        (raise "Unsupported #include directives.")
        (transunit-fix tunit)))
    (make-transunit :comment nil
                    :includes nil
                    :declons (copy-fn-ext-declon-list tunit.declons target-fn new-fn)
                    :info tunit.info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-filepath-transunit-map
  ((map filepath-transunit-mapp)
   (target-fn identp)
   (new-fn identp))
  :guard (filepath-transunit-map-annop map)
  :short "Transform a filepath."
  :returns (new-map filepath-transunit-mapp
                    :hyp (filepath-transunit-mapp map))
  (b* (((when (omap::emptyp map))
        nil)
       ((mv path tunit) (omap::head map)))
    (omap::update (c$::filepath-fix path)
                  (copy-fn-transunit tunit target-fn new-fn)
                  (copy-fn-filepath-transunit-map (omap::tail map)
                                                  target-fn
                                                  new-fn)))
  :verify-guards :after-returns)

(define copy-fn-transunit-ensemble
  ((tunits transunit-ensemblep)
   (target-fn identp)
   (new-fn identp))
  :guard (transunit-ensemble-annop tunits)
  :short "Transform a translation unit ensemble."
  :returns (new-tunits transunit-ensemblep)
  (b* (((transunit-ensemble tunits) tunits))
    (c$::make-transunit-ensemble
      :units (copy-fn-filepath-transunit-map tunits.units
                                             target-fn
                                             new-fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-code-ensemble
  ((code code-ensemblep)
   (target-fn identp)
   (new-fn identp))
  :guard (code-ensemble-annop code)
  :returns (new-code code-ensemblep)
  :short "Transform a code ensemble."
  (b* (((code-ensemble code) code))
    (change-code-ensemble
     code
     :transunits
     (copy-fn-transunit-ensemble code.transunits target-fn new-fn))))
