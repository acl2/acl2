; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
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
(include-book "deftrans")
(include-book "utilities/free-vars")

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
    (xdoc::code
      "int foo(int y, int z) {"
      "  int x = 5;"
      "  return x + y - z;"
      "}")
    (xdoc::p
      "Copying @('foo') and creating a new function @('bar') yields the
       following:")
    (xdoc::code
      "int foo(int y, int z) {"
      "  int x = 5;"
      "  return x + y - z;"
      "}"
      "int bar(int y, int z) {"
      "  int x = 5;"
      "  return x + y - z;"
      "}")
    (xdoc::p
      "This transformation is not likely to be useful in isolation. Most often
       it is an initial step before applying different transformations to the
       two duplicates.")
    (xdoc::p
      "Currently, this transformation does <i>not</i> rename recursive function
       calls in the body to match the new function name. This is planned to
       change soon."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-fundef
  ((fundef fundefp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a function definition."
  :returns (fundef? fundef-optionp)
  (b* (((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor))
    (dirdeclor-case
      fundef.declor.decl
      :function-params
      (if (equal target-fn
                 (dirdeclor-get-ident fundef.declor.decl.decl))
          ;; Return
          (make-fundef
            :extension fundef.extension
            :spec fundef.spec
            :declor (make-declor
                      :pointers fundef.declor.pointers
                      :decl (make-dirdeclor-function-params
                              :decl (dirdeclor-ident new-fn)
                              :params fundef.declor.decl.params
                              :ellipsis fundef.declor.decl.ellipsis))
            :decls fundef.decls
            ;; TODO: need to replace the recursive function calls with the new
            ;;   function name.
            ;; :body (TODO-RENAME-RECUR target-fn new-fn fundef.body))
            :body fundef.body)
        nil)
      :otherwise nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-extdecl
  ((extdecl extdeclp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform an external declaration."
  :returns (mv (found booleanp)
               (extdecls extdecl-listp))
  (extdecl-case
   extdecl
   :fundef (b* ((fundef?
                 (copy-fn-fundef
                   extdecl.unwrap
                   target-fn
                   new-fn)))
             (if fundef?
                 (mv t (list (extdecl-fix extdecl) (extdecl-fundef fundef?)))
               (mv nil (list (extdecl-fix extdecl)))))
   :decl (mv nil (list (extdecl-fix extdecl)))
   :empty (mv nil (list (extdecl-fix extdecl)))))

(define copy-fn-extdecl-list
  ((extdecls extdecl-listp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a list of external declarations."
  :returns (new-extdecls extdecl-listp)
  (b* (((when (endp extdecls))
        nil)
       ((mv found new-extdecls)
        (copy-fn-extdecl (first extdecls) target-fn new-fn)))
    (append new-extdecls
            (if found
                (extdecl-list-fix (rest extdecls))
              (copy-fn-extdecl-list (rest extdecls) target-fn new-fn)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-transunit
  ((tunit transunitp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a translation unit."
  :returns (new-tunit transunitp)
  (b* (((transunit tunit) tunit))
    (transunit (copy-fn-extdecl-list tunit.decls target-fn new-fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define copy-fn-filepath-transunit-map
  ((map filepath-transunit-mapp)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a filepath."
  :returns (new-map filepath-transunit-mapp
                    :hyp (filepath-transunit-mapp map))
  (b* (((when (omap::emptyp map))
        nil)
       ((mv path tunit) (omap::head map)))
    (omap::update (deftrans-filepath path "COPY-FN")
                  (copy-fn-transunit tunit target-fn new-fn)
                  (copy-fn-filepath-transunit-map (omap::tail map)
                                                  target-fn
                                                  new-fn)))
  :verify-guards :after-returns)

(define copy-fn-transunit-ensemble
  ((tunits transunit-ensemblep)
   (target-fn identp)
   (new-fn identp))
  :short "Transform a translation unit ensemble."
  :returns (new-tunits transunit-ensemblep)
  (b* (((transunit-ensemble tunits) tunits))
    (transunit-ensemble
      (copy-fn-filepath-transunit-map tunits.unwrap
                                      target-fn
                                      new-fn))))
