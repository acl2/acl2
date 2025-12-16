; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/fty/deffold-map" :dir :system)

(include-book "../../syntax/abstract-syntax-trees")
(include-book "../../syntax/validation-information")

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration
  ;; Necessary for the deffold-map termination.
  :tau t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map funcall-fun-rename-fn
  :parents (rename-fn)
  :types (c$::exprs/decls/stmts)
  :extra-args ((uid c$::uidp) (new-fn identp))
  :short "Rename a function within a @('funcall') function expression."
  :override
  ((c$::expr
     (b* ((uid (c$::uid-fix uid))
          (new-fn (ident-fix new-fn)))
       (expr-case
         c$::expr
         :ident (if (and (var-infop c$::expr.info)
                         (c$::uid-equal (c$::var-info->uid c$::expr.info)
                                        uid))
                    (make-expr-ident :ident new-fn :info nil)
                  (expr-fix c$::expr))
         :paren (expr-paren
                  (expr-funcall-fun-rename-fn expr.inner uid new-fn))
         :gensel
         (make-expr-gensel
           :control expr.control
           :assocs (genassoc-list-funcall-fun-rename-fn
                     expr.assocs uid new-fn))
         :cast (make-expr-cast :type expr.type
                               :arg (expr-funcall-fun-rename-fn
                                      expr.arg uid new-fn))
         :otherwise (expr-fix c$::expr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-fn
  :parents (utilities)
  :types #!c$(exprs/decls/stmts
              fundef
              fundef-option
              ext-declon
              ext-declon-list)
  :extra-args ((uid c$::uidp) (new-fn identp))
  :override
  ((c$::expr
     :funcall
     (make-expr-funcall
       :fun (expr-funcall-fun-rename-fn expr.fun uid new-fn)
       :args (expr-list-rename-fn expr.args uid new-fn)))))
