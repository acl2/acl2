; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../deftrans")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  ;; Generates the identify transformation
  (deftrans identity-trans)

  (c$::input-files :files ("test1.c")
                   :const *old*)

  (defconst *new*
    (identity-trans-transunit-ensemble *old*))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "int main() {
  int x = 5;
  return x + 0;
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (deftrans my-simpadd0
    :expr (lambda (expr)
            (expr-case
              expr
              :ident (expr-fix expr)
              :const (expr-fix expr)
              :string (expr-fix expr)
              :paren (expr-paren (my-simpadd0-expr expr.inner))
              :gensel (make-expr-gensel
                        :control (my-simpadd0-expr expr.control)
                        :assocs (my-simpadd0-genassoc-list expr.assocs))
              :arrsub (make-expr-arrsub
                        :arg1 (my-simpadd0-expr expr.arg1)
                        :arg2 (my-simpadd0-expr expr.arg2))
              :funcall (make-expr-funcall
                         :fun (my-simpadd0-expr expr.fun)
                         :args (my-simpadd0-expr-list expr.args))
              :member (make-expr-member
                        :arg (my-simpadd0-expr expr.arg)
                        :name expr.name)
              :memberp (make-expr-memberp
                         :arg (my-simpadd0-expr expr.arg)
                         :name expr.name)
              :complit (make-expr-complit
                         :type (my-simpadd0-tyname expr.type)
                         :elems (my-simpadd0-desiniter-list expr.elems)
                         :final-comma expr.final-comma)
              :unary (make-expr-unary
                       :op expr.op
                       :arg (my-simpadd0-expr expr.arg))
              :sizeof (expr-sizeof (my-simpadd0-tyname expr.type))
              :sizeof-ambig (prog2$
                              (raise "Misusage error: ~x0." (expr-fix expr))
                              (expr-fix expr))
              :alignof (make-expr-alignof :type (my-simpadd0-tyname expr.type)
                                          :uscores expr.uscores)
              :cast (make-expr-cast
                      :type (my-simpadd0-tyname expr.type)
                      :arg (my-simpadd0-expr expr.arg))
              :binary (b* ((arg1 (my-simpadd0-expr expr.arg1))
                           (arg2 (my-simpadd0-expr expr.arg2)))
                        ;; zero-folding occurs here
                        (if (c$::expr-zerop arg2)
                            arg1
                          (make-expr-binary
                            :op expr.op
                            :arg1 arg1
                            :arg2 arg2
                            :info expr.info)))
              :cond (make-expr-cond
                      :test (my-simpadd0-expr expr.test)
                      :then (my-simpadd0-expr-option expr.then)
                      :else (my-simpadd0-expr expr.else))
              :comma (make-expr-comma
                       :first (my-simpadd0-expr expr.first)
                       :next (my-simpadd0-expr expr.next))
              :cast/call-ambig (prog2$
                                 (raise "Misusage error: ~x0." (expr-fix expr))
                                 (expr-fix expr))
              :cast/mul-ambig (prog2$
                                (raise "Misusage error: ~x0." (expr-fix expr))
                                (expr-fix expr))
              :cast/add-ambig (prog2$
                                (raise "Misusage error: ~x0." (expr-fix expr))
                                (expr-fix expr))
              :cast/sub-ambig (prog2$
                                (raise "Misusage error: ~x0." (expr-fix expr))
                                (expr-fix expr))
              :cast/and-ambig (prog2$
                                (raise "Misusage error: ~x0." (expr-fix expr))
                                (expr-fix expr))
              :stmt (expr-stmt (my-simpadd0-block-item-list expr.items))
              :tycompat (make-expr-tycompat
                          :type1 (my-simpadd0-tyname expr.type1)
                          :type2 (my-simpadd0-tyname expr.type2))
              :offsetof (make-expr-offsetof
                          :type (my-simpadd0-tyname expr.type)
                          :member (my-simpadd0-member-designor expr.member))
              :va-arg (make-expr-va-arg
                        :list (my-simpadd0-expr expr.list)
                        :type (my-simpadd0-tyname expr.type))
              :extension (expr-extension (my-simpadd0-expr expr.expr)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (c$::input-files :files ("test1.c")
                   :const *old*)

  (defconst *new*
    (my-simpadd0-transunit-ensemble *old*))

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "int main() {
  int x = 5;
  return x;
}
")

  :with-output-off nil)
