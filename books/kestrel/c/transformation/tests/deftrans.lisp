; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../deftrans")

(include-book "../../syntax/parser")
(include-book "../../syntax/printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generates the identify transformation
(deftrans identity-trans)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftrans my-simpadd0
  :expr (lambda (expr)
       (expr-case
            expr
            :ident (expr-fix expr)
            :const (expr-fix expr)
            :string (expr-fix expr)
            :paren (expr-paren (my-simpadd0-expr expr.unwrap))
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
                          :arg2 arg2)))
            :cond (make-expr-cond
                    :test (my-simpadd0-expr expr.test)
                    :then (my-simpadd0-expr expr.then)
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
                              (expr-fix expr)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filepath*
  (filepath "file.c"))

(defconst *old-filedata*
  (filedata
   (acl2::string=>nats
    "int main() {
  int x = 5;
  return x + 0;
}
")))

(defconst *old-fileset*
  (fileset
   (omap::update *old-filepath*
                 *old-filedata*
                 nil)))

(defconst *old-transunits*
  (b* (((mv erp transunits) (c$::parse-fileset *old-fileset* nil)))
    (if erp
        (cw "~@0" erp)
      transunits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *transunits-identity-trans*
  (identity-trans-transunit-ensemble *old-transunits*))

(defconst *fileset-identity-trans*
  (c$::print-fileset *transunits-identity-trans* (c$::default-priopt)))

(defconst *filepath-identity-trans*
  (filepath "file.IDENTITY-TRANS.c"))

(defconst *filedata-identity-trans*
  (omap::lookup *filepath-identity-trans*
                (fileset->unwrap *fileset-identity-trans*)))

(assert-event
 (equal
  (acl2::nats=>string
   (filedata->unwrap *filedata-identity-trans*))
  "int main() {
  int x = 5;
  return x + 0;
}
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *transunits-my-simpadd0*
  (my-simpadd0-transunit-ensemble *old-transunits*))

(defconst *fileset-my-simpadd0*
  (c$::print-fileset *transunits-my-simpadd0* (c$::default-priopt)))

(defconst *filepath-my-simpadd0*
  (filepath "file.MY-SIMPADD0.c"))

(defconst *filedata-my-simpadd0*
  (omap::lookup *filepath-my-simpadd0*
                (fileset->unwrap *fileset-my-simpadd0*)))

(assert-event
 (equal
  (acl2::nats=>string
   (filedata->unwrap *filedata-my-simpadd0*))
  "int main() {
  int x = 5;
  return x;
}
"))
