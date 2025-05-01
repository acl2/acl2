;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(in-package :z3)
(solver-init)

(defun convert-ast-to-list (ast &optional context)
  (let ((ctx (or context *default-context*)))
    (if (not (equal (z3-get-ast-kind ctx ast) :APP_AST))
        (ast-to-value ast ctx)
        (let* ((decl (z3-get-app-decl ctx ast))
               (decl-kind (z3-get-decl-kind ctx decl)))
          (match decl-kind
              (:OP_UNINTERPRETED
               (if (zerop (z3-get-app-num-args ctx ast))
                   (list :VAR (intern (z3-get-symbol-string ctx (z3-get-decl-name ctx (z3-get-app-decl ctx ast)))))
                   (error "unsupported uninterpreted function application")))
            (:OP_INTERNAL
             (ast-to-value ast ctx))
            (otherwise
             (cons (z3-get-decl-kind ctx (z3-get-app-decl ctx ast))
                   (loop for i below (z3-get-app-num-args ctx ast)
                         for arg = (z3-get-app-arg ctx ast i)
                         collect (convert-ast-to-list arg ctx)))))))))
;; replace ... with whatever you want your package to be
;;(in-package ...)
;;(import 'z3::convert-ast-to-list)

;; some examples

(convert-ast-to-list (convert-to-ast '(= 7 27)))

(convert-ast-to-list
 (convert-to-ast '(= (+ x (* 3 5)) (+ 1 2 3))
                 (fresh-env-from-spec (x :int))))

(convert-ast-to-list
 (convert-to-ast '(= (seq.++ "a" x "ba" x) (seq.++ y y "aba"))
                 (fresh-env-from-spec (x :string y :string))))
