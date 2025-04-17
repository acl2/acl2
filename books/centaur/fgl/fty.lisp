;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(in-package "FTY")

(include-book "def-fgl-rewrite")
(include-book "centaur/fty/database" :dir :system)


(defxdoc fgl-fty-support
  :parents (fgl::fgl)
  :short "Utilities for supporting @(see fty) types in <see topic=\"@(url fgl::fgl)\">fgl</see>.")

(program)

#!fgl
(defmacro check-might-be-true (free-var x)
  ;; this returns t when x is not syntactically always false, i.e. syntactically seems to sometimes be true
  `(not (check-true ,free-var (not ,x))))


(defun fgl-fty-field-thms (fields prod sum wrld)
  (if (atom fields)
      nil
    (b* (((flexprod-field f) (car fields))
         ((flexprod prod))
         ((flexsum sum)))
      (list* (intern-in-package-of-symbol
              (concatenate 'string (symbol-name f.acc-name) "-OF-" (symbol-name prod.ctor-name))
              f.acc-name)
             (intern-in-package-of-symbol
              (concatenate 'string (symbol-name (acl2::deref-macro-name f.acc-name (macro-aliases wrld)))
                           "-OF-" (symbol-name sum.fix) "-" (symbol-name sum.xvar))
              f.acc-name)
             (fgl-fty-field-thms (cdr fields) prod sum wrld)))))


(define fgl-fty-rules-for-product (prod
                                   sum
                                   wrld)
  (b* (((fty::flexprod prod))
       ((fty::flexsum sum))
       (disable (cons prod.ctor-name
                      (flexprod-fields->acc-names prod.fields)))
       (enable (append (fgl-fty-field-thms prod.fields prod sum wrld)
                       (list
                        ;; Return type (pred of constructor) theorem
                        (if (eq prod.guard t)
                            (intern-in-package-of-symbol
                             (concatenate 'string (symbol-name sum.pred) "-OF-" (symbol-name prod.ctor-name))
                             prod.ctor-name)
                          (intern-in-package-of-symbol
                           (concatenate 'string "RETURN-TYPE-OF-" (symbol-name prod.ctor-name))
                           prod.ctor-name))
                        ;; equal of constructor
                        (intern-in-package-of-symbol
                         (concatenate 'string "EQUAL-OF-" (symbol-name prod.ctor-name))
                         prod.ctor-name)))))
    (mv disable enable)))


(define fgl-fty-rules-for-products (prods sum wrld)
  (b* (((when (atom prods)) (mv nil nil))
       ((mv disable1 enable1) (fgl-fty-rules-for-product (car prods) sum wrld))
       ((mv disable2 enable2) (fgl-fty-rules-for-products (cdr prods) sum wrld)))
    (mv (append disable1 disable2)
        (append enable1 enable2))))


(define fgl-fty-rules-for-sum (sum wrld)
  (b* (((flexsum sum))
       ((mv prod-disables prod-enables)
        (fgl-fty-rules-for-products sum.prods sum wrld))
       (disables (append (and sum.kind (list sum.kind))
                         (list* sum.fix
                                sum.pred
                                prod-disables)))
       (enables (append (and sum.kind
                             ;; sum-kind-of-sum-fix
                             (list (intern-in-package-of-symbol
                                    (concatenate 'string
                                                 (symbol-name (acl2::deref-macro-name sum.kind (macro-aliases wrld)))
                                                 "-OF-" (symbol-name sum.fix) "-" (symbol-name sum.xvar))
                                    sum.kind)))
                        (list*
                         (b* ((pred-of-fix
                               ;; BAD -- sometimes the theorem is called foo-pred-of-foo-fix,
                               ;; but sometimes return-type-of-foo-fix.new-x
                               (intern-in-package-of-symbol
                                (concatenate 'string (symbol-name sum.pred) "-OF-" (symbol-name sum.fix))
                                sum.fix))
                              ((when (fgetprop pred-of-fix 'acl2::classes nil wrld))
                               pred-of-fix))
                           (intern-in-package-of-symbol
                            (concatenate 'string "RETURN-TYPE-OF-" (symbol-name sum.fix) ".NEW-" (symbol-name sum.xvar))
                            sum.fix))
                         (intern-in-package-of-symbol
                          (concatenate 'string (symbol-name sum.fix) "-WHEN-" (symbol-name sum.pred))
                          sum.fix)
                         prod-enables))))
    (mv disables enables)))


(define add/remove-fgl-rules-for-fty-sum-fn (sumname wrld)
  (b* (((mv & sum) (search-deftypes-table sumname (get-flextypes wrld)))
       ((mv disables enables) (fgl-fty-rules-for-sum sum wrld)))
    `(progn (fgl::remove-fgl-rewrites . ,disables)
            (fgl::add-fgl-rewrites . ,enables))))

(defmacro add/remove-fgl-rules-for-fty-sum (sumname)
  `(make-event (add/remove-fgl-rules-for-fty-sum-fn ',sumname (w state))))


(defxdoc add/remove-fgl-rules-for-fty-sum
  :parents (fgl-fty-support)
  :short "Utility that updates the FGL rewriting theory to support an FTY sum or product type,
removing definitions and adding supporting rewrite rules."
  :long "
<p>Usage:</p>
 @({
  (fty::add/remove-fgl-rules-for-fty-sum sumname)
 })
<p>where @('sumname') is the name of the sum or product type.</p>")


(define fty-prods-find-by-kind (kind prods)
  (if (atom prods)
      nil
    (if (eq kind (flexprod->kind (car prods)))
        (car prods)
      (fty-prods-find-by-kind kind (cdr prods)))))

(define fgl-fty-sum-default-prod-tree (prods)
  (if (atom (cdr prods))
      (flexprod->kind (car prods))
    (cons (flexprod->kind (car prods))
          (fgl-fty-sum-default-prod-tree (cdr prods)))))


(def-primitive-aggregate fgl-fty-splitter-branch
  (varname
   true-branch ;; either a fgl-fty-splitter-branch or a fgl-fty-splitter-leaf
   false-branch)
  :tag :branch)

(def-primitive-aggregate fgl-fty-splitter-leaf
  (prod ;; flexprod
   field-vars
   field-merges)
  :tag :leaf)


(define fgl-fty-find-field-merge-entry (prod-kind field field-merges)
  (if (atom field-merges)
      nil
    (b* ((entry (car field-merges)))
      (cond ((eq (car entry) field) (cadr entry))
            ((and (eq (car entry) prod-kind)
                  (eq (cadr entry) field))
             (caddr entry))
            (t (fgl-fty-find-field-merge-entry prod-kind field (cdr field-merges)))))))

(define fgl-fty-prod-field-merges (fields prod-kind field-merges)
  (if (atom fields)
      nil
    (cons (fgl-fty-find-field-merge-entry prod-kind (flexprod-field->name (car fields)) field-merges)
          (fgl-fty-prod-field-merges (cdr fields) prod-kind field-merges))))


(define fgl-fty-prod-tree-or-of-names (tree)
  (if (atom tree)
      (symbol-name tree)
    (concatenate 'string (fgl-fty-prod-tree-or-of-names (car tree))
                 "-OR-"
                 (fgl-fty-prod-tree-or-of-names (cdr tree)))))

(define fgl-fty-sum-elaborate-prod-tree (tree sum field-merges)
  (if (atom tree)
      (let ((prod (fty-prods-find-by-kind tree (flexsum->prods sum))))
        (if prod
            (b* (((flexprod prod)))
              (make-fgl-fty-splitter-leaf
               :prod prod
               :field-merges (fgl-fty-prod-field-merges prod.fields prod.kind field-merges)))
          (raise "Couldn't find product ~x0" tree)))
    (let ((varname (intern-in-package-of-symbol
                    (concatenate 'string "IS-" (fgl-fty-prod-tree-or-of-names (car tree)))
                    (flexsum->name sum))))
      (make-fgl-fty-splitter-branch
       :varname varname
       :true-branch (fgl-fty-sum-elaborate-prod-tree (car tree) sum field-merges)
       :false-branch (fgl-fty-sum-elaborate-prod-tree (cdr tree) sum field-merges)))))



(define fgl-fty-splitter-tree-varnames (tree)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree)))
               (cons tree.varname (append (fgl-fty-splitter-tree-varnames tree.true-branch)
                                          (fgl-fty-splitter-tree-varnames tree.false-branch)))))
    (t (b* (((fgl-fty-splitter-leaf tree)))
         tree.field-vars))))

(define fgl-splitter-tree-compute-varnames (tree varnames-acc)
  ;; returns (mv new-tree varnames-acc)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree))
                  (varname (acl2::new-symbol tree.varname varnames-acc))
                  (varnames-acc (cons varname varnames-acc))
                  ((mv new-true varnames-acc)
                   (fgl-splitter-tree-compute-varnames tree.true-branch varnames-acc))
                  ((mv new-false varnames-acc)
                   (fgl-splitter-tree-compute-varnames tree.false-branch varnames-acc)))
               (mv (make-fgl-fty-splitter-branch
                    :varname varname
                    :true-branch new-true
                    :false-branch new-false)
                   varnames-acc)))
    (t (b* (((fgl-fty-splitter-leaf tree))
            ((flexprod tree.prod))
            (vars (acl2::new-symbols (flexprod-fields->names tree.prod.fields) varnames-acc))
            (varnames-acc (append vars varnames-acc)))
         (mv (change-fgl-fty-splitter-leaf
              tree :field-vars vars)
             varnames-acc)))))

(define fgl-fty-splitter-tree-function-body (tree)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree)))
               `(if ,tree.varname
                    ,(fgl-fty-splitter-tree-function-body tree.true-branch)
                  ,(fgl-fty-splitter-tree-function-body tree.false-branch))))
    (t (b* (((fgl-fty-splitter-leaf tree))
            ((flexprod prod) tree.prod))
         `(,prod.ctor-name . ,tree.field-vars)))))

(define fgl-fty-splitter-tree-kind-expr (tree)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree)))
               `(if ,tree.varname
                    ,(fgl-fty-splitter-tree-kind-expr tree.true-branch)
                  ,(fgl-fty-splitter-tree-kind-expr tree.false-branch))))
    (t (b* (((fgl-fty-splitter-leaf tree))
            ((flexprod prod) tree.prod))
         prod.kind))))

(define fgl-fty-splitter-tree-prod-fields-accessor-thm (pathcond field field-var splitter-call)
  (b* (((flexprod-field field)))
    `(fgl::def-fgl-rewrite ,(intern-in-package-of-symbol
                             (concatenate 'string (symbol-name field.acc-name)
                                          "-OF-" (symbol-name (car splitter-call)))
                             (car splitter-call))
       (equal (,field.acc-name ,splitter-call)
              ,(if field.fix
                   `(if (and . ,pathcond)
                        (,field.fix ,field-var)
                      (,field.fix nil))
                 `(and ,@pathcond ,field-var)))
       :hints(("Goal" :in-theory (enable ,(intern-in-package-of-symbol
                                           (concatenate 'string (symbol-name field.acc-name)
                                                        "-WHEN-WRONG-KIND")
                                           field.acc-name)))))))

(define fgl-fty-splitter-tree-prod-fields-accessor-thms (pathcond fields field-vars splitter-call)
  (if (atom fields)
      nil
    (cons (fgl-fty-splitter-tree-prod-fields-accessor-thm pathcond (car fields) (car field-vars) splitter-call)
          (fgl-fty-splitter-tree-prod-fields-accessor-thms pathcond (cdr fields) (cdr field-vars) splitter-call))))


(define fgl-fty-splitter-tree-accessor-thms (pathcond tree splitter-call)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree)))
               (append (fgl-fty-splitter-tree-accessor-thms
                        (append pathcond (list tree.varname))
                        tree.true-branch splitter-call)
                       (fgl-fty-splitter-tree-accessor-thms
                        (append pathcond (list `(not ,tree.varname)))
                        tree.false-branch splitter-call))))
    (t (b* (((fgl-fty-splitter-leaf tree))
            ((flexprod prod) tree.prod))
         (fgl-fty-splitter-tree-prod-fields-accessor-thms pathcond prod.fields tree.field-vars splitter-call)))))

(define suffix-symbol (varname suffix pkg)
  (intern-in-package-of-symbol (concatenate 'string (symbol-name varname) suffix) pkg))

(define suffix-symbols (varnames suffix pkg)
  (if (atom varnames)
      nil
    (cons (suffix-symbol (car varnames) suffix pkg)
          (suffix-symbols (cdr varnames) suffix pkg))))

(define fgl-fty-splitter-tree-suffix-varnames (tree suffix pkg)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree)))
               (make-fgl-fty-splitter-branch
                :varname (suffix-symbol tree.varname suffix pkg)
                :true-branch (fgl-fty-splitter-tree-suffix-varnames tree.true-branch suffix pkg)
                :false-branch (fgl-fty-splitter-tree-suffix-varnames tree.false-branch suffix pkg))))
    (t (b* (((fgl-fty-splitter-leaf tree)))
         (change-fgl-fty-splitter-leaf tree :field-vars (suffix-symbols tree.field-vars suffix pkg))))))


(define fgl-fty-splitter-can-be-true/false-bindings (pathcond tree pkg)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree))
                  (can-be-true (suffix-symbol tree.varname "-CAN-BE-TRUE" pkg))
                  (can-be-false (suffix-symbol tree.varname "-CAN-BE-FALSE" pkg)))
               (append `((,can-be-true
                          (fgl::check-might-be-true ,can-be-true
                                                    (and ,@pathcond ,tree.varname t)))
                         (,can-be-false
                          (fgl::check-might-be-true ,can-be-false
                                                    (and ,@pathcond (not ,tree.varname) t))))
                       (fgl-fty-splitter-can-be-true/false-bindings (append pathcond (list tree.varname)) tree.true-branch pkg)
                       (fgl-fty-splitter-can-be-true/false-bindings (append pathcond `((not ,tree.varname))) tree.false-branch pkg))))
    (t nil)))


(define fgl-fty-merge-field-arg (then-last-test else-last-test var1 var2 merge)
  (b* (((flexprod-field field)))
    `(if ,then-last-test
         (if ,else-last-test
             (,(or merge 'if) test ,var1 ,var2)
           ,var1)
       (if ,else-last-test
           ,var2
         nil))))

(define fgl-fty-merge-field-args (then-last-test else-last-test vars1 vars2 merges)
  (if (atom vars1)
      nil
    (cons (fgl-fty-merge-field-arg then-last-test else-last-test (car vars1) (car vars2) (car merges))
          (fgl-fty-merge-field-args then-last-test else-last-test (cdr vars1) (cdr vars2) (cdr merges)))))
  

(define fgl-fty-splitter-merge-args (then-last-test else-last-test tree-1 tree-2 pkg)
  (case (tag tree-1)
    (:branch (b* (((fgl-fty-splitter-branch tree-1))
                  ((fgl-fty-splitter-branch tree-2)))
               (cons (if then-last-test
                         `(if ,then-last-test
                              (if ,else-last-test
                                  (if test ,tree-1.varname ,tree-2.varname)
                                ,tree-1.varname)
                            (if ,else-last-test
                                ,tree-2.varname
                              nil))
                       `(if test ,tree-1.varname ,tree-2.varname))
                     (append
                      (fgl-fty-splitter-merge-args (suffix-symbol tree-1.varname "-CAN-BE-TRUE" pkg)
                                                   (suffix-symbol tree-2.varname "-CAN-BE-TRUE" pkg)
                                                   tree-1.true-branch tree-2.true-branch pkg)
                      (fgl-fty-splitter-merge-args (suffix-symbol tree-1.varname "-CAN-BE-FALSE" pkg)
                                                   (suffix-symbol tree-2.varname "-CAN-BE-FALSE" pkg)
                                                   tree-1.false-branch tree-2.false-branch pkg)))))
    (t (b* (((fgl-fty-splitter-leaf tree-1))
            ((fgl-fty-splitter-leaf tree-2)))
         (fgl-fty-merge-field-args then-last-test else-last-test tree-1.field-vars tree-2.field-vars tree-1.field-merges)))))

(define fgl-fty-splitter-subtree-has-kind (kind tree)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree)))
               (or (fgl-fty-splitter-subtree-has-kind kind tree.true-branch)
                   (fgl-fty-splitter-subtree-has-kind kind tree.false-branch))))
    (t (b* (((fgl-fty-splitter-leaf tree))
            ((flexprod prod) tree.prod))
         (and (eq prod.kind kind) tree)))))

(define fgl-fty-splitter-args-for-var-of-kind (kind tree xvar)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree))
                  (true-branch (fgl-fty-splitter-subtree-has-kind kind tree.true-branch)))
               (cons (and true-branch t)
                     (append
                      (fgl-fty-splitter-args-for-var-of-kind kind tree.true-branch xvar)
                      (fgl-fty-splitter-args-for-var-of-kind kind tree.false-branch xvar)))))
    (t (b* (((fgl-fty-splitter-leaf tree))
            ((flexprod prod) tree.prod))
         (if (eq prod.kind kind)
             (flexprod-fields-acc-calls prod.fields xvar)
           (make-list (len tree.field-vars) :initial-element nil))))))

(define fgl-fty-splitter-tree-merge-splitter-with-kind-thms (if-name sum tree subtree splitter-name)
  (case (tag subtree)
    (:branch (b* (((fgl-fty-splitter-branch subtree)))
               (append (fgl-fty-splitter-tree-merge-splitter-with-kind-thms if-name sum tree subtree.true-branch splitter-name)
                       (fgl-fty-splitter-tree-merge-splitter-with-kind-thms if-name sum tree subtree.false-branch splitter-name))))
    (t (b* (((fgl-fty-splitter-leaf subtree))
            ((flexsum sum))
            ((flexprod prod) subtree.prod)
            (varnames (fgl-fty-splitter-tree-varnames tree)))
         `((fgl::def-fgl-branch-merge ,(intern-in-package-of-symbol
                                        (concatenate 'string "IF-OF-" (symbol-name splitter-name) "-WITH-" (symbol-name prod.kind))
                                        splitter-name)
             (implies (and (equal (,sum.kind ,sum.xvar) ,prod.kind)
                           (,sum.pred ,sum.xvar))
                      (equal (if test (,splitter-name . ,varnames) ,sum.xvar)
                             (,if-name test (,splitter-name . ,varnames)
                                       (,splitter-name . ,(fgl-fty-splitter-args-for-var-of-kind prod.kind tree sum.xvar)))))))))))

(define fgl-fty-splitter-self-merge-args (fields field-merges xvar)
  (if (atom fields)
      nil
    (b* (((flexprod-field field) (car fields)))
      (cons `(,(or (car field-merges) 'if) test ,field.name (,field.acc-name ,xvar))
            (fgl-fty-splitter-self-merge-args (Cdr fields) (cdr field-merges) xvar)))))

(define fgl-fty-splitter-ctor-kind-merge-args (tree kind1 kind2 xvar)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree))
                  (kind1-in-truebr (fgl-fty-splitter-subtree-has-kind kind1 tree.true-branch))
                  (kind1-in-falsebr (fgl-fty-splitter-subtree-has-kind kind1 tree.false-branch))
                  (kind2-in-truebr (fgl-fty-splitter-subtree-has-kind kind2 tree.true-branch))
                  (kind2-in-falsebr (fgl-fty-splitter-subtree-has-kind kind2 tree.false-branch))
                  (arg (if kind1-in-truebr
                           (if kind2-in-truebr
                               t
                             (if kind2-in-falsebr
                                 'test
                               t))
                         (if kind2-in-truebr
                             (if kind1-in-falsebr
                                 '(not test)
                               t)
                           nil))))
               (cons arg
                     (append (fgl-fty-splitter-ctor-kind-merge-args tree.true-branch kind1 kind2 xvar)
                             (fgl-fty-splitter-ctor-kind-merge-args tree.false-branch kind1 kind2 xvar)))))
    (t (b* (((fgl-fty-splitter-leaf tree))
            ((flexprod prod) tree.prod))
         (cond ((eq prod.kind kind1) (flexprod-fields->names prod.fields))
               ((eq prod.kind kind2) (flexprod-fields-acc-calls prod.fields xvar))
               (t (make-list (len prod.fields) :initial-element nil)))))))
  

(define fgl-fty-splitter-tree-merge-ctor-with-kind-thms (sum prod field-merges tree subtree splitter-name)
  (case (tag subtree)
    (:branch (b* (((fgl-fty-splitter-branch subtree)))
               (append (fgl-fty-splitter-tree-merge-ctor-with-kind-thms sum prod field-merges tree subtree.true-branch splitter-name)
                       (fgl-fty-splitter-tree-merge-ctor-with-kind-thms sum prod field-merges tree subtree.false-branch splitter-name))))
    (t (b* (((fgl-fty-splitter-leaf subtree))
            ((flexsum sum))
            ((flexprod prod2) subtree.prod)
            ((flexprod prod) prod))
         `((fgl::def-fgl-branch-merge ,(intern-in-package-of-symbol
                                        (concatenate 'string "IF-OF-" (symbol-name prod.kind) "-WITH-" (symbol-name prod2.kind))
                                        splitter-name)
             (implies (and (equal (,sum.kind ,sum.xvar) ,prod2.kind)
                           (,sum.pred ,sum.xvar))
                      (equal (if test (,prod.ctor-name . ,(flexprod-fields->names prod.fields)) ,sum.xvar)
                             ,(if (eq prod2.kind prod.kind)
                                  `(,prod.ctor-name . ,(fgl-fty-splitter-self-merge-args prod.fields field-merges sum.xvar))
                                `(,splitter-name . ,(fgl-fty-splitter-ctor-kind-merge-args tree prod.kind prod2.kind sum.xvar)))))))))))

(define fgl-fty-splitter-tree-merge-ctors-with-kind-thms (sum tree subtree splitter-name)
  (case (tag subtree)
    (:branch (b* (((fgl-fty-splitter-branch subtree)))
               (append (fgl-fty-splitter-tree-merge-ctors-with-kind-thms sum tree subtree.true-branch splitter-name)
                       (fgl-fty-splitter-tree-merge-ctors-with-kind-thms sum tree subtree.false-branch splitter-name))))
    (t (b* (((fgl-fty-splitter-leaf subtree)))
         (fgl-fty-splitter-tree-merge-ctor-with-kind-thms sum subtree.prod subtree.field-merges tree tree splitter-name)))))

(define fgl-fty-dotted-field-vars (var fields pkg)
  (if (atom fields)
      nil
    (cons (intern-in-package-of-symbol
           (concatenate 'string (symbol-name var) "." (symbol-name (flexprod-field->name (car fields))))
           pkg)
          (fgl-fty-dotted-field-vars var (cdr fields) pkg))))
  
(define fgl-fty-merge-constants-splitter-args (xkind ykind tree pkg)
  (case (tag tree)
    (:branch (b* (((fgl-fty-splitter-branch tree))
                  (x-truebr (fgl-fty-splitter-subtree-has-kind xkind tree.true-branch))
                  (x-falsebr (fgl-fty-splitter-subtree-has-kind xkind tree.false-branch))
                  (y-truebr (fgl-fty-splitter-subtree-has-kind ykind tree.true-branch))
                  (y-falsebr (fgl-fty-splitter-subtree-has-kind ykind tree.false-branch))
                  (test (if x-truebr
                            (if y-truebr
                                t
                              (if y-falsebr
                                  'test
                                t))
                          (if y-truebr
                              (if x-falsebr
                                  '(not test)
                                t)
                            nil))))
               (cons test
                     (append (fgl-fty-merge-constants-splitter-args xkind ykind tree.true-branch pkg)
                             (fgl-fty-merge-constants-splitter-args xkind ykind tree.false-branch pkg)))))
    (t (b* (((fgl-fty-splitter-leaf tree))
            ((flexprod prod) tree.prod))
         (cond ((eq xkind prod.kind)
                (fgl-fty-dotted-field-vars 'x prod.fields pkg))
               ((eq ykind prod.kind)
                (fgl-fty-dotted-field-vars 'y prod.fields pkg))
               (t (make-list (len prod.fields) :initial-element nil)))))))

(define fgl-fty-merge-prod-args (fields merges pkg)
  (if (atom fields)
      nil
    (cons `(,(or (car merges) 'if)
            test
            ,(intern-in-package-of-symbol
              (concatenate 'string "X." (symbol-name (flexprod-field->name (car fields))))
              pkg)
            ,(intern-in-package-of-symbol
              (concatenate 'string "Y." (symbol-name (flexprod-field->name (car fields))))
              pkg))
          (fgl-fty-merge-prod-args (cdr fields) (cdr merges) pkg))))

(define fgl-fty-merge-constants-body-prods2 (xkind prods tree splitter-name)
  (if (atom prods)
      nil
    (b* (((flexprod prod) (car prods)))
      `(,prod.kind
        ,(if (eq xkind prod.kind)
             (b* ((subtree (fgl-fty-splitter-subtree-has-kind xkind tree))
                  (merges (fgl-fty-splitter-leaf->field-merges subtree)))
               `(,prod.ctor-name . ,(fgl-fty-merge-prod-args prod.fields merges splitter-name)))
           `(,splitter-name
             . ,(fgl-fty-merge-constants-splitter-args xkind prod.kind tree splitter-name)))
        . ,(fgl-fty-merge-constants-body-prods2 xkind (cdr prods) tree splitter-name)))))
                   
                                                                      
                                                                      

(define fgl-fty-merge-constants-body-prods1 (casemacro prods all-prods tree splitter-name)
  (if (atom prods)
      nil
    (b* (((flexprod prod) (car prods)))
      `(,prod.kind
        (,casemacro y . ,(fgl-fty-merge-constants-body-prods2 prod.kind all-prods tree splitter-name))
        . ,(fgl-fty-merge-constants-body-prods1 casemacro (cdr prods) all-prods tree splitter-name)))))
                          

(define fgl-fty-merge-constants-body (casemacro prods tree splitter-name)
  `(,casemacro x
     . ,(fgl-fty-merge-constants-body-prods1 casemacro prods prods tree splitter-name)))




(define fgl-fty-sum-splitter (splitter-name
                              prod-tree ;; Cons tree whose leaves are kind symbols of the products, describing how the cases are split.
                                        ;; Can be nil, in which case it defaults to (:kind1 :kind2 ... :kindn-1 . :kindn)
                              field-merges ;; Elements of the form (prod-kind field-name merge-function) or just (field-name merge-function).
                              hints ;; for the main splitter merge theorem
                              sum)
  (b* (((flexsum sum))
       (base-tree (or prod-tree (fgl-fty-sum-default-prod-tree sum.prods)))
       (elab-tree (fgl-fty-sum-elaborate-prod-tree base-tree sum field-merges))
       ((mv tree &) (fgl-splitter-tree-compute-varnames elab-tree nil))
       (vars (fgl-fty-splitter-tree-varnames tree))
       (splitter-call `(,splitter-name . ,vars))
       (if-name (intern-in-package-of-symbol
                 (concatenate 'string "IF-FOR-" (symbol-name splitter-name))
                 splitter-name))
       (tree-1 (fgl-fty-splitter-tree-suffix-varnames tree "-1" splitter-name))
       (tree-2 (fgl-fty-splitter-tree-suffix-varnames tree "-2" splitter-name))
       (varnames-1 (fgl-fty-splitter-tree-varnames tree-1))
       (varnames-2 (fgl-fty-splitter-tree-varnames tree-2)))
    `(define ,splitter-name ,vars
       :verify-guards nil
       :returns split
       ,(fgl-fty-splitter-tree-function-body tree)
       ///
       (fgl::def-fgl-rewrite ,(intern-in-package-of-symbol
                               (concatenate 'string (symbol-name sum.pred)
                                            "-OF-" (symbol-name splitter-name))
                               splitter-name)
         (,sum.pred ,splitter-call))

       (fgl::def-fgl-rewrite ,(intern-in-package-of-symbol
                               (concatenate 'string (symbol-name sum.kind)
                                            "-OF-" (symbol-name splitter-name))
                               splitter-name)
         (equal (,sum.kind ,splitter-call)
                ,(fgl-fty-splitter-tree-kind-expr tree)))

       ,@(fgl-fty-splitter-tree-accessor-thms nil tree splitter-call)

       (defun ,if-name (x y z)
         (if x y z))
       (fgl::remove-fgl-rewrite ,if-name)

       (fgl::def-fgl-rewrite ,(intern-in-package-of-symbol
                               (concatenate 'string (symbol-name if-name) "-OF-" (symbol-name splitter-name))
                               splitter-name)
         (equal (,if-name test
                          (,splitter-name . ,varnames-1)
                          (,splitter-name . ,varnames-2))
                (b* (,@(fgl-fty-splitter-can-be-true/false-bindings '(test) tree-1 splitter-name)
                     ,@(fgl-fty-splitter-can-be-true/false-bindings '((not test)) tree-2 splitter-name))
                  (,splitter-name . ,(fgl-fty-splitter-merge-args nil nil tree-1 tree-2 splitter-name))))
         :hints ,hints)

       (fgl::def-fgl-branch-merge ,(intern-in-package-of-symbol
                                    (concatenate 'string "IF-OF-" (symbol-name splitter-name))
                                    splitter-name)
         (equal (if test (,splitter-name . ,varnames-1) (,splitter-name . ,varnames-2))
                (,if-name test
                          (,splitter-name . ,varnames-1)
                          (,splitter-name . ,varnames-2))))
       

       ,@(fgl-fty-splitter-tree-merge-splitter-with-kind-thms if-name sum tree tree splitter-name)
    
       ,@(fgl-fty-splitter-tree-merge-ctors-with-kind-thms sum tree tree splitter-name)

       (fgl::def-fgl-branch-merge ,(intern-in-package-of-symbol
                                    (concatenate 'string "IF-OF-" (symbol-name sum.name) "-CONSTANTS")
                                    sum.name)
         (implies (and (,sum.pred x)
                       (,sum.pred y))
                  (equal (if test (fgl::concrete x) (fgl::concrete y))
                         ,(fgl-fty-merge-constants-body
                           sum.case sum.prods tree splitter-name))))

       (fgl::remove-fgl-rewrite ,splitter-name)
       (fgl::disable-execution ,splitter-name))))


(define def-fgl-fty-sum-splitter-fn (splitter-name sumname args wrld)
  (b* (((std::extract-keyword-args
         :other-args bad-args
         prod-tree
         field-merges
         hints)
        args)
       (- (and bad-args (raise "Bad arguments: ~x0" bad-args)))
       ((mv & sum) (search-deftypes-table sumname (get-flextypes wrld))))
    (fgl-fty-sum-splitter splitter-name
                          prod-tree
                          field-merges
                          hints
                          sum)))

(defmacro def-fgl-fty-sum-splitter (splitter-name sumname &rest args)
  `(make-event (def-fgl-fty-sum-splitter-fn ',splitter-name ',sumname ',args (w state))))
                                          

(defxdoc def-fgl-fty-sum-splitter
  :parents (fgl-fty-support)
  :short "Add a representation for the FGL rewriter that can symbolically represent an
element of a sum type, even if that element might be of different kinds under
different conditions."
  :long "
<p>Background: Typical use of FGL aims to do a single rewriting pass through a
term, hopefully without repeatedly re-evaluating subterms due to case
splits. The way to manage this is to use a symbolic representation that covers
the different values that a given subterm can take.  FGL natively offers
bit-level symbolic Boolean and integer representations, but doesn't
automatically know how to merge the various different forms that a terms can
take in general. FTY sum types can pose a problem in this respect. For example,
suppose FOO is a sum type that has two constructors (products) BAR and BAZ,
where BAR takes an integer and BAZ takes a Boolean. If a term computes an
object of type FOO that is sometimes of type BAR and sometimes of type BAZ, FGL
needs special instructions to deal with this effectively. This macro aims to
provide a good solution to this.</p>

<p>Usage:</p>
@({
 (fty::def-fgl-fty-sum-splitter name-for-splitter sumname

    ;; optional: cons tree representing the decision tree among the member
    ;; products -- using the member products' kind keywords
    :prod-tree ((:kind1 . :fourth-kind) :second-kind . :kind3)

    ;; optional: directs certain fields to be merged using a function other
    ;; than IF (but equivalent).  Usual use case is to specify fgl::if!, which
    ;; makes any of the specified fields just \"merge\" by creating an IF term
    ;; rather than trying to symbolically represent the contents of both.
    :field-merges ((:second-kind some-field fgl::if!)             ;; specify both the kind and the field
                   (another-field my-particular-if-equivalent))   ;; specify just the field, if it's uniquely named

    ;; Hints to prove the main theorem that merges representations -- usually not needed
    :hints ...)
 })

<p>Here @('name-for-splitter') is the name for the new function representing a
symbolic object of the sum type, and @('sumname') is the name of the FTY sum
type.</p>

")
