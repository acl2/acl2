; Syntheto Library
;
; Translate acl2 to syntheto abstract syntax
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "abstract-syntax")
(include-book "static-semantics-types")
(include-book "std/strings/suffixp" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)

(define bad-syntheto-termp ((e expressionp))
  (equal (expression-kind e) ':bad-expression))
(define bad-syntheto-term (e)
  :returns (e expressionp)
  (expression-bad-expression e)
  ///
  (defthm bad-syntheto-termp-bad-syntheto-term
    (bad-syntheto-termp (bad-syntheto-term e))
    :hints (("Goal" :in-theory (enable bad-syntheto-termp))))
)

(define replace-var-types ((tvs typed-variable-listp) (tys type-listp))
  :returns (vs typed-variable-listp)
  (if (or (endp tvs)
          (endp tys))
      nil
    (cons (make-typed-variable
           :name (typed-variable->name (car tvs))
           :type (car tys))
          (replace-var-types (cdr tvs) (cdr tys)))))

;; This should be good enough for now
(define fixing-fn-p ((x symbolp))
  :returns (b booleanp)
  (str::strsuffixp "FIX" (symbol-name x)))

(define syntheto-type-predicate-symbolp (x)
  :returns (b booleanp)
  (and (symbolp x)
       (equal (symbol-package-name x)
              "SYNDEF")
       (str::strsuffixp "-P" (symbol-name x))))

(define syntheto-product-constructor (x (ctxt contextp))
  :returns (mv (str* (or (null str*) (identifierp str*)))
               (flds identifier-listp))
  (b* (((unless (and (symbolp x)
                     (equal (symbol-package-name x)
                            "SYNDEF")))
        (mv nil nil))
       (nm (symbol-name x))
       (id (make-identifier :name nm))
       (typedef (get-type-definition id (context->tops ctxt)))
       ((when (not typedef))
        (mv nil nil))
       (definer (type-definition->body typedef))
       ((when (not definer))
        (mv nil nil)))
    (type-definer-case definer
     :product (mv id (field-list->name-list (type-product->fields definer.get)))
     :sum (mv nil nil)
     :subset (mv nil nil))))

(define a-to-d-literal-expr ((e atom))
  :returns (new-e expressionp)
  (cond ((booleanp e)
         (expression-literal (literal-boolean e)))
        ((characterp e)
         (expression-literal (literal-character e)))
        ((stringp e)
         (expression-literal (literal-string e)))
        ((natp e)
         (expression-literal (literal-integer e)))
        ((integerp e)                   ; Must be negative!
         (expression-unary (unary-op-minus) (expression-literal (literal-integer (- e)))))
        (t (bad-syntheto-term e))))

(define built-in-poly-op ((fn symbolp))
  :returns (f (or (null f)
                  (identifierp f)))
  (case fn
    (endp (make-identifier :name "is_empty"))
    (car (make-identifier :name "first"))
    (first (make-identifier :name "first"))
    (acl2::last1 (make-identifier :name "last"))
    (cdr (make-identifier :name "rest"))
    (rest (make-identifier :name "rest"))
    (len (make-identifier :name "length"))
    (length (make-identifier :name "string_length"))
    (cons (make-identifier :name "add"))
    (append (make-identifier :name "append"))
    (set::insert (make-identifier :name "add")))
  ///
  (defthm identifierp-built-in-poly-op
    (implies (built-in-poly-op op)
             (identifierp (built-in-poly-op op)))))

(define binary-fn-op ((fn symbolp))
  :returns (b-op (or (null b-op)
                     (binary-opp b-op)))
  (case fn
    (equal (binary-op-eq))
    (s-equal (binary-op-eq))
    (s-notequal (binary-op-ne))
    (> (binary-op-gt))
    (>= (binary-op-ge))
    (< (binary-op-lt))
    (<= (binary-op-le))
    (and (binary-op-and))
    (or (binary-op-or))
    (implies (binary-op-implies))
    (implied (binary-op-implied))
    (iff (binary-op-iff))
    (+ (binary-op-add))
    (binary-+ (binary-op-add))
    (- (binary-op-sub))
    (* (binary-op-mul))
    (binary-* (binary-op-mul))
    (/ (binary-op-div))
    (REM (binary-op-rem)))
  ///
  (defthm binary-opp-of-a-to-d-expr     ; Don't know why this is necessary
    (implies (binary-fn-op fn)
             (binary-opp (binary-fn-op fn)))))

(define unary-fn-op ((fn symbolp))
  :returns (b-op (or (null b-op)
                     (unary-opp b-op)))
  (case fn
    (not (unary-op-not))
    (- (unary-op-minus)))
  ///
  (defthm unary-opp-of-a-to-d-expr     ; Don't know why this is necessary
    (implies (unary-fn-op fn)
             (unary-opp (unary-fn-op fn)))))

(define binder-listp (l)
  :returns (b booleanp)
  :enabled t
  (or (null l)
      (and (consp l)
           (consp (car l))
           (typed-variablep (caar l))
           (expressionp (cdar l))
           (binder-listp (cdr l)))))

(define make-binds ((d-binds binder-listp) (d-body expressionp))
  :returns (new-e expressionp :hyp (expressionp d-body))
  (if (endp d-binds)
      d-body
    (make-expression-bind
      :variables (list (caar d-binds))
      :value (cdar d-binds)
      :body (make-binds (cdr d-binds) d-body))))

(define let-bind-listp (l)
  :enabled t
  :returns (b booleanp)
  (or (null l)
      (and (consp l)
           (consp (car l))
           (symbolp (caar l))
           (consp (cdar l))
           (null (cddar l))
           (let-bind-listp (cdr l)))))

(define cond-clause-listp (l)
  :enabled t
  :returns (b booleanp)
  (or (null l)
      (and (consp l)
           (consp (car l))
           (consp (cdar l))
           (null (cddar l))
           (cond-clause-listp (cdr l)))))

(define filter-trivial-binders ((d-binds binder-listp))
  :returns (reduced-d-binds binder-listp :hyp :guard)
  (if (endp d-binds)
      ()
    (b* (((cons (cons tv bind-e) r-d-binds) d-binds)
         (r-reduced-d-binds (filter-trivial-binders r-d-binds)))
      (if (and (equal ':variable (expression-kind bind-e))
               (equal (expression-variable->name bind-e)
                      (typed-variable->name tv)))
          r-reduced-d-binds
        (cons (car d-binds)
              r-reduced-d-binds)))))

(local (in-theory (disable acl2::search-from-start)))

(define try-product-field-ref-function ((f-name stringp))
  :returns (mv (matches? booleanp)
               (type-name stringp :hyp :guard)
               (field-name stringp :hyp :guard))
  (let ((pos (search "->" f-name)))
    (if (and pos
             (> pos 0)
             (> (length f-name) (+ pos 2)))
        (mv t
            (subseq f-name 0 pos)
            (subseq f-name (+ pos 2) nil))
      (mv nil "" ""))))

(define lookup-typed-variable-list ((nm stringp) (tvl typed-variable-listp))
  :returns (tv maybe-typed-variablep)
  (if (endp tvl)
      nil
    (if (equal nm (identifier->name (typed-variable->name (car tvl))))
        (typed-variable-fix (car tvl))
      (lookup-typed-variable-list nm (cdr tvl)))))

;; Needed for termination of infer-types-from-expression
(defthm expression-if->then-decreases
  (implies (and (expressionp e)
                (equal (expression-kind e) :if))
           (< (acl2-count (expression-if->then e))
              (acl2-count e)))
  :hints (("Goal" :in-theory (enable expressionp expression-if->then expression-kind))))

(defthm expression-bind->body-decreases
  (implies (and (expressionp e)
                (equal (expression-kind e) :bind))
           (< (acl2-count (expression-bind->body e))
              (acl2-count e)))
  :hints (("Goal" :in-theory (enable expressionp expression-bind->body expression-kind))))

;; !! Todo: handle rest of the cases
(define infer-types-from-expression ((e expressionp) (locals typed-variable-listp) (ctxt contextp))
  :returns (ty type-listp)
  (if (mbt (expressionp e))
      (case (expression-kind e)
        (:literal (case (literal-kind (expression-literal->get e))
                    (:boolean (list (make-type-boolean)))
                    (:character (list (make-type-character)))
                    (:string (list (make-type-string)))
                    (:integer (list (make-type-integer)))))
        (:variable (let ((tv (lookup-typed-variable-list (identifier->name (expression-variable->name e))
                                                         locals)))
                     (if tv (list (typed-variable->type tv))
                       (list (make-type-defined :name (make-identifier :name "unknown"))))))
        (:call (b* (((expression-call call) e)
                    ((mv err? & outputs & &)
                     (get-function-in/out/pre/post call.function call.types ctxt))
                    ((when err?)
                     (list (make-type-defined :name (make-identifier :name "unknown")))))
                 (typed-variable-list->type-list outputs)))
        (:product-construct (list (make-type-defined :name (expression-product-construct->type e))))
        (:if (infer-types-from-expression (expression-if->then e)
                                          locals ctxt))
        (:binary
         (case (binary-op-kind (expression-binary->operator e))
           ((:eq :ne :gt :ge :lt :le :and :or :implies :implied :iff)
            (list (make-type-boolean)))
           ((:add :sub :mul :div :rem)
            (list (make-type-integer)))))
        (:bind
         (infer-types-from-expression (expression-bind->body e)
                                      (append (expression-bind->variables e) locals)
                                      ctxt))
        (otherwise (list (make-type-defined :name (make-identifier :name "unknown")))))
    (list (make-type-defined :name (make-identifier :name "shouldn't happen")))))

(defconst *expression-true-term*
  (expression-literal (literal-boolean t)))

(define expression-true-term-p ((e expressionp))
  (equal e *expression-true-term*))

(defconst *expression-false-term*
  (expression-literal (literal-boolean nil)))

(define expression-false-term-p ((e expressionp))
  (equal e *expression-false-term*))

(define predicate-must-be-true-p ((f symbolp))
  (or (member f '(integerp listp acl2::mbt acl2::mbt$))
      (syntheto-type-predicate-symbolp f)))

(defconst *identity-expressions*
  (list (cons (binary-op-and) *expression-true-term*)
        (cons (binary-op-or) *expression-false-term*)
        (cons (binary-op-add) (expression-literal (literal-integer 0)))
        (cons (binary-op-mul) (expression-literal (literal-integer 1)))))

(define remove-identity-elements ((args expression-listp) (id-exp expressionp))
  :returns (e expression-listp :hyp :guard)
  (if (endp args)
      ()
    (if (equal (car args) id-exp)
        (remove-identity-elements (cdr args) id-exp)
      (cons (car args)
            (remove-identity-elements (cdr args) id-exp)))))

(define expression-unreachable-termp (sexpr)
  (or (equal sexpr ':undefined)
      (member-equal sexpr
                    '((default-integer)
                      (default-nil)))))

(define nary-to-binary ((bin-op binary-opp) (args expression-listp) (id-exp expressionp))
  :returns (e expressionp :hyp :guard)
  (if (endp args)
      id-exp
    (if (endp (cdr args))
        (car args)
      (expression-binary bin-op (car args)
                         (nary-to-binary bin-op (cdr args) id-exp)))))

(defines a-to-d-expr-fns
  (define a-to-d-expr (e (locals typed-variable-listp) (ctxt contextp))
    :returns (new-e expressionp)
    (b* (((when (and (symbolp e)
                     (not (member e '(nil t)))))
          (expression-variable (make-identifier :name (symbol-name e))))
         ((when (atom e))
          (a-to-d-literal-expr e))
         ((cons f args) e)
         ((unless (true-listp args))
          (bad-syntheto-term e))
         ((unless (symbolp f))
          (bad-syntheto-term e))
         (f-name (symbol-name f))
         ((when (and (or (equal f 'let)
                         (equal f 'let*))
                     (= (len args) 2)
                     (let-bind-listp (first args))))
          (let ((d-body (a-to-d-expr (second args) locals ctxt))
                (d-binds (filter-trivial-binders (a-to-d-binders (first args) locals ctxt))))
            (if (null d-binds)
                d-body
              (make-binds d-binds d-body))))
         ;; ((when (equal f 'let*))
         ;;  (bad-syntheto-term e))
         ((when (and (eq f 'cond)       ; Better to avoid creating this!
                     (cond-clause-listp args))) 
          (a-to-d-cond-clauses args e locals ctxt))
         ;; ((when (prefixp "MAKE-" f-name))
         ;;  (make-expression-product-construct
         ;;   :type (make-identifier :name (subseq f-name 5 nil))
         ;;   :fields :field-name expr pairs))
         (new-args (a-to-d-exprs args locals ctxt))
         (len-args (len new-args))
         ((when (and (equal len-args 3)
                     (eq f 'if)))
          (if (or (expression-true-term-p (car new-args))
                  (expression-unreachable-termp (caddr args))) ; Condition must have been an mbt!
              (cadr new-args)
            (if (expression-false-term-p (car new-args))
                (caddr new-args)
              (expression-if (car new-args) (cadr new-args) (caddr new-args)))))
         ((when (and (equal len-args 1)
                     (or (fixing-fn-p f)
                         (eq f 'quote))))
          (car new-args))
         ((mv product-type-id field-ids)
          (syntheto-product-constructor f ctxt))
         ((when (and (identifierp product-type-id)
                     (= (len field-ids) (len new-args))))
          (expression-product-construct product-type-id (initializer-list-from-flds-vals field-ids new-args)))
         (poly-op (and (equal len-args 1)
                       (built-in-poly-op f)))
         ((when poly-op)
          (make-expression-call
           :function poly-op
           :types (infer-types-from-expression (if (= (len new-args) 2)
                                                   (cadr new-args)
                                                 (car new-args))
                                               locals ctxt)
           :arguments new-args))
         ((when (and (equal len-args 1)
                     (equal f 'consp))) ; Special case
          (let ((arg-types (infer-types-from-expression (car new-args) locals ctxt)))
            (expression-unary (unary-op-not)
                              (expression-call (make-identifier :name "is_empty")
                                               arg-types new-args))))
         ((when (and (equal len-args 1)
                     (equal f 'cadr)))  ; Special case
          (let ((arg-types (infer-types-from-expression (car new-args) locals ctxt)))
            (expression-call (make-identifier :name "first")
                             arg-types
                             (list (expression-call (make-identifier :name "rest")
                                                    arg-types new-args)))))
         ((when (and (equal len-args 1)
                     (equal f 'zp)))    ; Special case
          (expression-binary (binary-op-eq)
                             (car new-args)
                             (expression-literal (literal-integer 0))))
         (bin-op (and (>= len-args 2)
                      (binary-fn-op f)))
         ((when bin-op)
          (if (case-match e            ; !! Short cut !! Assuming this is implied by guard
                (('<= 0 n) (symbolp n))
                (('not ('> 0 n)) (symbolp n)))
              *expression-true-term*
            (if (and (eq f '+)
                     (integerp (car args))
                     (< (car args) 0))
                (expression-binary (binary-op-sub)
                                   (second new-args)
                                   (expression-literal (literal-integer (- (car args)))))
              (if (and (eq f '*)
                       (equal (car args) -1)
                       (= len-args 2))
                  (expression-unary (unary-op-minus) (second new-args))
                (let* ((identity? (assoc-equal bin-op *identity-expressions*))
                       (identity (if identity? (cdr identity?)
                                   (bad-syntheto-term nil))))
                  (nary-to-binary bin-op (remove-identity-elements new-args identity) identity))))))
         ((when (predicate-must-be-true-p f))
          *expression-true-term*)
         (unary-op (and (equal len-args 1)
                        (unary-fn-op f)))
         ((when unary-op)
          (if (and (equal f 'not)
                   (equal (expression-kind (car new-args))
                          ':literal))
              (if (equal (car new-args)
                         *expression-true-term*)
                  *expression-false-term*
                *expression-true-term*)
            (or (case-match e
                  (('not ('consp x))
                   (let* ((new-x (a-to-d-expr x locals ctxt))
                          (arg-types (infer-types-from-expression new-x locals ctxt)))
                     (expression-call (make-identifier :name "is_empty")
                                      arg-types (list new-x)))))
                (expression-unary unary-op (car new-args)))))
         (f-id (make-identifier :name f-name))
         (fundef? (get-function-definition f-id (context->tops ctxt)))
         ((when fundef?)
          (expression-call f-id () new-args))
         ((mv field-ref? type-name field-name)
          (try-product-field-ref-function f-name))
         ((when (and field-ref? (equal len-args 1)))
          (make-expression-product-field
           :type (make-identifier :name type-name)
           :target (car new-args)
           :field (make-identifier :name field-name)))
         )
      (bad-syntheto-term e)))
  (define a-to-d-exprs ((l true-listp) (locals typed-variable-listp) (ctxt contextp))
    :returns (exprs expression-listp)
    (if (endp l)
        ()
      (cons (a-to-d-expr (car l) locals ctxt)
            (a-to-d-exprs (cdr l) locals ctxt))))
  (define a-to-d-binders ((let-binds let-bind-listp) (locals typed-variable-listp) (ctxt contextp))
    :returns (binds binder-listp)
    (if (atom let-binds)
        ()
      (b* (((cons (list v val) r-binds) let-binds)
           (r-binders (a-to-d-binders r-binds locals ctxt))
           (bind-val (a-to-d-expr val locals ctxt))
           (types (infer-types-from-expression bind-val locals ctxt))
           (type (if (= (len types) 1)
                     (first types)
                   (make-type-defined :name (make-identifier :name "unknown"))))
           (typed-var (make-typed-variable :name (make-identifier :name (symbol-name v))
                                           :type type)))
        (cons (cons typed-var bind-val)
              r-binders))))
  (define a-to-d-cond-clauses ((cond-clauses cond-clause-listp) e (locals typed-variable-listp) (ctxt contextp))
    :returns (e expressionp)
    (if (atom cond-clauses)
        (expression-bad-expression e)
      (b* (((cons (list cond val) r-clauses) cond-clauses)
           ((when (null r-clauses))
            (if (equal cond 't)
                (a-to-d-expr val locals ctxt)
              (expression-bad-expression e)))
           (cond-val (a-to-d-expr cond locals ctxt))
           (else-val (a-to-d-cond-clauses r-clauses e locals ctxt))
           (then-val (a-to-d-expr val locals ctxt)))
        (expression-if cond-val then-val else-val))))
  :verify-guards nil
  ///
  (verify-guards a-to-d-expr)
  )  ;; a-to-d-expr-fns

(defconst *predicate-type-alist*
  `((integerp . ,(make-type-integer))
    (natp . ,(make-type-integer))
    (numberp . ,(make-type-integer))
    (booleanp . ,(make-type-boolean))
    (stringp . ,(make-type-string))
    (characterp . ,(make-type-character))))

(defconst *string-type-alist*
  `(("INT" . ,(make-type-integer))
    ("BOOL" . ,(make-type-boolean))
    ("STRING" . ,(make-type-string))
    ("CHARACTER" . ,(make-type-character))))

(define type-from-pred-string ((pred-str stringp))
  :returns (ty-expr typep)
  :measure (length pred-str)
  :ruler-extenders :all
  :verify-guards nil
  (if (not (stringp pred-str))
      (progn$ (er hard? 'acl2-to-deep "unknown type constructor name")
              (make-type-boolean))
    (let ((base-type? (assoc-equal pred-str *string-type-alist*)))
      (if base-type?
          (cdr base-type?)
        (if (and (> (length pred-str) 2)
                 (str::strsuffixp "]" pred-str))
            ;; Type constructor map, set, sequence, or option
            (b* ((bracket-pos (position #\[ pred-str))
                 ((unless (and bracket-pos
                               (> bracket-pos 3)
                               (< (+ bracket-pos 3) (length pred-str))))
                  (progn$ (er hard? 'acl2-to-deep "Illegal type constructor predicate")
                          (make-type-boolean))) ; shouldn't happen
                 (type-constructor-str (subseq pred-str 0 bracket-pos))
                 (type-arg-str (subseq pred-str (+ bracket-pos 1) (- (length pred-str) 1))))
              (if (equal type-constructor-str "MAP")
                  (b* ((split-pos (position #\- type-arg-str)) ; Actually -> and assumes any nested maps are curried!
                       ((unless (and split-pos
                                     (> split-pos 0)
                                     (< (+ split-pos 2) (length type-arg-str))))
                        (progn$ (er hard? 'acl2-to-deep "illegal map predicate")
                                (make-type-boolean))) ; shouldn't happen
                       (dom-str (subseq type-arg-str 0 split-pos))
                       (dom (if (< (length dom-str) (length pred-str)) ; Always true but proof apparently hard
                                (type-from-pred-string dom-str)
                              (make-type-boolean)))
                       (ran-str (subseq type-arg-str (+ split-pos 2) nil))
                       (ran (if (< (length ran-str) (length pred-str)) ; Always true but proof apparently hard
                                (type-from-pred-string ran-str)
                              (make-type-boolean))))
                    (make-type-map
                     :domain dom
                     :range ran))
                (let ((type-arg (if (< (length type-arg-str) (length pred-str)) ; Always true but proof apparently hard
                                    (type-from-pred-string type-arg-str)
                                  (make-type-boolean))))
                  (cond ((equal type-constructor-str "SET")
                         (make-type-set :element type-arg))
                        ((equal type-constructor-str "SEQUENCE")
                         (make-type-sequence :element type-arg))
                        ((equal type-constructor-str "OPTION")
                         (make-type-option :base type-arg))
                        (t (progn$ (er hard? 'acl2-to-deep "unknown type constructor name")
                                   (make-type-boolean)))))))
          (make-type-defined :name (make-identifier :name pred-str)))))))
(verify-guards type-from-pred-string)

(define type-from-pred ((pred symbolp))
  :returns (ty-expr maybe-typep)
  (b* ((built-in-type? (assoc pred *predicate-type-alist*))
       ((when built-in-type?)
        (cdr built-in-type?))
       (pred-str (symbol-name pred)))
    (if (and (> (length pred-str) 2)
             (str::strsuffixp "-P" pred-str))
        (type-from-pred-string (subseq pred-str 0 (- (length pred-str) 2)))
      nil)))

(define typing-alistp (l)
  :enabled t
  (or (null l)
      (and (consp l)
           (consp (car l))
           (symbolp (caar l))
           (typep (cdar l))
           (typing-alistp (cdr l)))))

(define analyze-guard-conjuncts ((guard-conjuncts true-listp) (ctxt contextp))
  :returns (mv (typings typing-alistp)
               (preconditions expression-listp))
  (if (endp guard-conjuncts)
      (mv nil nil)
    (b* (((cons this-conj r-conjs) guard-conjuncts)
         ((mv r-typings r-preconditions)
          (analyze-guard-conjuncts r-conjs ctxt))
         (type? (and (= (len this-conj) 2)
                     (symbolp (first this-conj))
                     (symbolp (second this-conj))
                     (type-from-pred (first this-conj))))
         ((when type?)
          (mv (cons (cons (second this-conj) type?) r-typings)
              r-preconditions))
         (trans-conj (a-to-d-expr this-conj () ctxt)))
      (mv r-typings (if (or (expression-true-term-p trans-conj)
                            (bad-syntheto-termp trans-conj))
                        r-preconditions ; Just ignore for now
                      (cons trans-conj r-preconditions))))))

(define infer-inputs ((formals symbol-listp)
                      (guard-typings typing-alistp)
                      (old-inputs typed-variable-listp)
                      (old-outputs typed-variable-listp))
  :returns (new-inputs typed-variable-listp)
  (if (endp formals)
      ()
    (b* (((cons this-formal r-formals) formals)
         (this-var-identifier (make-identifier :name (symbol-name this-formal)))
         (r-val (infer-inputs r-formals guard-typings old-inputs old-outputs))
         (guard-type? (assoc this-formal guard-typings))
         ((when guard-type?)
          (cons (make-typed-variable
                 :name this-var-identifier
                 :type (cdr guard-type?))
                r-val))
         (input-tv (lookup-typed-variable-list (symbol-name this-formal) old-inputs)))
      (if input-tv
          (cons input-tv r-val)
        (if (equal this-formal 'syndef::|vertices|) ; Temporary hack!!
            (cons (make-typed-variable
                   :name this-var-identifier
                   :type (make-type-sequence
                          :element (make-type-defined :name (make-identifier :name "point"))))
                  r-val)
          (if (= (len old-outputs) 1)
              (cons (make-typed-variable
                     :name this-var-identifier
                     :type (typed-variable->type (car old-outputs)))
                    r-val)
            (cons (make-typed-variable
                   :name this-var-identifier
                   :type (type-integer))
                  r-val)))))))

(define lambda-to-header-and-body ((new-fn-name stringp)
                                   (formals symbol-listp)
                                   acl2-body
                                   (new-guard-conjuncts true-listp)
                                   (old-header function-headerp)
                                   ;(old-body expressionp)
                                   (ctxt contextp))
  :returns (mv (new-header function-headerp)
               (new-definer function-definerp)
               (maybe-new-precondition maybe-expressionp))
  (b* (((function-header old-header) old-header)
       ((mv guard-typings preconditions)
        (analyze-guard-conjuncts new-guard-conjuncts ctxt))
       (maybe-new-precondition (and preconditions
                                    (conjoin-expressions preconditions)))
       (new-inputs (infer-inputs formals guard-typings old-header.inputs old-header.outputs))
       (new-header (make-function-header :name (make-identifier :name new-fn-name)
                                         :inputs new-inputs
                                         :outputs old-header.outputs))
       (new-placeholder-def (toplevel-function (make-function-definition
                                                :header new-header
                                                :definer (make-function-definer-regular
                                                          :measure nil
                                                          ;; Place holder!
                                                          :body (expression-literal (literal-boolean nil))))))
       (ctxt (context-add-toplevel new-placeholder-def ctxt))
       (local-vars (append new-inputs (local-variables acl2-body))) ; Put local vars later because last resort
       (new-body (a-to-d-expr acl2-body local-vars ctxt))
       (body-types (infer-types-from-expression new-body local-vars ctxt))
       (new-header (make-function-header :name (make-identifier :name new-fn-name)
                                         :inputs new-inputs
                                         :outputs (replace-var-types old-header.outputs body-types)))
       (new-definer (make-function-definer-regular
                     :measure nil
                     :body new-body)))
    (mv new-header new-definer maybe-new-precondition)))

(define acl2-to-deep-fn ((new-fn symbolp)
                         (formals symbol-listp)
                         acl2-def
                         (new-guard-conjuncts true-listp)
                         (old-synth-def function-definitionp)
                         (ctxt contextp))
  :returns (new-synth-def function-definitionp :hyp :guard)
  (b* (((function-definition old-def) old-synth-def)
       ;((function-header old-header) old-def.header)
       ((unless (equal (function-definer-kind old-def.definer)
                :regular))
        old-synth-def)                  ; Error
       ((function-definer-regular old-definer) old-def.definer)
       ((mv new-header new-definer maybe-new-precondition)
        (lambda-to-header-and-body (symbol-name new-fn) formals acl2-def new-guard-conjuncts
                                   old-def.header ;; old-definer.body
                                   ctxt)) )
    (make-function-definition :header new-header
                              :precondition maybe-new-precondition
                              ; :postcondition ; get from old postcondition?
                              :definer new-definer)))

(define acl2-to-deep-thm ((thm-name symbolp)
                          thm-body
                          (old-synth-def function-definitionp)
                          (ctxt contextp))
  :returns (new-synth-def theoremp :hyp :guard)
  (b* (((function-definition old-def) old-synth-def)
       ((function-header old-header) old-def.header))
    (make-theorem :name (make-identifier :name (symbol-name thm-name))
                  :variables old-header.inputs
                  :formula (a-to-d-expr thm-body old-header.inputs ctxt))))
