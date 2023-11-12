(load "util.lsp")
(in-package :structs)

(defstruct (TaggedSExpr)
  (id nil :type optional-number)
  expr)

(set-pprint-dispatch 'TaggedSExpr
                     (lambda (stream val)
                       (pprint (TaggedSExpr-expr val) stream)))

(deftype optional-TaggedSExpr ()
  `(or TaggedSExpr null (member :missing)))

(defmethod print-object ((obj TaggedSExpr) out)
  (with-slots (expr)
      obj
    (format out "~a" expr)))

(declaim (ftype (function (TaggedSExpr TaggedSExpr) boolean) ts-expr-equalp))
(defun ts-expr-equalp (s1 s2)
  (equal (TaggedSExpr-expr s1) (TaggedSExpr-expr s2)))

(defstruct (ProofStep)
  (id nil :type (or number list)) ;; identifier(s) for XText
  (rel nil :type (or string symbol null)) ;; The relation (string)
  (before nil :type optional-TaggedSExpr) ;; The LHS of the step (s-expr)
  (after nil :type optional-TaggedSExpr) ;; The RHS of the step (s-expr)
  (hints nil :type list) ;; List of hints used to prove this step (list of hint s-exprs)
  (bounds (cons -1 -1) :type (cons number number)) ;; (cons nat nat) The start and end of the text corresponding to this step in the proof file
  )

(defstruct (CtxItem)
  (id nil :type optional-number) ;; identifier for XText
  (name 'DEFAULTNAME :type symbol) ;; Name (symbol in pkg proof)
  (stmt nil :type optional-TaggedSExpr) ;; (s-expr)
  (hints nil :type list) ;; List of hints (if a derived context item)
  (bounds (cons -1 -1) :type (cons number number));; (cons nat nat) The start and end of the text corresponding to this context item in the proof file
  (type-predicatep nil :type boolean)
  )

(defmethod print-object ((obj CtxItem) out)
  (print-unreadable-object (obj out)
                           (with-slots (name stmt)
                               obj
                               (format out "~a: ~a" name stmt))))

(defstruct (ProofStrategy)
  (id nil :type optional-number)
  (kind :equational-reasoning
        :type
        (member :equational-reasoning
                :case-analysis
                :decomposition
                :induction
                :induction-case
                :termination))
  params)

(defstruct (Proof)
  (id nil :type optional-number)
  (kind "" :type string) ;; (oneof "Problem" "Theorem" "Lemma")
  (name "" :type string) ;; (string)
  (stmt nil :type optional-TaggedSExpr) ;; (s-expr)
  (exportation nil :type optional-TaggedSExpr) ;; (s-expr)
  (contract-completion nil :type optional-TaggedSExpr) ;; (s-expr)
  (goal nil :type optional-TaggedSExpr) ;; (s-expr)
  (steps nil :type list) ;; (listof ProofStep)
  ctx ;; (alist symbol CtxItem)
  derived-ctx ;; (alist symbol CtxItem)
  (strategy (make-ProofStrategy) :type ProofStrategy)
  (cases nil :type list) ;; (listof Proof)
  )

(deftype optional-Proof ()
  `(or Proof null))

(defstruct (ProofMessage)
  (id nil :type (or number list))
  (severity :error :type (member :error :warn :info))
  (description "" :type string)
  (category "" :type string)
  proof
  kind
  )

(deftype Status ()
  '(member :ok :warn :fail))

(deftype optional-GenThm ()
  `(or (function (t) list) null))

(defstruct (CompletedProofDatum)
  (status :ok :type Status)
  (proof nil :type optional-Proof)
  (gen-thm nil :type optional-GenThm))

(deftype CompletedProofData ()
  `(or null
       (cons CompletedProofDatum list)))
