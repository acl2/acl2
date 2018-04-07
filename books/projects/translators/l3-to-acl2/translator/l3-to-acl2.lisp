(in-package "ACL2")

; General comments:

; We translate objects of option type to nil, for NONE, and (SOME . x), for
; SOME x.  We considered translating (SOME . x) to x in the case that x cannot
; be nil, but we worried that case-matching would be awkward to work out in
; that case.

; We start by including l3, so that various functions are defined, e.g.: BITS
; and BL are defined, for use in term-stobj-out below; type-expr, for use in
; l3-trans-formal below.
(include-book "l3")

(defun trans-breaker ()
; To trace errors, e.g.:
; (set-iprint t)
; (trace$ (trans-breaker :entry (break$)))
  (declare (xargs :guard t))
  nil)

(defmacro trans-err (&rest args)
  `(prog2$ (trans-breaker) ; to break: (trace$ (trans-breaker :entry (break$)))
           (trans-er ,@args)))

(defstobj bindings
  str-to-const    ; alist mapping strings to constant symbols
  const-to-str    ; alist mapping constant symbols to strings
  sym-to-str      ; alist mapping symbols seen to strings they came from
  str-to-sym      ; inverse of sym-to-str
  st$-fields      ; alist binding each field to nil or (for array) dimension
  construct-alist ; alist mapping constructor types to field names
  bw              ; binding world, extended with some stobjs-out for defs
  )

(defun str-to-sym-alistp (x)
  (declare (xargs :guard (alistp x)))
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (stringp (caar x))
                (symbolp (cdar x))
                (not (assoc-equal (caar x) (cdr x)))
                (not (rassoc-eq (cdar x) (cdr x)))
                (str-to-sym-alistp (cdr x))))))

(defthm str-to-sym-alistp-forward-to-alistp
  (implies (str-to-sym-alistp x)
           (alistp x))
  :rule-classes :forward-chaining)

(defun invert-alist (x)
  (declare (xargs :guard (alistp x)))
  (cond ((endp x) nil)
        (t (acons (cdar x)
                  (caar x)
                  (invert-alist (cdr x))))))

(defconst *initial-bindings*
  '(("t" . T_VAR)
    ("nil" . NIL_VAR)))

(defun initialize-bindings (str-to-sym wrld ctx bindings)
  (declare (xargs :stobjs bindings))
  (let ((str-to-sym (append *initial-bindings* str-to-sym)))
    (cond
     ((not (and (alistp str-to-sym)
                (str-to-sym-alistp str-to-sym)))
      (trans-err ctx
                 "STR-TO-SYM should be, after extending by ~x0, an alist ~
                  mapping strings to symbols, without duplicate CARs or CDRs; ~
                  but that extension is:~|~x1"
                 *initial-bindings* str-to-sym))
     (t (let* ((bindings (update-str-to-const nil bindings))
               (bindings (update-const-to-str nil bindings))
               (bindings (update-str-to-sym str-to-sym bindings))
               (bindings (update-sym-to-str (invert-alist str-to-sym)
                                            bindings))
               (bindings (update-st$-fields nil bindings))
               (bindings (update-construct-alist nil bindings))
               (bindings (update-bw wrld bindings)))
          (trans-value nil))))))

(defun l3-reparse (x)

; Replaces subexpressions
;   qvar"s"
;   qvar"state"
; and for that matter, any
;   qvar x
; by just qvar.
; Also, replaces subexpressions
;   bvar"name"
; by
;   (var "name" bty)

  (cond ((atom x) x)
        ((atom (cdr x))
         (cons (l3-reparse (car x))
               (cdr x)))
        (t (case (car x)
             (bvar (cons (list 'var (cadr x) 'bty)
                         (l3-reparse (cddr x))))
             (nvar (cons (list 'var (cadr x) 'nty)
                         (l3-reparse (cddr x))))
             (ivar (cons (list 'var (cadr x) 'ity)
                         (l3-reparse (cddr x))))
             (qvar (cons 'qvar
                         (l3-reparse (cddr x))))
             (svar (cons (list 'var (cadr x) 'sty)
                         (l3-reparse (cddr x))))
             (uvar (cons (list 'var (cadr x) 'uty)
                         (l3-reparse (cddr x))))
             (vvar (cons (list 'var (cadr x) 'vty)
                         (l3-reparse (cddr x))))
             (cty  (cons (list 'cty (cadr x))
                         (l3-reparse (cddr x))))
             (otherwise (cons (l3-reparse (car x))
                              (l3-reparse (cdr x))))))))

; At this point we get lazy.  If we want to convert to guard-verified :logic
; mode then at a minimum, we'll need to define a "good-bindings-p" predicate
; that says that sym-to-str and str-to-sym are alists mapping symbols to/from
; strings.
(program)

(defun l3-trans-constant (s ctx bindings)

; S is expected to be a string (we cause an error if not).  We translate s to a
; constant symbol or nil.

  (declare (xargs :stobjs bindings))
  (cond
   ((not (stringp s))
    (trans-err ctx
               "String expected, but got:~|~x0"
               s))
   (t (trans-value (cdr (assoc-equal s (str-to-const bindings)))))))

(defun l3-trans-sym (s ctx bindings)

; S is expected to be a string (we cause an error if not).  We translate s to a
; symbol, using bindings and avoiding the returning of symbol ST$.

  (declare (xargs :stobjs bindings))
  (cond
   ((not (stringp s))
    (trans-err ctx
               "String expected, but got:~|~x0"
               s))
   ((string-equal s "ST$")
    (trans-err ctx
               "The name ST$ is reserved."))
   (t (let* ((str-to-sym (str-to-sym bindings))
             (pair (assoc-equal s str-to-sym)))
        (cond
         (pair (trans-value (cdr pair)))
         (t
          (let* ((sym (intern (string-upcase (if (position #\' s)
                                                 (substitute #\- #\' s)
                                               s))
                              "ACL2"))
                 (sym-to-str (sym-to-str bindings))
                 (pair (assoc-eq sym sym-to-str)))
            (cond
             ((null pair)
              (let* ((bindings (update-str-to-sym (acons s sym str-to-sym)
                                                  bindings))
                     (bindings (update-sym-to-str (acons sym s sym-to-str)
                                                  bindings)))
                (trans-value sym)))
             (t (trans-err ctx
                           "Strings ~x0 and ~x1 both map to symbol '~x2.  ~
                            Re-run with keyword argument :STR-TO-SYM set to ~
                            an alist that binds at least one of these strings ~
                            to some other symbol."
                           (cdr pair) s sym))))))))))

(defun l3-trans-type-expr (texpr ctx bindings)

; Texpr is a type-expression, which we want to translate to a corresponding
; symbolic type expression or a list of such.  For example, the type-expression

; (PTy (CTy "funcT")
;      (PTy (CTy "shiftT")
;           (PTy (FTy 7)
;                (PTy (FTy 7)
;                     (FTy 7)))))

; translates to the list:

; (funct shiftt (unsigned-byte 7) (unsigned-byte 7) (unsigned-byte 7))

; Also, for example, (lty (CTy "instruction")) translates to instruction-list.

  (declare (xargs :stobjs bindings))
  (case-match texpr
    (('cty s)
     (l3-trans-sym s ctx bindings))
    (('pty t1 t2)
     (trans-er-let*
      ((x1 (l3-trans-type-expr t1 ctx bindings))
       (x2 (l3-trans-type-expr t2 ctx bindings)))
      (trans-value (if (and (consp t2)
                            (eq (car t2) 'pty))
                       (cons x1 x2)
                     (list x1 x2)))))
    (('fty n)
     (cond ((posp n)
            (trans-value (list 'unsigned-byte n)))
           (t (trans-err ctx
                         "Unexpected type expression:~|~x0"
                         texpr))))
    (('lty t1)
     (trans-er-let*
      ((x1 (l3-trans-type-expr t1 ctx bindings)))
      (trans-value (type-list-name x1))))
    (('oty t1)
     (trans-er-let*
      ((x1 (l3-trans-type-expr t1 ctx bindings)))
      (trans-value (list 'oty x1))))
    (& (case texpr
         (F1 (trans-value (list 'unsigned-byte 1)))
         (F4 (trans-value (list 'unsigned-byte 4)))
         (F8 (trans-value (list 'unsigned-byte 8)))
         (F16 (trans-value (list 'unsigned-byte 16)))
         (F32 (trans-value (list 'unsigned-byte 32)))
         (F64 (trans-value (list 'unsigned-byte 64)))
         (bTy (trans-value 'bty))
         (sTy (trans-value 'sty))
         (uTy (trans-value 'uty))
         (qTy (trans-value 'qty))
         (otherwise
          (trans-err ctx
                     "Unexpected type expression:~|~x0"
                     texpr))))))

(defun l3-trans-construct-1 (cl ctx bindings)
  (declare (xargs :stobjs bindings))
  (case-match cl
    ((s '[])
     (l3-trans-sym s ctx bindings))
    ((s ('sqbkt texpr))
     (trans-er-let*
      ((sym (l3-trans-sym s ctx bindings))
       (texpr (l3-trans-type-expr texpr ctx bindings)))
      (trans-value (list sym texpr))))
    (& (trans-err ctx
                  "Illegal CONSTRUCT clause:~|~x0"
                  cl))))

(defun l3-trans-construct-rec (clauses ctx bindings)
  (declare (xargs :stobjs bindings))
  (cond ((endp clauses)
         (trans-value nil))
        (t (trans-er-let*
            ((cl (l3-trans-construct-1 (car clauses) ctx bindings))
             (x (l3-trans-construct-rec (cdr clauses) ctx bindings)))
            (trans-value (cons cl x))))))

(defun construct-constructors (clauses)

; Clauses is the second argument of a construct form.  We skip over atomic
; members of clauses, but for each cons (constructor-name types), we collect up
; constructor-name.

  (cond ((endp clauses) nil)
        ((atom (car clauses))
         (construct-constructors (cdr clauses)))
        (t (cons (caar clauses)
                 (construct-constructors (cdr clauses))))))

(defun l3-trans-construct (name clauses ctx bindings)
  (declare (xargs :stobjs bindings))
  (trans-er-let*
   ((sym (l3-trans-sym name ctx bindings))
    (x (l3-trans-construct-rec clauses ctx bindings)))
   (let* ((field-names (construct-constructors x))
          (old-construct-alist (construct-alist bindings))
          (bindings (if field-names
                        (update-construct-alist
                         (put-assoc-eq sym field-names old-construct-alist)
                         bindings)
                      bindings)))
     (trans-value (list 'construct sym x)))))

(defmacro extend-st$-fields (sym-expr val)

; Sym-expr is an expression whose value is a tuple (trans-value sym), where sym
; is the (translated) name of an st$ field.  Val is to be associated with that
; name in the st$-fields of bindings.

  `(trans-er-let*
    ((sym ,sym-expr))
    (let ((bindings
           (update-st$-fields (put-assoc-eq sym ,val (st$-fields bindings))
                              bindings)))
      (trans-value sym))))

(defun l3-trans-st$-field (field ctx bindings)
  (declare (xargs :stobjs bindings))
  (case-match field
    ((name ('CTy &))
     (extend-st$-fields (l3-trans-sym name ctx bindings) nil))
    ((name ('ATy t1 t2))
     (trans-er-let*
      ((x1 (l3-trans-type-expr t1 ctx bindings))
       (x2 (l3-trans-type-expr t2 ctx bindings)))
      (case-match x1
        (('unsigned-byte n)
         (let ((expt-2-n (expt 2 n)))
           (trans-er-let*
            ((sym (extend-st$-fields (l3-trans-sym name ctx bindings)
                                     expt-2-n)))
            (trans-value
             (case-match x2
               (('unsigned-byte &)
                `(,sym :type (array ,x2 (,expt-2-n)) :initially 0))
               (&
                `(,sym :type (array t (,expt-2-n)))))))))
        (& (trans-err ctx
                      "Illegal defstobj array field spec:~|~x0"
                      field)))))
    ((name t1)
     (trans-er-let*
      ((sym (extend-st$-fields (l3-trans-sym name ctx bindings) nil))
       (x1 (l3-trans-type-expr t1 ctx bindings)))
      (cond
       ((and (consp x1)
             (eq (car x1) 'unsigned-byte))
        (trans-value `(,sym :type ,x1 :initially 0)))
       ((symbolp x1)
        (trans-value `(,sym :type (satisfies ,(make-type x1)))))
       (t
        (trans-value `(,sym)))

; If x1 is an option type expression, or for that matter any other type
; expression not handled above, we simply make no constraints on the type of
; the field.  This seems harmless enough for now, though we may want to revisit
; it when we start doing proofs.

;       (trans-err ctx
;                  "Unexpected type for stobj field, ~x0"
;                  x1)
       )))
    (& (trans-err ctx
                  "Illegal defstobj field spec:~|~x0"
                  field))))

(defun l3-trans-st$-fields (fields ctx bindings)
  (declare (xargs :stobjs bindings))
  (cond ((endp fields) (trans-value nil))
        (t (trans-er-let*
            ((field (l3-trans-st$-field (car fields) ctx bindings))
             (fields (l3-trans-st$-fields (cdr fields) ctx bindings)))
            (trans-value (cons field fields))))))

(defun l3-trans-st$ (fields ctx bindings)
  (declare (xargs :stobjs bindings))
  (trans-er-let*
   ((tfields (l3-trans-st$-fields fields ctx bindings)))
   (trans-value `(defstobj+ st$ ,@tfields))))

(defun l3-trans-record (name fields ctx bindings)
; !! Needs to be written.
; Example:
; ("CauseRegister" (sqbkt ("'rst" (FTy 27)) ("ExcCode" (FTy 5))))
; so name is "CauseRegister"
  (declare (xargs :stobjs bindings)
           (ignore fields))
  (trans-err ctx
             "Sorry: l3-trans-record is not yet implemented (attempted to ~
              translate a record definition for name ~x0)."
             name))

(mutual-recursion

(defun l3-get-type-mop (mop expr ctx bindings)
; Keep in sync with l3-trans-map.
; !! Need to support fst and snd.
  (declare (xargs :stobjs bindings))
  (case-match mop
    ('length (trans-value '(integer 0 *)))
    ('bnot (l3-get-type expr ctx bindings))
    ('not (trans-value 'bty))
    (('cast x)
     (l3-trans-type-expr x ctx bindings))
    (& (trans-err ctx
                  "Unimplemented mop for l3-get-type-mop: ~x0"
                  mop))))

(defun l3-get-type (l3-expr ctx bindings)

; Warning: keep in sync with l3-trans-expr and expr-st$-out-p.

; Return the translated type of expr.

  (declare (xargs :stobjs bindings))
  (case-match l3-expr
    ('lu (trans-value 'uTy))
    ('qvar (trans-value 'qTy))
    ('lt (trans-value 'bty))
    ('lf (trans-value 'bty))
    (('lnl typ)
     (l3-trans-type-expr typ ctx bindings))
    (('llc ('sqbkt &) expr)
     (l3-get-type expr ctx bindings))
    (('ll ('sqbkt . exprs))
     (cond ((null exprs) ; maybe impossible?
            (trans-value 'null))
           (t (trans-er-let*
               ((x (l3-get-type (car exprs) ctx bindings)))
               (cond ((symbolp x)
                      (trans-value (type-list-name x)))
                     (t (trans-err ctx
                                   "~x0 doesn't know how to get the type for ~
                                     expression~|  ~x1~|because it doesn't ~
                                     know how to get the list type ~
                                     corresponding to the type ~x2."
                                   'l3-get-type
                                   l3-expr
                                   x)))))))
    (('var & typ)
     (l3-trans-type-expr typ ctx bindings))
    (('avar typ)
     (l3-trans-type-expr typ ctx bindings))
    (('lc & typ)
     (l3-trans-type-expr typ ctx bindings))
    (('const & typ)
     (l3-trans-type-expr typ ctx bindings))
    (('lw & n)
     (trans-value `(unsigned-byte ,n)))
    (('tp ('sqbkt . args))
     (l3-get-type-lst args ctx bindings))
    (('ite & expr1 expr2) ; same as for bop (except for error message)
     (trans-er-let*
      ((x1 (l3-get-type expr1 ctx bindings))
       (x2 (l3-get-type expr2 ctx bindings)))
      (cond ((equal x1 x2)
             (trans-value x1))
            (t (trans-er
                "Obtained different types for second and third arguments of ~
                 expression~|~x0~|, as follow.~|  True-branch: ~
                 ~x1~|  False-branch: ~x2"
                l3-expr x1 x2)))))
    (('bop & expr1 expr2) ; same as for ite (except for error message)
     (trans-er-let*
      ((x1 (l3-get-type expr1 ctx bindings))
       (x2 (l3-get-type expr2 ctx bindings)))
      (cond ((equal x1 x2)
             (trans-value x1))
            (t (trans-er
                "Obtained different types for second and third arguments of ~
                 expression~|~x0~|, as follow.~|  True-branch: ~
                 ~x1~|  False-branch: ~x2"
                l3-expr x1 x2)))))
    (('mop mop expr1)
     (l3-get-type-mop mop expr1 ctx bindings))
    (('apply ('const & ('ATy 'qTy t1)) 'qvar)
     (l3-trans-type-expr t1 ctx bindings))
    (('apply ('call & ('ATy 'qTy typ) &) &)
     (l3-trans-type-expr typ ctx bindings))
    (('apply ('dest & ('ATy & typ) 'qvar) &)
; !! Need to consider records other than the state record.
     (l3-trans-type-expr typ ctx bindings))
    (('dest & typ 'qvar)
; !! Need to consider records other than the state record.
     (l3-trans-type-expr typ ctx bindings))
    (('rupd & &)
; !! Need to consider records other than the state record.
     (trans-value 'qTy))
    (('call & typ &)
     (l3-trans-type-expr typ ctx bindings))
    (('cs & ('sqbkt (& x) . &))
; We could check that all clauses give the same type, but that seems
; unnecessary at this point.
     (l3-get-type x ctx bindings))
    (('let & & x)
     (l3-get-type x ctx bindings))
    (('cc ('sqbkt . lst))
     (trans-er-let*
      ((n (l3-trans-width-lst lst ctx bindings)))
      (trans-value `(unsigned-byte ,n))))
    (('bl n x)
     (trans-er-let*
      ((typ (l3-get-type x ctx bindings)))
      (let ((expected `(unsigned-byte ,n)))
        (cond ((equal typ expected)
               (trans-value typ))
              (t (trans-err ctx
                            "Unexpected type, ~x0, for ~x1 (expected type to ~
                             be ~x2), in expression:~|~x3."
                           typ x expected l3-expr))))))
    (('ex & & & typ)
     (l3-trans-type-expr typ ctx bindings))
    (('eq & &)
     (trans-value `bty))
    (& (trans-err ctx
                  "Unrecognized type expression: ~x0"
                  l3-expr))))

(defun l3-get-type-lst (lst ctx bindings)
  (declare (xargs :stobjs bindings))
  (cond ((endp lst) (trans-value nil))
        (t (trans-er-let*
            ((x1 (l3-get-type (car lst) ctx bindings))
             (x2 (l3-get-type-lst (cdr lst) ctx bindings)))
            (trans-value (cons x1 x2))))))

(defun l3-trans-width (x ctx bindings)
  (declare (xargs :stobjs bindings))
  (trans-er-let*
   ((typ (l3-get-type x ctx bindings)))
   (case-match typ
     (('unsigned-byte n)
      (trans-value n))
     (& (trans-err ctx
                   "Unable to compute bit width for ~x0."
                   x)))))

(defun l3-trans-width-lst (lst ctx bindings)
  (declare (xargs :stobjs bindings))
  (cond ((endp lst) (trans-value 0))
        (t (trans-er-let*
            ((n1 (l3-trans-width (car lst) ctx bindings))
             (n2 (l3-trans-width-lst (cdr lst) ctx bindings)))
            (trans-value (+ n1 n2))))))
)

(defun l3-trans-st$-field-name (field array-p update-p ctx bindings)
  (declare (xargs :stobjs bindings))
  (trans-er-let*
   ((sym (l3-trans-sym field ctx bindings)))
   (let ((pair (assoc-eq sym (st$-fields bindings)))
         (key2 (if array-p :array :non-array)))
     (cond ((null pair)
            (trans-err ctx
                       "Implementation error: Failed to find symbol ~x0 (from ~
                        field ~x1) in ~x2"
                       sym field '(st$-fields bindings)))
           ((not (iff (cdr pair) array-p))
            (trans-err ctx
                       "Implementation error: symbol ~x0 (from field ~x1) is ~
                        associated in ~x2 with ~x3, but array-p is ~x4 in ~
                        call:~|~x5"
                       sym field '(st$-fields bindings) (cdr pair) array-p
                       `(l3-trans-st$-field-name
                         ,field ,array-p ,update-p ,ctx bindings)))
           ((eq update-p 'map)
            (trans-value (stobj-mapper-name
                          (defstobj-fnname sym :updater key2 nil)
                          nil)))
           (update-p (trans-value (defstobj-fnname sym :updater key2 nil)))
           (t (trans-value (defstobj-fnname sym :accessor key2 nil)))))))

(defun type-st$-out-p (x n)

; This function is called at the top level with n = nil.

; X is an untranslated type.  We return a non-nil result iff x represents
; state.  If x is a pair type, then in that case we return n+k where state is
; the kth component of the resulting tuple; otherwise we return t.

  (case-match x
    ('qty (or n t))
    (('pty 'qty &) n)
    (('pty & x2)
     (type-st$-out-p x2
                     (if (null n) 1 (1+ n))))
    (& nil)))

(mutual-recursion

(defun expr-st$-out-p (x)

; Warning: keep in sync with l3-get-type and l3-trans-expr.

; X is an untranslated expression.  We return t if x represents a value of st$,
; n if x represents an mv for which component number n (0-based) represents a
; value of st$, and nil otherwise.

  (case-match x
    ('lu nil)
    ('qvar t)
    ('lt nil)
    ('lf nil)
    (('lnl &) nil)
    (('llc . &) nil)
    (('ll . &) nil)
    (('var & &) nil)
    (('avar typ)
     (not (eq typ 'qty)))
    (('lc & &) nil)
    (('const & &) nil)
    (('lw & &) nil)
    (('tp ('sqbkt . args))
     (expr-st$-out-listp args 0))
    (('ite & tbr fbr)
     (let ((x1 (expr-st$-out-p tbr))
           (x2 (expr-st$-out-p fbr)))
       (cond ((not (eq x1 x2))
              (cond ((iff x1 x2)
                     (er hard 'expr-st$-out-p
                         "Surprise!  Expr-st$-out-p returns different state ~
                          results, ~x0 and ~x1, for the two branches of an ~
                          ITE expression:~|~x2"
                         x1 x2 x))
                    (t
                     (er hard 'expr-st$-out-p
                         "Surprise!  The following ITE expression seems to ~
                          return state in its ~s0 branch but not in its ~s1 ~
                          branch:~|~x2"
                         (if x1 "true" "false")
                         (if x1 "false" "true")
                         x))))
             (t (or x1 x2)))))
    (('bop . &) nil)
    (('mop . &) nil)
    (('apply ('const & ('ATy 'qTy t1)) 'qvar)
     (type-st$-out-p t1 nil))
    (('apply ('call & ('ATy & t1) &) &)
     (type-st$-out-p t1 nil))
    (('apply ('dest & & &) &) nil)
    (('dest & & &) nil)
    (('rupd & &) t)
; !! Need to consider records other than the state record.
    (('call & t1 &)
     (type-st$-out-p t1 nil))
    (('cs & ('sqbkt (& x1) . &))
     (expr-st$-out-p x1))
    (('let ('tp ('sqbkt . lst)) & &)
     (expr-st$-out-listp lst 0))
    (('let var & &)
     (eq var 'st$))
    (('cc ('sqbkt . &)) nil)
    (('bl & &) nil)
    (('ex & & & &) nil)
    (('ln &) nil)
    (('eq & &) nil)
    (& (er hard 'expr-st$-out-p
           "Unrecognized expression: ~x0"
           x))))

(defun expr-st$-out-listp (x n)
  (cond ((endp x) nil)
        ((expr-st$-out-p (car x)) n)
        (t (expr-st$-out-listp (cdr x) (1+ n)))))
)

(defun lift-st$-lst (args lst)

; !! Consider redoing to better match lift-st$, or maybe even eliminate this
; function if possible and only use lift-st$.

; Keep in sync with lift-st$.

; Args is a list of l3 expressions and lst is the corresponding list of
; translations.  We return (mv let-sym bs new-lst), where let-sym is nil, t,
; let, or let*; bs is a list of bindings for let or let* (according to
; let-sym); and new-lst is the result of replacing an element e of lst that
; represents st$, by st$ itself.  The intention is that either let-sym is nil
; or t, in which case lst is returned unchanged, or else e is equal to (let-sym
; bs st).  Also, lst contains an expression representing st$ if and only if
; let-sym is non-nil.

  (let ((posn (expr-st$-out-listp args 0)))
    (cond
     (posn (let ((st$-expr (nth posn lst)))
             (case-match st$-expr
               ('st$ (mv t nil lst))
               (('let (('st$ e)) body) ; assume single-threadedness:
                (mv 'let
                    `((st$ ,e))
                    (update-nth posn body lst)))
               (('let* bindings body) ; assume single-threadedness:
                (cond ((equal (remove-duplicates-eq (strip-cars bindings))
                              '(st$))
                       (mv 'let*
                           bindings
                           (update-nth posn body lst)))
                      (t (mv 'let
                             `((st$ ,st$-expr))
                             (update-nth posn 'st$ lst)))))
               (&
                (mv 'let
                    `((st$ ,st$-expr))
                    (update-nth posn 'st$ lst))))))
     (t (mv nil nil lst)))))

(defun lift-st$ (call posn)

; Keep in sync with lift-st$-lst.

; Call is (fn arg1 ... argk) and posn is the position (0-based in the call,
; 1-based in (arg1 ... argk)) of the st$ argument, which might be an expression
; other than 'st$ itself.  We rewrite call to make ACL2's single-threadedness
; check happy.

  (let ((st$-expr (nth posn call)))
    (case-match st$-expr
      ('st$ call)
      (('let (('st$ e)) body) ; assume single-threadedness:
       `(let* ((st$ ,e)
               (st$ ,body))
          ,(update-nth posn 'st$ call)))
      (('let* bindings body) ; assume single-threadedness:
       (cond ((equal (remove-duplicates-eq (strip-cars bindings))
                     '(st$))
              `(let* ,(append bindings `((st$ ,body)))
                 ,(update-nth posn 'st$ call)))
             (t `(let ((st$ ,st$-expr))
                   ,(update-nth posn 'st$ call)))))
      (&
       `(let ((st$ ,st$-expr))
          ,(update-nth posn 'st$ call))))))

(mutual-recursion

(defun l3-trans-expr (patp l3-expr ctx bindings)

; Warning: keep in sync with l3-get-type and expr-st$-out-p.

  (declare (xargs :stobjs bindings))
  (case-match l3-expr
    ('lu (trans-value '(unit-value)))
    ('qvar (trans-value 'st$))
    ('lt (trans-value '(true)))
    ('lf (trans-value '(false)))
    (('lnl &) (trans-value (if patp ''nil nil)))
    (('llc ('sqbkt expr1) expr2)
     (trans-er-let*
      ((x1 (l3-trans-expr patp expr1 ctx bindings))
       (x2 (l3-trans-expr patp expr2 ctx bindings)))
      (trans-value (if patp
                       `(,x1 . ,x2)
                     `(cons ,x1 ,x2)))))
    (('ll ('sqbkt . lst))
     (trans-er-let*
      ((x (l3-trans-expr-lst patp lst ctx bindings)))
      (trans-value (cond (patp ; (not (equal patp nil))
                          lst)
                         (t (cons 'list x))))))
    (('var s &)
     (l3-trans-sym s ctx bindings))
    (('avar &)
; Anthony expects that user code will only generate avar terms within case
; expressions.
     (trans-value '&))
    (('lc s &) ; enumerated type constant
     (trans-er-let*
      ((sym (l3-trans-sym s ctx bindings)))
      (trans-value (kwote sym))))
    (('const s &) ; non-enumerated type constant, or a def0-defined constant
     (trans-er-let*
      ((const (l3-trans-constant s ctx bindings)))
      (cond (const ; def0 case
             (trans-value const))
            (t (trans-er-let*
                ((sym (l3-trans-sym s ctx bindings)))
                (trans-value (kwote sym)))))))
    (('lw i &)
     (trans-value i))
    (('tp ('sqbkt . args))
     (trans-er-let*
      ((lst (l3-trans-expr-lst patp args ctx bindings)))
      (trans-value
       (cond
        (patp lst)
        (t (mv-let (let-sym bs new-lst)
                   (lift-st$-lst args lst)
                   (cond ((null let-sym) (cons 'tuple lst))
                         ((eq let-sym t) (cons 'mv lst))
                         (t `(,let-sym ,bs (mv ,@new-lst))))))))))
    (('ite . args)
     (trans-er-let*
      ((lst (l3-trans-expr-lst nil args ctx bindings)))
      (trans-value (cons 'if lst))))
    (('bop sym expr1 expr2)
; !! Should really cause an error here, and in many other analogous places, if
; patp is true, because we don't have a way of matching a function call (other
; than cons).
     (l3-trans-bop sym expr1 expr2 ctx bindings))
    (('mop mop expr)
     (l3-trans-mop mop expr ctx bindings))
    (('apply ('const s &) 'qvar)
     (trans-er-let*
      ((sym (l3-trans-sym s ctx bindings)))
      (trans-value `(,sym st$))))
    (('apply ('call s typ expr1) expr2)
     (trans-er-let*
      ((sym (l3-trans-sym s ctx bindings))
       (x1 (l3-trans-expr patp expr1 ctx bindings))
       (x2 (l3-trans-expr patp expr2 ctx bindings)))
      (cond ((eq sym 'raise-exception)
             (case-match typ
               (('ATy 'qTy ('PTy typ1 'qTy))
                (trans-er-let*
                 ((t1 (l3-trans-type-expr typ1 ctx bindings)))
                 (trans-value
                  (let ((type-term `(arb ,t1)))
                    (cond
                     ((eq x2 'st$)
                      `(,sym ,x1 ,type-term ,x2))
                     (t `(let ((st$ ,x2))
                           (,sym ,x1 ,type-term st$))))))))
               (& (trans-err ctx
                             "Unexpected type encountered for raise-exception ~
                              term:~|~x0"
                             l3-expr))))
            ((eq x2 'st$)
             (trans-value `(,sym ,x1 ,x2)))
            (t (trans-value `(let ((st$ ,x2))
                               (,sym ,x1 st$)))))))
    (('apply ('dest field & 'qvar) expr)
; !! Need to consider records other than the state record.
     (trans-er-let*
      ((sym (l3-trans-st$-field-name field t nil ctx bindings))
       (x (l3-trans-expr patp expr ctx bindings)))
      (trans-value `(,sym ,x st$))))
    (('dest field & 'qvar)
; !! Need to consider records other than the state record.
     (trans-er-let*
      ((sym (l3-trans-st$-field-name field nil nil ctx bindings)))
      (trans-value `(,sym st$))))
    (('rupd field ('tp ('sqbkt st$-expr
                               ('mop ('k1 &) init-expr))))

; !! Need to consider records other than the state record.  To elaborate:

; The above needs to be modified for the case that we are updating other than
; the state.  Probably we can just test, using expr-st$-out-p, whether st$-expr
; is a state expression.  If true, then use what's below.  If false, then think
; about what to use for the non-state case of record update.

; E.g.:
; (RUPD "R" (TP (SQBKT QVAR (MOP (K1 (FTY 7)) (LW 0 32)))))
; translates to:
; (map-update-r 0 st$)

     (trans-er-let*
      ((sym (l3-trans-st$-field-name field t 'map ctx bindings))
       (trans-st$-expr (l3-trans-expr patp st$-expr ctx bindings))
       (trans-init-expr (l3-trans-expr patp init-expr ctx bindings)))
      (trans-value
       (lift-st$ `(,sym ,trans-init-expr ,trans-st$-expr) 2))))
    (('rupd field ('tp ('sqbkt st$-expr
                               ('Fupd ('Dest field & 'qVar)
                                      index
                                      value))))
; !! Need to consider records other than the state record.
; See comment for first rupd case above.
     (trans-er-let*
      ((sym (l3-trans-st$-field-name field t t ctx bindings))
       (trans-st$-expr (l3-trans-expr patp st$-expr ctx bindings))
       (i (l3-trans-expr patp index ctx bindings))
       (v (l3-trans-expr patp value ctx bindings)))
      (trans-value (lift-st$ `(,sym ,i ,v ,trans-st$-expr) 3))))
    (('rupd field ('tp ('sqbkt st$-expr expr)))
; !! Need to consider records other than the state record.
; See comment for first rupd case above.
     (trans-er-let*
      ((sym (l3-trans-st$-field-name field nil t ctx bindings))
       (trans-st$-expr (l3-trans-expr patp st$-expr ctx bindings))
       (v (l3-trans-expr patp expr ctx bindings)))
      (trans-value (lift-st$ `(,sym ,v ,trans-st$-expr) 2))))
    (('call s typ expr)
     (trans-er-let*
      ((sym (l3-trans-sym s ctx bindings))
       (x (l3-trans-expr patp expr ctx bindings))
       (trans-typ (l3-trans-type-expr typ ctx bindings)))
      (case-match typ
        (('cty &)
         (cond ((member-eq sym
                           (cdr (assoc-eq trans-typ
                                          (construct-alist bindings))))
                (trans-value
                 (cond (patp `(',sym ,x))
                       (t `(call-constructor ,trans-typ ,sym ,x)))))
               (patp (trans-err ctx
                                "We do not know how to translate this ~
                                 function call into a case-match+ ~
                                 pattern:~|~x0"
                                l3-expr))
               (t (trans-value `(,sym ,x)))))
        (& (cond (patp (trans-err ctx
                                  "We do not know how to translate this ~
                                   function call into a case-match+ ~
                                   pattern:~|~x0"
                                  l3-expr))
                 (t (trans-value `(,sym ,x))))))))
    (('cs case-expr ('sqbkt . clauses))
     (trans-er-let*
      ((typ (l3-get-type l3-expr ctx bindings))
       (x (l3-trans-expr patp case-expr ctx bindings))
       (c (l3-trans-cs-clauses clauses typ ctx bindings)))
      (trans-value `(case-match+ ,x ,@c))))
    (('let expr0 expr1 expr2)
     (trans-er-let*
      ((x1 (l3-trans-expr patp expr1 ctx bindings))
       (x2 (l3-trans-expr patp expr2 ctx bindings)))
      (let ((stobjs-out (term-stobjs-out x1 nil (bw bindings))))
        (case-match expr0
          (('tp ('sqbkt . lst))
           (let ((let-macro (cond
                             ((and (consp x1)
                                   (eq (car x1) 'bl))
                              'mv-let-ignorable)
                             ((or (and (consp stobjs-out)
                                       (consp (cdr stobjs-out)))
                                  (member-eq 'qvar lst))
                              'mv-let)
                             (t 'slet))))
             (trans-er-let*
              ((x0 (l3-trans-expr-lst nil lst ctx bindings)))
              (trans-value `(,let-macro ,x0 ,x1 ,x2)))))
          (& (cond ((and (consp stobjs-out)
                         (consp (cdr stobjs-out)))
                    (trans-err ctx
                               "Attempted to bind non-tuple expression,~|  ~
                                ~x0,~|to expression generating stobjs-out = ~
                                ~x1:~|~x2"
                               expr0 stobjs-out expr1))
                   (t (trans-er-let*
                       ((x0 (l3-trans-expr patp expr0 ctx bindings)))
                       (trans-value
                        (case-match x2
                          (('let (b) body)
                           `(let* ((,x0 ,x1) ,b) ,body))
                          (('let* bs body)
                           `(let* ((,x0 ,x1) ,@bs) ,body))
                          (& `(let ((,x0 ,x1)) ,x2))))))))))))
    (('cc ('sqbkt . lst))
     (trans-er-let*
      ((x (l3-trans-cc-exprs lst ctx bindings)))
      (trans-value (cons 'cat x))))
    (('bl n expr)
     (cond ((natp n)
            (trans-er-let*
             ((x (l3-trans-expr patp expr ctx bindings)))
             (trans-value `(bl ,n ,x))))
           (t (trans-err ctx
                         "The first argument of BL is expected to be a natp, ~
                          which is not the case for:~|~x0."
                         l3-expr))))
    (('ex expr0 expr1 expr2 &)
     (trans-er-let*
      ((x0 (l3-trans-expr patp expr0 ctx bindings))
       (x1 (l3-trans-expr patp expr1 ctx bindings))
       (x2 (l3-trans-expr patp expr2 ctx bindings)))
      (trans-value `(bits ,x0 ,x1 ,x2))))
    (('ln n) ; only for l3-trans-expr (not for l3-get-type)
     (trans-value n))
    (('eq expr1 expr2)
     (trans-er-let*
      ((x1 (l3-trans-expr patp expr1 ctx bindings))
       (x2 (l3-trans-expr patp expr2 ctx bindings)))
      (let ((eq-sym (cond ((or (case-match x1
                                 (('quote sym)
                                  (symbolp sym)))
                               (case-match x2
                                 (('quote sym)
                                  (symbolp sym))))
                           'eq)
                          ((or (acl2-numberp x1)
                               (acl2-numberp x2))
                           'eql)
                          (t 'equal))))
        (trans-value `(,eq-sym ,x1 ,x2)))))
    (& (trans-err ctx
                  "Unrecognized expression: ~x0"
                  l3-expr))))

(defun l3-trans-cs-clauses (clauses typ ctx bindings)

; Note that typ is a translated type.

  (declare (xargs :stobjs bindings))
  (trans-er-let*
   ((trans-clauses (l3-trans-cs-clauses-rec clauses ctx bindings)))
   (let* ((cl (car (last trans-clauses)))
          (tst (car cl)))
     (cond ((eq tst '&)
            (trans-value trans-clauses))
           (t (trans-value
               (append trans-clauses
                       `((& (impossible

; Here we assume that if the processor state st$ is returned, then it is
; returned as st$ or (mv .. st$).

                             ,(case-match typ
                                ('qty 'st$)
                                ((t0 'qty)
                                 `(mv (arb ,t0) st$))
                                (&
                                 `(arb ,typ)))))))))))))

(defun l3-trans-cs-clauses-rec (clauses ctx bindings)
  (declare (xargs :stobjs bindings))
  (cond ((endp clauses)
         (trans-value nil))
        (t (trans-er-let*
            ((tst (l3-trans-expr t (caar clauses) ctx bindings))
             (val (l3-trans-expr nil (cadar clauses) ctx bindings))
             (rst (l3-trans-cs-clauses-rec (cdr clauses) ctx bindings)))
            (trans-value (cons (list tst val) rst))))))

(defun l3-trans-bop (bop expr1 expr2 ctx bindings)
  (declare (xargs :stobjs bindings))
  (trans-er-let*
   ((type (l3-get-type expr1 ctx bindings))
    (texpr1 (l3-trans-expr nil expr1 ctx bindings))
    (texpr2 (l3-trans-expr nil expr2 ctx bindings)))
   (case bop
     ((Add Sub Mul Bit)
      (case-match type
        (('unsigned-byte n) ; ((quote unsigned-byte) n)
         (let ((fn (cdr (or (assoc-eq bop
                                      '((add . n+)
                                        (sub . n-)
                                        (mul . n*)
                                        (bit . logbitp)))
                            (er hard ctx
                                "Implementation error for bop: ~x0"
                                bop)))))
           (trans-value `(,fn ,n ,texpr1 ,texpr2))))
        (& (trans-err ctx
                      "Illegal ~x0 type:~|~x1"
                      type))))
     ((BAnd BOr BXor
            Lt Gt Le Ge
            And Or)
      (let ((fn (cdr (or (assoc-eq bop
                                   '((band . logand)
                                     (bor . logior)
                                     (bxor . logxor)
                                     (lt . <)
                                     (gt . >)
                                     (le . <=)
                                     (ge . >=)
                                     (and . and)
                                     (or . or)))
                         (er hard ctx
                             "Implementation error for bop: ~x0"
                             bop)))))
        (trans-value `(,fn ,texpr1 ,texpr2))))
     (Ror (trans-value `(ash ,texpr1
                             ,(cond ((natp texpr2)
                                     (- texpr2))
                                    (t (list '- texpr2))))))
     (otherwise (trans-err ctx
                           "Unimplemented bop: ~x0"
                           bop)))))

(defun l3-trans-mop (mop expr ctx bindings)
; Keep in sync with l3-get-type-mop.
  (declare (xargs :stobjs bindings))
  (trans-er-let*
   ((from-type (l3-get-type expr ctx bindings))
    (trans-expr (l3-trans-expr nil expr ctx bindings)))
   (case-match mop
     ('length (trans-value (list 'len trans-expr)))
     ('bnot (trans-value (list 'lognot trans-expr)))
     ('not (trans-value (list 'not trans-expr)))
     ('fst (trans-value (list 'car trans-expr)))
     ('snd (trans-er-let*
            ((t1 (l3-get-type trans-expr ctx bindings)))
            (trans-value (list (case-match t1
                                 ((& &)
; second arg of input pair isn't itself a pair
                                  'cadr)
                                 (& 'cdr))
                               trans-expr))))
     (('cast to-type)
      (trans-er-let*
       ((to-type (l3-trans-type-expr to-type ctx bindings)))
       (trans-value `(cast (,from-type ,to-type) ,trans-expr))))
     (& (trans-err ctx
                   "Unimplemented mop for l3-trans-mop: ~x0"
                   mop)))))

(defun l3-trans-cc-exprs (lst ctx bindings)
  (declare (xargs :stobjs bindings))
  (cond ((endp lst) (trans-value nil))
        (t (trans-er-let*
            ((x (l3-trans-expr nil (car lst) ctx bindings))
             (n (l3-trans-width (car lst) ctx bindings))
             (rest (l3-trans-cc-exprs (cdr lst) ctx bindings)))
            (trans-value (list* x n rest))))))

(defun l3-trans-expr-lst (patp lst ctx bindings)
  (declare (xargs :stobjs bindings))
  (cond ((endp lst) (trans-value nil))
        (t (trans-er-let*
            ((x1 (l3-trans-expr patp (car lst) ctx bindings))
             (x2 (l3-trans-expr-lst patp (cdr lst) ctx bindings)))
            (trans-value (cons x1 x2))))))
)

(mutual-recursion

(defun l3-trans-formal (formal ctx bindings)
  (declare (xargs :stobjs bindings))
  (case-match formal
    (('tp ('sqbkt . formals))
     (l3-trans-formal-lst formals ctx bindings))
    (('var name typ)
     (trans-er-let*
      ((x (l3-trans-sym name ctx bindings))
       (typ (l3-trans-type-expr typ ctx bindings)))
      (trans-value (list x (type-expr x typ)))))
    ('qvar (trans-value 'st$))
    (& (trans-err ctx
                  "Unexpected formal passed to l3-trans-formal:~|~x0"
                  formal))))

(defun l3-trans-formal-lst (formals ctx bindings)
  (declare (xargs :stobjs bindings))
  (cond ((endp formals) (trans-value nil))
        (t (trans-er-let*
            ((x (l3-trans-formal (car formals) ctx bindings))
             (lst (l3-trans-formal-lst (cdr formals) ctx bindings)))
            (trans-value (cons x lst))))))
)

(defun l3-trans-def (name formal expr closep measure-expr ctx bindings)
  (declare (xargs :stobjs bindings))
  (trans-er-let*
   ((sym (l3-trans-sym name ctx bindings))
    (trans-formal (l3-trans-formal formal ctx bindings))
    (trans-expr (l3-trans-expr nil expr ctx bindings))
    (trans-measure-expr ; only used if measure-expr is non-nil
     (if (null measure-expr)
         (trans-value nil) ; arbitrary
       (l3-trans-expr nil measure-expr ctx bindings))))
   (trans-value `(defun-struct ,sym
                   ,(if closep
                        `(,trans-formal st$)
                      `(,trans-formal))
                   ,@(and measure-expr
                          `(:measure ,trans-measure-expr))
                   ,@(and (or closep (eq 'st$ trans-formal))
                          '((declare (xargs :stobjs st$))))
                   ,trans-expr))))

(defun sym-to-const (str)
  (intern
   (concatenate 'string "*" (string-upcase str) "*")
   "ACL2"))

(defun l3-trans-def0 (name expr ctx bindings)
  (declare (xargs :stobjs bindings))
  (let ((sym (sym-to-const name)))
    (cond ((assoc-eq sym (const-to-str bindings))
           (trans-err ctx
                      "Apparently def0 was applied to two strings with the ~
                       same upper-case, ~x0 and ~x1.  A workaround is not yet ~
                       implemented, but probably could be."
                      (cdr (assoc-eq sym (const-to-str bindings)))
                      name))
          (t (let* ((bindings (update-str-to-const
                               (acons name sym (str-to-const bindings))
                               bindings))
                    (bindings (update-const-to-str
                               (acons sym name (const-to-str bindings))
                               bindings)))
               (trans-er-let*
                ((trans-expr (l3-trans-expr nil expr ctx bindings)))
                (trans-value `(defconst ,sym
                                ,trans-expr))))))))

(defmacro chk-pass1p (when-pass1-p-true form)
  (declare (xargs :guard (booleanp when-pass1-p-true)))
  `(cond ((eq pass1p ,when-pass1-p-true) ,form)
         (t (trans-value nil))))

(defun main-state-name-p (name)
  (equal name "state"))

(defun l3-to-acl2-fn3 (pass1p input-list ctx bindings state acc)
  (declare (xargs :stobjs (bindings state)))
  (cond
   ((endp input-list)
    (mv nil
        (if pass1p acc (reverse acc))
        bindings
        state))
   (t
    (let ((x (l3-reparse (car input-list))))
      (mv-let
       (erp form bindings)
       (case-match x
         (('val '_ '= 'Construct
                ('sqbkt (name ('sqbkt . clauses))))
          (chk-pass1p t (l3-trans-construct name clauses ctx bindings)))
         (('val '_ '= 'Record
                (name ('sqbkt . fields)))
          (chk-pass1p t
                      (if (main-state-name-p name)
                          (l3-trans-st$ fields ctx bindings)
                        (l3-trans-record name fields ctx bindings))))
         (('Def "raise'exception" . &)
          (chk-pass1p
           t
           (trans-value
            '(value-triple
              "See l3.lisp for the definition of raise-exception"))))
         (('def name formal
                ('Close 'qVar expr))
          (chk-pass1p nil
                      (l3-trans-def name formal expr t nil ctx bindings)))
         (('def name formal expr)
          (chk-pass1p nil
                      (l3-trans-def name formal expr nil nil ctx bindings)))
         (('tdef name formal
                 ('close 'qvar expr)
                 ('close ('var var-name &)
                         ('cs ('var var-name &)
                              ('sqbkt (('tp ('sqbkt . &))
                                       measure-expr)))))
          (declare (ignore var-name))
          (chk-pass1p nil
                      (l3-trans-def name formal expr t measure-expr ctx
                                    bindings)))
         (('def0 name expr)
          (chk-pass1p nil
                      (l3-trans-def0 name expr ctx bindings)))
         (& (trans-err ctx
                       "Unexpected input form:~|~x0"
                       x)))
       (cond
        (erp (mv-let
              (erp2 val2 state)
              (er soft erp
                  "Translation problem for ~x0: ~@1"
                  x form)
              (declare (ignore erp2 val2))
              (l3-to-acl2-fn3 pass1p (cdr input-list) ctx bindings state
                              (cons `(value-triple (list :error ,x))
                                    acc))))
        (t (l3-to-acl2-fn3 pass1p (cdr input-list) ctx bindings state
                           (if form
                               (cons form acc)
                             acc)))))))))

(defun l3-to-acl2-fn2 (input-list str-to-sym logic-p ctx bindings state)
  (declare (xargs :stobjs (bindings state)))
  (mv-let
   (erp initial-acc bindings)
   (initialize-bindings str-to-sym (w state) ctx bindings)
   (cond
    (erp (mv-let (erp2 val2 state)
                 (cmp-to-error-triple (mv erp initial-acc))
                 (declare (ignore erp2 val2))
                 (mv erp initial-acc bindings state)))
    (t (mv-let
        (erp1 new-acc bindings state)
        (l3-to-acl2-fn3 t input-list ctx bindings state initial-acc)
        (mv-let
         (erp2 result bindings state)
         (l3-to-acl2-fn3 nil input-list ctx bindings state
                         (cond ((null logic-p)
                                (cons '(program) new-acc))
                               ((eq logic-p :logic-only) ; not guard-verified
                                (cons '(set-verify-guards-eagerness 0)
                                      new-acc))
                               (t new-acc)))
         (mv (or erp1 erp2) result bindings state)))))))

(defun l3-to-acl2-fn1 (input-list str-to-sym logic-p ctx state)
  (declare (xargs :stobjs state))
  (with-local-stobj
   bindings
   (mv-let
    (erp val bindings state)
    (l3-to-acl2-fn2 input-list str-to-sym logic-p ctx bindings state)
    (mv erp val state))))

(include-book "misc/file-io" :dir :system)

(defconst *l3-book-path*
  "projects/translators/l3-to-acl2/translator/l3")

(defun l3-to-acl2-fn (infile outfile logic-p str-to-sym form state)
  (declare (xargs :stobjs state))
  (er-let* ((ctx (value 'l3-to-acl2)) ; (ctx (mv nil 'l3-to-acl2 state))
            (input-list (read-file infile state))
            (output-list (l3-to-acl2-fn1 input-list str-to-sym logic-p ctx
                                         state)))
    (write-list (list* '(in-package "ACL2")
                       `(value-triple '(:generated-by ,form))
                       `(include-book ,*l3-book-path* :dir :system)
                       output-list)
                outfile
                ctx
                state)))

(defmacro l3-to-acl2 (&whole form infile outfile &key logic str-to-sym)
  `(l3-to-acl2-fn ,infile ,outfile ,logic ,str-to-sym ',form state))
