; C++ Syntax Extension for ACL2 Kestrel C Library
;
; Pretty-printer: converts a cpp-expr AST to a readable Lisp s-expression.
;
; Usage (in an ACL2 session after including this book):
;
;   (b* ((dialect  (c::make-dialect :std (c::standard-c17)))
;        (parstate (c$::init-parstate "" (acl2::string=>nats "5 % 7 * 8")
;                                     dialect nil parstate))
;        ((mv erp ast & parstate) (parse-cpp-expr parstate)))
;     (cpp-expr-to-sexpr ast))
;   =>  (* (REM 5 7) 8)
;
; Or use the convenience wrapper:
;
;   (parse-and-pretty "5 * 7 % 8" parstate)
;   =>  (mv '(REM (* 5 7) 8) parstate)
;
; Operator mapping to Lisp symbols:
;   Arithmetic:   * / rem + -                 (standard ACL2 names; % is REM)
;   Shifts:       << >>
;   Relational:   < > <= >= == !=
;   Bitwise:      logand logxor logior
;   Logical:      and or
;   Assignment:   := += -= *= /= %= &= |= ^= <<= >>=   (right-associative)
;   Ternary:      (if test then else)                   (right-associative)
;   Comma:        (progn lhs rhs)
;   Prefix unary: unary+ - not lognot deref &  ++ --
;   Postfix:      post++ post--

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integer constant -> ACL2 integer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Decimal and octal constants yield an ACL2 integer; a hexadecimal constant
;; yields (:hex <digit-chars>) since its chars may include letters.
(define cpp-iconst-to-value ((ic c$::iconstp))
  :returns (val)
  (b* ((core (c$::iconst->core ic)))
    (c$::dec/oct/hex-const-case core
      :dec (c$::dec/oct/hex-const-dec->value core)
      :oct (c$::dec/oct/hex-const-oct->value core)
      :hex (cons :hex (c$::dec/oct/hex-const-hex->digits core)))))

;; Lift a c$::const (integer, float, enum, or char literal) to a value.
(define cpp-const-to-value ((c c$::constp))
  :returns (val)
  (c$::const-case c
    :int   (cpp-iconst-to-value (c$::const-int->iconst c))
    :float :float-const
    :enum  (list :enum (ident->unwrap (c$::const-enum->ident c)))
    :char  :char-const))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operator-to-symbol helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cpp-binop-to-symbol ((op c$::binopp))
  :returns (sym symbolp)
  (c$::binop-case op
    :mul     '*
    :div     '/
    :rem     'rem      ; C++ % is truncating remainder, not mathematical modulo
    :add     '+
    :sub     '-
    :shl     '<<
    :shr     '>>
    :lt      '<
    :gt      '>
    :le      '<=
    :ge      '>=       ; also stands in for <=> (spaceship): deliberate approx.
    :eq      '==
    :ne      '!=
    :bitand  'logand
    :bitxor  'logxor
    :bitior  'logior
    :logand  'and
    :logor   'or
    :otherwise '\?\?))

(define cpp-assign-op-to-symbol ((op cpp-assign-op-p))
  :returns (sym symbolp)
  (cpp-assign-op-case op
    :simple  ':=
    :add     '+=
    :sub     '-=
    :mul     '*=
    :div     '/=
    :rem     '%=
    :bitand  '&=
    :bitor   '|\|=|
    :bitxor  '^=
    :lshift  '<<=
    :rshift  '>>=))

(define cpp-unop-to-symbol ((op c$::unopp))
  :returns (sym symbolp)
  (c$::unop-case op
    :plus    'unary+
    :minus   '-
    :lognot  'not
    :bitnot  'lognot
    :indir   'deref    ; pointer dereference *p
    :address '&        ; address-of &x
    :otherwise '\?\?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main pretty-printer (mutually recursive over expr and expr-list)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines cpp-expr-to-sexpr
  :short "Convert a @(tsee cpp-expr) AST to a Lisp s-expression."
  :ruler-extenders :all

  (define cpp-expr-to-sexpr ((expr cpp-expr-p))
    :returns (sexpr)
    :measure (cpp-expr-count expr)
    (cpp-expr-case expr
      :ident  (ident->unwrap expr.name)
      :const  (cpp-const-to-value expr.value)
      :string :string-literal
      :this   'this
      :paren  (cpp-expr-to-sexpr expr.inner)
      :scoped (list :scoped
                    (ident->unwrap expr.scope)
                    (cpp-expr-to-sexpr expr.inner))
      :arrsub     (list 'aref
                        (cpp-expr-to-sexpr expr.array)
                        (cpp-expr-to-sexpr expr.index))
      :call       (cons (cpp-expr-to-sexpr expr.fun)
                        (cpp-expr-list-to-sexpr expr.args))
      :member     (list :dot   (cpp-expr-to-sexpr expr.object)
                               (ident->unwrap expr.name))
      :memberp    (list :arrow (cpp-expr-to-sexpr expr.object)
                               (ident->unwrap expr.name))
      :dot-star   (list :dot-star
                        (cpp-expr-to-sexpr expr.lhs)
                        (cpp-expr-to-sexpr expr.rhs))
      :arrow-star (list :arrow-star
                        (cpp-expr-to-sexpr expr.lhs)
                        (cpp-expr-to-sexpr expr.rhs))
      :postinc    (list 'post++ (cpp-expr-to-sexpr expr.arg))
      :postdec    (list 'post-- (cpp-expr-to-sexpr expr.arg))
      :static-cast      (list 'static_cast      (cpp-expr-to-sexpr expr.arg))
      :dynamic-cast     (list 'dynamic_cast     (cpp-expr-to-sexpr expr.arg))
      :reinterpret-cast (list 'reinterpret_cast (cpp-expr-to-sexpr expr.arg))
      :const-cast       (list 'const_cast       (cpp-expr-to-sexpr expr.arg))
      :typeid-expr      (list 'typeid           (cpp-expr-to-sexpr expr.arg))
      :typeid-type      '(typeid :type)
      :c-cast           (list 'c-cast           (cpp-expr-to-sexpr expr.arg))
      :preinc       (list '++ (cpp-expr-to-sexpr expr.arg))
      :predec       (list '-- (cpp-expr-to-sexpr expr.arg))
      :unary        (list (cpp-unop-to-symbol expr.op)
                          (cpp-expr-to-sexpr expr.arg))
      :sizeof-expr  (list 'sizeof (cpp-expr-to-sexpr expr.arg))
      :sizeof-type  '(sizeof :type)
      :alignof-type '(alignof :type)
      :new          (list* 'new :type (cpp-expr-list-to-sexpr expr.args))
      :delete       (if expr.arrayp
                        (list 'delete[] (cpp-expr-to-sexpr expr.arg))
                      (list 'delete    (cpp-expr-to-sexpr expr.arg)))
      :rethrow      'rethrow
      :throw-expr   (list 'throw    (cpp-expr-to-sexpr expr.arg))
      :co-await     (list 'co_await (cpp-expr-to-sexpr expr.arg))
      :binary   (list (cpp-binop-to-symbol expr.op)
                      (cpp-expr-to-sexpr expr.lhs)
                      (cpp-expr-to-sexpr expr.rhs))
      :assign   (list (cpp-assign-op-to-symbol expr.op)
                      (cpp-expr-to-sexpr expr.lhs)
                      (cpp-expr-to-sexpr expr.rhs))
      :cond     (list 'if
                      (cpp-expr-to-sexpr expr.test)
                      (cpp-expr-to-sexpr expr.then)
                      (cpp-expr-to-sexpr expr.else))
      :comma    (list 'progn
                      (cpp-expr-to-sexpr expr.lhs)
                      (cpp-expr-to-sexpr expr.rhs))
      :lambda   :lambda))

  (define cpp-expr-list-to-sexpr ((exprs cpp-expr-listp))
    :returns (sexprs true-listp)
    :measure (cpp-expr-list-count exprs)
    (if (endp exprs)
        nil
      (cons (cpp-expr-to-sexpr (car exprs))
            (cpp-expr-list-to-sexpr (cdr exprs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Convenience wrapper (interactive; guards not verified)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parse INPUT as a C++ expression and return its pretty-printed s-expression.
;; Returns (:parse-error input) on a parse error.
(define parse-and-pretty ((input stringp) (parstate parstatep))
  :returns (mv (sexpr)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :verify-guards nil
  (b* ((dialect  (c::make-dialect :std (c::standard-c17)))
       (parstate (c$::init-parstate ""
                                    (acl2::string=>nats input)
                                    dialect
                                    nil
                                    parstate))
       ((mv erp ast & parstate) (parse-cpp-expr parstate))
       ((when erp) (mv (list :parse-error input) parstate)))
    (mv (cpp-expr-to-sexpr ast) parstate)))
