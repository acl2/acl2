; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")       ; for parse-top-exp-from-string etc.
(include-book "printer")                ; for print-expr and print-file

(include-book "std/util/defmacro-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Parser tests.
;;
;; Each test is a single `assert-event' (see the test macros below), so
;; this book fails to certify if the parser, abstractor, or printer ever
;; drift from these expectations.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ test-parse (src expected)
  :parents (parsing-and-printing)
  :short "Test that a standalone Remora expression parses to an expected
          AST and that the AST round-trips through the printer."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('src') is a string of Remora source for a standalone expression;
     @('expected') is the expected @(tsee expr) AST, built with
     @('make-') constructors.  The expansion is an @(tsee assert-event)
     that checks two things:")
   (xdoc::ol
    (xdoc::li
     "@(tsee parse-top-exp-from-string) on @('src') yields
      @('expected');")
    (xdoc::li
     "printing @('expected') with @(tsee print-expr) and re-parsing
      yields @('expected') again (a print/parse round trip)."))
   (xdoc::p
    "To keep the work minimal, each intermediate result is bound once:
     the source is parsed once, the AST is printed once, and that
     printout is parsed once for the round trip (two parses and one
     print per test).  A failing check reports the offending values
     with @(tsee cw)."))
  `(assert-event
    (let* ((expected ,expected)
           (parsed   (parse-top-exp-from-string ,src))       ; parse #1
           (reparsed (parse-top-exp-from-string (print-expr expected)))) ; print + parse #2
      (and (or (equal parsed expected)
               (cw "~%test-parse FAILED (parse) ~x0~%  got:      ~x1~%  expected: ~x2~%"
                   ,src parsed expected))
           (or (equal reparsed expected)
               (cw "~%test-parse FAILED (round trip) ~x0~%  re-parsed: ~x1~%  expected:  ~x2~%"
                   ,src reparsed expected))))))

(defmacro+ test-roundtrip (src)
  :parents (parsing-and-printing)
  :short "Test that a standalone Remora expression parses and that the
          resulting AST round-trips through the printer."
  :long
  (xdoc::topstring
   (xdoc::p
    "Like @(tsee test-parse), but without an expected AST, for cases
     where we don't want to bother constructing the AST by hand:
     the expansion is an @(tsee assert-event) that checks only that
     @(tsee parse-top-exp-from-string) on @('src') succeeds and that
     printing the resulting AST with @(tsee print-expr) and re-parsing
     yields the same AST.  A failing check reports the offending values
     with @(tsee cw)."))
  `(assert-event
    (let* ((parsed (parse-top-exp-from-string ,src)))        ; parse #1
      (or (and (not (reserrp parsed))
               (equal (parse-top-exp-from-string (print-expr parsed)) ; print + parse #2
                      parsed))
          (cw "~%test-roundtrip FAILED: ~x0~%  parsed to: ~x1~%" ,src parsed)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Small helpers for building expected ASTs.

;; The integer atom whose decimal digits are DIGITS, e.g. (int-atom '(#\4 #\2))
;; is the atom 42.
(define int-atom ((digits str::dec-digit-char-listp))
  :guard (consp digits)
  :returns (a atomp)
  (make-atom-base :lit (make-base-lit-int :lit (make-int-lit :digits digits))))

;; A bare integer literal in *expression* position.  Per the grammar, an atom
;; used as an expression is abstracted to an `expr-atom', preserving the
;; information that it was written as an atom; a later desugaring pass turns it
;; into the rank-0 (scalar) array (array [] <atom>).
(define int-expr ((digits str::dec-digit-char-listp))
  :guard (consp digits)
  (make-expr-atom :atom (int-atom digits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Arrays and frames.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ---- Empty arrays: (array <shape> <element-type>) -> :array-empty ----

;; The motivating example: a 0-length array of Int.
(test-parse "(array [0] Int)"
            (make-expr-array-empty
             :dims '(0)
             :type (make-type-base :type (base-type-int))))

;; An empty array can have several dimensions as long as one of them is 0
;; (the parser is permissive about this; the 0-dim requirement is a semantic
;; check, not a syntactic one -- see the (array [2] Int) test below).
(test-parse "(array [3 0 1] Int)"
            (make-expr-array-empty
             :dims '(3 0 1)
             :type (make-type-base :type (base-type-int))))

;; The element type can be any base type.
(test-parse "(array [0] Bool)"
            (make-expr-array-empty
             :dims '(0)
             :type (make-type-base :type (base-type-bool))))

(test-parse "(array [0] Float)"
            (make-expr-array-empty
             :dims '(0)
             :type (make-type-base :type (base-type-float))))

;; The "must contain a 0 dimension" rule is NOT enforced at parse time: this
;; parses fine to :array-empty; the well-formedness/semantics reject it later.
(test-parse "(array [2] Int)"
            (make-expr-array-empty
             :dims '(2)
             :type (make-type-base :type (base-type-int))))

;; The element type may be a compound type; the AST is verbose, so we only
;; round-trip these (we don't check against hand-created AST).
(test-roundtrip "(array [0] (A Int [3]))")      ; array-of-arrays element type
(test-roundtrip "(array [0] *t)")               ; array type variable
(test-roundtrip "(array [0] (-> (Int) Bool))")  ; function element type

;; The array-type index is an ispace: a bare dim stays an ispace :dim,
;; whereas (dims d) is an ispace :shape holding a singleton dims shape.
;; So (A Int 3) and (A Int (dims 3)) intentionally abstract to different
;; ASTs (they are to be unified later, during desugaring).
(test-parse "(array [0] (A Int 3))"
            (make-expr-array-empty
             :dims '(0)
             :type (make-type-array
                    :elem (make-type-base :type (base-type-int))
                    :ispace (make-ispace-dim
                             :dim (make-dim-const :val 3)))))
(test-parse "(array [0] (A Int (dims 3)))"
            (make-expr-array-empty
             :dims '(0)
             :type (make-type-array
                    :elem (make-type-base :type (base-type-int))
                    :ispace (make-ispace-shape
                             :shape (make-shape-dims
                                     :dims (list (make-dim-const
                                                  :val 3)))))))

;; A dim variable, shape variable, and bracket splice as the array index
;; all parse and round-trip.
(test-roundtrip "(array [0] (A Int $d))")       ; dim-variable index
(test-roundtrip "(array [0] (A Int @s))")       ; shape-variable index
(test-roundtrip "(array [0] (A Int [3 4]))")    ; bracket-splice index

;; ---- Non-empty arrays: (array <shape> <atom> ...) -> :array ----

;; A vector of two integers.
(test-parse "(array [2] 3 4)"
            (make-expr-array
             :dims '(2)
             :atoms (list (int-atom '(#\3)) (int-atom '(#\4)))))

;; A scalar (rank-0) array written explicitly.
(test-parse "(array [] 5)"
            (make-expr-array
             :dims nil
             :atoms (list (int-atom '(#\5)))))

;; Multi-digit literals.
(test-parse "(array [3] 10 20 30)"
            (make-expr-array
             :dims '(3)
             :atoms (list (int-atom '(#\1 #\0))
                          (int-atom '(#\2 #\0))
                          (int-atom '(#\3 #\0)))))

;; Zero atoms with *no* element type is rejected: the non-empty `array'
;; form requires at least one atom (1*( ws atom )), and the empty form
;; requires a type.  The Haskell implementation rejects this identically.
(assert-event
 (reserrp (parse-top-exp-from-string "(array [0])")))

;; ---- Empty frames: (frame <shape> <element-type>) -> :frame-empty ----

(test-parse "(frame [0] Int)"
            (make-expr-frame-empty
             :dims '(0)
             :type (make-type-base :type (base-type-int))))

(test-parse "(frame [2 0] Bool)"
            (make-expr-frame-empty
             :dims '(2 0)
             :type (make-type-base :type (base-type-bool))))

;; ---- Non-empty frames: (frame <shape> <expr> ...) -> :frame ----

;; Frame cells are expressions (here, variable references).
(test-parse "(frame [2] x y)"
            (make-expr-frame
             :dims '(2)
             :exprs (list (make-expr-var :name "x")
                          (make-expr-var :name "y"))))

;; A bare integer cell is a scalar array expression (see int-expr).
(test-parse "(frame [1] 7)"
            (make-expr-frame
             :dims '(1)
             :exprs (list (int-expr '(#\7)))))

;; Frame cells that are themselves arrays.
(test-roundtrip "(frame [2] (array [2] 1 2) (array [2] 3 4))")

;; Bracket notation is sugar for a frame; it parses to :bracket (desugaring to
;; :frame happens in a later pass), and round-trips through the printer.
(test-parse "[0 3]"
            (make-expr-bracket
             :exprs (list (int-expr '(#\0))
                          (int-expr '(#\3)))))
(test-roundtrip "[1 2 3]")

;; Note, currently the only place "[]" can occur is in shape and shape-lit.
;; We plan to add tests for that.

;; ---- Let bindings: ispace-bind -> :ispace ----

;; An ispace binding aliasing a dimension.
(test-parse "(let ((ispace $d 3)) 0)"
            (make-expr-let
             :binds (list (make-bind-ispace
                           :var (make-ispace-var-dim :name "d")
                           :ispace (make-ispace-dim
                                    :dim (make-dim-const :val 3))))
             :body (int-expr '(#\0))))

;; Dimension arithmetic and shape aliases in ispace bindings round-trip.
(test-roundtrip "(let ((ispace $d (+ 5 (- 3)))) 0)")
(test-roundtrip "(let ((ispace @s [2 3])) 0)")

;; ---- Arrow types: single argument type without parentheses ----

;; (-> T R) abbreviates (-> (T) R): both abstract to the same :fun AST
;; with a singleton input list.
(test-parse "(array [0] (-> Int Bool))"
            (make-expr-array-empty
             :dims '(0)
             :type (make-type-funn
                    :in (list (make-type-base :type (base-type-int)))
                    :out (make-type-base :type (base-type-bool)))))

;; A single argument type that itself starts with "(" backtracks out of
;; the parenthesized-list alternative and parses as one type.
(test-roundtrip "(array [0] (-> (A Int 3) Int))")
(test-roundtrip "(array [0] (-> (-> Int Int) Int))")
(test-roundtrip "(array [0] (-> [Int 3] Int))")

;; ---- Combined application (@) with no value arguments ----

;; The value arguments of the @ sugar may be absent entirely, leaving
;; just the instantiation: (@iota/static _ ([5])) means
;; (i-app iota/static [5]).  The :capp AST records an empty args list.
(test-parse "(@iota/static _ ([5]))"
            (make-expr-capp
             :fun (make-expr-var :name "iota/static")
             :targs (type-list-option-none)
             :iargs (make-ispace-list-option-some
                     :val (list (make-ispace-shape
                                 :shape (make-shape-splice
                                         :ispaces (list
                                                   (make-ispace-dim
                                                    :dim (make-dim-const
                                                          :val 5)))))))
             :args nil))

;; ---- Minimum arities ----
;;
;; The parameter/argument lists of these forms must be non-empty,
;; matching the Haskell implementation (which rejects every input
;; below); the exceptions, tested positively at the end, are the
;; @ sugar's value arguments (tested in the @ section below), the
;; parenthesized argument list of an arrow type, and the parameters
;; of fun/t-fun/i-fun let bindings.

(assert-event
 (reserrp (parse-top-exp-from-string "(let ((val f (fn () 3))) 0)")))
(assert-event
 (reserrp (parse-top-exp-from-string "(let ((val f (t-fn () 3))) 0)")))
(assert-event
 (reserrp (parse-top-exp-from-string "(let ((val f (i-fn () 3))) 0)")))
(assert-event
 (reserrp (parse-top-exp-from-string "(let () 3)")))
(assert-event
 (reserrp (parse-top-exp-from-string "(let ((val b (box () 3 Int))) 0)")))
(assert-event
 (reserrp (parse-top-exp-from-string "(array [2])")))
(assert-event
 (reserrp (parse-top-exp-from-string "(frame [2])")))
(assert-event
 (reserrp (parse-top-exp-from-string "(f)")))
(assert-event
 (reserrp (parse-top-exp-from-string "(t-app f)")))
(assert-event
 (reserrp (parse-top-exp-from-string "(i-app f)")))
(assert-event
 (reserrp (parse-top-exp-from-string "(array [0] (Forall () Int))")))
(assert-event
 (reserrp (parse-top-exp-from-string "(array [0] (Pi () Int))")))
(assert-event
 (reserrp (parse-top-exp-from-string "(array [0] (Sigma () Int))")))

;; A zero-argument arrow type IS legal (the implementation's arrow
;; parser uses a possibly-empty parenthesized list).
(test-roundtrip "(array [0] (-> () Int))")

;; Zero-parameter fun/t-fun/i-fun let bindings are also legal
;; (their signatures use possibly-empty parameter lists).
(test-roundtrip "(let ((fun (f) 3)) 0)")
(test-roundtrip "(let ((t-fun (f () : Int) 3)) 0)")
(test-roundtrip "(let ((i-fun (f () : Int) 3)) 0)")

;; ---- Unbox expressions ----

;; A single-witness unbox round-trips.
(test-roundtrip
 "(unbox ($d xs (box (3) [1 2 3] (Sigma ($n) [Int $n]))) 0)")

;; Multiple witnesses are allowed.
(test-roundtrip
 "(unbox ($m $n xs (box (2 3) [1 2 3] (Sigma ($a $b) [Int $b]))) 0)")

;; A zero-witness unbox is rejected: the grammar requires at least one
;; ispace-var (1*( ispace-var ws ) in unbox-spec), as does the Haskell
;; implementation.
(assert-event
 (reserrp (parse-top-exp-from-string
           "(unbox (x (box (3) [1 2 3] (Sigma ($n) [Int $n]))) 0)")))

;; A value binder that is ispace-var-shaped (an identifier starting
;; with "$") is consumed by the greedy ispace-var repetition, so the
;; parse fails; the Haskell implementation rejects this identically.
;; See side condition [SC4] in grammar.abnf.
(assert-event
 (reserrp (parse-top-exp-from-string
           "(unbox ($d $x (box (3) [1 2 3] (Sigma ($n) [Int $n]))) 0)")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Source files: imports and declarations.
;;
;; These use the file-level pipeline (parse-from-string, print-file)
;; rather than the standalone-expression one, via analogous test macros.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ test-parse-file (src expected)
  :parents (parsing-and-printing)
  :short "Test that a Remora source file parses to an expected AST and
          that the AST round-trips through the printer."
  :long
  (xdoc::topstring
   (xdoc::p
    "File-level analogue of @(tsee test-parse):
     @('src') is a string with the contents of a Remora source file
     (imports followed by declarations);
     @('expected') is the expected @(tsee file) AST.
     The expansion is an @(tsee assert-event) that checks that
     @(tsee parse-from-string) on @('src') yields @('expected'),
     and that printing @('expected') with @(tsee print-file) and
     re-parsing yields @('expected') again.
     A failing check reports the offending values with @(tsee cw)."))
  `(assert-event
    (let* ((expected ,expected)
           (parsed   (parse-from-string ,src))               ; parse #1
           (reparsed (parse-from-string (print-file expected)))) ; print + parse #2
      (and (or (equal parsed expected)
               (cw "~%test-parse-file FAILED (parse) ~x0~%  got:      ~x1~%  expected: ~x2~%"
                   ,src parsed expected))
           (or (equal reparsed expected)
               (cw "~%test-parse-file FAILED (round trip) ~x0~%  re-parsed: ~x1~%  expected:  ~x2~%"
                   ,src reparsed expected))))))

(defmacro+ test-roundtrip-file (src)
  :parents (parsing-and-printing)
  :short "Test that a Remora source file parses and that the resulting
          AST round-trips through the printer."
  :long
  (xdoc::topstring
   (xdoc::p
    "File-level analogue of @(tsee test-roundtrip), without an expected
     AST: the expansion is an @(tsee assert-event) that checks only that
     @(tsee parse-from-string) on @('src') succeeds and that printing
     the resulting AST with @(tsee print-file) and re-parsing yields the
     same AST.  A failing check reports the offending values with
     @(tsee cw)."))
  `(assert-event
    (let* ((parsed (parse-from-string ,src)))                ; parse #1
      (or (and (not (reserrp parsed))
               (equal (parse-from-string (print-file parsed)) ; print + parse #2
                      parsed))
          (cw "~%test-roundtrip-file FAILED: ~x0~%  parsed to: ~x1~%" ,src parsed)))))

;; ---- Degenerate files ----

;; A file may be empty: zero imports and zero declarations.
(test-parse-file "" (make-file :imports nil :decls nil))

;; Or contain only whitespace and comments.
(test-parse-file "  ; nothing to see here"
                 (make-file :imports nil :decls nil))

;; ---- Imports ----

;; An import is the import keyword and a string literal (the path).
(test-parse-file "(import \"lib\")"
                 (make-file
                  :imports (list (make-import
                                  :path (list (make-char-lit-char
                                               :code (char-code #\l))
                                              (make-char-lit-char
                                               :code (char-code #\i))
                                              (make-char-lit-char
                                               :code (char-code #\b)))))
                  :decls nil))

(test-roundtrip-file "(import \"dotlib.remora\") (import \"more.remora\")")

;; ---- Declarations: def ----

;; A def wraps any of the let-style binding forms.
(test-parse-file "(def (val y 2))"
                 (make-file
                  :imports nil
                  :decls (list (make-decl-def
                                :bind (make-bind-val
                                       :var "y"
                                       :type? (type-option-none)
                                       :expr (int-expr '(#\2)))))))

;; A typed val bind and a fun bind, def0.remora style.
(test-roundtrip-file "(def (fun (add (x Int) (y Int) : Int) (+ x y)))
                      (def (val (x : Int) 1))")

;; A def wrapping a combined polymorphic function binding (@-form),
;; dotlib.remora style.
(test-roundtrip-file
 "(def (fun (@dot (&t) ($n)
             (plus (-> (&t &t) &t))
             (mul (-> (&t &t) &t))
             (x [&t $n]) (y [&t $n]) : &t)
    (@reduce (&t) ((- $n 1) []) plus (mul x y))))")

;; ---- Declarations: entry ----

;; A minimal entry point: no parameters, no return type.
(test-parse-file "(entry (main) 0)"
                 (make-file
                  :imports nil
                  :decls (list (make-decl-entry
                                :var "main"
                                :params nil
                                :type? (type-option-none)
                                :expr (int-expr '(#\0))))))

;; Entry with parameters and a return type.
(test-roundtrip-file "(entry (main (x Int) (y Int) : Int) (+ x y))")

;; ---- Whole files: imports, defs, and an entry together ----

(test-roundtrip-file
 "(import \"dotlib.remora\")
  (def (val y 10))
  (entry (main)
    (@dot (Float) (3) f.+ f.* [1.0 2.0 3.0] [4.0 5.0 6.0]))")
