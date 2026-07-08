; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")       ; for parse-from-string
(include-book "printer")                ; for print-prog

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Parser tests.
;;
;; Each test checks two things:
;;   (1) parsing from a string to the expected AST, built with `make-'
;;       constructors;
;;   (2) printing the AST from (1) and re-parsing to yield the same AST
;;       (a print/parse round trip).
;;
;; Each test is a single `assert-event', so this book fails to certify if the
;; parser, abstractor, or printer ever drift from these expectations.  To keep
;; the work minimal, each macro binds its intermediate results once: the source
;; is parsed once, the AST is printed once, and that printout is parsed once for
;; the round trip (two parses and one print per test).  A failing check reports
;; the offending values with `cw'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests both correct parsing and print/parse round-trip.
(defmacro test-parse (src expected)
  `(assert-event
    (let* ((expected ,expected)
           (parsed   (parse-from-string ,src))               ; parse #1
           (reparsed (parse-from-string (print-prog expected)))) ; print + parse #2
      (and (or (equal parsed expected)
               (cw "~%test-parse FAILED (parse) ~x0~%  got:      ~x1~%  expected: ~x2~%"
                   ,src parsed expected))
           (or (equal reparsed expected)
               (cw "~%test-parse FAILED (round trip) ~x0~%  re-parsed: ~x1~%  expected:  ~x2~%"
                   ,src reparsed expected))))))

;; Tests that parse succeeds and print/parse round-trip,
;; but does not test against a hand-written AST,
;; for cases where we don't want to bother constructing the AST by hand.
(defmacro test-roundtrip (src)
  `(assert-event
    (let* ((parsed (parse-from-string ,src)))                ; parse #1
      (or (and (not (reserrp parsed))
               (equal (parse-from-string (print-prog parsed)) ; print + parse #2
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
            (make-prog
             :expr (make-expr-array-empty
                    :dims '(0)
                    :type (make-type-base :type (base-type-int)))))

;; An empty array can have several dimensions as long as one of them is 0
;; (the parser is permissive about this; the 0-dim requirement is a semantic
;; check, not a syntactic one -- see the (array [2] Int) test below).
(test-parse "(array [3 0 1] Int)"
            (make-prog
             :expr (make-expr-array-empty
                    :dims '(3 0 1)
                    :type (make-type-base :type (base-type-int)))))

;; The element type can be any base type.
(test-parse "(array [0] Bool)"
            (make-prog
             :expr (make-expr-array-empty
                    :dims '(0)
                    :type (make-type-base :type (base-type-bool)))))

(test-parse "(array [0] Float)"
            (make-prog
             :expr (make-expr-array-empty
                    :dims '(0)
                    :type (make-type-base :type (base-type-float)))))

;; The "must contain a 0 dimension" rule is NOT enforced at parse time: this
;; parses fine to :array-empty; the well-formedness/semantics reject it later.
(test-parse "(array [2] Int)"
            (make-prog
             :expr (make-expr-array-empty
                    :dims '(2)
                    :type (make-type-base :type (base-type-int)))))

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
            (make-prog
             :expr (make-expr-array-empty
                    :dims '(0)
                    :type (make-type-array
                           :elem (make-type-base :type (base-type-int))
                           :ispace (make-ispace-dim
                                    :dim (make-dim-const :val 3))))))
(test-parse "(array [0] (A Int (dims 3)))"
            (make-prog
             :expr (make-expr-array-empty
                    :dims '(0)
                    :type (make-type-array
                           :elem (make-type-base :type (base-type-int))
                           :ispace (make-ispace-shape
                                    :shape (make-shape-dims
                                            :dims (list (make-dim-const
                                                         :val 3))))))))

;; A dim variable, shape variable, and bracket splice as the array index
;; all parse and round-trip.
(test-roundtrip "(array [0] (A Int $d))")       ; dim-variable index
(test-roundtrip "(array [0] (A Int @s))")       ; shape-variable index
(test-roundtrip "(array [0] (A Int [3 4]))")    ; bracket-splice index

;; ---- Non-empty arrays: (array <shape> <atom> ...) -> :array ----

;; A vector of two integers.
(test-parse "(array [2] 3 4)"
            (make-prog
             :expr (make-expr-array
                    :dims '(2)
                    :atoms (list (int-atom '(#\3)) (int-atom '(#\4))))))

;; A scalar (rank-0) array written explicitly.
(test-parse "(array [] 5)"
            (make-prog
             :expr (make-expr-array
                    :dims nil
                    :atoms (list (int-atom '(#\5))))))

;; Multi-digit literals.
(test-parse "(array [3] 10 20 30)"
            (make-prog
             :expr (make-expr-array
                    :dims '(3)
                    :atoms (list (int-atom '(#\1 #\0))
                                 (int-atom '(#\2 #\0))
                                 (int-atom '(#\3 #\0))))))

;; Zero atoms with a 0 shape and *no* element type: this is the non-empty
;; `array' form with an empty atom list (distinct from :array-empty, which
;; carries a type).  Non-emptiness is a separate semantic check.
(test-parse "(array [0])"
            (make-prog
             :expr (make-expr-array :dims '(0) :atoms nil)))

;; ---- Empty frames: (frame <shape> <element-type>) -> :frame-empty ----

(test-parse "(frame [0] Int)"
            (make-prog
             :expr (make-expr-frame-empty
                    :dims '(0)
                    :type (make-type-base :type (base-type-int)))))

(test-parse "(frame [2 0] Bool)"
            (make-prog
             :expr (make-expr-frame-empty
                    :dims '(2 0)
                    :type (make-type-base :type (base-type-bool)))))

;; ---- Non-empty frames: (frame <shape> <expr> ...) -> :frame ----

;; Frame cells are expressions (here, variable references).
(test-parse "(frame [2] x y)"
            (make-prog
             :expr (make-expr-frame
                    :dims '(2)
                    :exprs (list (make-expr-var :name "x")
                                 (make-expr-var :name "y")))))

;; A bare integer cell is a scalar array expression (see int-expr).
(test-parse "(frame [1] 7)"
            (make-prog
             :expr (make-expr-frame
                    :dims '(1)
                    :exprs (list (int-expr '(#\7))))))

;; Frame cells that are themselves arrays.
(test-roundtrip "(frame [2] (array [2] 1 2) (array [2] 3 4))")

;; Bracket notation is sugar for a frame; it parses to :bracket (desugaring to
;; :frame happens in a later pass), and round-trips through the printer.
(test-parse "[0 3]"
            (MAKE-PROG
             :EXPR (MAKE-EXPR-BRACKET
                    :EXPRS (LIST
                            (MAKE-EXPR-ATOM
                             :ATOM (MAKE-ATOM-BASE
                                    :LIT (MAKE-BASE-LIT-INT
                                          :LIT (MAKE-INT-LIT
                                                :SIGN? NIL
                                                :DIGITS (LIST #\0)))))
                            (MAKE-EXPR-ATOM
                             :ATOM (MAKE-ATOM-BASE
                                    :LIT (MAKE-BASE-LIT-INT
                                          :LIT (MAKE-INT-LIT
                                                :SIGN? NIL
                                                :DIGITS (LIST #\3)))))))))
(test-roundtrip "[1 2 3]")

;; Note, currently the only place "[]" can occur is in shape and shape-lit.
;; We plan to add tests for that.

;; ---- Let bindings: ispace-bind -> :ispace ----

;; An ispace binding aliasing a dimension.
(test-parse "(let ((ispace $d 3)) 0)"
            (make-prog
             :expr (make-expr-let
                    :binds (list (make-bind-ispace
                                  :var (make-ispace-var-dim :name "d")
                                  :ispace (make-ispace-dim
                                           :dim (make-dim-const :val 3))))
                    :body (int-expr '(#\0)))))

;; Dimension arithmetic and shape aliases in ispace bindings round-trip.
(test-roundtrip "(let ((ispace $d (+ 5 (- 3)))) 0)")
(test-roundtrip "(let ((ispace @s [2 3])) 0)")
