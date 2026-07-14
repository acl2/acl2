; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "parser-interface")
(include-book "printer")
(include-book "std/util/defmacro-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *ir-newline*
  (coerce (list #\Newline) 'string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ test-parse-ir (src expected)
  :parents (parsing-and-printing)
  :short "Test that Futhark IR source parses to an expected AST and
          that the expected AST round-trips through the printer."
  `(assert-event
    (let* ((expected ,expected)
           (parsed (parse-ir-from-string ,src))
           (printed (print-fut-program expected))
           (reparsed (parse-ir-from-string printed)))
      (and (or (equal parsed expected)
               (cw "~%test-parse-ir FAILED (parse) ~x0~%  got:      ~x1~%  expected: ~x2~%"
                   ,src parsed expected))
           (or (equal reparsed expected)
               (cw "~%test-parse-ir FAILED (round trip) ~x0~%  printed:  ~x1~%  re-parsed: ~x2~%  expected:  ~x3~%"
                   ,src printed reparsed expected))))))

(defmacro+ test-roundtrip-ir (src)
  :parents (parsing-and-printing)
  :short "Test that Futhark IR source parses and that the resulting
          AST round-trips through the printer."
  `(assert-event
    (let* ((parsed (parse-ir-from-string ,src)))
      (or (and (not (reserrp parsed))
               (equal (parse-ir-from-string (print-fut-program parsed))
                      parsed))
          (cw "~%test-roundtrip-ir FAILED: ~x0~%  parsed to: ~x1~%"
              ,src parsed)))))

(defmacro+ test-reject-parser (parser src)
  :parents (parsing-and-printing)
  :short "Test that a core parser rejects an invalid complete input."
  `(assert-event
    (b* (((mv tree rest) (,parser (string=>codepoints ,src))))
      (or (reserrp tree)
          (consp rest)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *basic0-fut-soacs*
"name_source {1010}
types {

}

fun
  v_1007 (x_97 : [2i64]i32,
          y_98 : [2i64]i32)
  : {[2i64]i32} = {
  let {v_1005 : [2i64]i32} =
    map(2i64,
        {x_97, y_98},
        \\ {v_1002 : i32,
           v_1003 : i32}
          : {i32} ->
          let {v_1004 : i32} =
            add32(v_1002, v_1003)
          in {v_1004})
  let {v_1006 : [2i64]i32} =
    v_1005
  in {v_1006}
}

entry(\"main\",
      {},
      {[]i32})
  entry_main ()
  : {[2i64]i32} = {
  let {v_1000 : [2i64]i32} =
    [1i32, 2i32] : []i32
  let {v_1001 : [2i64]i32} =
    [2i32, 4i32] : []i32
  let {v_1008 : [2i64]i32} =
    apply v_1007(v_1000, v_1001)
    : {[2i64]i32}
  let {v_1009 : [2i64]i32} =
    v_1008
  in {v_1009}
}")

(defconst *current-basic0-fut-soacs*
"name_source {144}
types {

}



fun
  v_141 (x_130 : [2i64]i32,
         y_131 : [2i64]i32)
  : {[2i64]i32} = {
  let {v_139 : [2i64]i32} =
    map(2i64,
        {x_130, y_131},
        \\ {v_135 : i32,
           v_136 : i32}
          : {i32} ->
          let {v_137 : i32} =
            add32(v_135, v_136)
          in {v_137},
        \\ {v_138 : i32}
          : {i32} ->
          {v_138})
  let {v_140 : [2i64]i32} =
    v_139
  in {v_140}
}

entry(\"main\",
      {},
      []i32)
  entry_main ()
  : {[2i64]i32} = {
  let {v_133 : [2i64]i32} =
    [1i32, 2i32] : []i32
  let {v_134 : [2i64]i32} =
    [2i32, 4i32] : []i32
  let {v_142 : [2i64]i32} =
    apply v_141(v_133, v_134)
    : {[2i64]i32}
  let {v_143 : [2i64]i32} =
    v_142
  in {v_143}
}")

(defconst *current-remora-forms-fut-soacs*
"types {

}

fun
  v_1 (x_1 : [2i64]i32)
  : {[2i64]i32} = {
  let {v_2 : [2i64]i32} =
    map(2i64,
        {x_1},
        \\ {v_3 : i32}
          : {i32} ->
          {v_3})
  in {v_2}
}

entry(\"main\",
      {},
      []i32)
  entry_main ()
  : {i32} = {
  {iota/static_88}
}")

(defconst *entry-result-types-edge-fut-soacs*
"types {

}

entry(\"zero\",
      {},
      {})
  entry_zero ()
  : {} = {
  {}
}

entry(\"pair\",
      {},
      {i32, i64})
  entry_pair ()
  : {i32, i64} = {
  {1i32, 2i64}
}")

(defconst *documented-entry-fut-soacs*
"types {

}

entry(\"main\",
      {},
      i32,
      \"Returns one value.\")
  entry_main ()
  : {i32} = {
  {1i32}
}")

(defconst *constructor-coverage-fut-soacs*
"name_source {77}
types {

}

fun
  f (x : i32,
     xs : [2i64]i32)
  : {i32, [2i64]i32} = {
  let {y : i32} =
    add32((x), 1i32)
  let {arr : [2i64]i32} =
    [y, 2i32] : []i32
  let {mapped : [2i64]i32} =
    map(2i64,
        {xs},
        \\ {z : i32}
          : {i32} ->
          {z})
  let {applied : i32} =
    apply g(y)
    : {i32}
  in {applied, mapped}
}

entry(\"main\\n\",
      {},
      {i32, []i32})
  entry_main ()
  : {i32, [2i64]i32} = {
  {f(3i32, [1i32, 2i32] : []i32)}
}")

(defconst *type-i32*
  (make-fut-type-prim :name "i32"))

(defconst *type-i64*
  (make-fut-type-prim :name "i64"))

(defconst *type-vector-i32*
  (make-fut-type-array :size "2i64" :elem *type-i32*))

(defconst *type-open-i32*
  (make-fut-type-array :size nil :elem *type-i32*))

(defconst *constructor-entry-result-expr*
  (make-expr-call
   :fun "f"
   :args
   (list
    (make-expr-literal :text "3i32")
    (make-expr-array
     :elems (list (make-expr-literal :text "1i32")
                  (make-expr-literal :text "2i32"))
     :type *type-i32*))))

(defconst *constructor-coverage-ast*
  (make-fut-program
   :name-source "77"
   :decls
   (list
    (make-decl-fun
     :name "f"
     :params (list (make-param :name "x" :type *type-i32*)
                   (make-param :name "xs" :type *type-vector-i32*))
     :result-types (list *type-i32* *type-vector-i32*)
     :body
     (make-body-block
      :stmts
      (list
       (make-stmt-let
        :pattern (list (make-param :name "y" :type *type-i32*))
        :expr (make-expr-call
               :fun "add32"
               :args (list (make-expr-paren
                            :expr (make-expr-var :name "x"))
                           (make-expr-literal :text "1i32"))))
       (make-stmt-let
        :pattern (list (make-param :name "arr" :type *type-vector-i32*))
        :expr (make-expr-array
               :elems (list (make-expr-var :name "y")
                            (make-expr-literal :text "2i32"))
               :type *type-i32*))
       (make-stmt-let
        :pattern (list (make-param :name "mapped" :type *type-vector-i32*))
        :expr (make-expr-map
               :args (list
                      (make-expr-literal :text "2i64")
                      (make-expr-brace
                       :elems (list (make-expr-var :name "xs")))
                      (make-expr-lambda
                       :params (list (make-param :name "z"
                                                 :type *type-i32*))
                       :result-types (list *type-i32*)
                       :body (make-body-block
                              :stmts nil
                              :results (list (make-expr-var
                                              :name "z")))))))
       (make-stmt-let
        :pattern (list (make-param :name "applied" :type *type-i32*))
        :expr (make-expr-apply
               :fun "g"
               :args (list (make-expr-var :name "y"))
               :result-types (list *type-i32*))))
      :results (list (make-expr-var :name "applied")
                     (make-expr-var :name "mapped"))))
    (make-decl-entry
     :external-name (str::cat "main" *ir-newline*)
     :entry-result-types (list *type-i32* *type-open-i32*)
     :name "entry_main"
     :params nil
     :result-types (list *type-i32* *type-vector-i32*)
     :body
     (make-body-block
      :stmts nil
      :results (list *constructor-entry-result-expr*))))))

(test-parse-ir *constructor-coverage-fut-soacs*
               *constructor-coverage-ast*)

(assert-event
 (b* ((program (parse-ir-from-string *basic0-fut-soacs*)))
   (and (not (reserrp program))
        (equal (fut-program->name-source program) "1010")
        (equal (len (fut-program->decls program)) 2))))

(assert-event
 (b* ((program (parse-ir-from-string *current-basic0-fut-soacs*)))
   (and (not (reserrp program))
        (equal (fut-program->name-source program) "144")
        (equal (len (fut-program->decls program)) 2))))

(assert-event
 (b* ((program (parse-ir-from-string *current-remora-forms-fut-soacs*)))
   (and (not (reserrp program))
        (equal (len (fut-program->decls program)) 2))))

(assert-event
 (b* ((program (parse-ir-from-string *entry-result-types-edge-fut-soacs*))
      ((when (reserrp program)) nil)
      (decls (fut-program->decls program))
      ((unless (and (consp decls)
                    (consp (cdr decls))
                    (endp (cddr decls))))
       nil)
      (zero-decl (car decls))
      (pair-decl (cadr decls)))
   (and (equal (decl-kind zero-decl) :entry)
        (equal (decl-entry->entry-result-types zero-decl) nil)
        (equal (decl-kind pair-decl) :entry)
        (equal (len (decl-entry->entry-result-types pair-decl)) 2))))

(assert-event
 (b* ((program (parse-ir-from-string *documented-entry-fut-soacs*))
      ((when (reserrp program)) nil)
      (decls (fut-program->decls program))
      ((unless (and (consp decls)
                    (endp (cdr decls))
                    (equal (decl-kind (car decls)) :entry)))
       nil)
      (decl (car decls)))
   (and (equal (decl-entry->doc decl) "Returns one value.")
        (equal (parse-ir-from-string (print-fut-program program))
               program))))

(assert-event
 (b* ((input (string=>codepoints *basic0-fut-soacs*))
      (tree (parse-ir-cst-from-codepoints input))
      ((when (reserrp tree)) nil))
   (equal (parser-symbols-to-nats (abnf::tree->string tree))
          input)))

(test-reject-parser parse-result-types "{i32,}")
(test-reject-parser parse-params "(x : i32,)")
(test-reject-parser parse-exp "{x,}")
(test-reject-parser parse-entry-result-types "{i32,}")
(test-reject-parser parse-entry-attr
                    "entry(\"x\", {}, {i32}, \"doc\")")
(test-reject-parser parse-type "[]i32")
(test-reject-parser parse-exp "[1i32]")
(test-reject-parser parse-exp "[1i32] : i32")
(test-reject-parser parse-exp "apply f(x)")
(test-reject-parser parse-exp
                    "map(2i64, {x})")
(test-reject-parser parse-exp
                    "map(2i64, {x}, \\ {y : i32} : {i32} -> {y}, x)")
(test-reject-parser parse-exp
                    (str::cat
                     "map(2i64, {x}, \\ {y : i32} : {i32} -> {y}, "
                     "\\ {z : i32} : {i32} -> {z}, "
                     "\\ {w : i32} : {i32} -> {w})"))
(test-reject-parser parse-exp
                    "map(2i64, {1i32}, \\ {y : i32} : {i32} -> {y})")

(assert-event
 (equal (print-expr
         (make-expr-apply :fun "f" :args nil :result-types nil))
        "apply f() : {}"))

(assert-event
 (and (ir-literal-tokenp "-1i32")
      (not (ir-name-tokenp "-1i32"))))

(assert-event
 (b* (((mv tree rest) (parse-exp (string=>codepoints "-1i32")))
      ((when (reserrp tree)) nil)
      ((unless (endp rest)) nil)
      (expr (abs-exp tree)))
   (and (not (reserrp expr))
        (equal expr (make-expr-literal :text "-1i32")))))

(assert-event
 (b* (((mv tree rest)
       (parse-string-lit (string=>codepoints "\"main\\n\"")))
      ((when (reserrp tree)) nil)
      ((unless (endp rest)) nil)
      (text (abs-string-lit tree)))
   (and (not (reserrp text))
        (equal text (str::cat "main" *ir-newline*)))))

(assert-event
 (equal (print-string-literal (str::cat "main" *ir-newline*))
        "\"main\\n\""))

(assert-event
 (equal (print-result-types
         (list (make-fut-type-prim :name "longtype")
               (make-fut-type-prim :name "other"))
         :width 10)
        (str::cat "{longtype,"
                  *ir-newline*
                  " other}")))

(defconst *unicode-entry-fut-soacs-codepoints*
  (append
   (string=>codepoints
    "types {

}

entry(\"")
   (append
    (list #x03C0)
    (append
     (string=>codepoints
      "\",
      {},
      i32)
  ")
     (append
      (list #x03C0)
      (string=>codepoints
       "_1 ()
  : {i32} = {
  {1i32}
}"))))))

(assert-event
 (b* ((source (codepoints=>string
               *unicode-entry-fut-soacs-codepoints*))
      ((when (reserrp source)) nil)
      (program (parse-ir-from-string source))
      ((when (reserrp program)) nil)
      (decls (fut-program->decls program))
      ((unless (and (consp decls)
                    (endp (cdr decls))
                    (equal (decl-kind (car decls)) :entry)))
       nil)
      (pi-string (codepoints=>string (list #x03C0)))
      ((when (reserrp pi-string)) nil)
      (pi-name (codepoints=>string (list #x03C0 #x5F #x31)))
      ((when (reserrp pi-name)) nil)
      (decl (car decls))
      (printed (print-fut-program program))
      (program2 (parse-ir-from-string printed)))
   (and (equal (decl-entry->external-name decl) pi-string)
        (equal (decl-entry->name decl) pi-name)
        (equal program2 program))))

(test-roundtrip-ir *basic0-fut-soacs*)

(test-roundtrip-ir *current-basic0-fut-soacs*)

(test-roundtrip-ir *current-remora-forms-fut-soacs*)

(test-roundtrip-ir *entry-result-types-edge-fut-soacs*)

(test-roundtrip-ir *documented-entry-fut-soacs*)
