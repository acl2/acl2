; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test messages.

; The (show-msg ...) forms can be entered into the shell to observe the result.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro show-msg (msg)
  `(cw "~@0~%" ,msg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(show-msg (char-to-msg nil))

(show-msg (char-to-msg 0))

(show-msg (char-to-msg 10))

(show-msg (char-to-msg 32))

(show-msg (char-to-msg 50))

(show-msg (char-to-msg 64))

(show-msg (char-to-msg 65))

(show-msg (char-to-msg 127))

(show-msg (char-to-msg 128))

(show-msg (char-to-msg 200))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(show-msg (token-to-msg (token-keyword "while")))

(show-msg (token-to-msg (token-ident (ident "a"))))

(show-msg (token-to-msg (token-const
                         (const-int
                          (iconst
                           (dec/oct/hex-const-dec 1)
                           nil)))))

(show-msg (token-to-msg (token-stringlit (stringlit nil nil))))

(show-msg (token-to-msg (token-punctuator "+")))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(show-msg (position-to-msg (position 1 0)))

(show-msg (position-to-msg (position 98 34)))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

(show-msg (span-to-msg (span (position 1 0) (position 6 90))))

(show-msg (span-to-msg (span (position 5 10) (position 5 15))))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test operations on positions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-init)
        (position 1 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-inc-column 1 (position 1 0))
        (position 1 1)))

(assert-event
 (equal (position-inc-column 1 (position 7 17))
        (position 7 18)))

(assert-event
 (equal (position-inc-column 8 (position 7 17))
        (position 7 25)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-inc-line 1 (position 1 0))
        (position 2 0)))

(assert-event
 (equal (position-inc-line 1 (position 20 0))
        (position 21 0)))

(assert-event
 (equal (position-inc-line 1 (position 20 44))
        (position 21 0)))

(assert-event
 (equal (position-inc-line 10 (position 20 44))
        (position 30 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test operations on spans.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (span-join (span (position 5 13) (position 5 17))
                   (span (position 5 20) (position 5 23)))
        (span (position 5 13) (position 5 23))))

(assert-event
 (equal (span-join (span (position 2 0) (position 2 10))
                   (span (position 4 10) (position 6 29)))
        (span (position 2 0) (position 6 29))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test simple operations on parser states.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-init-parstate (list)
  `(assert-event
    (equal (init-parstate ,list)
           (parstate ,list (position-init) nil nil nil nil nil))))

(test-init-parstate nil)

(test-init-parstate (list 1))

(test-init-parstate (list 1 2 3))

(test-init-parstate (acl2::string=>nats "abc"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (parsize (init-parstate nil)) 0))

(assert-event
 (equal (parsize (init-parstate (list 72 99 21))) 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test reading and unreading of characters.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event ; empty file
 (b* ((pstate0 (init-parstate nil))
      ((mv erp char? pos pstate) (read-char pstate0)))
   (and (not erp)
        (not char?)
        (equal pos (position 1 0)) ; just past end of (empty) file
        (equal pstate pstate0))))

(assert-event ; disallowed character 0
 (b* (((mv erp & & &) (read-char (init-parstate (list 0)))))
   erp))

(assert-event ; character 32
 (b* ((pstate0 (init-parstate (list 32 1 2 3)))
      ((mv erp char? pos pstate) (read-char pstate0)))
   (and (not erp)
        (equal char? 32)
        (equal pos (position 1 0))
        (equal pstate
               (change-parstate
                pstate0
                :bytes (list 1 2 3)
                :position (position 1 1)
                :chars-read (list (char+position 32 (position 1 0))))))))

(assert-event ; line feed
 (b* ((pstate0 (init-parstate (list 10 1 2 3)))
      ((mv erp char? pos pstate) (read-char pstate0)))
   (and (not erp)
        (equal char? 10)
        (equal pos (position 1 0))
        (equal pstate
               (change-parstate
                pstate0
                :bytes (list 1 2 3)
                :position (position 2 0)
                :chars-read (list (char+position 10 (position 1 0))))))))

(assert-event ; carriage return
 (b* ((pstate0 (init-parstate (list 13 1 2 3)))
      ((mv erp char? pos pstate) (read-char pstate0)))
   (and (not erp)
        (equal char? 10)
        (equal pos (position 1 0))
        (equal pstate
               (change-parstate
                pstate0
                :bytes (list 1 2 3)
                :position (position 2 0)
                :chars-read (list (char+position 10 (position 1 0))))))))

(assert-event ; carriage return + line feed
 (b* ((pstate0 (init-parstate (list 13 10 1 2 3)))
      ((mv erp char? pos pstate) (read-char pstate0)))
   (and (not erp)
        (equal char? 10)
        (equal pos (position 1 0))
        (equal pstate
               (change-parstate
                pstate0
                :bytes (list 1 2 3)
                :position (position 2 0)
                :chars-read (list (char+position 10 (position 1 0))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (b* ((pstate0 (init-parstate (list 65 66 67))) ; A B C
      ((mv erp1 char-a pos-a pstate1) (read-char pstate0))
      ((mv erp2 char-b pos-b pstate2) (read-char pstate1))
      (pstate3 (unread-char pstate2))
      ((mv erp4 char-b2 pos-b2 pstate4) (read-char pstate3))
      ((mv erp5 char-c pos-c pstate5) (read-char pstate4))
      ((mv erp6 char-eof pos-eof pstate6) (read-char pstate5)))
   (and (not erp1)
        (not erp2)
        (not erp4)
        (not erp5)
        (not erp6)
        (equal char-a 65)
        (equal char-b 66)
        (equal char-b2 66)
        (equal char-c 67)
        (equal char-eof nil)
        (equal pos-a (position 1 0))
        (equal pos-b (position 1 1))
        (equal pos-b2 (position 1 1))
        (equal pos-c (position 1 2))
        (equal pos-eof (position 1 3))
        (equal pstate1
               (change-parstate
                pstate0
                :bytes (list 66 67)
                :position (position 1 1)
                :chars-read (list (char+position 65 (position 1 0)))))
        (equal pstate2
               (change-parstate
                pstate1
                :bytes (list 67)
                :position (position 1 2)
                :chars-read (list (char+position 66 (position 1 1))
                                  (char+position 65 (position 1 0)))))
        (equal pstate3
               (change-parstate
                pstate2
                :chars-read (list (char+position 65 (position 1 0)))
                :chars-unread (list (char+position 66 (position 1 1)))))
        (equal pstate4
               (change-parstate
                pstate3
                :chars-read (list (char+position 66 (position 1 1))
                                  (char+position 65 (position 1 0)))
                :chars-unread nil))
        (equal pstate5
               (change-parstate
                pstate4
                :bytes nil
                :position (position 1 3)
                :chars-read (list (char+position 67 (position 1 2))
                                  (char+position 66 (position 1 1))
                                  (char+position 65 (position 1 0)))))
        (equal pstate6
               pstate5))))

(assert-event
 (b* ((pstate0 (init-parstate (list 65 10 66))) ; A LF B
      ((mv erp1 char-a pos-a pstate1) (read-char pstate0))
      ((mv erp2 char-nl pos-nl pstate2) (read-char pstate1))
      (pstate3 (unread-chars 2 pstate2))
      ((mv erp4 char-a2 pos-a2 pstate4) (read-char pstate3))
      ((mv erp5 char-nl2 pos-nl2 pstate5) (read-char pstate4))
      (pstate6 (unread-char pstate5))
      ((mv erp7 char-nl3 pos-nl3 pstate7) (read-char pstate6))
      ((mv erp8 char-b pos-b pstate8) (read-char pstate7))
      ((mv erp9 char-eof pos-eof pstate9) (read-char pstate8)))
   (and (not erp1)
        (not erp2)
        (not erp4)
        (not erp5)
        (not erp7)
        (not erp8)
        (not erp9)
        (equal char-a 65)
        (equal char-nl 10)
        (equal char-a2 65)
        (equal char-nl2 10)
        (equal char-nl3 10)
        (equal char-b 66)
        (equal char-eof nil)
        (equal pos-a (position 1 0))
        (equal pos-a2 (position 1 0))
        (equal pos-nl (position 1 1))
        (equal pos-nl2 (position 1 1))
        (equal pos-nl3 (position 1 1))
        (equal pos-b (position 2 0))
        (equal pos-eof (position 2 1))
        (equal pstate1
               (change-parstate
                pstate0
                :bytes (list 10 66)
                :position (position 1 1)
                :chars-read (list (char+position 65 (position 1 0)))))
        (equal pstate2
               (change-parstate
                pstate1
                :bytes (list 66)
                :position (position 2 0)
                :chars-read (list (char+position 10 (position 1 1))
                                  (char+position 65 (position 1 0)))))
        (equal pstate3
               (change-parstate
                pstate2
                :chars-read nil
                :chars-unread (list (char+position 65 (position 1 0))
                                    (char+position 10 (position 1 1)))))
        (equal pstate4
               (change-parstate
                pstate3
                :chars-read (list (char+position 65 (position 1 0)))
                :chars-unread (list (char+position 10 (position 1 1)))))
        (equal pstate5
               (change-parstate
                pstate4
                :chars-read (list (char+position 10 (position 1 1))
                                  (char+position 65 (position 1 0)))
                :chars-unread nil))
        (equal pstate6
               (change-parstate
                pstate5
                :chars-read (list (char+position 65 (position 1 0)))
                :chars-unread (list (char+position 10 (position 1 1)))))
        (equal pstate7
               (change-parstate
                pstate6
                :chars-read (list (char+position 10 (position 1 1))
                                  (char+position 65 (position 1 0)))
                :chars-unread nil))
        (equal pstate8
               (change-parstate
                pstate7
                :bytes nil
                :position (position 2 1)
                :chars-read (list (char+position 66 (position 2 0))
                                  (char+position 10 (position 1 1))
                                  (char+position 65 (position 1 0)))))
        (equal pstate9
               pstate8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Testing lexing functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lex-identifier/keyword

(assert-event
 (b* ((first-char (char-code #\w))
      (first-pos (position 8 3))
      (pstate (init-parstate (acl2::string=>nats " abc")))
      (pstate (change-parstate pstate :position (position 8 4)))
      ((mv erp lexeme span &)
       (lex-identifier/keyword first-char first-pos pstate)))
   (and (not erp)
        (equal lexeme (lexeme-token (token-ident (ident "w"))))
        (equal span (span (position 8 3) (position 8 3))))))

(assert-event
 (b* ((first-char (char-code #\u))
      (first-pos (position 8 3))
      (pstate (init-parstate (acl2::string=>nats "abc456")))
      (pstate (change-parstate pstate :position (position 8 4)))
      ((mv erp lexeme span &)
       (lex-identifier/keyword first-char first-pos pstate)))
   (and (not erp)
        (equal lexeme (lexeme-token (token-ident (ident "uabc456"))))
        (equal span (span (position 8 3) (position 8 9))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-parse (fn input &key cond)
  ;; optional COND may be over variables AST, SPAN, PSTATE
  ;; and also EOF-POS for PARSE-EXTERNAL-DECLARATION-LIST
  `(assert-event
    (b* ((,(if (eq fn 'parse-external-declaration-list)
               '(mv erp ?ast ?span ?eofpos ?pstate)
             '(mv erp ?ast ?span ?pstate))
          (,fn (init-parstate (acl2::string=>nats ,input)))))
      (if erp
          (cw "~@0" erp) ; CW returns NIL, so ASSERT-EVENT fails
        ,(or cond t))))) ; ASSERT-EVENT passes if COND is absent or else holds

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-cast-expression

(test-parse
 parse-cast-expression
 "0xFFFF"
 :cond (expr-case ast :const))

(test-parse
 parse-cast-expression
 "(uint32_t) x"
 :cond (expr-case ast :cast))

(test-parse
 parse-cast-expression
 "(T) (x)"
 :cond (expr-case ast :cast/call-ambig))

(test-parse
 parse-cast-expression
 "(T) * x"
 :cond (expr-case ast :cast/mul-ambig))

(test-parse
 parse-cast-expression
 "(T) + x"
 :cond (expr-case ast :cast/add-ambig))

(test-parse
 parse-cast-expression
 "(T) - x"
 :cond (expr-case ast :cast/sub-ambig))

(test-parse
 parse-cast-expression
 "(T) & x"
 :cond (expr-case ast :cast/and-ambig))

(test-parse
 parse-cast-expression
 "(A(B)) ++ (C) [3]"
 :cond (and (expr-case ast :cast/call-ambig)
            (equal (expr-cast/call-ambig->inc/dec ast)
                   (list (inc/dec-op-inc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-unary-expression

(test-parse
 parse-unary-expression
 "123")

(test-parse
 parse-unary-expression
 "sizeof y"
 :cond (expr-case ast :unary))

(test-parse
 parse-unary-expression
 "sizeof (x+y)"
 :cond (expr-case ast :unary))

(test-parse
 parse-unary-expression
 "sizeof (_Atomic(int))"
 :cond (expr-case ast :sizeof))

(test-parse
 parse-unary-expression
 "sizeof (var_or_tydef)"
 :cond (expr-case ast :sizeof-ambig))

(test-parse
 parse-unary-expression
 "sizeof(also(ambig))"
 :cond (expr-case ast :sizeof-ambig))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-postfix-expression

(test-parse
 parse-postfix-expression
 "var"
 :cond (expr-case ast :ident))

(test-parse
 parse-postfix-expression
 "var[4]"
 :cond (expr-case ast :arrsub))

(test-parse
 parse-postfix-expression
 "var[4].a->u(y,w)[q+e]"
 :cond (and (expr-case ast :arrsub)
            (expr-case (expr-arrsub->arg1 ast) :funcall)
            (expr-case (expr-arrsub->arg2 ast) :binary)))

(test-parse
 parse-postfix-expression
 "(int[]) { 1, 2, 3, }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-array/function-abstract-declarator

(test-parse
 parse-array/function-abstract-declarator
 "[]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[const]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[const _Atomic]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[*uu]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[*]"
 :cond (dirabsdeclor-case ast :array-star))

(test-parse
 parse-array/function-abstract-declarator
 "[80]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[restrict 80+0]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[static restrict 80+0]"
 :cond (dirabsdeclor-case ast :array-static1))

(test-parse
 parse-array/function-abstract-declarator
 "[restrict static 80+0]"
 :cond (dirabsdeclor-case ast :array-static2))

(test-parse
 parse-array/function-abstract-declarator
 "(id)"
 :cond (dirabsdeclor-case ast :function))

(test-parse
 parse-array/function-abstract-declarator
 "(int x, int y)"
 :cond (dirabsdeclor-case ast :function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-direct-abstract-declarator

(test-parse
 parse-direct-abstract-declarator
 "(*)"
 :cond (dirabsdeclor-case ast :paren))

(test-parse
 parse-direct-abstract-declarator
 "(*)[]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-direct-abstract-declarator
 "(*)[const _Atomic]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-direct-abstract-declarator
 "(*)[80]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-direct-abstract-declarator
 "(*)[80](int x, int y)"
 :cond (dirabsdeclor-case ast :function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-direct-declarator

(test-parse
 parse-direct-declarator
 "x"
 :cond (dirdeclor-case ast :ident))

(test-parse
 parse-direct-declarator
 "(x)"
 :cond (dirdeclor-case ast :paren))

(test-parse
 parse-direct-declarator
 "x[]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[10]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[a+b]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[const a+b]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[const volatile a+b]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[static a+b]"
 :cond (dirdeclor-case ast :array-static1))

(test-parse
 parse-direct-declarator
 "x[static const a+b]"
 :cond (dirdeclor-case ast :array-static1))

(test-parse
 parse-direct-declarator
 "x[const static a+b]"
 :cond (dirdeclor-case ast :array-static2))

(test-parse
 parse-direct-declarator
 "x[*]"
 :cond (dirdeclor-case ast :array-star))

(test-parse
 parse-direct-declarator
 "x[*y]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[restrict *]"
 :cond (dirdeclor-case ast :array-star))

(test-parse
 parse-direct-declarator
 "x[restrict *y]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[_Atomic static *y]"
 :cond (dirdeclor-case ast :array-static2))

(test-parse
 parse-direct-declarator
 "(a)(b)"
 :cond (dirdeclor-case ast :function-params))

(test-parse
 parse-direct-declarator
 "f(int, _Bool)"
 :cond (dirdeclor-case ast :function-params))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-abstract-declarator

(test-parse
 parse-abstract-declarator
 "[a[3]]"
 :cond (and (equal (absdeclor->pointers ast) nil)
            (dirabsdeclor-case (absdeclor->decl? ast) :array)))

(test-parse
 parse-abstract-declarator
 "(a)"
 :cond (and (equal (absdeclor->pointers ast) nil)
            (dirabsdeclor-case (absdeclor->decl? ast) :function)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-declarator

(test-parse
 parse-declarator
 "o")

(test-parse
 parse-declarator
 "*o")

(test-parse
 parse-declarator
 "*o[15]")

(test-parse
 parse-declarator
 "(*o)[15]")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-parameter-declaration

(test-parse
 parse-parameter-declaration
 "int x,"
 :cond (amb?-declor/absdeclor-case (paramdecl->decl ast) :declor))

(test-parse
 parse-parameter-declaration
 "int *x,"
 :cond (amb?-declor/absdeclor-case (paramdecl->decl ast) :declor))

(test-parse
 parse-parameter-declaration
 "int *,"
 :cond (amb?-declor/absdeclor-case (paramdecl->decl ast) :absdeclor))

(test-parse
 parse-parameter-declaration
 "int (x)(y))"
 :cond (amb?-declor/absdeclor-case (paramdecl->decl ast) :ambig))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-declarator-or-abstract-declarator

(test-parse
 parse-declarator-or-abstract-declarator
 "zzz,"
 :cond (amb?-declor/absdeclor-case ast :declor))

(test-parse
 parse-declarator-or-abstract-declarator
 "(*),"
 :cond (amb?-declor/absdeclor-case ast :absdeclor))

(test-parse
 parse-declarator-or-abstract-declarator
 "(h),"
 :cond (amb?-declor/absdeclor-case ast :ambig))

(test-parse
 parse-declarator-or-abstract-declarator
 "(h)[*],"
 :cond (amb?-declor/absdeclor-case ast :ambig))

(test-parse
 parse-declarator-or-abstract-declarator
 "(h)[*](uint32_t),"
 :cond (amb?-declor/absdeclor-case ast :ambig))

(test-parse
 parse-declarator-or-abstract-declarator
 "(h)[*](uint32_t)(T,T),"
 :cond (amb?-declor/absdeclor-case ast :ambig))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-expression-or-type-name

(test-parse
 parse-expression-or-type-name
 "abc)"
 :cond (amb?-expr/tyname-case ast :ambig))

(test-parse
 parse-expression-or-type-name
 "id(id))"
 :cond (amb?-expr/tyname-case ast :ambig))

(test-parse
 parse-expression-or-type-name
 "+x)"
 :cond (amb?-expr/tyname-case ast :expr))

(test-parse
 parse-expression-or-type-name
 "int *)"
 :cond (amb?-expr/tyname-case ast :tyname))

(test-parse
 parse-expression-or-type-name
 "a + b)"
 :cond (amb?-expr/tyname-case ast :expr))

(test-parse
 parse-expression-or-type-name
 "a _Atomic)"
 :cond (amb?-expr/tyname-case ast :tyname))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-block-item

(test-parse
 parse-block-item
 "idx = &((char*)session_peak())[i*BUFSIZE];")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-external-declaration-list

(test-parse
 parse-external-declaration-list
 "struct mystruct
{
   int *val;
};")

(test-parse
 parse-external-declaration-list
 "typedef void foo;
struct bar
{
 int val;
};")

(test-parse
 parse-external-declaration-list
 "int ith(int *a) {
 return a[0];
}")

(test-parse
 parse-external-declaration-list
 "int ith(int a[]) {
 return a[0];
}")

(test-parse
 parse-external-declaration-list
 "void foo (int val) {
 printf(\"Val = %d\\n\", val);
}")

(test-parse
 parse-external-declaration-list
 "int main() { }")

(test-parse
 parse-external-declaration-list
 "int foo (unsigned int v)
{
 return (v >> 1);
}")

(test-parse
 parse-external-declaration-list
 "void encrypt (uint32_t* v) {
}")

(test-parse
 parse-external-declaration-list
 "void encrypt () {
  uint32_t v0=1;
}")

(test-parse
 parse-external-declaration-list
 "void foo () {
  gen_config_t gen_config = {100};
}")

(test-parse
 parse-external-declaration-list
 "int A [] = {0,1,2,3};")

(test-parse
 parse-external-declaration-list
 "int spec_int(unsigned int v)
{
  unsigned int c;
  for (c = 0; v; v >>= 1)
    c += v & 1;
  return c;
}")

(test-parse
 parse-external-declaration-list
 "int sum(int a[], int n) {
  int s = 0;
  for (int i = 1; i <= n; ++i)
    s += a[i];
  return s;
}")

(test-parse
 parse-external-declaration-list
 "int foo (char x, char y) { return x < y && y < x; }")

(test-parse
 parse-external-declaration-list
 "int foo (int x, int y) { return x < y || y < x; }")

(test-parse
 parse-external-declaration-list
 "int foo (int x) { int z = 0 ; z &= x; }")

(test-parse
 parse-external-declaration-list
 "void foo () {
  while (x > y) {
    x++;
  }
}")

(test-parse
 parse-external-declaration-list
 "int foo () {
  int i = 0;
  i--;
}")

(test-parse
 parse-external-declaration-list
 "int main() {
 int a = 10, b = 5;
 a %= b;
}")

(test-parse
 parse-external-declaration-list
 "char string[] = \"\";")

(test-parse
 parse-external-declaration-list
 "void foo () {
  managedtask * newtask = (managedtask *) malloc(sizeof(managedtask));
}")

(test-parse
 parse-external-declaration-list
 "void foo () {
 idx = (arr)[3];
}")

(test-parse
 parse-external-declaration-list
 "void test(int i)
{
    y[i] = (i ? inv : src)[i];
}")

(test-parse
 parse-external-declaration-list
 "extern char *tmpnam (char[20]);")

(test-parse
 parse-external-declaration-list
 "extern int __uflow (FILE *);")

(test-parse
 parse-external-declaration-list
 "int c[1][2];")

(test-parse
 parse-external-declaration-list
 "struct A
{
  int c1, c2;
};")

(test-parse
 parse-external-declaration-list
 "long long foo () {
  return 1LL;
}")
