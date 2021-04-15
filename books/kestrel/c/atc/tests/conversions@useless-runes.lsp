(|f|
 (200 8
      (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (166 26 (:REWRITE DEFAULT-CAR))
 (132 8 (:DEFINITION INTEGER-LISTP))
 (132 4 (:DEFINITION TRUE-LISTP))
 (96 8
     (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (92 12
     (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (60 4 (:DEFINITION LEN))
 (38 38
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
               . 2))
 (38 38
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP
               . 1))
 (38 38
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 2))
 (38 38
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 1))
 (38 38
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP
               . 2))
 (38 38
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP
               . 1))
 (38 38
     (:REWRITE C::CONSP-WHEN-MEMBER-EQUAL-OF-ATC-SYMBOL-TYPE-ALISTP
               . 2))
 (38 38
     (:REWRITE C::CONSP-WHEN-MEMBER-EQUAL-OF-ATC-SYMBOL-TYPE-ALISTP
               . 1))
 (38 38
     (:REWRITE C::CONSP-WHEN-MEMBER-EQUAL-OF-ATC-SYMBOL-FNINFO-ALISTP
               . 2))
 (38 38
     (:REWRITE C::CONSP-WHEN-MEMBER-EQUAL-OF-ATC-SYMBOL-FNINFO-ALISTP
               . 1))
 (34 34 (:REWRITE DEFAULT-CDR))
 (28 8
     (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (20 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (16
    16
    (:REWRITE TRUE-LISTP-OF-CDR-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP))
 (16
   16
   (:REWRITE TRUE-LISTP-OF-CDR-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP))
 (16 16 (:REWRITE DEFAULT-<-1))
 (16 8
     (:REWRITE C::SETP-WHEN-TYPE-OPTION-SETP))
 (16 8 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (16 8 (:REWRITE C::SETP-WHEN-IDENT-SETP))
 (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 8
    (:TYPE-PRESCRIPTION C::TYPE-OPTION-SETP))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (8 8 (:TYPE-PRESCRIPTION C::IDENT-SETP))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (8 8
    (:REWRITE TRUE-LISTP-WHEN-THEOREM-SYMBOL-LISTP))
 (8 8
    (:REWRITE TRUE-LISTP-WHEN-TERMFN-LISTP))
 (8 8
    (:REWRITE TRUE-LISTP-WHEN-MACRO-SYMBOL-LISTP))
 (8 8
    (:REWRITE TRUE-LISTP-WHEN-LAMBDA-LISTP))
 (8 8
    (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
 (8 8 (:REWRITE SET::IN-SET))
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1)))
(|g|)
(C::*PROGRAM*-WELL-FORMED)
(|f-RETURNS-VALUE|)
(|f-EXEC-CONST-LIMIT-CORRECT| (975 1
                                   (:REWRITE C::EXEC-BLOCK-ITEM-LIST-UNROLL))
                              (157 157 (:REWRITE C::VALUEP-WHEN-POINTERP))
                              (29 29 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
                              (29 29
                                  (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
                              (29 29 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
                              (29 29
                                  (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
                              (29 29
                                  (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
                              (25 25
                                  (:REWRITE C::NOT-ERRORP-WHEN-VALUE-LISTP))
                              (25 25
                                  (:REWRITE C::NOT-ERRORP-WHEN-UCHAR-ARRAYP))
                              (25 25
                                  (:REWRITE C::NOT-ERRORP-WHEN-SCOPE-LISTP))
                              (25 25
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-5))
                              (21 21
                                  (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
                              (21 21
                                  (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
                              (21 21
                                  (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
                              (21 21
                                  (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
                              (21 21
                                  (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
                              (21 21 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
                              (21 21
                                  (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
                              (21 21 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
                              (21 21
                                  (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
                              (21 21
                                  (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
                              (18 18
                                  (:REWRITE C::NOT-UCHARP-WHEN-USHORTP))
                              (18 18 (:REWRITE C::NOT-UCHARP-WHEN-UINTP))
                              (18 18
                                  (:REWRITE C::NOT-UCHARP-WHEN-SSHORTP))
                              (18 18 (:REWRITE C::NOT-UCHARP-WHEN-SCHARP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
                              (10 10 (:REWRITE C::NOT-SLONGP-WHEN-ULONGP))
                              (10 10
                                  (:REWRITE C::NOT-SLONGP-WHEN-ULLONGP))
                              (10 10
                                  (:REWRITE C::NOT-SLONGP-WHEN-SLLONGP))
                              (10 10
                                  (:REWRITE C::NOT-SLONGP-WHEN-POINTERP))
                              (10 10
                                  (:REWRITE C::NOT-SLLONGP-WHEN-ULONGP))
                              (10 10
                                  (:REWRITE C::NOT-SLLONGP-WHEN-ULLONGP))
                              (10 10
                                  (:REWRITE C::NOT-SLLONGP-WHEN-SLONGP))
                              (10 10
                                  (:REWRITE C::NOT-SLLONGP-WHEN-POINTERP))
                              (10 10
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-2))
                              (10 10
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-1))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-8))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-7))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-6))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-5))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-4))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-3))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-2))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
                              (6 6 (:REWRITE C::EXEC-STMT-UNROLL-2))
                              (6 6 (:REWRITE C::EXEC-STMT-UNROLL-1))
                              (4 1 (:REWRITE C::NOT-SINTP-WHEN-UCHARP))
                              (2 1 (:REWRITE C::INIT-SCOPE-BASE-2))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-USHORTP))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-ULONGP))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-ULLONGP))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-UINTP))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-SSHORTP))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-SLONGP))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-SLLONGP))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-SCHARP))
                              (1 1 (:REWRITE C::NOT-SINTP-WHEN-POINTERP))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-8))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-7))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-6))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-5))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-4)))
(|f-EXEC-VAR-LIMIT-CORRECT|)
(C::|*PROGRAM*-f-CORRECT|)
(|g-RETURNS-VALUE|)
(|g-EXEC-CONST-LIMIT-CORRECT| (512 1
                                   (:REWRITE C::EXEC-BLOCK-ITEM-LIST-UNROLL))
                              (64 64 (:REWRITE C::VALUEP-WHEN-POINTERP))
                              (20 17 (:REWRITE C::NOT-SINTP-WHEN-UCHARP))
                              (17 17 (:REWRITE C::NOT-SINTP-WHEN-USHORTP))
                              (17 17 (:REWRITE C::NOT-SINTP-WHEN-ULONGP))
                              (17 17 (:REWRITE C::NOT-SINTP-WHEN-ULLONGP))
                              (17 17 (:REWRITE C::NOT-SINTP-WHEN-UINTP))
                              (17 17 (:REWRITE C::NOT-SINTP-WHEN-SSHORTP))
                              (17 17 (:REWRITE C::NOT-SINTP-WHEN-SLONGP))
                              (17 17 (:REWRITE C::NOT-SINTP-WHEN-SLLONGP))
                              (17 17 (:REWRITE C::NOT-SINTP-WHEN-SCHARP))
                              (17 17
                                  (:REWRITE C::NOT-SINTP-WHEN-POINTERP))
                              (16 16
                                  (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
                              (16 16
                                  (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
                              (16 16
                                  (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
                              (16 16
                                  (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
                              (16 16
                                  (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
                              (16 16 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
                              (16 16
                                  (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
                              (16 16 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
                              (16 16
                                  (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
                              (16 16
                                  (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
                              (15 15
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-5))
                              (15 15
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-4))
                              (14 14
                                  (:REWRITE C::NOT-ERRORP-WHEN-VALUE-LISTP))
                              (14 14
                                  (:REWRITE C::NOT-ERRORP-WHEN-UCHAR-ARRAYP))
                              (14 14
                                  (:REWRITE C::NOT-ERRORP-WHEN-SCOPE-LISTP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
                              (11 11
                                  (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
                              (11 11 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
                              (11 11 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
                              (11 11 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
                              (11 11 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
                              (11 11
                                  (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
                              (11 11 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
                              (11 11
                                  (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
                              (11 11 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
                              (11 11
                                  (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
                              (11 11
                                  (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
                              (6 6 (:REWRITE C::EXEC-STMT-UNROLL-2))
                              (6 6 (:REWRITE C::EXEC-STMT-UNROLL-1))
                              (5 5 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-1))
                              (5 5 (:REWRITE C::EXEC-EXPR-PURE-BASE-8))
                              (5 5 (:REWRITE C::EXEC-EXPR-PURE-BASE-7))
                              (5 5 (:REWRITE C::EXEC-EXPR-PURE-BASE-6))
                              (5 5 (:REWRITE C::EXEC-EXPR-PURE-BASE-5))
                              (5 5 (:REWRITE C::EXEC-EXPR-PURE-BASE-4))
                              (5 5 (:REWRITE C::EXEC-EXPR-PURE-BASE-3))
                              (5 5 (:REWRITE C::EXEC-EXPR-PURE-BASE-2))
                              (2 1 (:REWRITE C::INIT-SCOPE-BASE-2))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-8))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-7))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-6))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-5))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-4)))
(|g-EXEC-VAR-LIMIT-CORRECT|)
(C::|*PROGRAM*-g-CORRECT|)
