(|f|)
(C::*PROGRAM*-WELL-FORMED)
(|f-RETURNS-VALUE|)
(|f-EXEC-CONST-LIMIT-CORRECT| (560 1
                                   (:REWRITE C::EXEC-BLOCK-ITEM-LIST-UNROLL))
                              (15 15
                                  (:REWRITE C::NOT-ERRORP-WHEN-VALUE-LISTP))
                              (15 15
                                  (:REWRITE C::NOT-ERRORP-WHEN-SCOPE-LISTP))
                              (15 15
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-5))
                              (15 15
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-4))
                              (15 15
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-3))
                              (15 15
                                  (:REWRITE C::EXEC-EXPR-PURE-UNROLL-2))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-USHORTP))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-ULONGP))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-ULLONGP))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-UINTP))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-UCHARP))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-SSHORTP))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-SLONGP))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-SLLONGP))
                              (12 12 (:REWRITE C::NOT-SINTP-WHEN-SCHARP))
                              (11 11
                                  (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
                              (11 11
                                  (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
                              (11 11
                                  (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
                              (11 11
                                  (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
                              (11 11 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
                              (11 11
                                  (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
                              (11 11 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
                              (11 11
                                  (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-8))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-7))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-6))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-5))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-4))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-3))
                              (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-2))
                              (7 7 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
                              (7 7 (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
                              (7 7 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
                              (7 7 (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
                              (7 7
                                 (:REWRITE C::NOT-POINTERP-WHEN-USHORTP))
                              (7 7
                                 (:REWRITE C::NOT-POINTERP-WHEN-ULONGP))
                              (7 7
                                 (:REWRITE C::NOT-POINTERP-WHEN-ULLONGP))
                              (7 7 (:REWRITE C::NOT-POINTERP-WHEN-UINTP))
                              (7 7
                                 (:REWRITE C::NOT-POINTERP-WHEN-UCHARP))
                              (7 7
                                 (:REWRITE C::NOT-POINTERP-WHEN-SSHORTP))
                              (7 7
                                 (:REWRITE C::NOT-POINTERP-WHEN-SLONGP))
                              (7 7
                                 (:REWRITE C::NOT-POINTERP-WHEN-SLLONGP))
                              (7 7 (:REWRITE C::NOT-POINTERP-WHEN-SINTP))
                              (7 7
                                 (:REWRITE C::NOT-POINTERP-WHEN-SCHARP))
                              (6 6 (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
                              (6 6
                                 (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
                              (6 6 (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
                              (6 6
                                 (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
                              (6 6 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
                              (6 6 (:REWRITE C::EXEC-STMT-UNROLL-2))
                              (6 6 (:REWRITE C::EXEC-STMT-UNROLL-1))
                              (2 1 (:REWRITE C::INIT-SCOPE-BASE-2))
                              (1 1 (:REWRITE C::NOT-UCHARP-WHEN-USHORTP))
                              (1 1 (:REWRITE C::NOT-UCHARP-WHEN-UINTP))
                              (1 1 (:REWRITE C::NOT-UCHARP-WHEN-SSHORTP))
                              (1 1 (:REWRITE C::NOT-UCHARP-WHEN-SCHARP))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-8))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-7))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-6))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-5))
                              (1 1 (:REWRITE C::EXEC-STMT-BASE-4)))
(|f-EXEC-VAR-LIMIT-CORRECT|)
(C::|*PROGRAM*-f-CORRECT|)
