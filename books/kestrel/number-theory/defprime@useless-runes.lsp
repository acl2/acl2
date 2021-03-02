(PRIMES::DEFPRIME-FN (7 1
                        (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
                     (3 3 (:REWRITE DEFAULT-CDR))
                     (2 2
                        (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
                     (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
                     (2 2 (:REWRITE DEFAULT-CAR))
                     (2 1 (:REWRITE DEFAULT-PKG-IMPORTS))
                     (2 1
                        (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
                     (2 1 (:DEFINITION TRUE-LISTP))
                     (1 1
                        (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
                     (1 1
                        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
                     (1 1 (:REWRITE DEFAULT-<-2))
                     (1 1 (:REWRITE DEFAULT-<-1)))
