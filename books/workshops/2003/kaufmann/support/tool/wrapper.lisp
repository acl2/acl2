(in-package "ACL2")

; This macro is developed to make it easy to call transform-defuns in the
; Makefile in support/rtl/, after ld-ing pkgs.lisp there.

(defmacro simplify-model ()
  (let* ((rel4 "rtl/rel4/")
         (rel4-lib (concatenate 'string rel4 "lib/"))
         (rel4-lib-top (concatenate 'string rel4-lib "top"))
         (rel4-support (concatenate 'string rel4 "support/"))
         (bvecp-helpers (concatenate 'string rel4-support "bvecp-helpers"))
         (simplify-model-helpers
          (concatenate 'string rel4-lib "simplify-model-helpers")))
    `(state-global-let*
      ((print-case :downcase set-print-case))
      (ld
       '((INCLUDE-BOOK
          "../tool/simplify-defuns")
         (INCLUDE-BOOK
          "bvecp-raw")
         (INCLUDE-BOOK
          ,rel4-lib-top :dir :system)
         (INCLUDE-BOOK
          ,simplify-model-helpers :dir :system)
         (DISABLE-FORCING)
         (TRANSFORM-DEFUNS
          "model-raw.lisp" *OLD2NEW-PKG-ALIST*
          :out-defs "model-defs.lisp"
          :defs-pre `((include-book
                       "ordinals/e0-ordinal" :dir :system)
                      (set-well-founded-relation e0-ord-<)
                      (SET-INHIBIT-WARNINGS "THEORY" "DISABLE" "NON-REC")
                      (INCLUDE-BOOK
                       "common")
                      (INCLUDE-BOOK
                       "model-macros")
                      (SET-IRRELEVANT-FORMALS-OK T)
                      (SET-IGNORE-OK T)
                      (DEFLABEL MODEL-START-OF-DEFS)
                      (SET-BOGUS-MUTUAL-RECURSION-OK T))
          :equalities "model-eq.lisp"
          :eq-pre '((LOCAL (INCLUDE-BOOK
                            "bvecp-raw"))
                    (LOCAL (INCLUDE-BOOK
                            ,rel4-lib-top :dir :system))
                    (LOCAL (INCLUDE-BOOK
                            ,simplify-model-helpers :dir :system))
                    (INCLUDE-BOOK
                     "model-raw")
                    (INCLUDE-BOOK
                     "model")

; We have seen cases where things blow up at %%P0-PROPERTY-LEMMA because of an
; attempt to untranslate during preprocess-clause with sigs-btree set.

                    (LOCAL (TABLE USER-DEFINED-FUNCTIONS-TABLE NIL NIL :clear))
                    (LOCAL (DISABLE-FORCING)))
          :thm-file-pairs
          '(("bvecp-raw.lisp"
             "bvecp.lisp"
             ((INCLUDE-BOOK
               "model")
              (LOCAL (INCLUDE-BOOK
                      "model-eq"))
              (LOCAL (INCLUDE-BOOK
                      "bvecp-raw"))
              (LOCAL (INCLUDE-BOOK
                      ,bvecp-helpers :dir :system)))))))))))
