; Use with-supporters to just get the code of the Axe Basic Rewriter
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/with-supporters" :dir :system)

;; todo: also need to include all the calls of add-known-boolean (making sure
;; the functions are defined)

(with-supporters
 (local (include-book "rewriter-basic"))
 ;; things that with-supporters cannot determine are needed (feel free to
 ;; extend this list as needed to make this with-supporters command work):
 :names (acons-fast
         farg1 farg2 farg3 farg4
         call-of
         *print-when-expanding*
         erp-nil
         erp-t
         pairlis$-fast
         *max-fixnum*
         enquote
         *non-nil*
         *memoization-size*
         *syntactically-boolean-fns*
         *trimmable-non-arithmetic-operators*
         *trimmable-arithmetic-operators*
         *trimmable-operators*
         *operators-whose-size-we-know*
         *non-trimmable-bv-operators*
         *axe-invisible-fns-table*
         *unrelievable-hyp*
         *unrelievable-hyps*
         get-rules-for-fn
         pack-in-package-of-symbol
         pack$-fn)
 ;; TODO: This should not be needed:
 (defun simp-term-basic-wrapper (term assumptions
                                      rule-alist interpreted-function-alist
                                      monitored-symbols memoizep
                                      count-hits print normalize-xors wrld)
   (simp-term-basic term assumptions
                    rule-alist interpreted-function-alist
                    monitored-symbols memoizep
                    count-hits print normalize-xors wrld))

 ;;redundant, also helpful
 (DEFUN MAKE-RULE-ALIST! (RULE-NAMES WRLD)
   (DECLARE (XARGS :GUARD (AND (TRUE-LISTP RULE-NAMES)
                               (SYMBOL-LISTP RULE-NAMES)
                               (ILKS-PLIST-WORLDP WRLD))))
   (MV-LET (ERP RULE-ALIST)
     (MAKE-RULE-ALIST RULE-NAMES WRLD)
     (IF ERP
         (ER HARD? 'MAKE-RULE-ALIST!
             "Error making rule alist.")
         RULE-ALIST))))
