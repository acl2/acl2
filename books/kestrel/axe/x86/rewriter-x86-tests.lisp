; Tests of the x86 Rewriter
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "rewriter-x86")
(include-book "x86-rules")
(include-book "std/testing/assert-bang" :dir :system)

(defmacro simp-term-x86-wrapper (term
                                  &key
                                  (assumptions 'nil)
                                  (rule-alist 'nil)
                                  (interpreted-function-alist 'nil)
                                  (known-booleans 'nil)
                                  (normalize-xors 'nil)
                                  (limits 'nil)
                                  (memoizep 't)
                                  (count-hits 't)
                                  (print 't)
                                  (monitored-symbols 'nil)
                                  (fns-to-elide 'nil))
  `(acl2::simp-term-x86 ,term
                        ,assumptions
                        ,rule-alist
                        ,interpreted-function-alist
                        ,known-booleans
                        ,normalize-xors
                        ,limits
                        ,memoizep
                        ,count-hits
                        ,print
                        ,monitored-symbols
                        ,fns-to-elide))

(acl2::assert!
  (mv-let (erp term)
    (simp-term-x86-wrapper
      '(write '1 '1000 xval (write '2 '2000 yval (write '1 '1000 other-val x86)))
      :rule-alist (acl2::make-rule-alist! '(write-becomes-write-of-clear-extend-axe
                                            clear-extend-of-write-continue-axe
                                            clear-extend-of-write-finish
                                            clear-extend-of-write-of-clear-retract ;clear-retract-of-write-of-clear-retract
                                            write-of-clear-retract)
                                          (w state)))
    (and (not erp)
         (equal term '(write '1 '1000 xval (write '2 '2000 yval x86))))))
