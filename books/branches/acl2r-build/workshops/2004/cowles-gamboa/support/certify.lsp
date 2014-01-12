(ubt! 1)

(defpkg "TAIL-REC"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "tail-rec" 1)

:u :u

(defpkg "WyoM1"
  (set-difference-equal
   (union-eq '(ASSOC-EQUAL LEN NTH ZP SYNTAXP
                           QUOTEP FIX NFIX E0-ORDINALP E0-ORD-<)
             (union-eq
	      *acl2-exports*
	      *common-lisp-symbols-from-main-lisp-package*))
   '(PC PROGRAM PUSH POP REVERSE STEP ++)))

(certify-book "WyoM1" 1)

:u :u

(include-book "WyoM1")

(certify-book "WyoM1-utilities" 1)

:u :u

(include-book "WyoM1-utilities")

(certify-book "WyoM1-correct" 1)

:u :u

(certify-book "knuth")

:u
