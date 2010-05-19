
(in-package "ACL2")

(defpkg "POS"
  (union-eq *acl2-exports*
	    *common-lisp-symbols-from-main-lisp-package*))

(certify-book "prime-fac" 
	      1
	      )
:u :u

(DEFPKG "ACL2-ASG"
  (SET-DIFFERENCE-EQUAL
   (UNION-EQ *ACL2-EXPORTS* 
	     *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*)
   '(ZERO)))

(certify-book "ed1" 
	      1   
	      nil ;;compile-flg
	      )
:u :u

(certify-book "ed2a" 
	      0   
	      nil ;;compile-flg
	      )
:u

(certify-book "ed2b")
:u

(DEFPKG "ACL2-ASG"
  (SET-DIFFERENCE-EQUAL
   (UNION-EQ *ACL2-EXPORTS* 
	     *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*)
   '(ZERO)))

(DEFPKG "ACL2-AGP"
  (SET-DIFFERENCE-EQUAL
   (UNION-EQ *ACL2-EXPORTS* 
	     *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*)
   '(ZERO)))

(DEFPKG "ACL2-CRG"
  (SET-DIFFERENCE-EQUAL
   (UNION-EQ *ACL2-EXPORTS* 
	     *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*)
   '(ZERO)))

(certify-book "ed3"
	      3   
	      nil ;;compile-flg
	      )
:u :u :u :u

(defpkg "INT-MOD"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed4aa" 
	      1
	      nil ;;compile-flg
	      )
:u :u

(defpkg "INT-MOD"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed4ab" 
	      1)
:u :u

(defpkg "INT-REM"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed4ba" 
	      1
	      nil ;;compile-flg
	      )
:u :u

(defpkg "INT-REM"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed4bb" 
	      1)
:u :u

(defpkg "INT-C-MOD"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed4ca" 
	      1
	      nil ;;compile-flg
	      )
:u :u

(defpkg "INT-C-MOD"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed4cb" 
	      1)
:u :u

(defpkg "INT-RND-REM"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed4da" 
	      1
	      nil ;;compile-flg
	      )
:u :u

(defpkg "INT-RND-REM"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed4db" 
	      1
	      )
:u :u

(defpkg "GAUSS-INT"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "ed5aa" 
	      1
	      nil ;;compile-flg
	      )
:u :u

(defconst *import-symbols*
  (set-difference-eq
   (union-eq *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)
     '(null + * - < = / commutativity-of-* associativity-of-* 
	    commutativity-of-+ associativity-of-+ distributivity)))

(defpkg "FLD"
  *import-symbols*)

(defpkg "FUTER"
  *import-symbols*)

(defpkg "FUMON"
  (union-eq *import-symbols*
	    '(FLD::fdp FUTER::terminop)))

(defpkg "FUPOL"
  (union-eq *import-symbols*
	    '(FUTER::naturalp FUTER::terminop FUMON::monomio FUMON::coeficiente
			    FUMON::termino FUMON::monomiop)))

(defpkg "FUNPOL"
  (set-difference-eq *import-symbols*
		     '(rem)))

(certify-book "ed6a" 
	      6
	      nil ;;compile-flg
	      )
:u :u :u :u :u :u :u

