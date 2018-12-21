
(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defconst *import-symbols*
  (set-difference-eq
   (union-eq *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)
     '(null + * - < = / commutativity-of-* associativity-of-* 
	    commutativity-of-+ associativity-of-+ distributivity)))

(defpkg "FLD"
  *import-symbols*)

(certify-book "coe-fld"
	      2
	      nil ;;compile-flg
	      )

:u :u :u

(defconst *import-symbols*
  (set-difference-eq
   (union-eq *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*)
     '(null + * - < = / commutativity-of-* associativity-of-* 
	    commutativity-of-+ associativity-of-+ distributivity)))

(defpkg "FUTER"
  *import-symbols*)

(certify-book "futermino"
	      2
	      nil ;;compile-flg
	      )

:u :u :u

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

(certify-book "fumonomio"
	      4
	      nil ;;compile-flg
	      )

:u :u :u :u :u

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

(certify-book "fupolinomio"
	      5
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u

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

(certify-book "fuforma-normal"
	      5
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u

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

(certify-book "fusuma"
	      5
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u

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

(certify-book "fucongruencias-suma"
	      5
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u

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

(certify-book "fuopuesto"
	      5
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u

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

(certify-book "fuproducto"
	      5
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u

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

(certify-book "fucongruencias-producto"
	      5
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u

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

(certify-book "fupolinomio-normalizado"
	      6
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u :u

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

(certify-book "fuquot-rem"
	      6
	      nil ;;compile-flg
	      )

:u :u :u :u :u :u :u
