(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defconst *export-symbols*
  (union-eq *acl2-exports*
	    (union-eq '(len true-listp defung defequiv defcong i-am-here
			zp defrefinement defabbrev defstub e0-ord-< 
			e0-ordinalp cdr-cons car-cons car-cdr-elim
		        booleanp booleanp-compound-recognizer commutativity-of-+
			complex-rationalp unicity-of-0 associativity-of-+
			binary-append default-car default-cdr cons-equal
			binary-+ acl2-numberp fix nfix alistp assoc-equal
			put-assoc-equal value-of union-eq defpkg
			a b x y z alist key i j l k m list x-equiv y-equiv 
			x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 z1 z2 z3 z4 z5
			*export-symbols*)
		      *common-lisp-symbols-from-main-lisp-package*)))

(defconst *symbols-kept-as-acl2-symbols*
  '(in remove-el perm perm-reflexive remove-el-swap remove-el-in 
    perm-remove car-perm perm-symmetric perm-in perm-transitive
    perm-remove-el-app perm-app-cons))

(defconst *sets-symbols*
  (union-eq *export-symbols* *symbols-kept-as-ACL2-symbols*))

(defpkg "SETS" *sets-symbols*)

(defconst *FAST-SETS-symbols*
  (union-eq 
   *sets-symbols*
   '(sets::=< sets::== sets::depth sets::no-dups)))

(defpkg "FAST-SETS" *fast-sets-symbols*)


(defconst *relations-symbols*
  (union-eq 
   *export-symbols*
   '(sets::in sets::=< sets::== sets::depth  fast-sets::intersect
     fast-sets::add fast-sets::set-union fast-sets::minus)))

(defpkg "RELATIONS"
  *relations-symbols*)


(defconst *MODEL-CHECK-symbols*
  (union-eq 
   *export-symbols*
   (append '(acl2::perm acl2::remove-el)
	   '(sets::in sets::=< sets::== sets::s< sets::=<-perm sets::no-dups)
	   '(fast-sets::intersect fast-sets::add fast-sets::set-union 
	     fast-sets::set-complement fast-sets::minus fast-sets::cardinality
	     fast-sets::make-list-set fast-sets::remove-dups)
	   '(relations::relationp relations::inverse relations::image
				  relations::rel-range-subset))))

(defpkg "MODEL-CHECK" *model-check-symbols*)
