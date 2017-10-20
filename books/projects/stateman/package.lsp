(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

#!ACL2
(defpkg "SMAN"
  (union-eq
   *acl2-exports*
   *common-lisp-symbols-from-main-lisp-package*
   STD::*std-exports*
   '(binary-logand binary-logior binary-logxor
		   ASH-TO-FLOOR *ts-nil* *ts-t* ts= *t* *nil* *0*
		   ffn-symb fargn type-alistp nvariablep variablep conjoin fquotep
		   flambdap fargs memb llist l<
		   distributivity-of-minus-over-+
		   tau-bounder-+ tau-bounder-* tau-bounder-mod tau-bounder-logand
		   tau-bounder-logior tau-bounder-logxor tau-bounder-ash
		   find-minimal-logand2 find-minimal-logand1 find-minimal-logand
		   find-maximal-logand2 find-maximal-logand1 find-maximal-logand
		   TAU-BOUNDER-LOGIOR-CORRECT TAU-BOUNDER-LOGXOR-CORRECT
		   int1 int2 tau-interval-dom tau-intervalp x y
		   nonlinearp-default-hint
		   merge-term-order merge-sort-term-order how-many perm
		   convert-perm-to-how-many
		   )))

     

; (acl2::deffalias fquotep acl2::fquotep)

