; Copyright (C) 2014, ForrestHunt, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Symbolic State Management -- Version 22
; J Strother Moore
; Fall/Winter, 2014/2015
; Georgetown, TX and Edinburgh, Scotland
;
; Original author: David L. Rager <ragerdl@gmail.com>
; Copyright assigned to ForrestHunt, Inc by David L. Rager

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

#!ACL2
(defpkg "SMAN"
  (union-eq
   *acl2-exports*
   *common-lisp-symbols-from-main-lisp-package*
   STD::*std-exports*
   '(binary-logand binary-logior binary-logxor
		   ash-to-floor *ts-nil* *ts-t* ts= *t* *nil* *0*
		   ffn-symb fargn type-alistp nvariablep variablep conjoin fquotep
		   flambdap fargs memb llist l<
		   distributivity-of-minus-over-+
		   tau-bounder-+ tau-bounder-* tau-bounder-mod tau-bounder-logand
		   tau-bounder-logior tau-bounder-logxor tau-bounder-ash
		   find-minimal-logand2 find-minimal-logand1 find-minimal-logand
		   find-maximal-logand2 find-maximal-logand1 find-maximal-logand
		   tau-bounder-logior-correct tau-bounder-logxor-correct
		   int1 int2 tau-interval-dom tau-intervalp x y
		   nonlinearp-default-hint
		   merge-term-order merge-sort-term-order how-many perm
		   convert-perm-to-how-many)))

