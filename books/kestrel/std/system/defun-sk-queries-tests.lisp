; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defun-sk-queries")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (defun-sk-quantifier-p 'exists))

(assert! (defun-sk-quantifier-p 'forall))

(assert! (not (defun-sk-quantifier-p "forall")))

(assert! (not (defun-sk-quantifier-p 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (defun-sk-rewrite-kind-p :default))

(assert! (defun-sk-rewrite-kind-p :direct))

(assert! (defun-sk-rewrite-kind-p :custom))

(assert! (not (defun-sk-rewrite-kind-p '(a b 44))))

(assert! (not (defun-sk-rewrite-kind-p :customized)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (defun-sk-p 'cons (w state))))

(assert! (not (defun-sk-p 'not (w state))))

(assert! (not (defun-sk-p 'len (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (not (defun-sk-p 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (defun-sk-namep 33 (w state))))

(assert! (not (defun-sk-namep '(1 2 3) (w state))))

(assert! (not (defun-sk-namep "aa" (w state))))

(assert! (not (defun-sk-namep 'symb (w state))))

(assert! (not (defun-sk-namep 'cons (w state))))

(assert! (not (defun-sk-namep 'not (w state))))

(assert! (not (defun-sk-namep 'len (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (not (defun-sk-namep 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) nil)
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :strengthen nil)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:strengthen . nil)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :strengthen t)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:strengthen . t)))
 (assert-equal (defun-sk-strengthen 'f (w state)) t)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :skolem-name fw)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'fw)
 (assert-equal (defun-sk-options 'f (w state)) '((:skolem-name . fw)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :thm-name ft)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:thm-name . ft)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'ft)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :witness-dcls nil)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:witness-dcls . nil)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b))
   :witness-dcls ((declare (xargs :verify-guards nil))))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state))
               '((:witness-dcls . ((declare (xargs :verify-guards nil))))))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (declare (xargs :verify-guards nil)) (exists b (atom b)))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) nil)
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :quant-ok nil)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:quant-ok . nil)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :quant-ok t)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:quant-ok . t)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :constrain nil)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:constrain . nil)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :constrain t)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:constrain . t)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) 'f-definition)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists b (atom b)) :constrain fd)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:constrain . fd)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) 'fd)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f (a) (exists b (cons a b)))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (cons a b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(cons a b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) nil)
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(cons a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f (a) (exists b (cons a b)) :strengthen nil :skolem-name fw)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (cons a b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(cons a b))
 (assert-equal (defun-sk-witness 'f (w state)) 'fw)
 (assert-equal (defun-sk-options 'f (w state)) '((:skolem-name . fw)
                                                 (:strengthen . nil)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(cons a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f (a) (exists b (cons a b)) :strengthen t :thm-name ft)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (cons a b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(cons a b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:thm-name . ft)
                                                 (:strengthen . t)))
 (assert-equal (defun-sk-strengthen 'f (w state)) t)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'ft)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(cons a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f (a1 a2 a3) (exists b (list a1 a2 a3 b))
   :skolem-name fw :thm-name ft)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists b (list a1 a2 a3 b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(list a1 a2 a3 b))
 (assert-equal (defun-sk-witness 'f (w state)) 'fw)
 (assert-equal (defun-sk-options 'f (w state)) '((:thm-name . ft)
                                                 (:skolem-name . fw)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'ft)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state))
               '(cons a1 (cons a2 (cons a3 (cons b 'nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (exists (b1 b2) (cons b1 b2)))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(exists (b1 b2) (cons b1 b2)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b1 b2))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(cons b1 b2))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) nil)
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(cons b1 b2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f (a1 a2)
   (exists (b1 b2 b3) (let ((lhs (list a1 a2))
                            (rhs (list b1 b2 b3)))
                        (equal lhs rhs))))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state))
               '(exists (b1 b2 b3) (let ((lhs (list a1 a2))
                                         (rhs (list b1 b2 b3)))
                                     (equal lhs rhs))))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'exists)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b1 b2 b3))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(let ((lhs (list a1 a2))
                                                      (rhs (list b1 b2 b3)))
                                                  (equal lhs rhs)))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) nil)
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-suff)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state))
               '((lambda (lhs rhs) (equal lhs rhs))
                 (cons a1 (cons a2 'nil))
                 (cons b1 (cons b2 (cons b3 'nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall b (atom b)))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) nil)
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall b (atom b)) :rewrite :default)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:rewrite . :default)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall b (atom b)) :rewrite :direct)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:rewrite . :direct)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :direct)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall (b) (atom b))
   :rewrite (implies (not (atom b)) (not (f))))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall (b) (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state))
               '((:rewrite . (implies (not (atom b)) (not (f))))))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :custom)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall b (atom b))
   :rewrite (implies (f) (atom b)))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state))
               '((:rewrite . (implies (f) (atom b)))))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :custom)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall b (atom b))
   :rewrite (implies (f) (not (consp b))))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state))
               '((:rewrite . (implies (f) (not (consp b))))))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :custom)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall b (atom b))
   :thm-name f-custom
   :rewrite (implies (f) (not (consp b))))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state))
               '((:rewrite . (implies (f) (not (consp b))))
                 (:thm-name . f-custom)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :custom)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-custom)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall b (atom b)) :rewrite :direct :skolem-name fw)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall b (atom b)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(atom b))
 (assert-equal (defun-sk-witness 'f (w state)) 'fw)
 (assert-equal (defun-sk-options 'f (w state)) '((:skolem-name . fw)
                                                 (:rewrite . :direct)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :direct)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(atom b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f () (forall (b1 b2) (+ b1 b2)))
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall (b1 b2) (+ b1 b2)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b1 b2))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(+ b1 b2))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) nil)
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state)) '(binary-+ b1 b2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-sk f (a) (forall (b1 b2 b3) (* a b1 b2 b3)) :witness-dcls nil)
 (assert! (defun-sk-p 'f (w state)))
 (assert! (defun-sk-namep 'f (w state)))
 (assert-equal (defun-sk-body 'f (w state)) '(forall (b1 b2 b3) (* a b1 b2 b3)))
 (assert-equal (defun-sk-quantifier 'f (w state)) 'forall)
 (assert-equal (defun-sk-bound-vars 'f (w state)) '(b1 b2 b3))
 (assert-equal (defun-sk-imatrix 'f (w state)) '(* a b1 b2 b3))
 (assert-equal (defun-sk-witness 'f (w state)) 'f-witness)
 (assert-equal (defun-sk-options 'f (w state)) '((:witness-dcls . nil)))
 (assert-equal (defun-sk-strengthen 'f (w state)) nil)
 (assert-equal (defun-sk-classicalp 'f (w state)) t)
 (assert-equal (defun-sk-rewrite-kind 'f (w state)) :default)
 (assert-equal (defun-sk-rewrite-name 'f (w state)) 'f-necc)
 (assert-equal (defun-sk-definition-name 'f (w state)) nil)
 (assert-equal (defun-sk-matrix 'f (w state))
               '(binary-* a (binary-* b1 (binary-* b2 b3)))))
