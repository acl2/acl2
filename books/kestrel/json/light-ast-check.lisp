; JSON Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "std/util/defrule" :dir :system)

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lightweight predicates on JSON ASTs.

;; The deftagsum predicates such as valuep are expensive, since they
;; validate the entire JSON structure.  After calling the predicate,
;; you have to do (eq :TAG (value-kind x)), making the check verbose
;; as well.  This file defines predicates that just check the top-level
;; structure that can be used to decide how to recur when walking a JSON AST.

;; E.g., (and (valuep x) (eq :OBJECT (value-kind x)))
;;       ==> (top-jobjectp x)

;; The latter call does not check the full structure, but it does check
;; enough to make sure that x could not be any other kind of jason::value.

;; Note that if the structure is always accessed through a fixtype API,
;; predicates of this kind are generally not needed.

(define jnullp (j)
  (equal j '(:null)))

;; Just to make sure if the lisp representation changes, this will catch it.
(defthm jnullp-implies-valuep
  (implies (jnullp j)
           (and (valuep j)
                (eq :NULL (value-kind j))))
  :hints (("Goal" :use jnullp))
  :rule-classes nil)

(define jtruep (j)
  (equal j '(:true)))

;; Just to make sure if the lisp representation changes, this will catch it.
(defthm jtruep-implies-valuep
  (implies (jtruep j)
           (and (valuep j)
                (eq :TRUE (value-kind j))))
  :hints (("Goal" :use jtruep))
  :rule-classes nil)

(define jfalsep (j)
  (equal j '(:false)))

;; Just to make sure if the lisp representation changes, this will catch it.
(defthm jfalsep-implies-valuep
  (implies (jfalsep j)
           (and (valuep j)
                (eq :FALSE (value-kind j))))
  :hints (("Goal" :use jfalsep))
  :rule-classes nil)

(define jstringp (j)
  (and (consp j)
       (eq :STRING (car j))
       (consp (cdr j))
       (stringp (cadr j))
       (null (cddr j))))

;; Just to make sure if the lisp representation changes, this will catch it.
(defthm jstringp-implies-valuep
  (implies (jstringp j)
           (and (valuep j)
                (eq :STRING (value-kind j))))
  :hints (("Goal" :in-theory (enable jstringp valuep value-kind)))
  :rule-classes nil)

(define jnumberp (j)
  (and (consp j)
       (eq :NUMBER (car j))
       (consp (cdr j))
       (rationalp (cadr j))
       (null (cddr j))))

;; Just to make sure if the lisp representation changes, this will catch it.
(defthm jnumberp-implies-valuep
  (implies (jnumberp j)
           (and (valuep j)
                (eq :NUMBER (value-kind j))))
  :hints (("Goal" :in-theory (enable jnumberp valuep value-kind)))
  :rule-classes nil)

;; Partial checkers on just the top of arrays, objects, and members.

(define top-jarrayp (j)
  (and (consp j)
       (eq :ARRAY (car j))
       (true-listp (cdr j))
       (consp (cdr j))
       (null (cddr j))
       (true-listp (cadr j))))

;; Since this is just the top, it top-jarrayp does not imply valuep.
;; But we should at least prove the other direction
;; so that we can hopefully catch changes of representation.
;;
(defrule array-valuep-implies-top-jarrayp
  (implies (and (valuep j)
                (eq :ARRAY (value-kind j)))
           (top-jarrayp j))
  ;; see how top-jvaluep handles this (using (len ..) instead)
  :prep-books ((include-book "std/lists/top" :dir :system)
	       (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))
  :enable (top-jarrayp valuep value-kind acl2::equal-len-const)
  :rule-classes nil)

;; If x is a top-jarrayp, then we want to be sure
;; that if x is a valuep, it can't be any other kind than :ARRAY.
;;
(defthmd top-jarrayp-implies-no-other-kind-of-value
  (implies (top-jarrayp j)
	   (implies (valuep j)
		    (eq (value-kind j) :ARRAY)))
  :hints (("Goal" :in-theory (enable valuep value-kind top-jarrayp))))

;; A member is an alist of length 2, with keys NAME and VALUE in that order.
;; However, stating it that way is not as easy for the prover to use.
;; So we disassemble it step by step.
;;
(define top-jmemberp (j)
  (and (consp j)
       (consp (car j))
       (eq 'NAME (caar j))
       ;; the name must be string
       (stringp (cdar j))
       (consp (cdr j))
       (consp (cadr j))
       (eq 'VALUE (caadr j))
       ;; not checking the actual value
       (null (cddr j))))

;; Hopefully if the lisp representation changes, this theorem will catch it.
;;
(defthmd memberp-implies-top-jmemberp
  (implies (memberp j)
           (top-jmemberp j))
  :hints (("Goal" :in-theory (enable top-jmemberp memberp))))

;; Since values are not directly under objects, let's validate
;; the structure at least to where the values occur.
;;
(define top-jmember-listp (jmemberlist)
  (or (null jmemberlist)
      (and (consp jmemberlist)
           (top-jmemberp (car jmemberlist))
           (top-jmember-listp (cdr jmemberlist)))))

(defthmd member-listp-implies-top-jmember-listp
  (implies (member-listp j)
           (top-jmember-listp j))
  :hints (("Goal" :in-theory (enable top-jmember-listp memberp-implies-top-jmemberp))))

(define top-jobjectp (j)
  (and (consp j)
       (eq :OBJECT (car j))
       (true-listp (cdr j))
       (eql (len (cdr j)) 1)
       (true-listp (cadr j))
       (top-jmember-listp (cadr j))))

(defthmd object-valuep-implies-top-jobjectp
  (implies (and (valuep j)
                (eq :OBJECT (value-kind j)))
           (top-jobjectp j))
  :hints (("Goal" :in-theory (enable valuep value-kind top-jobjectp top-jmember-listp member-listp-implies-top-jmember-listp))))

;; If x is a top-jobjectp, then we want to be sure
;; that if x is a valuep, it can't be any other kind than :OBJECT.
(defthmd top-jobjectp-implies-no-other-kind-of-value
  (implies (top-jobjectp j)
	   (implies (valuep j)
		    (eq (value-kind j) :OBJECT)))
  :hints (("Goal" :in-theory (enable valuep value-kind top-jobjectp))))

;; Some tests would be good.
