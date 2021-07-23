; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "semantics-shallow")

(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These are examples from Zcash (see :DOC ZCASH::ZCASH).
; They may be moved to the Zcash library at some point.

; Each example defines a PFCS named relation
; and proves its equivalence with an ACL2 specification,
; using the PFCS shallowly embedded semantics.

; These are simple examples for now,
; but they should demonstrate how PFCS can support
; the modular verification of hierarchical gadgets.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; boolean constraints [ZPS:A.3.1.1]

(define make-rel-boolean ()
  :returns (def definitionp)
  (make-definition
   :name 'rel-boolean
   :para '(b)
   :body (list
          (make-constraint-equal
           :left (expression-mul
                  (expression-sub (expression-const 1)
                                  (expression-var 'b))
                  (expression-var 'b))
           :right (expression-const 0)))))

(make-event (sesem-definition (make-rel-boolean) 'p))

(defruled rel-boolean-to-spec
  (implies (and (rtl::primep p)
                (pfield::fep b p))
           (equal (rel-boolean b p)
                  (or (equal b 0)
                      (equal b 1))))
  :enable rel-boolean)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; conditional equality [ZPS:A.3.1.2]

(define make-rel-condeq ()
  :returns (def definitionp)
  (make-definition
   :name 'rel-condeq
   :para '(a b c)
   :body (list
          (make-constraint-equal
           :left (expression-mul
                  (expression-var 'a)
                  (expression-sub (expression-var 'b)
                                  (expression-var 'c)))
           :right (expression-const 0)))))

(make-event (sesem-definition (make-rel-condeq) 'p))

(defruled rel-condeq-to-spec
  (implies (and (rtl::primep p)
                (pfield::fep a p)
                (pfield::fep b p)
                (pfield::fep c p))
           (equal (rel-condeq a b c p)
                  (or (equal a 0)
                      (equal b c))))
  :enable rel-condeq)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; selection constraints [ZPS:A.3.1.3]

(define make-rel-select ()
  :returns (def definitionp)
  (make-definition
   :name 'rel-select
   :para '(b x y z)
   :body (list
          (make-constraint-equal
           :left (expression-mul
                  (expression-var 'b)
                  (expression-sub (expression-var 'y)
                                  (expression-var 'x)))
           :right (expression-sub (expression-var 'y)
                                  (expression-var 'z))))))

(make-event (sesem-definition (make-rel-select) 'p))

(defruled rel-select-to-spec
  (implies (and (rtl::primep p)
                (pfield::fep b p)
                (pfield::fep x p)
                (pfield::fep y p)
                (pfield::fep z p)
                (rel-boolean b p)) ; precondition
           (equal (rel-select b x y z p)
                  (equal z
                         (if (equal b 1) x y))))
  :enable (rel-select
           rel-boolean-to-spec) ; uses spec of rel-boolean
  :prep-books
  ((include-book "kestrel/prime-fields/equal-of-add-rules" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; nonzero constraints [ZPS:A.3.1.4]

(define make-rel-nonzero ()
  :returns (def definitionp)
  (make-definition
   :name 'rel-nonzero
   :para '(a)
   :body (list
          (make-constraint-equal
           :left (expression-mul
                  (expression-var 'ainv)
                  (expression-var 'a))
           :right (expression-const 1)))))

(make-event (sesem-definition (make-rel-nonzero) 'p))

(defruled rel-nonzero-to-spec
  (implies (and (rtl::primep p)
                (pfield::fep a p))
           (equal (rel-nonzero a p)
                  (not (equal a 0))))
  :use (left-implies-right right-implies-left)

  :prep-lemmas

  ((defruled left-implies-right
     (implies (and (rtl::primep p)
                   (pfield::fep a p))
              (implies (rel-nonzero a p)
                       (not (equal a 0))))
     :enable rel-nonzero)

   (defrule right-implies-left
     (implies (and (rtl::primep p)
                   (pfield::fep a p))
              (implies (not (equal a 0))
                       (rel-nonzero a p)))
     :use (:instance rel-nonzero-suff (ainv (pfield::inv a p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exclusive-or constrains [ZPS:A.3.1.5]

(define make-rel-xor ()
  :returns (def definitionp)
  (make-definition
   :name 'rel-xor
   :para '(a b c)
   :body (list
          (make-constraint-equal
           :left (expression-mul (expression-mul
                                  (expression-const 2)
                                  (expression-var 'a))
                                 (expression-var 'b))
           :right (expression-add (expression-var 'a)
                                  (expression-sub (expression-var 'b)
                                                  (expression-var 'c)))))))

(make-event (sesem-definition (make-rel-xor) 'p))

(defruled rel-xor-to-spec
  (implies (and (rtl::primep p)
                (pfield::fep a p)
                (pfield::fep b p)
                (pfield::fep c p)
                (rel-boolean a p) ; precondition
                (rel-boolean b p) ; precondition
                (> p 2)) ; additional precondition
           (equal (rel-xor a b c p)
                  (equal c (if (equal a b) 0 1))))
  :enable (rel-xor
           rel-boolean-to-spec)) ; use spec of rel-boolean
