; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "lifting")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These are (simple) examples from Zcash (see :DOC ZCASH::ZCASH).
; They may be moved to the Zcash library at some point.

; Each example defines a (deeply embedded) PFCS named relation
; and proves its equivalence with an ACL2 specification.
; First the PFCS definition is lifted (automatically).
; Then the lifted (shallowly embedded) definition
; is proved equivalent to the specification.
; Finally the original definition is proved equivalent to the specification,
; by composing the liftin theorem with the manually proved theorem;
; (this theorem composition could be automated).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; boolean constraints [ZPS:A.3.1.1]

(define make-rel-boolean ()
  :returns (def definitionp)
  (make-definition
   :name (name "rel-boolean")
   :para (list (name "b"))
   :body (list
          (make-constraint-equal
           :left (expression-mul
                  (expression-sub (expression-const 1)
                                  (expression-var (name "b")))
                  (expression-var (name "b")))
           :right (expression-const 0)))))

(lift (make-rel-boolean))

(defruled rel-boolean-to-spec
  (implies (and (primep p)
                (fep b p))
           (equal (rel-boolean b p)
                  (or (equal b 0)
                      (equal b 1))))
  :enable rel-boolean)

(defruled definition-satp-of-rel-boolean-to-spec
  (implies (and (primep p)
                (equal (lookup-definition (name "rel-boolean") defs)
                       (make-rel-boolean))
                (fep b p))
           (equal (definition-satp (name "rel-boolean") defs (list b) p)
                  (or (equal b 0)
                      (equal b 1))))
  :in-theory '((:e make-rel-boolean)
               (:e name))
  :use (definition-satp-to-rel-boolean
         rel-boolean-to-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; conditional equality [ZPS:A.3.1.2]

(define make-rel-condeq ()
  :returns (def definitionp)
  (make-definition
   :name (name "rel-condeq")
   :para (list (name "a") (name "b") (name "c"))
   :body (list
          (make-constraint-equal
           :left (expression-mul
                  (expression-var (name "a"))
                  (expression-sub (expression-var (name "b"))
                                  (expression-var (name "c"))))
           :right (expression-const 0)))))

(lift (make-rel-condeq))

(defruled rel-condeq-to-spec
  (implies (and (primep p)
                (fep a p)
                (fep b p)
                (fep c p))
           (equal (rel-condeq a b c p)
                  (or (equal a 0)
                      (equal b c))))
  :enable rel-condeq)

(defruled definition-satp-of-rel-condeq-to-spec
  (implies (and (primep p)
                (equal (lookup-definition (name "rel-condeq") defs)
                       (make-rel-condeq))
                (fep a p)
                (fep b p)
                (fep c p))
           (equal (definition-satp (name "rel-condeq") defs (list a b c) p)
                  (or (equal a 0)
                      (equal b c))))
  :in-theory '((:e make-rel-condeq)
               (:e name))
  :use (definition-satp-to-rel-condeq
         rel-condeq-to-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; selection constraints [ZPS:A.3.1.3]

(define make-rel-select ()
  :returns (def definitionp)
  (make-definition
   :name (name "rel-select")
   :para (list (name "b") (name "x") (name "y") (name "z"))
   :body (list
          (make-constraint-equal
           :left (expression-mul
                  (expression-var (name "b"))
                  (expression-sub (expression-var (name "y"))
                                  (expression-var (name "x"))))
           :right (expression-sub (expression-var (name "y"))
                                  (expression-var (name "z")))))))

(lift (make-rel-select))

(defruled rel-select-to-spec
  (implies (and (primep p)
                (fep b p)
                (fep x p)
                (fep y p)
                (fep z p)
                (rel-boolean b p)) ; precondition
           (equal (rel-select b x y z p)
                  (equal z
                         (if (equal b 1) x y))))
  :enable (rel-select
           rel-boolean-to-spec) ; uses spec of rel-boolean
  :prep-books
  ((include-book "kestrel/prime-fields/equal-of-add-rules" :dir :system)))

(defruled definition-satp-of-rel-select-to-spec
  (implies (and (primep p)
                (equal (lookup-definition (name "rel-select") defs)
                       (make-rel-select))
                (fep b p)
                (fep x p)
                (fep y p)
                (fep z p)
                (rel-boolean b p)) ; precondition
           (equal (definition-satp (name "rel-select") defs (list b x y z) p)
                  (equal z
                         (if (equal b 1) x y))))
  :in-theory '((:e make-rel-select)
               (:e name))
  :use (definition-satp-to-rel-select
         rel-select-to-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; nonzero constraints [ZPS:A.3.1.4]

(define make-rel-nonzero ()
  :returns (def definitionp)
  (make-definition
   :name (name "rel-nonzero")
   :para (list (name "a"))
   :body (list
          (make-constraint-equal
           :left (expression-mul
                  (expression-var (name "ainv"))
                  (expression-var (name "a")))
           :right (expression-const 1)))))

(lift (make-rel-nonzero))

(defruled rel-nonzero-to-spec
  (implies (and (primep p)
                (fep a p))
           (equal (rel-nonzero a p)
                  (not (equal a 0))))
  :use (left-implies-right right-implies-left)

  :prep-lemmas

  ((defruled left-implies-right
     (implies (and (primep p)
                   (fep a p))
              (implies (rel-nonzero a p)
                       (not (equal a 0))))
     :enable rel-nonzero)

   (defrule right-implies-left
     (implies (and (primep p)
                   (fep a p))
              (implies (not (equal a 0))
                       (rel-nonzero a p)))
     :use (:instance rel-nonzero-suff (ainv (inv a p))))))

(defruled definition-satp-of-rel-nonzero-to-spec
  (implies (and (primep p)
                (equal (lookup-definition (name "rel-nonzero") defs)
                       (make-rel-nonzero))
                (fep a p))
           (equal (definition-satp (name "rel-nonzero") defs (list a) p)
                  (not (equal a 0))))
  :in-theory '((:e make-rel-nonzero)
               (:e name))
  :use (definition-satp-to-rel-nonzero
         rel-nonzero-to-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; exclusive-or constrains [ZPS:A.3.1.5]

(define make-rel-xor ()
  :returns (def definitionp)
  (make-definition
   :name (name "rel-xor")
   :para (list (name "a") (name "b") (name "c"))
   :body (list
          (make-constraint-equal
           :left (expression-mul (expression-mul
                                  (expression-const 2)
                                  (expression-var (name "a")))
                                 (expression-var (name "b")))
           :right (expression-add (expression-var (name "a"))
                                  (expression-sub (expression-var
                                                   (name "b"))
                                                  (expression-var
                                                   (name "c"))))))))

(lift (make-rel-xor))

(defruled rel-xor-to-spec
  (implies (and (primep p)
                (fep a p)
                (fep b p)
                (fep c p)
                (rel-boolean a p) ; precondition
                (rel-boolean b p) ; precondition
                (> p 2)) ; additional precondition
           (equal (rel-xor a b c p)
                  (equal c (if (equal a b) 0 1))))
  :enable (rel-xor
           rel-boolean-to-spec)) ; use spec of rel-boolean

(defruled definition-satp-of-rel-xor-to-spec
  (implies (and (primep p)
                (equal (lookup-definition (name "rel-xor") defs)
                       (make-rel-xor))
                (fep a p)
                (fep b p)
                (fep c p)
                (rel-boolean a p) ; precondition
                (rel-boolean b p) ; precondition
                (> p 2)) ; additional precondition
           (equal (definition-satp (name "rel-xor") defs (list a b c) p)
                  (equal c (if (equal a b) 0 1))))
  :in-theory '((:e make-rel-xor)
               (:e name))
  :use (definition-satp-to-rel-xor
         rel-xor-to-spec))
