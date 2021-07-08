; Arrays in the JVM
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "array-building")
(include-book "floats")
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
;(include-book "coi/lists/nth-and-update-nth" :dir :system) ;since clear-nth is called below

(in-theory (disable ;MEMBER-OF-CONS ;bad rule; can match on constants
                    ; SUBSETP-CAR-MEMBER ;bad rule, introduces subset reasoning out of nowhere
                    TRUE-LISTP ;for speed
;                    CONSP-FROM-LEN-CHEAP
                    ;list::open-equiv
                    ))

;move
(defthm clr-non-nil-when-get-class
  (implies (and (equal (get-class ad heap) val)
                val
                (not (equal (class-pair) a)))
           (clr a (g ad heap)))
  :hints (("Goal" :in-theory (enable get-class))))

;;Recognize a list of java-floats:
(defforall-simple jvm::java-floatp :guard t)

;;Recognize a list of java-doubles:
(defforall-simple jvm::java-doublep :guard t)

;;;
;;; all-null-or-addresses-bound-to-object-of-type
;;;

(defun all-null-or-addresses-bound-to-object-of-type (contents element-type heap)
  (declare (xargs :guard (and (true-listp contents)
                              (jvm::typep element-type)
                              (jvm::heapp heap))))
  (if (endp contents)
      t
    (let ((item (first contents)))
      (and (or (null-refp item) ;; We allow an array item that is a reference to be null.
               ;; Otherwise, it must be bound in the heap to an object of the correct class
               (and (addressp item)
                    ;; (set::in item (rkeys heap)) ;caueses problems if element-type is nil?
                    (equal element-type (get-class item heap))))
           (all-null-or-addresses-bound-to-object-of-type (rest contents) element-type heap)))))

(defthm all-null-or-addresses-bound-to-object-of-type-of-set-field
  (implies (and (not (equal pair (class-pair)))
                ;; (not element-type)
                )
           (equal (all-null-or-addresses-bound-to-object-of-type contents element-type (set-field ad pair val heap))
                  (all-null-or-addresses-bound-to-object-of-type contents element-type heap)))
  :hints (("Goal"
           :induct (all-null-or-addresses-bound-to-object-of-type contents element-type heap)
           :expand ((all-null-or-addresses-bound-to-object-of-type contents element-type(set-field ad pair val heap)))
           :in-theory (enable all-null-or-addresses-bound-to-object-of-type
                              memberp-of-cons-when-constant))))

(defthm all-null-or-addresses-bound-to-object-of-type-of-set-field-when-not-memberp
  (implies (not (memberp ad ads))
           (equal (all-null-or-addresses-bound-to-object-of-type ads element-type (set-field ad pair val heap))
                  (all-null-or-addresses-bound-to-object-of-type ads element-type heap)))
  :hints (("Goal" :in-theory (enable all-null-or-addresses-bound-to-object-of-type))))

;pair can be (clas-pair) or something else
(defthm all-null-or-addresses-bound-to-object-of-type-of-set-field-same
  (implies (all-null-or-addresses-bound-to-object-of-type ads element-type heap)
           (all-null-or-addresses-bound-to-object-of-type ads element-type (set-field ad pair element-type heap)))
  :hints (("Goal" :in-theory (enable all-null-or-addresses-bound-to-object-of-type))))

(defthm all-null-or-addresses-bound-to-object-of-type-of-update-nth
  (implies (and (all-null-or-addresses-bound-to-object-of-type ads element-type heap)
                (or (null-refp ad)
                    (and (addressp ad)
                         (equal element-type (get-class ad heap))))
                (natp n)
                (< n (len ads)))
           (all-null-or-addresses-bound-to-object-of-type (update-nth n ad ads) element-type heap))
  :hints (("Goal" :in-theory (enable all-null-or-addresses-bound-to-object-of-type update-nth))))

(defund primitive-array-contents-okp (contents element-type)
  (declare (xargs :guard (and (true-listp contents)
                              (jvm::primitive-typep element-type))))
  (if (equal element-type ':int)
      (all-unsigned-byte-p 32 contents)
    (if (equal element-type ':byte)
        (all-unsigned-byte-p 8 contents)
      (if (equal element-type ':boolean)
          (all-unsigned-byte-p 1 contents)
        (if (equal element-type ':short)
            (all-unsigned-byte-p 16 contents)
          (if (equal element-type ':char)
              (all-unsigned-byte-p 16 contents)
            (if (equal element-type ':long)
                (all-unsigned-byte-p 64 contents)
              (if (equal element-type ':float)
                  (all-java-floatp contents)
                (if (equal element-type ':double)
                    (all-java-doublep contents)
                  (er hard 'primitive-array-contents-okp "Unexpeted type: ~x0" element-type))))))))))

(defthm primitive-array-contents-okp-of-int
  (equal (primitive-array-contents-okp contents :int)
         (all-unsigned-byte-p 32 contents))
  :hints (("Goal" :in-theory (enable primitive-array-contents-okp))))

(defthm primitive-array-contents-okp-of-byte
  (equal (primitive-array-contents-okp contents :byte)
         (all-unsigned-byte-p 8 contents))
  :hints (("Goal" :in-theory (enable primitive-array-contents-okp))))

(defthm primitive-array-contents-okp-of-boolean
  (equal (primitive-array-contents-okp contents :boolean)
         (all-unsigned-byte-p 1 contents))
  :hints (("Goal" :in-theory (enable primitive-array-contents-okp))))

(defthm primitive-array-contents-okp-of-short
  (equal (primitive-array-contents-okp contents :short)
         (all-unsigned-byte-p 16 contents))
  :hints (("Goal" :in-theory (enable primitive-array-contents-okp))))

(defthm primitive-array-contents-okp-of-char
  (equal (primitive-array-contents-okp contents :char)
         (all-unsigned-byte-p 16 contents))
  :hints (("Goal" :in-theory (enable primitive-array-contents-okp))))

(defthm primitive-array-contents-okp-of-long
  (equal (primitive-array-contents-okp contents :long)
         (all-unsigned-byte-p 64 contents))
  :hints (("Goal" :in-theory (enable primitive-array-contents-okp))))

(defthm primitive-array-contents-okp-of-float
  (equal (primitive-array-contents-okp contents :float)
         (all-java-floatp contents))
  :hints (("Goal" :in-theory (enable primitive-array-contents-okp))))

(defthm primitive-array-contents-okp-of-double
  (equal (primitive-array-contents-okp contents :double)
         (all-java-doublep contents))
  :hints (("Goal" :in-theory (enable primitive-array-contents-okp))))

;; To be left enabled usually
(defun array-contents-okp (contents element-type heap)
  (declare (xargs :guard (and (true-listp contents)
                              (jvm::typep element-type)
                              (not (jvm::is-array-typep element-type))
                              (jvm::heapp heap))
                  :guard-hints (("Goal" :in-theory (enable jvm::typep)))))
  (if (jvm::class-namep element-type)
      ;; These pointers can be null since they are not "part of" the array:
      (all-null-or-addresses-bound-to-object-of-type contents element-type heap)
    ;; could drop these checks since bv-array-read now carries a type?
    (primitive-array-contents-okp contents element-type)))

;; (defthm array-contents-okp-of-set-field-same
;;   (implies (array-contents-okp contents element-type heap)
;;            (array-contents-okp contents element-type (set-field ad pair element-type heap)))
;;   :hints (("Goal" :in-theory (enable array-contents-okp))))

;; (defthm array-contents-okp-of-set-field-when-not-class-namep
;;   (implies (not (jvm::class-namep element-type))
;;            (equal (array-contents-okp contents element-type (set-field ad pair val heap))
;;                   (array-contents-okp contents element-type heap)))
;;   :hints (("Goal" :in-theory (enable array-contents-okp))))

;; (defthm array-contents-okp-of-set-field-irrel
;;   (implies (not (equal pair (class-pair)))
;;            (equal (array-contents-okp contents element-type (set-field ad pair val heap))
;;                   (array-contents-okp contents element-type heap)))
;;   :hints (("Goal" :in-theory (enable array-contents-okp))))

;; (thm
;;  (implies (ARRAY-CONTENTS-OKP contents ELEMENT-TYPE HEAP)
;;           (ARRAY-CONTENTS-OKP contents ELEMENT-TYPE (SET-FIELD AD2 (array-contents-pair) VAL HEAP)))
;;  :hints (("Goal" :in-theory (enable ARRAY-CONTENTS-OKP))))

;; (defthm array-contents-okp-of-set-field-when-primitive-typep
;;   (implies (and (array-contents-okp contents element-type heap)
;;                 (jvm::primitive-typep element-type))
;;            (array-contents-okp contents element-type (set-field ad pair val heap)))
;;   :hints (("Goal" :in-theory (enable array-contents-okp))))

;; (defthm array-contents-okp-of-update-nth-when-class-namep
;;   (implies (and (array-contents-okp ads element-type heap)
;;                 (jvm::class-namep element-type)
;;                 (or (null-refp ad)
;;                     (and (addressp ad)
;;                          (equal element-type (get-class ad heap))))
;;                 (natp n)
;;                 (< n (len ads)))
;;            (array-contents-okp (update-nth n ad ads) element-type heap))
;;   :hints (("Goal" :in-theory (enable array-contents-okp))))

;;;
;;; array-refp and array-ref-listp
;;;

;ELEMENT-TYPE is the type of the primitive elements stored in the array, so a 3-d array of bytes
;has element type :BYTE.
;checks all the dims (can we be more flexible?)
(mutual-recursion
 ;; Test whether AD points to a well-formed array with DIMS dimensions and the given ELEMENT-TYPE in HEAP.
 (defund array-refp (ad dims element-type heap)
   (declare (xargs :measure (make-ord 1 (+ 1 (len dims)) (acl2-count ad))
                   :guard (and (nat-listp dims)
                               (consp dims) ; must be at least one dimension
                               (jvm::typep element-type)
                               (not (jvm::is-array-typep element-type))
                               (jvm::heapp heap))))
   (and (addressp ad) ;implies that is it not null
        (set::in ad (rkeys heap))
        (equal (jvm::make-array-type (len dims) element-type)
               (get-class ad heap))
        (let ((contents (array-contents ad heap)))
          (and (true-listp contents)
               (equal (len contents) (first dims))
               (unsigned-byte-p 31 (first dims))
               (if (endp (rest dims))
                   ;; single array dimension:
                   (array-contents-okp contents element-type heap)
                 ;; More than one array dimension (must be an array of pointers to subarrays):
                 (and (array-ref-listp contents (rest dims) element-type heap)
                      (no-duplicatesp-equal contents) ;disallows structure sharing (fixme think about structure sharing on the sub-levels (not disallowed by this?) and also between levels (possibly disallowed due to conflicting values of get-class))
                      ))))))

 (defund array-ref-listp (ads dims element-type heap)
   (declare (xargs :measure (make-ord 1 (+ 1 (len dims)) (acl2-count ads))
                   :guard (and (true-listp ads)
                               (nat-listp dims)
                               (consp dims)
                               (jvm::typep element-type)
                               (not (jvm::is-array-typep element-type))
                               (jvm::heapp heap))))
   (if (endp ads)
       t
     (and (array-refp (first ads) dims element-type heap)
          (array-ref-listp (rest ads) dims element-type heap)))))

;;;
;;; theorems about array-refp
;;;

(defthm array-refp-forward-to-addressp
  (implies (array-refp ad dims element-type heap)
           (addressp ad))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable array-refp))))

(defthm addressp-when-array-refp
  (implies (and (array-refp item dims element-type heap)
                (consp dims))
           (addressp item))
  :hints (("Goal" :in-theory (enable array-refp))))

;; True because item is an address
(defthm address-or-nullp-when-array-refp
  (implies (and (array-refp item dims element-type heap)
                (consp dims))
           (address-or-nullp item))
  :hints (("Goal" :in-theory (enable array-refp))))

(defthm not-null-refp-when-array-refp
  (implies (and (array-refp item dims element-type heap)
                (consp dims))
           (not (null-refp item)))
  :hints (("Goal" :use (:instance addressp-when-array-refp)
           :in-theory (disable addressp-when-array-refp))))

;similar to the below
;;TODO: Decide whether get-class will be enabled or disabled?
(defthm get-field-class-when-array-refp
  (implies (and (array-refp ad dims type heap)
                (consp dims))
           (equal (get-field ad (class-pair) heap)
                  (jvm::make-array-type (len dims) type)))
  :hints (("Goal" :in-theory (enable get-class array-refp))))

;similar to the above
(defthm get-class-when-array-refp
  (implies (and (array-refp ad dims type heap)
                (consp dims))
           (equal (get-class ad heap)
                  (jvm::make-array-type (len dims) type)))
  :hints (("Goal" :in-theory (enable array-refp))))

(defthm array-length-when-array-refp
  (implies (and (array-refp ad dims type heap)
                ;(consp dims)
                )
           (equal (array-length ad heap)
                  (car dims)))
  :hints (("Goal" :in-theory (enable array-refp))))

;similar to the above
(defthm len-of-contents-when-array-refp
  (implies (and (array-refp ad dims type heap) ;dims is a free variable
                (consp dims))
           (equal (len (get-field ad (array-contents-pair) heap))
                  (car dims))))

;similar to the above
;breaks the get-field abstraction (but we might do that in the machine model for efficiency)
(defthm len-of-g-of-g-contents-when-array-refp
  (implies (and (array-refp ad dims type heap)
                (consp dims)
                )
           (equal (len (g (array-contents-pair) (g ad heap)))
                  (car dims)))
  :hints (("Goal" :use (:instance len-of-contents-when-array-refp)
           :in-theory (e/d (get-field) (len-of-contents-when-array-refp)))))

(defthm consp-of-contents-when-array-refp
  (implies (array-refp ad dims type heap) ; dims is a free variable
           (equal (consp (get-field ad (array-contents-pair) heap))
                  (posp (car dims))))
  :hints (("Goal" :in-theory (enable array-refp))))

(defthm in-of-rkeys-when-array-refp
  (implies (and (array-refp ad dims type heap) ; dims is a free variable
                (consp dims))
           (set::in ad (rkeys heap)))
  :hints (("Goal" :expand ((array-refp ad dims type heap)))))

(defthm equal-of-get-field-contents-and-nil-when-array-refp
  (implies (array-refp ad dims type heap)
           (equal (equal (get-field ad (array-contents-pair) heap) nil)
                  (not (< 0 (car dims)))))
  :hints (("Goal" :in-theory (enable array-refp))))

;commutes the equal, only needed for Axe?
(defthm equal-of-nil-and-get-field-contents-when-array-refp
  (implies (array-refp ad dims type heap)
           (equal (equal nil (get-field ad (array-contents-pair) heap))
                  (not (< 0 (car dims)))))
  :hints (("Goal" :in-theory (enable array-refp))))

;rename
(defthm unique-contents-when-array-refp
  (implies (and (array-refp ad dims type heap)
                (< 1 (len dims)))
           (no-duplicatesp-equal (get-field ad (array-contents-pair) heap)))
  :hints (("Goal" :in-theory (enable array-refp))))

;rename
(defthm ubp-of-dim
  (implies (array-refp ad (cons dim dims) type heap)
           (unsigned-byte-p 31 dim))
  :hints (("Goal" :in-theory (enable array-refp))))

(defthm unsigned-byte-p-when-array-refp
  (implies (and (array-refp ad (cons dim dims) type heap) ;free vars here
                (natp size)
                (<= 31 size))
           (unsigned-byte-p size dim))
  :hints (("Goal" :use (:instance ubp-of-dim)
           :in-theory (disable ubp-of-dim ARRAY-REFP))))

(defthm unsigned-byte-p-of-array-length-when-array-refp
  (implies (array-refp ad dims type heap)
           (unsigned-byte-p 31 (array-length ad heap)))
  :hints (("Goal" :in-theory (enable array-refp))))

(defthm true-listp-of-get-field-contents
  (implies (and (array-refp ad dims type heap) ;dims and type are free vars
                (consp dims))
           (true-listp (get-field ad (array-contents-pair) heap)))
  :hints (("Goal" :in-theory (enable array-refp))))


;todo: make versions for addresses, floats, and doubles
(defthm ARRAY-REFP-of-set-field-of-set-field-initialize
  (implies (and (eql 1 (len dims))
                (true-listp dims)
                (unsigned-byte-p 31 (first dims))
                (ADDRESSP AD)
                (jvm::primitive-typep type)
                (primitive-array-contents-okp vals type)
                (equal (len vals) (first dims))
                (equal array-type `(:ARRAY ,type))
                (true-listp vals))
           (ARRAY-REFP ad
                       dims
                       type
                       (SET-FIELD ad
                                  (class-pair)
                                  array-type
                                  (SET-FIELD ad
                                             (array-contents-pair)
                                             vals
                                             heap))))
  :hints (("Goal" :expand ((ARRAY-REFP AD DIMS type
                                       (SET-FIELD AD (class-pair)
                                                  `(:ARRAY ,type)
                                                  (SET-FIELD AD
                                                             (array-contents-pair)
                                                             VALS HEAP))))
           :in-theory (enable ARRAY-REFP))))

;weird case (you don't know whether the addresses alias, but the contents are okay):
(defthm array-refp-of-set-field-contents-may-alias
  (implies (and (array-refp ad dims element-type heap)
                (equal 1 (len dims))
                (equal (car dims) (len val))
                (true-listp val)
                (array-contents-okp val element-type heap))
           (array-refp ad dims element-type (set-field ad2 (array-contents-pair) val heap)))
  :hints (("Goal" :in-theory (e/d (array-refp GET-CLASS GET-FIELD) (S-IFF))
           :expand ((:free (element-type heap)
                           (ARRAY-REFP AD DIMS element-type heap))))))

(defthm array-refp-of-set-field-contents-same
  (implies (and (array-refp ad dims element-type heap)
                (equal 1 (len dims)))
           (equal (array-refp ad dims element-type (set-field ad (array-contents-pair) val heap))
                  (and (true-listp val)
                       (array-contents-okp val element-type heap)
                       (equal (car dims) (len val)))))
  :hints (("Goal" :in-theory (e/d (array-refp get-class get-field) (s-iff))
           :expand ((:free (element-type heap)
                           (array-refp ad dims element-type heap))))))

;not sure I like this rule because of the free var vals
(defthm array-refp-of-set-field-contents-lemma
  (implies (and (array-refp ad dims type (set-field ad (array-contents-pair) vals heap)) ;vals is a free var, this says that everything except the contents is ok
                (jvm::primitive-typep type) ;gen?
;                (natp (first dim))
;                (true-listp dims)
                (equal 1 (len dims))
                (true-listp vals2)
                (equal (first dims) (len vals2))
                (primitive-array-contents-okp vals2 type))
           (array-refp ad dims type (set-field ad (array-contents-pair) vals2 heap)))
  :hints (("Goal" :in-theory (enable memberp-of-cons-when-constant array-refp))))

; matches a constant list of dims (note that axe does not match a cons pattern with a constant, unlike ACL2)
(defthm array-refp-of-set-field-irrel-one-dim-primitive
  (implies (and (jvm::primitive-typep type) ;otherwise, we could be changing the type of an object whose address is in the array
                (equal (len dims) 1)
                (not (equal ad1 ad2)))
           (equal (array-refp ad1 dims type (set-field ad2 pair value heap))
                  (array-refp ad1 dims type heap)))
  :hints (("Goal" :in-theory (enable array-refp
                                     get-class
                                     memberp-of-cons-when-constant))))

;; This version is for non-primitive element types.
(defthm array-refp-of-set-field-irrel-one-dim-non-primitive
  (implies (and (jvm::class-namep element-type)
                (equal (len dims) 1)
                (not (equal ad ad2))
                (or (not (equal pair (class-pair)))
                    (not (memberp ad2 (array-contents ad heap)))))
           (equal (array-refp ad dims element-type (set-field ad2 pair val heap))
                  (array-refp ad dims element-type heap)))
  :hints (("Goal" :in-theory (enable array-refp get-class))))

;; This one sets multiple fields with set-fields.
(defthm array-refp-of-set-fields-irrel-one-dim-primitive
  (implies (and (jvm::primitive-typep type) ;otherwise, we could be changing the type of an object whose address is in the array
                (equal (len dims) 1)
                (not (equal ad1 ad2)))
           (equal (array-refp ad1 dims type (set-fields ad2 bindings heap))
                  (array-refp ad1 dims type heap)))
  :hints (("Goal" :in-theory (enable set-fields))))

;;;
;;; theorems about array-ref-listp
;;;

(defthm array-ref-listp-of-cdr
  (implies (array-ref-listp ads dims element-type heap)
           (array-ref-listp (cdr ads) dims element-type heap))
  :hints (("Goal" :in-theory (enable array-ref-listp))))

(defthm array-refp-of-car
  (implies (and (array-ref-listp ads dims element-type heap)
                (consp ads))
           (array-refp (car ads) dims element-type heap))
  :hints (("Goal" :in-theory (enable array-ref-listp))))

(defthm array-refp-when-memberp
  (implies (and (array-ref-listp ads dims element-type heap)
                (memberp ad ads))
           (array-refp ad dims element-type heap))
  :hints (("Goal" :induct (true-listp ads)
           :in-theory (enable (:i true-listp) array-ref-listp))))

(defthm get-field-class-when-array-ref-listp-one-dim
  (implies (and (array-ref-listp ads dims type heap)
                (consp dims)
                (memberp ad  ads))
           (equal (get-field ad  (class-pair) heap)
                  (jvm::make-array-type (len dims) type)))
  :hints (("Goal" :induct (true-listp ads)
           :in-theory (e/d (true-listp array-ref-listp get-class)
                           (car-becomes-nth-of-0)))))

(defthm not-null-refp-when-array-ref-listp-one-dim
  (implies (and (array-ref-listp ads dims type heap)
                (equal 1 (len dims))
                (memberp ad  ads))
           (not (null-refp ad )))
  :hints (("Goal" :induct (true-listp ads)
           :expand ((array-refp (car ads)
                                dims
                                type heap)
                    (array-ref-listp ads dims
                                     type heap))
           :in-theory (e/d (true-listp array-ref-listp get-class)
                           (car-becomes-nth-of-0)))))

(defthm addressp-when-array-ref-listp-and-memberp
  (implies (and (array-ref-listp ads dims type heap)
                (memberp ad  ads))
           (addressp ad ))
  :hints (("Goal" :induct (true-listp ads)
           :in-theory (e/d (true-listp array-ref-listp get-class)
                           (car-becomes-nth-of-0)))))

(defthm len-of-contents-when-array-ref-listp
  (implies (and (array-ref-listp ads dims type heap)
                (memberp ad  ads))
           (equal (len (get-field ad  (array-contents-pair) heap))
                  (first dims)))
  :hints (("Goal" :induct (true-listp ads)
           :expand ((array-refp (car ads)
                                dims
                                type heap)
                    (array-ref-listp ads dims
                                     type heap))
           :in-theory (e/d (true-listp array-refp get-class)
                           (car-becomes-nth-of-0)))))

(defthm true-listp-of-get-field-contents-when-array-ref-listp
  (implies (and (array-ref-listp ads dims type heap)
                (consp dims)
                (memberp ad  ads))
           (true-listp (get-field ad  (array-contents-pair) heap)))
  :hints (("Goal" :use (:instance true-listp-of-get-field-contents)
           :in-theory (disable true-listp-of-get-field-contents))))

;rename
(defthm get-field-length-when-array-ref-listp
  (implies (and (array-ref-listp ads dims type heap)
                (eql 1 (len dims))
                (true-listp dims)
                (consp ads))
           (equal (array-length (nth 0 ads) heap)
                  (car dims)))
  :hints (("Goal" :expand ((array-ref-listp ads dims type heap)))))

(defthm unsigned-byte-p-of-car-when-array-ref-listp
  (implies (and (array-ref-listp ads dims type heap)
                (equal 1 (len dims))
                (consp ads))
           (unsigned-byte-p 31 (car dims)))
  :hints (("Goal" :induct (true-listp ads)
           :expand ((array-refp (car ads)
                                dims
                                type heap)
                    (array-ref-listp ads dims
                                     type heap))
           :in-theory (e/d (true-listp array-refp get-class)
                           (car-becomes-nth-of-0
                            ;;bag::len-1-and-memberp-means-you-know-x
                            )))))

(defthm get-field-class-of-nth-when-array-ref-listp
  (implies (and (array-ref-listp ads dims element-type heap)
                (consp dims)
                (natp n)
                (< n (len ads)))
           (equal (get-field (nth n ads) (class-pair) heap)
                  (jvm::make-array-type (len dims) element-type))))

(defthm consp-of-get-field-contents-when-array-ref-listp
  (implies (and (array-ref-listp ads dims type heap)
                (consp dims)
                (memberp ad ads))
           (equal (consp (get-field ad (array-contents-pair) heap))
                  (not (zp (first dims)))))
  :hints (("Goal"
           :induct (true-listp ads)
           :in-theory (enable array-ref-listp
                              array-refp
                              (:i true-listp)))))

;;;
;;; addresses-of-array-ref
;;;

;only the addresses occupied by the array itself (not, e.g., the pointers stored in an array of pointers)
;returns a bag
(mutual-recursion
 (defun addresses-of-array-ref (ad dims heap)
   (declare (xargs :measure (make-ord 1 (+ 1 (len dims)) 0)
                   ;; :guard (and ;want to call array-refp but what about the element-type?
                   ;;         (consp dims)
                   ;;             (true-listp dims)
                   ;;             (all-natp dims)
                   ;;             (addressp ad))
                   ))
   (if (endp (rest dims)) ;one dimension
       (list ad)
     ;; more than one dimension:
     (cons ad
           (addresses-of-array-ref-list (get-field ad (array-contents-pair) heap)
                                        (car dims) ;what if this is not the length of the contents?
                                        (cdr dims)
                                        heap))))

;ads-left counts down...
 (defun addresses-of-array-ref-list (ads ads-left dims heap)
   (declare (xargs :measure (make-ord 1 (+ 1 (len dims)) (+ 1 (nfix ads-left)))
                   ;; :guard (and (consp dims)
                   ;;             (true-listp dims)
                   ;;             (all-natp dims)
                   ;;             (natp ads-left)
                   ;;             (true-listp ads)
                   ;;             (all-addressp ads))
                   ))
   (if (zp ads-left)
       nil
     (append (addresses-of-array-ref (nth (+ -1 ads-left) ads) dims heap)
             (addresses-of-array-ref-list ads (+ -1 ads-left) dims heap)))))

;; (defthm addresses-of-array-ref-opener
;;   (implies (syntaxp (and (quotep dim)
;;                          (< (cadr dim) 20)))
;;            (equal (addresses-of-array-ref item (cons dim dims) heap)
;;                   (let* ((contents (get-field item (array-contents-pair) heap))
;;                          )
;;                     (cons item (addresses-of-array-ref-list contents dim dims heap))))))

(defthm addresses-of-array-ref-list-open-when-small-constant
  (implies (and (syntaxp (and (quotep items-left)
                              (< (cadr items-left) 20)))
                (not (zp items-left))
                )
           (equal (addresses-of-array-ref-list item-list items-left dims heap)
                  (append (addresses-of-array-ref (nth (+ -1 items-left) item-list) dims heap)
                          (addresses-of-array-ref-list item-list (+ -1 items-left) dims heap))))
  :hints (("Goal" :in-theory (enable))))

(defthm addresses-of-array-ref-one-dim
  (implies (and (eql 1 (len dims))
                (true-listp dims))
           (equal (addresses-of-array-ref ad dims heap)
                  (list ad)))
  :hints (("Goal" :expand ((ADDRESSES-OF-ARRAY-REF AD DIMS HEAP))
           :in-theory (enable addresses-of-array-ref))))

(local
 (defun ifun (n)
   (if (zp n)
       n
     (ifun (+ -1 n)))))

;; (defthm addresses-of-array-ref-list-when-dims-is-nil
;;   (equal (addresses-of-array-ref-list item-list items-left nil heap)
;;          nil)
;;   :hints (("Goal" :induct (ifun items-left)
;;            :expand (addresses-of-array-ref-list item-list items-left nil heap)
;;            :in-theory (enable addresses-of-array-ref-list))))

(defopeners jvm::get-array-element-type)

;; (defun jvm::get-array-element-type-of-ref (ad heap)
;;   (let ((class (get-class ad  heap)))
;;     (jvm::get-array-element-type class)))

;;;
;;; get-array-dimensions-of-ref-aux
;;;

;; This assumes all sub-arrays have the same size
;; Returns a list of natps
(defund get-array-dimensions-of-ref-aux (ad type heap)
  (declare (xargs :measure (acl2-count type)
                  :hints (("Goal" :in-theory (enable JVM::GET-ARRAY-COMPONENT-TYPE)))))
  (if (atom type)
      nil ; no more dimensions
    (let* ((contents (array-contents ad heap))
           (dim (len contents)))
      (if (eql 0 dim) ;if we hit a dimension with 0 elements, return 0's for all subsequent dimensions as well
          (repeat (jvm::number-of-array-dimensions type) 0)
        (cons dim
              (get-array-dimensions-of-ref-aux (nth 0 contents) ;recur on the first element
                                               (jvm::get-array-component-type type)
                                               heap))))))

(defthm GET-ARRAY-DIMENSIONS-OF-REF-AUX-of-set-field-irrel
  (implies (and (or (not (equal pair (array-contents-pair)))
                    (not (equal ad ad2)))
                (jvm::typep desc)
                (<= (jvm::number-of-array-dimensions desc) 1))
           (equal (GET-ARRAY-DIMENSIONS-OF-REF-AUX ad desc (SET-FIELD ad2 pair val heap))
                  (GET-ARRAY-DIMENSIONS-OF-REF-AUX ad desc heap)))
  :hints (("Goal" :in-theory (e/d (JVM::GET-ARRAY-COMPONENT-TYPE jvm::typep JVM::NUMBER-OF-ARRAY-DIMENSIONS
                                                           get-array-dimensions-of-ref-aux)
                                  (;LIST::EQUAL-CONS-CASES
                                   ))
           :expand ((JVM::NUMBER-OF-ARRAY-DIMENSIONS (CADR DESC))
                    (GET-ARRAY-DIMENSIONS-OF-REF-AUX AD DESC HEAP)
                    (GET-ARRAY-DIMENSIONS-OF-REF-AUX (NTH 0
                                                          (GET-FIELD AD
                                                                     (array-contents-pair)
                                                                     HEAP))
                                                     (CADR DESC)
                                                     HEAP)))))

(defthm get-array-dimensions-of-ref-aux-of-set-field-same-1d
  (implies (and (equal (jvm::number-of-array-dimensions desc) 1)
                (jvm::typep desc))
           (equal (get-array-dimensions-of-ref-aux ad desc (set-field ad (array-contents-pair) val heap))
                  (list (len val))))
  :hints (("Goal" :in-theory (e/d (jvm::get-array-component-type jvm::typep GET-ARRAY-DIMENSIONS-OF-REF-AUX)
                                  (jvm::primitive-typep))
           :expand ((get-array-dimensions-of-ref-aux ad desc (set-field ad (array-contents-pair) val heap))))))

(defopeners get-array-dimensions-of-ref-aux)

;;;
;;; get-array-dimensions-of-ref
;;;

(defun get-array-dimensions-of-ref (ad heap)
  (let ((type (get-class ad  heap)))
    (get-array-dimensions-of-ref-aux ad  type heap)))

;; ;the item must be either a pointer or a primitive value, neither of which is nil
;; (defthm not-array-refp-of-nil
;;   (not (array-refp nil dims element-type heap))
;;   :hints (("Goal" :in-theory (enable array-refp))))

(defthm nth-when-n-is-zp-2
  (implies (and (syntaxp (not (quotep n))) ;prevents loops
                (zp n))
           (equal (nth n x)
                  (nth 0 x)))
  :hints (("Goal" :in-theory (e/d (nth) (nth-of-cdr)))))

(defthm refs-differ-when-array-dimensions-differ
  (implies (and (array-refp ad1 dims element-type heap) ;just to make sure it is an array (we could do other things here instead)
                (not (equal (get-array-dimensions-of-ref ad1 heap)
                            (get-array-dimensions-of-ref ad2 heap))))
           (not (equal ad1 ad2))))

(defthm refs-differ-when-array-dimensions-differ-alt
  (implies (and (array-refp ad2 dims element-type heap) ;just to make sure it is an array (we could do other things here instead)
                (not (equal (get-array-dimensions-of-ref ad1 heap)
                            (get-array-dimensions-of-ref ad2 heap))))
           (not (equal ad1 ad2))))




;; (thm
;;  (implies (not (equal ad a2))
;;           (equal (ARRAY-REFP ad DIMS type (SET-FIELD AD2 PAIR VAL HEAP))
;;                  (ARRAY-REFP ad DIMS type HEAP)))
;;  :hints (("Goal" :expand (ARRAY-REFP ad DIMS type (SET-FIELD AD2 PAIR VAL HEAP))
;;           :in-theory (enable array-refp))))

(defthm array-ref-listp-of-set-field-irrel-single-dim
  (implies (and (not (memberp ad ads))
                (jvm::primitive-typep type)
                (eql 1 (len dims)))
           (equal (array-ref-listp ads dims type (set-field ad pair val heap))
                  (array-ref-listp ads dims type heap)))
  :hints (("Goal" :induct (true-listp ads)
           :in-theory (enable true-listp
                              memberp-of-cons-when-constant
                              array-ref-listp
                              array-refp ;why?
                              get-class))))

(defthm array-ref-listp-of-set-fields-irrel-single-dim
  (implies (and (not (memberp ad ads))
                (jvm::primitive-typep type)
                (eql 1 (len dims)))
           (equal (array-ref-listp ads dims type (set-fields ad bindings heap))
                  (array-ref-listp ads dims type heap)))
  :hints (("Goal" ;:induct (true-listp ads)
           :in-theory (enable set-fields))))


(make-flag array-refp)

(defthm-flag-array-refp
  ;; Calls of set-field where the field is not relevant to arrays do not affect array-refp.
  (defthm array-refp-of-set-field-irrel-field-name
    (implies (not (memberp pair (array-object-fields)))
             (equal (array-refp ad dims element-type (set-field ad2 pair val heap))
                    (array-refp ad dims element-type heap)))
    :flag array-refp)
  ;; Calls of set-field where the field is not relevant to arrays do not affect array-ref-listp.
  (defthm array-ref-listp-of-set-field-irrel-field-name
    (implies (not (memberp pair (array-object-fields)))
             (equal (array-ref-listp ads dims element-type (set-field ad2 pair val heap))
                    (array-ref-listp ads dims element-type heap)))
    :flag array-ref-listp)
  :hints (("Goal"
           :expand ((array-refp ad dims element-type (set-field ad2 pair val heap)))
           :in-theory (enable array-ref-listp
                              array-refp
                              get-class
                              get-field
                              memberp-of-cons-when-constant))))

;this could be a defmap
(defun array-contents-list (ads heap)
  (if (endp ads)
      nil
    (cons (array-contents (car ads) heap)
          (array-contents-list (cdr ads) heap))))

(defun myind (n lst)
  (if (zp n)
      (list n lst)
    (myind (+ -1 n) (cdr lst))))

(defthm nth-of-array-contents-list
  (implies (and (integerp n) ;t;(not (zp n))
                (<= 0 n)
                (< n (len ads)))
           (equal (nth n (array-contents-list ads heap))
                  (array-contents (nth n ads) heap)))
  :hints (("Goal" :induct (myind n ads))))

(defthm len-of-array-contents-list
  (equal (len (array-contents-list ads heap))
         (len ads)))

;get contents of 2D array at ref
;returns a list with one element per row of the outer array.  the element is a list of the contents of the corresponding row
(defun array-contents2 (ad heap)
  (array-contents-list
   (array-contents ad heap) ;returns a list of references
   heap))

(defthm not-consp-when-number-of-array-dimensions-is-0
  (implies (and (equal (jvm::number-of-array-dimensions desc) free) ;the free variable makes this somewhat cheap (TODO: instead, rewrite this hyp?)
                (zp free)
                (jvm::typep desc))
           (not (consp desc))))

;(in-theory (disable NO-DUPLICATESP-EQUAL-OF-CONS))

;(in-theory (disable CONS-OF-NTH-AND-NTH-PLUS-1))

(defthm array-contents-list-of-set-field-irrel
  (implies (not (memberp ad ads))
           (equal (array-contents-list ads (set-field ad pair value heap))
                  (array-contents-list ads heap))))

(defthm array-contents-list-of-set-field-irrel2
  (implies (not (equal pair (array-contents-pair)))
           (equal (array-contents-list ads (set-field ad pair value heap))
                  (array-contents-list ads heap))))

(defthm array-contents-list-of-clear-field-irrel
  (implies (not (memberp ad ads))
           (equal (array-contents-list ads (clear-field ad pair heap))
                  (array-contents-list ads heap)))
  :hints (("Goal" :in-theory (e/d (clear-field) (SET-TO-NIL-EQUAL-CLEAR-FIELD)))))

(defthm array-contents-list-of-set-fields-irrel
  (implies (not (memberp ad ads))
           (equal (array-contents-list ads (set-fields ad pairs heap))
                  (array-contents-list ads heap))))

;; (defthm nth-not-memberp-of-cdr-when-unique
;;   (implies (and (natp n)
;;                 (< n (len lst))
;;                 (no-duplicatesp-equal lst))
;;            (not (memberp (nth n lst) lst)))
;;   :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))



;bozo should this take a heap or the already extracted contents?
(defund array-row (n ad heap)
  (get-field (nth n (get-field ad (array-contents-pair) heap)) (array-contents-pair) heap))

(defun arraydimension2 (ad heap)
  (len ;(array-contents (nth 0 (array-contents ad heap)) heap)
   (array-row 0 ad heap)
   ))

(defthm array-ref-listp-of-initialize-one-dim-array-irrel-single-dim
  (implies (and (not (memberp ad ads))
                (jvm::primitive-typep type) ;if it's a reference type, might set the class of an element initialize-one-dim-array
                (eql 1 (len dims)))
           (equal (array-ref-listp ads dims type (jvm::initialize-one-dim-array ad type contents iodas))
                  (array-ref-listp ads dims type iodas)))
  :hints (("Goal" :in-theory (enable jvm::initialize-one-dim-array))))


;; (defthm array-refp-of-initialize-2d-array
;;   (implies (and (natp numrows)
;;                 ;(integerp numcols)
;;                 (jvm::intp numrows)
;;                 (jvm::intp numcols)
;;                 (<= 0 numcols)
;;                 (member-equal type '(:BYTE :int)) ;bozo redo things to gen this
;;                 )
;;            (ARRAY-REFP ad (list numrows numcols) type (JVM::INITIALIZE-2D-ARRAY ad type numrows numcols heap)))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-2d-array JVM::INITIALIZE-ONE-DIM-ARRAY))))


;; (defthm get-field-length-of-INITIALIZE-2D-ARRAY-same
;;   (implies (natp numrows)
;;            (equal (array-length ad (JVM::INITIALIZE-2D-ARRAY ad type numrows numcols heap))
;;                   numrows))
;;  :hints (("Goal" :in-theory (enable JVM::INITIALIZE-2D-ARRAY))))

;; (defthm get-field-length-of-initialize-2d-array-same-2
;;   (implies (and (natp numrows)
;;                 (memberp ad (n-new-ads numrows (set::insert ad2 (rkeys heap)))))
;;            (equal (array-length ad (jvm::initialize-2d-array ad2 type numrows numcols heap))
;;                   (nfix numcols)))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-2d-array))))

;; (thm
;;  (IMPLIES (NOT (CONSP REF-LIST))
;;           (ARRAY-REF-LISTP ADS ITEMS-LEFT NIL ':BYTE HEAP))
;;  :hints (("Goal" :expand (ARRAY-REF-LISTP ADS ITEMS-LEFT NIL :BYTE HEAP)
;;           :in-theory (enable ARRAY-REF-LISTP))))

(defthm nth-not-equal-nth-when-unique
  (implies (and (natp m)
                (< m (len lst))
                (natp n)
                (< n (len lst))
                (no-duplicatesp-equal lst)
                (not (equal m n))
                )
           (equal (equal (nth n lst) (nth m lst))
                  nil))
  :hints (("Goal" :in-theory (e/d (no-duplicatesp-equal nth) (nth-of-cdr)))))

;dims is now just a variable, so this matches better
(defthm ubp-of-arraylen-better
  (implies (and (array-refp ad dims type heap)
                (consp dims))
           (unsigned-byte-p 31 (array-length ad heap)))
  :hints (("Goal" :in-theory (enable array-refp))))

;could be expensive?
(defthm ARRAY-REFP-of-set-field-when-blah
  (IMPLIES (AND (ARRAY-REF-LISTP ADS dims TYPE HEAP) ;ref-list is a free var
                (MEMBERP AD ADS)
                (jvm::primitive-typep type) ;gen!
                (equal 1 (len dims))
                (true-listp dims)
                (primitive-array-contents-okp val type)
                (true-listp val)
                (equal (len val) (first dims)))
           (ARRAY-REFP ad DIMS type
                       (SET-FIELD ad (array-contents-pair) VAL HEAP)))
  :HINTS (("Goal" :INDUCT (TRUE-LISTP ADS)
           :IN-THEORY (E/D (TRUE-LISTP ARRAY-REFP GET-CLASS)
                           (CAR-BECOMES-NTH-OF-0
;CONS-EQUAL-REWRITE-CONSTANT-VERSION
                            ;; BAG::LEN-1-AND-MEMBERP-MEANS-YOU-KNOW-X
                            )))))

;(in-theory (disable BAG::LEN-AT-MOST-1-AND-MEMBERP-MEAN-LEN-EXACTLY-1)) ;todo: should use polarities?

;(in-theory (disable TRUE-LISTP-WHEN-NOT-CONSP)) ;seems that this could be slow

;(in-theory (disable LIST::EQUAL-CAR-DIFFERENTIAL)) ;seems that this could be slow

;given a list of 1-d arrays, if we set the contents of any of them to a suitable value, we still get a list of well-formed 1-d arrays
(defthm array-ref-listp-of-set-field-lemma
  (implies (and (array-ref-listp ads dims type heap)
                (jvm::primitive-typep type) ;gen?
                (equal 1 (len dims))
                (primitive-array-contents-okp val type)
                (true-listp val)
                (equal (len val) (first dims))
                (memberp ad ads))
           (array-ref-listp ads dims type (set-field ad (array-contents-pair) val heap)))
  :hints (("Goal" :induct (true-listp ads)
           :expand ((array-ref-listp ads dims type heap)
                    (:free (type) (array-ref-listp ads dims type
                                                   (set-field ad
                                                              (array-contents-pair)
                                                              val heap))))
           :in-theory (e/d (true-listp array-refp get-class)
                           (car-becomes-nth-of-0)))))

;; (thm
;;  (implies (and (array-refp-aux ad dims element-type heap 'nil)
;;                (member-eq element-type '(:byte :boolean :short :int)) ;gen!
;;                (eql 2 (len dims)) ;gen?
;;                (true-listp dims)
;;                (posp (first dims))
;;                )
;;           (equal (GET-ARRAY-DIMENSIONS-OF-REF ad heap)
;;                  dims))
;;  :otf-flg t
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :do-not-induct t
;;           :expand ((GET-ARRAY-DIMENSIONS-OF-REF-AUX AD (MAKE-ARRAY-DESCRIPTOR 2 ELEMENT-TYPE)
;;                                                  HEAP)
;;                    (ARRAY-REFP-AUX AD DIMS ELEMENT-TYPE HEAP NIL)
;;                    (GET-ARRAY-DIMENSIONS-OF-REF-AUX ad
;;                                                     (GET-FIELD AD (class-pair)
;;                                                                HEAP)
;;                                                     HEAP)
;;                    (GET-ARRAY-DIMENSIONS-OF-REF-AUX AD (MAKE-ARRAY-DESCRIPTOR 1 ELEMENT-TYPE) HEAP))

;;           :in-theory (e/d (ARRAY-REFP-AUX) (CONS-EQUAL-REWRITE-CONSTANT-VERSION)))))

;disabled because this can be slow
(defthmd refs-differ-when-classes
  (implies (not (equal (get-class ad1 heap)
                       (get-class ad2 heap)))
           (not (equal ad1 ad2))))

;move
(defthmd not-equal-of-nth-when-not-memberp
  (implies (and (not (memberp a x))
                (natp n)
                (< N (LEN X)))
           (not (equal a (nth n x)))))
;move
(defthm equal-of-car-and-nth-when-no-duplicatesp-equal
  (implies (and (no-duplicatesp-equal x)
                (consp x)
                (natp n)
                (< n (len x)))
           (equal (equal (car x) (nth n x))
                  (zp n))))



;bbozo gen
;2d
(defthm ARRAY-REFP-of-set-field-irrel-byte
  (implies (and (not (equal ad ad2))
                (not (memberp ad2 (array-contents ad heap))))
           (equal (ARRAY-REFP ad (list numrows numcols) ':byte (SET-FIELD ad2 pair val heap))
                  (ARRAY-REFP ad (list numrows numcols) ':byte heap)))
  :otf-flg t
  :hints (("Goal" :expand ((ARRAY-REFP ad (list numrows numcols) ':byte heap)
                           (ARRAY-REFP ad (list numrows numcols) ':byte (SET-FIELD ad2 pair val heap)))
           :in-theory (enable ARRAY-REFP get-class))))

;; This one can get rid of inner set-fields that are irrelevant
(defthm array-refp-of-set-field-of-set-field-irrel
  (implies (not (memberp pair2 (array-object-fields)))
           (equal (array-refp ad dims element-type (set-field ad1 pair1 value1 (set-field ad2 pair2 value2 heap)))
                  (array-refp ad dims element-type (set-field ad1 pair1 value1 heap))))
  :hints (("Goal" :use ((:instance set-field-of-set-field-both (ref1 ad1) (ref2 ad2))
                        (:instance array-refp-of-set-field-irrel-field-name (ad2 ad2) (pair pair2) (val value2) (heap (SET-FIELD AD1 PAIR1 VALUE1 HEAP))))
           :in-theory (disable set-field-of-set-field-both set-field-of-set-field-diff-1 set-field-of-set-field-diff-2 ;EQUAL-SET-FIELD-DESTRUCT-GEN
                               array-refp-of-set-field-irrel-field-name))))

(defthm array-ref-listp-of-set-field-of-set-field-irrel
  (implies (not (memberp pair2 (array-object-fields)))
           (equal (array-ref-listp ads dims element-type (set-field ad1 pair1 value1 (set-field ad2 pair2 value2 heap)))
                  (array-ref-listp ads dims element-type (set-field ad1 pair1 value1 heap))))
  :hints (("Goal" :use ((:instance set-field-of-set-field-both (ref1 ad1) (ref2 ad2))
                        (:instance array-ref-listp-of-set-field-irrel-field-name (ad2 ad2) (pair pair2) (val value2) (heap (SET-FIELD AD1 PAIR1 VALUE1 HEAP))))
           :in-theory (disable set-field-of-set-field-both
                               set-field-of-set-field-diff-1
                               set-field-of-set-field-diff-2 ;EQUAL-SET-FIELD-DESTRUCT-GEN
                               array-ref-listp-of-set-field-irrel-field-name))))



;todo: turn (list numrows) into a variable so it matches better
(defthm ARRAY-REFP-of-set-class
  (implies (and (jvm::class-namep element-type)
                (not (equal ad ad2))
;               (not (memberp ad2 (array-contents ad heap)))
                (ARRAY-REFP ad (list numrows) element-type heap) ;likely too strong! the class of ad2 won't be right
                )
           (ARRAY-REFp ad (list numrows) element-type (SET-FIELD ad2 (class-pair) element-type heap)))
  :otf-flg t
  :hints (("Goal" :expand ((ARRAY-REFP ad (list numrows) element-type heap)
                           (ARRAY-REFP ad (list numrows) element-type (SET-FIELD ad2 (class-pair) element-type heap)))
           :in-theory (enable ARRAY-REFP get-class))))

;Common idiom for updating an element of an array of pointers
(defthm array-refp-of-set-class-better
  (implies (and (jvm::class-namep element-type)
                (not (equal ad ad2))
                (ADDRESSP AD)
                (ADDRESSP AD2)
;               (not (memberp ad2 (array-contents ad heap)))
                (array-refp ad (list numrows) element-type heap)
                (equal oldcontents (GET-FIELD ad (array-contents-pair) heap)) ;can't substitute this in the LHS b/c that would give 2 heap terms thht won't match.  we expect this hyp to be proved by first rewriting to discard irrelevant set-fields
                (natp n)
                (< n (len (array-contents ad heap))))
           (array-refp ad
                       (list numrows)
                       element-type
                       (set-field ad2 (class-pair) element-type
                                  ;; update the contents
                                  (set-field ad
                                             (array-contents-pair)
                                             (update-nth n ad2 oldcontents)
                                             heap))))
  :otf-flg t
  :hints (("Goal" :expand ((array-refp ad (list numrows) element-type heap)
                           (array-refp ad (list numrows) element-type (set-field ad2 (class-pair) element-type heap)))
           :in-theory (enable array-refp get-class))))





(defthm array-refp-one-dim-of-initialize-one-dim-array-irrel
  (implies (and (not (equal ad ad2))
                (memberp type '(:byte :int :boolean :short)) ;drop?
                (eql 1 (len dims))
                (true-listp dims))
           (equal (array-refp ad dims type (jvm::initialize-one-dim-array ad2 type2 contents heap))
                  (array-refp ad dims type heap)))
  :hints (("Goal" :in-theory (enable jvm::initialize-one-dim-array))))

;2d
(defthm len-of-get-field-contents-when-array-ref-listp
  (implies (and (array-ref-listp ads (list colcount) type heap)
                (memberp ad ads))
           (equal (len (get-field ad (array-contents-pair) heap))
                  colcount))
  :hints (("Goal" :expand (array-refp ad (list rowcount colcount)
                                      :int heap)
           :induct (true-listp ads)
           :in-theory (e/d ( ;array-elem-2d2 ;array-elem-2d ;array-refp
                            array-contents2
                            array-row
                            true-listp
                            )
                           ( ;array-elem-2d2-recollapse
                            ;;array-elem-2d-recollapse
                            ;;array-ref-listp-open-when-consp
                            ;;array-row-recollapse
                            ;;array-elem-2d-of-cons ;bozo
                            ;;nth-of-array-row
                            )))))

;move
(defthm not-memberp-of-nth-0-and-cdr
  (implies (no-duplicatesp x)
           (not (memberp (nth 0 x) (cdr x)))))

;; (defthm clear-nth-of-array-contents-list
;;   (implies  (and (<= 0 n)
;;                  (integerp n)
;;                  (no-duplicatesp-equal ads)
;;                  (< n (len ads)))
;;             (equal (list::clear-nth n (array-contents-list ads heap))
;;                    (array-contents-list ads (clear-field (nth n ads) (array-contents-pair) heap))))
;;   :hints (("Goal" :induct (myind n ads) ;i accidentally had ads instead of ads here; should that be a warning?
;;            :expand ((ARRAY-CONTENTS-LIST ADS HEAP)
;;                     (ARRAY-CONTENTS-LIST
;;                      ADS
;;                      (CLEAR-FIELD (NTH 0 ADS)
;;                                   (array-contents-pair)
;;                                   HEAP)))
;;            :in-theory (e/d ( ;memberp-nth-and-cdr  ;yuck
;;                             LIST::CLEAR-NTH
;;                             no-duplicatesp-equal) (LIST::UPDATE-NTH-EQUAL-REWRITE
;;                                                    LIST::UPDATE-NTH-BECOMES-CLEAR-NTH))
;;            :do-not
;;            '(generalize eliminate-destructors))))

;BOZO make other versions?
(defthm array-refp-of-set-field-contents-both
  (implies (array-refp ad (list dim) ':int heap)
           (equal (array-refp ad (list dim) ':int (set-field ad2 (array-contents-pair) val heap))
                  (if (equal ad ad2)
                      (and (true-listp val)
                           (equal dim (len val))
                           (all-unsigned-byte-p 32 ;jvm::intp-list
                                                val))
                    t)))
  :hints (("Goal" :in-theory (enable GET-FIELD ;yuck
                                     array-contents-okp
                                     array-refp))))

;BOZO make other versions?
(defthm array-ref-listp-of-set-field-memberp
  (implies (and (memberp ad ads)
                (array-ref-listp ads (list dim) ':int heap)
                (and (true-listp val)
                     (equal dim (len val))
                     (all-unsigned-byte-p 32 ;jvm::intp-list
                                           val)))
           (array-ref-listp ads (list dim) ':int (set-field ad (array-contents-pair) val heap)))
  :hints (("Goal"
           :expand ((ARRAY-REF-listp ADS (LIST (LEN VAL))
                                     :INT
                                     (SET-FIELD AD (array-contents-pair)
                                                VAL HEAP)))
           :induct (len ads)
           :in-theory (enable (:induction len)))))

(defthm in-of-nth-and-rkeys-when-array-ref-listp
  (implies (and (array-ref-listp ads dims element-type heap)
                (natp n)
                (< n (len ads))
                (consp dims)
                )
           (SET::IN (NTH n ads) (RKEYS heap)))
  :hints (("Goal" ;:induct (len ads)
           :in-theory (e/d (array-ref-listp NTH) (NTH-OF-CDR
                                                 )))))

(defthm in-of-nth-of-contents-and-rkeys-when-array-refp
  (implies (and (array-refp ad dims element-type heap)
                (natp n)
                (< n (len (get-field ad (array-contents-pair) heap)))
                (consp (cdr dims)))
           (set::in (nth n (get-field ad (array-contents-pair) heap)) (rkeys heap)))
  :hints (("Goal" ;:induct (len ads)
           :do-not-induct t
;   :expand ((array-refp ad dims element-type heap))
           :use (:instance in-of-nth-and-rkeys-when-array-ref-listp
                           (dims (cdr dims))
                           (ads (get-field ad (array-contents-pair) heap)))
           :in-theory (e/d (array-refp (:i nth)) (
                                             in-of-nth-and-rkeys-when-array-ref-listp)))))
