; Axe rules about the JVM
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These rules call the axe-syntax functions.

(include-book "../axe-syntax-functions") ; for heavier-dag-term
(include-book "kestrel/jvm/execution-common" :dir :system) ; for TH
(include-book "kestrel/jvm/jvm-rules" :dir :system)
(include-book "kestrel/jvm/int-subtypes" :dir :system)
(include-book "../known-booleans")
(include-book "../bv-list-rules-axe")
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(local (include-book "kestrel/jvm/jvm-facts" :dir :system))

;; Declare some JVM-related functions to be known-booleans:
(add-known-boolean set::in)
(add-known-boolean array-refp)
(add-known-boolean array-ref-listp)
(add-known-boolean jvm::string-has-been-internedp)
(add-known-boolean jvm::intern-table-okp)
(add-known-boolean addressp)
(add-known-boolean address-or-nullp)
(add-known-boolean null-refp)
(add-known-boolean jvm::bound-in-class-tablep)
(add-known-boolean java-booleanp)
(add-known-boolean java-bytep)
(add-known-boolean java-shortp)
(add-known-boolean java-charp)
(add-known-boolean java-intp)
(add-known-boolean java-longp)
(add-known-boolean java-boolean-as-int-p)
(add-known-boolean java-byte-as-int-p)
(add-known-boolean java-short-as-int-p)
(add-known-boolean java-char-as-int-p)
(add-known-boolean jvm::java-floatp)
(add-known-boolean jvm::java-doublep)
(add-known-boolean jvm::heapp)
(add-known-boolean jvm::intern-tablep)
(add-known-boolean jvm::jvm-statep)
(add-known-boolean jvm::type-implementsp)

;TODO: Add 'axe' to the names of these rules

;breaks the abstraction. may be needed for axe, where operand-stack-size doesn't get executed
;todo: just use a constant opener?
(defthm jvm::operand-stack-size-of-nil
  (equal (jvm::operand-stack-size nil)
         0))

;Not really a JVM rule.
(defthmd s-diff-s-axe
  (implies (and (axe-syntaxp (heavier-dag-term b a))
                (not (equal a b)))
           (equal (s b y (s a x r))
                  (s a x (s b y r)))))

;perhaps oddly we move the set-fields with heavier ads to the front (they will be more likely to be referenced again soon)
(defthmd set-field-of-set-field-reorder
  (implies (and (axe-syntaxp (heavier-dag-term ref2 ref1))
                (not (equal ref1 ref2)))
           (equal (set-field ref1 pair1 value1
                             (set-field ref2 pair2 value2 heap))
                  (set-field ref2 pair2 value2
                             (set-field ref1 pair1 value1 heap)))))

;; For the same ref, sort by pairs:
(defthmd set-field-of-set-field-reorder-pairs
  (implies (and (axe-syntaxp (heavier-dag-term pair2 pair1))
                (not (equal pair1 pair2)))
           (equal (set-field ref pair1 value1 (set-field ref pair2 value2 heap))
                  (set-field ref pair2 value2 (set-field ref pair1 value1 heap)))))

;; We sort first by class name
(defthm set-static-field-of-set-static-field-diff-class-axe
  (implies (and (axe-syntaxp (heavier-dag-term class-name1 class-name2))
                (not (equal class-name1 class-name2)))
           (equal (jvm::set-static-field class-name1 field-name1 value1 (jvm::set-static-field class-name2 field-name2 value2 static-field-map))
                  (jvm::set-static-field class-name2 field-name2 value2 (jvm::set-static-field class-name1 field-name1 value1 static-field-map))))
  :hints (("Goal" :use set-static-field-of-set-static-field-diff-class
           :in-theory (disable set-static-field-of-set-static-field-diff-class))))

;; We sort second by field name (so here the class names must be the same)
(defthm set-static-field-of-set-static-field-diff-field-axe
  (implies (and (axe-syntaxp (heavier-dag-term field-name1 field-name2))
                (not (equal field-name1 field-name2)))
           (equal (jvm::set-static-field class-name field-name1 value1 (jvm::set-static-field class-name field-name2 value2 static-field-map))
                  (jvm::set-static-field class-name field-name2 value2 (jvm::set-static-field class-name field-name1 value1 static-field-map))))
  :hints (("Goal" :use set-static-field-of-set-static-field-diff-field
           :in-theory (disable set-static-field-of-set-static-field-diff-field))))

;fixme handle this!  can we keep th closed?  could just use the definition instead of this rule...
(defthmd th-rewrite
  (equal (th)
         0))



;todo: could restrict to BV terms
;used by Axe
;;Often used to prove that a value stored by set-field is non-nil, which tells
;;us that the corresponding heap address becomes bound by the set-field.
(defthmd not-equal-nil-when-integerp
  (implies (integerp x)
           (not (equal nil x)))
  :hints (("Goal" :in-theory (disable (:TYPE-PRESCRIPTION BVPLUS)))))

;; TODO: Make the equal a quick syntactic check?
(defthm address-or-nullp-when-addressp-free
  (implies (and (addressp free) ;poor man's backchain limit
                (equal free x))
           (address-or-nullp x)))

;; TODO: Make the equal a quick syntactic check?
(defthm not-null-refp-when-addressp-free
  (implies (and (addressp free) ;poor man's backchain limit
                (equal free x))
           (not (null-refp x))))

;; TODO: Make the equal a quick syntactic check?
;; use null-refp as the normal form
(defthm addressp-when-address-or-nullp-free
  (implies (and (address-or-nullp free) ;poor man's backchain limit
                (equal free x))
           (equal (addressp x)
                  (not (null-refp x)))))


(def-constant-opener jvm::pc)
(def-constant-opener jvm::locals)
(def-constant-opener jvm::stack)
(def-constant-opener jvm::locked-object)
(def-constant-opener jvm::method-info)
(def-constant-opener jvm::method-designator)
(def-constant-opener jvm::cur-class-name)
(def-constant-opener jvm::cur-method-name)
(def-constant-opener jvm::cur-method-descriptor)

(def-constant-opener jvm::method-program)

(def-constant-opener jvm::java-floatp)
(def-constant-opener jvm::float-signp)
(def-constant-opener jvm::make-regular-float)
(def-constant-opener jvm::float<)
(def-constant-opener jvm::float=)
(def-constant-opener jvm::regular-float-value)
(def-constant-opener jvm::fcmpl)
(def-constant-opener jvm::regular-floatp)

(def-constant-opener jvm::field-id-type)
(def-constant-opener jvm::field-publicp)
(def-constant-opener jvm::field-privatep)
(def-constant-opener jvm::field-protectedp)
(def-constant-opener jvm::field-staticp)
(def-constant-opener jvm::field-access-flags)

(def-constant-opener jvm::method-publicp)
(def-constant-opener jvm::method-privatep)
(def-constant-opener jvm::method-protectedp)
(def-constant-opener jvm::method-staticp)
(def-constant-opener jvm::method-nativep)
(def-constant-opener jvm::method-abstractp)
(def-constant-opener jvm::method-synchronizedp)
(def-constant-opener jvm::method-access-flags)

(def-constant-opener jvm::any-less-than-zero)

(def-constant-opener jvm::nth-local)
(def-constant-opener jvm::update-nth-local)
(def-constant-opener jvm::typep)
;(def-constant-opener jvm::reference-typep)
(def-constant-opener jvm::array-typep)
(def-constant-opener jvm::class-or-interface-namep)
(def-constant-opener jvm::primitive-typep)
(def-constant-opener jvm::class-namep)
(def-constant-opener jvm::field-namep)
(def-constant-opener jvm::field-idp)

(def-constant-opener jvm::lookup-method-in-class-info)

;; todo: improve def-constant-opener to handle a function and all supporters:
(def-constant-opener jvm::extract-package-name-from-class-name)
(def-constant-opener string-contains-charp)
(def-constant-opener position-equal)
(def-constant-opener position-equal-ac)
(def-constant-opener substring-before-last-occurrence)
(def-constant-opener reverse)
(def-constant-opener revappend)
(def-constant-opener substring-after-terminator)
(def-constant-opener readthroughterminator-aux)
(def-constant-opener jvm::bound-in-class-tablep)
(def-constant-opener jvm::binding)
(def-constant-opener jvm::bind)
(def-constant-opener jvm::lookup-method-in-classes)
(def-constant-opener jvm::initialize-one-dim-array)
(def-constant-opener jvm::make-frame)
(def-constant-opener jvm::count-slots-in-types)
(def-constant-opener jvm::type-slot-count)
(def-constant-opener jvm::set-static-field)
(def-constant-opener jvm::get-static-field)
(def-constant-opener set-field)
(def-constant-opener get-field)
(def-constant-opener jvm::get-array-component-type)
(def-constant-opener gen-init-bindings-for-class)

(def-constant-opener jvm::exception-handler-targets)

(def-constant-opener alistp)

(def-constant-opener new-ad)
(def-constant-opener new-ad-aux)
(def-constant-opener nth-new-ad)
(def-constant-opener n-new-ads2)

(def-constant-opener set::delete)
(def-constant-opener set::tail)
(def-constant-opener set::head)
(def-constant-opener set::emptyp)
(def-constant-opener set::sfix)
(def-constant-opener set::setp)
(def-constant-opener FAST-<<)

;fixme add type-prescription rule-classes to lots of booleanp rules?
(defthm booleanp-of-array-refp
  (booleanp (array-refp ad dims element-type heap)))

(defthm booleanp-of-array-ref-listp
  (booleanp (array-ref-listp ads dims element-type heap)))

(defthm <-of-constant-and-call-stack-size-when-negative
  (implies (and (syntaxp (quotep k))
                (< k 0))
           (< k (jvm::call-stack-size call-stack))))

(defthm integerp-of-call-stack-size
  (integerp (jvm::call-stack-size call-stack)))

;move
(defthmd posp-of-+-of-constant
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp x))
           (equal (posp (+ k x))
                  (< (- k) x))))

(defopeners jvm::make-array-type)
(defopeners jvm::resolve-class)
(defopeners jvm::reference-typep)
