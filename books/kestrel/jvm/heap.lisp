; More material on the JVM heap
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo switch to JVM package?

;how much of this stuff is common with android?

(include-book "heap0")
(include-book "maps")
;(include-book "heap-clearing")
(include-book "classes") ;for jvm::class-decl-non-static-fields, get-superclasses, and maybe other stuff
(include-book "class-tables") ;for all-bound-in-class-tablep
(include-book "kestrel/lists-light/all-equal-dollar" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (in-theory (disable true-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm len-of-strip-cars
  (equal (len (strip-cars x))
         (len x)))

(defthm len-of-strip-cads
  (equal (len (strip-cdrs x))
         (len x)))

(defthm alistp-of-append
  ;; [Jared] changed for compatibility with std/alists/alistp.lisp
  (equal (alistp (append x y))
         (and (alistp (true-list-fix x))
              (alistp y)))
  :hints(("Goal" :in-theory (enable append))))

;fixme: use this more
;call this boundp?
(defund bound-in-heap (ad heap)
  (set::in ad (acl2::dom heap)))

;; ============================================================================================
;;
;; init-ref-in-heap
;;
;; ============================================================================================

;; The stuff below used to be called build-an-instance.
;; I renamed the functions since they're no longer building an instance but rather initializing an instance in a heap by repeatedly calling set-field.

;; Eric rewrote some functions to call only set-field, not s
;; or bind.  In fact, they used to call cons. Yuck!  Now I can do
;; proofs without opening up set-field in my specs to get them to
;; match the result of applying these functions.  To me, this is
;; clearly the right approach.

(encapsulate (((default-value-for-unknown-type *) => *))
             (local (defun default-value-for-unknown-type (type) (declare (ignore type)) t))
             (defthm default-value-for-unknown-type-not-nil
               (iff (default-value-for-unknown-type type)
                    t)))

(defun default-value-for-float ()
  (declare (xargs :guard t))
  (jvm::make-regular-float :pos 0))

(defthmd default-value-for-float-not-nil
  (iff (default-value-for-float)
       t))

(defun default-value-for-double ()
  (declare (xargs :guard t))
  (jvm::make-regular-double :pos 0))

(defthmd default-value-for-double-not-nil
  (iff (default-value-for-double)
       t))

;fixme what about the return address type? can't appear here?
(defund default-value (type)
  (declare (xargs :guard (jvm::typep type)))
  (if (jvm::class-namep type)
      (null-ref)
    (if (member-eq type jvm::*integral-types*)
        0
      (if (eq type :boolean)
          0
        (if (eq type :float)
            (default-value-for-float)
          (if (eq type :double)
              (default-value-for-double)
            (if (jvm::is-array-typep type)
                (null-ref)
              (default-value-for-unknown-type type) ;0
              )))))))

(defthm default-value-non-nil
  (default-value desc)
  :rule-classes ((:type-prescription))
  :hints (("Goal" :in-theory (enable default-value))))


;each generated binding is of the form ((class-name . field-id) . value), where value is the default value (0 or null-ref)
;can we avoid consing these up?
(defund gen-init-bindings-for-class (field-info-alist class-name)
  (declare (xargs :guard (and (jvm::class-namep class-name)
                              (jvm::field-info-alistp field-info-alist))))
  (if (endp field-info-alist)
      nil
    (let* ((entry (first field-info-alist))
           (field-id (car entry))
;           (field-info (cdr entry))
 ;          (field-name (car field-id))
           (field-type (jvm::field-id-type field-id))
           ;;we could store the default value in the class table instead of recomputing it, but it's probably not worth it
           (default-value (default-value field-type)))
      (cons (cons (cons class-name field-id) default-value)
            (gen-init-bindings-for-class (rest field-info-alist) class-name)))))

(defthm alistp-of-gen-init-bindings-for-class
  (alistp (gen-init-bindings-for-class field-info-alist class-name))
  :hints (("Goal" :in-theory (enable gen-init-bindings-for-class))))

(defthm all-name-type-pairsp-of-strip-cars
  (implies (jvm::field-info-alistp field-info-alist)
           (jvm::all-field-idp (strip-cars field-info-alist)))
  :hints (("Goal" :in-theory (enable jvm::field-info-alistp))))

(defthm len-gen-init-bindings-for-class
  (equal (len (gen-init-bindings-for-class field-info-alist class-name))
         (len field-info-alist))
  :hints (("goal" :in-theory (enable gen-init-bindings-for-class))))

(defthm true-listp-gen-init-bindings-for-class
  (true-listp (gen-init-bindings-for-class field-info-alist class-name)))

(defthm not-memberp-of-class-pair-and-strip-cars-of-gen-init-bindings-for-class
  (implies (jvm::field-info-alistp field-info-alist)
           (not (memberp (class-pair) (strip-cars (acl2::gen-init-bindings-for-class field-info-alist class-name)))))
  :hints (("Goal" :in-theory (enable acl2::gen-init-bindings-for-class
                                     jvm::field-info-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: do we need to reify these?
(defund gen-init-bindings (class-names class-table)
  (declare (xargs :guard (and (jvm::all-class-namesp class-names)
                              (true-listp class-names)
                              (jvm::class-tablep class-table)
                              (jvm::all-bound-in-class-tablep class-names class-table))
                  :guard-hints (("Goal" :in-theory (e/d (JVM::CLASS-TABLEP
;                                                         key-list ;yuck (use this consistently and disable)
                                                         ) (JVM::FIELD-INFO-ALISTP
                                                            jvm::FIELD-INFO-ALISTP-OF-class-decl-non-static-fields))))))
  (if (endp class-names)
      nil
    (append (gen-init-bindings-for-class (jvm::class-decl-non-static-fields (jvm::get-class-info (car class-names) class-table))
					 (car class-names))
	    (gen-init-bindings (cdr class-names) class-table))))

(defthm true-listp-gen-init-bindings
  (true-listp (gen-init-bindings class-name class-table))
  :hints (("Goal" :in-theory (enable gen-init-bindings))))

(defthm alistp-of-gen-init-bindings
  (alistp (gen-init-bindings class-names class-table))
  :hints (("Goal" :in-theory (enable gen-init-bindings))))

(defthm all-heap-object-keyp-of-strip-cars-of-gen-init-bindings-for-class
  (implies (and (jvm::class-namep class-name)
                (jvm::field-info-alistp field-info-alist))
           (acl2::all-heap-object-keyp (strip-cars (acl2::gen-init-bindings-for-class field-info-alist class-name))))
  :hints (("Goal" :in-theory (e/d (acl2::gen-init-bindings-for-class JVM::FIELD-INFO-ALISTP) (jvm::field-idp)))))

(defthm all-heap-object-keyp-of-strip-cars-of-gen-init-bindings
  (implies (and (jvm::all-class-namesp class-names)
                (jvm::all-bound-in-class-tablep class-names class-table)
                (jvm::class-tablep class-table))
           (acl2::all-heap-object-keyp (strip-cars (acl2::gen-init-bindings class-names class-table))))
  :hints (("Goal" :in-theory (enable acl2::gen-init-bindings))))

(defthm not-memberp-of-class-pair-and-strip-cars-of-gen-init-bindings
  (implies (and (jvm::class-tablep class-table)
                (jvm::all-bound-in-class-tablep class-names class-table))
           (not (memberp (class-pair) (strip-cars (acl2::gen-init-bindings class-names class-table)))))
  :hints (("Goal" :in-theory (enable acl2::gen-init-bindings))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;would like to pass in less than the whole class table?
(defund init-ref-in-heap (ad class-name class-table heap)
  (declare (xargs :guard (and (acl2::addressp ad)
                              (jvm::class-tablep class-table)
                              (jvm::class-namep class-name)
                              (jvm::bound-in-class-tablep class-name class-table)
                              (jvm::heapp heap)
                              (not (jvm::is-an-interfacep class-name class-table)))
                  :guard-hints (("Goal" :in-theory (enable acl2::init-ref-in-heap acl2::all-addressp ;key-list
                                                           )))))
  ;; set the class:
  (set-class ad
	     class-name
	     (set-fields ad
                         ;; initialize all the (non-static) fields in the class and its superclasses:
                         (gen-init-bindings (cons class-name
                                                  (jvm::get-superclasses class-name class-table))
                                            class-table)
                         heap)))

(defthm jvm::get-class-of-init-ref-in-heap
  (implies (jvm::class-namep class-name)
           (equal (acl2::get-class ad (acl2::init-ref-in-heap ad class-name class-table heap))
                  class-name))
  :hints (("Goal" :in-theory (enable acl2::init-ref-in-heap acl2::get-class))))

(defthm get-field-of-special-data-class-and-init-ref-in-heap-same
  (equal (get-field ad (class-pair) (init-ref-in-heap ad class-name class-table heap))
         class-name)
  :hints (("Goal" :in-theory (enable init-ref-in-heap))))

(defthm get-field-of-init-ref-in-heap-diff-ref
  (implies (not (equal adr1 adr2))
	   (equal (get-field adr1 pair1 (init-ref-in-heap adr2 class-name class-table heap))
		  (get-field adr1 pair1 heap)))
  :hints (("Goal" :in-theory (enable init-ref-in-heap))))

;; (defthm strip-cars-gen-init-bindings-for-class
;;   (implies (not (equal adr1 adr2))
;; 	   (not (memberp adr1 (strip-cars
;; 			      (gen-init-bindings-for-class
;; 			       adr2
;; 			       class-name
;; 			       class-table)))))
;;   :hints (("Goal" :in-theory (enable gen-init-bindings-for-class memberp))))

;; (defthm strip-cars-gen-init-bindings
;;   (implies (not (equal adr1 adr2))
;; 	   (not (memberp adr1 (strip-cars
;; 			      (gen-init-bindings adr2
;; 						 class-names
;; 						 class-table)))))
;;   :hints (("Goal" :in-theory (enable gen-init-bindings))))

;; ;was called build-a-class-instance
;; ;redo this!
;; ;i'm not sure this is done right
;; (defun init-class-ref-in-heap (adr sfields class-table heap)
;;   (set-fields adr
;;    (append (gen-init-bindings-for-class "java.lang.Class" (cons "<name>" sfields))
;; 	   (gen-init-bindings-for-class
;; 					"java.lang.Object"
;; 					(class-decl-fields (jvm::get-class-info ;bound?
;;                                                             "java.lang.Object" class-table))))
;;    heap))
;BOZO do the bindings used for gen-init-bindings-for-class have, etc. the same form as the ones for set-field?


;; (defthm strip-cars-of-gen-init-bindings-for-class
;;   (equal (strip-cars (gen-init-bindings-for-class ad class-name field-ids))
;;          (my-repeat ad (len field-ids)))
;;   :hints (("goal" :in-theory (enable gen-init-bindings-for-class my-repeat))))



;; (defthm strip-cars-of-gen-init-bindings
;;   (equal (strip-cars (gen-init-bindings ad class-names class-table))
;;          (my-repeat ad (length (gen-init-bindings ad class-names class-table))))
;;   :hints (("goal" :in-theory (enable gen-init-bindings))))

;; ;why did i have to open up so much?
;; (defthm get-class-of-init-class-of-ref-in-heap
;;   (implies (not (equal 'special-data class-name))
;; 	   (equal (get-field adr 'special-data 'class
;; 			     (init-class-of-ref-in-heap adr class-name field-ids heap))
;; 		  (get-field adr 'special-data 'class
;; 			     heap)))
;;   :hints (("goal" :in-theory (enable init-class-of-ref-in-heap set-field get-field))))


;; (defthm get-class-of-INIT-REF-IN-HEAP-aux
;;   (implies (not (memberp 'special-data class-names))
;; 	   (EQUAL
;; 	    (GET-FIELD
;; 	     ADR
;; 	     'SPECIAL-DATA
;; 	     'CLASS
;; 	     (INIT-REF-IN-HEAP-AUX ADR class-names CLASS-TABLE heap))
;; 	    (GET-FIELD
;; 	     ADR
;; 	     'SPECIAL-DATA
;; 	     'CLASS
;; 	     heap)
;; 	    ))
;; 	   :hints (("Goal" :in-theory (enable INIT-REF-IN-HEAP-AUX)))
;;  )


;; (defthm get-class-of-INIT-REF-IN-HEAP
;;   (implies (not (memberp 'special-data (cons class-name
;; 					    (jvm::class-decl-superclasses
;; 					     (bound? class-name class-table)))))
;; 	   (equal
;; 	    (GET-FIELD
;; 	     adr
;; 	     'SPECIAL-DATA
;; 	     'CLASS
;; 	     (INIT-REF-IN-HEAP adr
;; 			       class-name
;; 			       CLASS-TABLE
;; 			       heap))
;; 	    class-name))
;;   :hints (("Goal" :in-theory (enable INIT-REF-IN-HEAP)))
;;   )

;; ;gross? breaks the map abstraction?
;; (defthm FIELD-IDP-of-caar
;;   (IMPLIES (AND (CONSP FIELD-INFO-MAP)
;;                 (mapp field-info-map)
;;                 (JVM::ALL-NAME-TYPE-PAIRSP (SET::2LIST (RKEYS FIELD-INFO-MAP))))
;;            (JVM::FIELD-IDP (CAAR FIELD-INFO-MAP)))
;;   :hints (("Goal" :expand ((JVM::ALL-NAME-TYPE-PAIRSP (SET::2LIST (KEY-SET FIELD-INFO-MAP)))
;;                            (KEY-SET FIELD-INFO-MAP))
;;            :in-theory (enable JVM::ALL-NAME-TYPE-PAIRSP SET::2LIST RKEYS mapp key-set))))

;; (defthm all-heap-object-keyp-of-strip-cars-of-gen-init-bindings-for-class-aux
;;   (implies (and (jvm::class-namep class-name)
;;                 (JVM::ALL-NAME-TYPE-PAIRSP field-ids)
;;                 (jvm::field-info-mapp field-info-map))
;;            (acl2::all-heap-object-keyp (strip-cars (acl2::gen-init-bindings-for-class-aux field-ids class-name field-info-map))))
;;   :hints (("Goal" :in-theory (e/d (acl2::gen-init-bindings-for-class-aux JVM::ALL-NAME-TYPE-PAIRSP jvm::field-info-mapp) (JVM::FIELD-IDP)))))

;; ;fixme move
;; ;fixme should jvm::class-decl-superclass be enabled or disabled?

;move?
(defthm heapp-of-init-ref-in-heap
  (implies (and (jvm::heapp heap)
                (jvm::bound-in-class-tablep class-name class-table)
                (jvm::class-namep class-name) ;implied by the above?
                (acl2::addressp ad)
                (jvm::class-tablep class-table)
                (not (jvm::is-an-interfacep class-name class-table)))
           (jvm::heapp (acl2::init-ref-in-heap ad class-name class-table heap)))
  :hints (("Goal" :in-theory (enable acl2::init-ref-in-heap acl2::all-addressp ;key-list
                                     ))))

(defthm rkeys-of-set-field
  (implies value ;(not (equal value nil))
           (equal (rkeys (set-field ad pair value heap))
                  (set::insert ad (rkeys heap))))
  :hints (("Goal" :in-theory (enable acl2::set-field))))

(defthm rkeys-of-set-field-both
  (equal (rkeys (set-field addr pair val heap))
         (if (and ;(not val)
                  (equal nil (s pair val (g addr heap))))
             (set::delete addr (rkeys heap))
           (set::insert addr (rkeys heap))))
  :hints (("Goal" :in-theory (enable set-field))))

(defthm rkeys-of-set-field-subset
  (set::subset (rkeys (set-field ad pair value heap))
               (set::insert ad (rkeys heap)))
  :hints (("Goal" :in-theory (enable set-field))))

(defthm rkeys-of-set-field-cases
  (or (equal (rkeys (set-field ad pair value heap))
             (set::insert ad (rkeys heap)))
      (equal (rkeys (set-field ad pair value heap))
             (set::delete ad (rkeys heap))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable set-field))))

(defthm rkeys-of-set-fields-subset
  (set::subset (rkeys (set-fields ad pairs heap))
               (set::insert ad (rkeys heap)))
  :hints (("Subgoal *1/2" :in-theory (disable rkeys-of-set-field-subset)
           :expand (SET-FIELDS AD PAIRS HEAP)
           :use (:instance rkeys-of-set-field-subset
                           (pair (CAAR PAIRS))
                           (value (CDAR PAIRS))
                           (heap (SET-FIELDS AD (CDR PAIRS) HEAP))))
          ("Goal" :in-theory (enable set-fields))))

(defthm set-fields-of-set-field
  (implies (not (memberp pair (strip-cars pairs)))
           (equal (set-fields ad pairs (set-field ad pair value heap))
                  (set-field ad pair value (set-fields ad pairs heap))))
  :hints (("Goal" :in-theory (enable set-fields))))

(local
 (progn
;do we still need this?
   (defun s-many (keys vals map)
     (if (endp keys)
         map
       (s-many (cdr keys)
               (cdr vals)
               (s (car keys) (car vals) map))))

   (defthm s-many-of-s-diff
     (equal (s-many keys vals (s key val map))
            (if (memberp key keys)
                (s-many keys vals map)
              (s key val (s-many keys vals map))))
     :hints (("subGoal *1/2" :cases ((equal key (car keys))))))

   (defthm s-many-iff
     (implies (and (no-duplicatesp-equal keys)
                   (equal (len keys) (len vals))
                   (not (all-equal$ nil vals)))
              (iff (s-many keys vals map)
                   (consp keys))))

   (defthm clr-of-s-many-diff
     (implies (not (memberp key keys))
              (equal (clr key (s-many keys vals map))
                     (s-many keys vals (clr key map))))
     :hints (("subGoal *1/2" :cases ((equal key (car keys))))))

   ;; used once below
   (defthmd set-fields-rewrite
     (implies (no-duplicatesp-equal (strip-cars bindings))
              (equal (SET-FIELDS AD BINDINGS HEAP)
                     (s ad (s-many (strip-cars bindings)
                                   (strip-cdrs bindings)
                                   (g ad heap))
                        heap)))
     :hints (("Goal" :do-not '(generalize eliminate-destructors)
              :in-theory (e/d (s-many set-fields set-field) ( ;S==R
                                                             )))))))

;todo: the unique test might be expensive and seems like overkill
;it should suffice to find one pair with a non-nil value that is not shadowed by an earlier pair..
(defthm rkeys-of-set-fields
  (implies (and (not (all-equal$ nil (strip-cdrs pairs)))
                (no-duplicatesp-equal (strip-cars pairs)))
           (equal (rkeys (set-fields ad pairs heap))
                  (set::insert ad (rkeys heap))))
  :hints (("Goal" :in-theory (enable set-fields-rewrite ;NO-DUPLICATESP-EQUAL-OF-CONS
                                     ))))


(defthm in-of-rkeys-of-set-fields-irrel
  (implies (not (equal ad ad2))
           (equal (set::in ad (rkeys (set-fields ad2 pairs heap)))
                  (set::in ad (rkeys heap))))
  :hints (("Goal" :in-theory (enable set-fields))))

(defthm rkeys-of-set-fields-cases
  (implies (consp pairs)
           (or (equal (rkeys (set-fields ad pairs heap))
                      (set::insert ad (rkeys heap)))
               (equal (rkeys (set-fields ad pairs heap))
                      (set::delete ad (rkeys heap)))))
  :rule-classes nil
  :otf-flg t
  :hints (("Goal" :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (set-fields endp) (SET::PICK-A-POINT-SUBSET-STRATEGY
                                              SET::DOUBLE-CONTAINMENT)))
          ("subGoal *1/2" :in-theory (disable ;SET::PICK-A-POINT-SUBSET-STRATEGY
                                              SET::DOUBLE-CONTAINMENT)
           :use (:instance rkeys-of-set-field-cases (pair (CAAR PAIRS)) (value (CDAR PAIRS)) (heap (SET-FIELDS AD (CDR PAIRS) HEAP)))
           :expand ((set-fields ad pairs heap)))))

(defthmd get-field-when-not-in-rkeys
  (implies (NOT (SET::IN AD (RKEYS HEAP)))
           (EQUAL (GET-FIELD AD pair HEAP)
                  nil))
  :hints (("Goal" :in-theory (enable GET-FIELD))))

(defthm GET-CLASS-of-set-field-irrel-pair
  (implies (not (equal pair (CLASS-PAIR)))
           (equal (GET-CLASS REF (set-FIELD REF2 pair val HEAP))
                  (GET-CLASS REF HEAP)))
  :hints (("Goal" :in-theory (e/d (get-class) ()))))

(defthm in-rkeys-when-get-field-non-nil-two
  (implies (get-field ad pair heap)
           (set::in ad (rkeys heap)))
  :hints
  (("Goal" :use (:instance g-iff-gen (a ad) (r heap))
    :in-theory (e/d (get-field)
                    (g-iff-gen)))))

;(thm
; (equal (G ad (SET-FIELDS ad bindings heap))

(defthm jvm::bound-in-heap-of-init-ref-in-heap
  (implies (jvm::class-namep class-name)
           (acl2::bound-in-heap ad (acl2::init-ref-in-heap ad class-name class-table heap)))
  :hints (("Goal" :in-theory (enable acl2::init-ref-in-heap acl2::bound-in-heap))))
