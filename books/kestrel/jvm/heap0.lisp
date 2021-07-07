; A model of the JVM heap
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;This book contains a model of the JVM heap.

;FIXME think hard about this new heap model to make sure it's faithful to the semantics of the JVM
;changes from the M5 heap model (references are not wrapped in a call of 'ref; now they are just integers)
;the heap is now a map, which admits nice g/s reasoning
;the new-ad functions (and related functions are guaranteed to return fresh addresses, without needing a heap invariant)

(include-book "kestrel/maps/maps" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "adstop")
(include-book "types")
(include-book "fields")
(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "utilities")
(include-book "utilities2")

(local (in-theory (disable g-iff-gen)))

(acl2::defforall-simple addressp)

(verify-guards acl2::all-addressp)

;; Most keys in the heap object are pairs of class names and field-ids.
(defun class-name-field-id-pairp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (jvm::class-namep (car x))
       (jvm::field-idp (cdr x))))

;Exception to the above comment (used to store the class of the heap object):
;fixme are there any other fake fields like this?
(defmacro class-pair ()
  ''(:special-data . :class))

(defun heap-object-keyp (x)
  (declare (xargs :guard t))
  (or (class-name-field-id-pairp x)
      (equal x (class-pair))))

(defthm heap-object-keyp-of-cons
  (iff (heap-object-keyp (cons x y))
       (or (and (jvm::class-namep x) (jvm::field-idp y))
           (and (eq :special-data x) (eq :class y))))
  :hints (("Goal" :in-theory (enable heap-object-keyp))))

(defforall-simple heap-object-keyp)
(verify-guards all-heap-object-keyp)

(defun jvm::heap-objectp (x)
  (declare (xargs :guard t))
  (and (mapp x)
       (let ((keys (key-list x)))
         (all-heap-object-keyp keys)
         ;;fixme add something about the values stored in the map? (each is either an address or a primitive?)
         )))

(defforall all-bound-to-heap-objectsp (key heap)
  (jvm::heap-objectp (g key heap))
;  :declares ((xargs :guard (string-listp key)))
  :fixed heap)

(verify-guards all-bound-to-heap-objectsp)

(defund jvm::heapp (heap)
  (declare (xargs :guard t))
  (and (mapp heap)
       (let ((keys (key-list heap)))
         (and (acl2::all-addressp keys)
              (all-bound-to-heap-objectsp keys heap)))))

(defthm addressp-when-in-domain-of-heapp
  (implies (and (set::in item (rkeys heap))
                (jvm::heapp heap))
           (addressp item))
  :hints (("Goal" :in-theory (enable jvm::heapp))))

(defun jvm::empty-heap () (declare (xargs :guard t)) (empty-map))

(defthm heapp-of-empty-heap
  (jvm::heapp (jvm::empty-heap)))

;fixme make sure this is used consistently...
;disable?
;the model used to use  '(ref -1)
;fixme use :null?
(defun null-ref ()
  (declare (xargs :guard t))
  -1)

(in-theory (disable (:executable-counterpart null-ref)))

;; used by Axe (TODO: why is null-ref being opened up?)
(defthm equal-of-minus-1-and-null-ref
  (equal (equal '-1 (null-ref))
         t))

(defthm not-addressp-of-null-ref
  (not (addressp (null-ref))))

(defthm equal-of-nil-and-null-ref
  (equal (equal nil (null-ref))
         nil)
  :hints (("Goal" :in-theory (enable null-ref))))

(defthm equal-of-null-ref-and-nil
  (equal (equal (null-ref) nil)
         nil)
  :hints (("Goal" :in-theory (enable null-ref))))

;;;
;;; null-refp
;;;

;disable?
(defun null-refp (ref)
  (declare (xargs :guard t))
  (equal (null-ref) ref))

(defthm null-refp-of-null-ref
  (null-refp (null-ref)))

(defthmd not-null-refp-when-addressp
  (implies (addressp ref)
           (not (null-refp ref))))

;justifies including null-refp in the list of known predicates
(defthm booleanp-of-null-refp
  (booleanp (null-refp ref)))

;;;
;;; address-or-nullp
;;;

(defun address-or-nullp (x)
  (declare (xargs :guard t))
  (or (addressp x)
      (equal (null-ref) x)))

;justifies including address-or-nullp in the list of known predicates
(defthm booleanp-of-address-or-nullp
  (booleanp (address-or-nullp x)))

(defthm addressp-when-address-or-nullp-and-not-null-refp
  (implies (and (address-or-nullp x)
                (not (null-refp x)))
           (addressp x)))

;watch for loops
(defthmd address-or-nullp-when-addressp
  (implies (addressp x)
           (address-or-nullp x)))

;normalize to null-refp or not null-refp
;watch for loops
(defthmd addressp-when-address-or-nullp
  (implies (address-or-nullp x)
           (equal (addressp x)
                  (not (null-refp x)))))

(defthm address-or-nullp-of-null-ref
  (address-or-nullp (null-ref)))

(defthm address-or-nullp-of-new-ad
  (address-or-nullp (new-ad ads)))

(defthm address-or-nullp-of-nth-new-ad
  (address-or-nullp (nth-new-ad n ads)))

;;
;; GET-FIELD
;;

(defthmd not-ifrp-when-mapp
  (implies (mapp heap)
           (not (ifrp heap)))
  :hints (("Goal" :in-theory (enable jvm::heapp))))

(defthmd not-ifrp-when-heapp
  (implies (jvm::heapp heap)
           (not (ifrp heap)))
  :hints (("Goal" :in-theory (enable jvm::heapp))))

(defthmd mapp-when-heap-objectp
  (implies (jvm::heap-objectp obj)
           (mapp obj))
  :hints (("Goal" :in-theory (enable jvm::heapp))))

(defthmd not-ifrp-of-g-when-heapp
  (IMPLIES (JVM::HEAPP HEAP)
           (NOT (IFRP (G AD HEAP))))
  :hints (("Goal"
           :cases ((member ad (SET::2LIST (RKEYS HEAP))))
           :in-theory (enable jvm::heapp not-ifrp-when-heapp not-ifrp-when-mapp mapp-when-heap-objectp))))

;; Returns the value in HEAP of the field of the object at AD corresponding to
;; PAIR.  PAIR is a pair of a class-name and a field-id (exceptions: the pairs
;; we use to store the class of an object and the contents of an array
;; (actually perhaps legal).
(defund get-field (ad pair heap)
  (declare (xargs :guard (and (addressp ad)
                              (or (class-name-field-id-pairp pair)
                                  (equal pair (class-pair)))
                              (jvm::heapp heap))
                  :guard-hints (("Goal" :in-theory (e/d (not-ifrp-of-g-when-heapp) (g-iff-gen))))))
  (fastg pair (fastg ad heap)))

(defthm get-field-of-nil
  (equal (get-field ad pair nil)
         nil)
  :hints (("Goal" :in-theory (enable get-field))))

;;
;; SET-FIELD
;;

;returns a new heap
(defund set-field (ad class-field-pair value heap)
  (declare (xargs :guard t)) ; require heapp?
  (let* ((old-instance (g ad heap))
         (new-instance (s class-field-pair value old-instance))
	 (new-heap (s ad new-instance heap)))
    new-heap))

(defthm all-bound-to-heap-objectsp-of-s
  (implies (and (all-bound-to-heap-objectsp keys heap)
                (case-split (jvm::heap-objectp val)))
           (all-bound-to-heap-objectsp keys (s key val heap)))
  :hints (("Goal" :in-theory (enable all-bound-to-heap-objectsp))))

(defthm addressp-fw
  (implies (addressp ad)
           ad)
  :rule-classes ((:forward-chaining)))

(defthm jvm::heap-objectp-of-s
  (implies (and (heap-object-keyp key)
                (jvm::heap-objectp heap))
           (jvm::heap-objectp (s key value heap))))

(defthm heapp-of-set-field
  (implies (and (jvm::heapp heap)
                (addressp ad)
                (heap-object-keyp class-field-pair))
           (jvm::heapp (set-field ad class-field-pair value heap)))
  :hints (("Goal" :in-theory (e/d (set-field jvm::heapp ;addressp
                                      ) (JVM::HEAP-OBJECTP)))))

(defthm set-field-nil-nil
  (equal (set-field ad pair nil nil)
         nil)
  :hints (("goal" :in-theory (enable set-field))))

(defund get-class (ad heap)
  (declare (xargs :guard (and (addressp ad)
                              (jvm::heapp heap))))
  (get-field ad (class-pair) heap))

;to be left enabled?
(defun set-class (ad new-class heap)
  (declare (xargs :guard t))
  (set-field ad (class-pair) new-class heap))

;; Theorems about get-field and set-field

;;
;;
;; Theorems about get of set
;;
;;

;fixme rename these to use my new naming scheme

;This logically subsumes the next 4 theorems but can cause a case-split, so I put it first (since more recent rules will be tried first).
(defthm get-field-of-set-field-both
  (equal (get-field ad1 pair1 (set-field ad2 pair2 value heap))
	 (if (and (equal ad1 ad2)
                  (equal pair1 pair2))
	     value
	   (get-field ad1 pair1 heap)))
  :hints (("Goal" :in-theory (enable get-field set-field))))

(defthm get-field-of-set-field-same
  (equal (get-field ref pair (set-field ref pair value heap))
	 value))

(defthm get-field-of-set-field-diff-2
  (implies (not (equal pair1 pair2))
	   (equal (get-field ref1 pair1 (set-field ref2 pair2 value heap))
		  (get-field ref1 pair1 heap))))

;classes can differ or fields can differ.  here, refs differ
(defthm get-field-of-set-field-diff-1
  (implies (not (equal ref1 ref2))
	   (equal (get-field ref1 pair1 (set-field ref2 pair2 value heap))
		  (get-field ref1 pair1 heap))))


;should the previous 3 rules be combined for efficiency?

;;
;;
;; Theorems about set of get
;;
;;

(defthm set-field-of-get-field-same
  (equal (set-field ref pair (get-field ref pair heap) heap)
	 heap)
  :hints (("goal" :in-theory (enable get-field set-field))))

;;
;;
;; Theorems about set of set
;;
;;

;We sort nested s(et) expressions by ref, then by class, then by field

;may cause case-split
;the :loop-stopper only need apply when the "then-part" of the if is chosen
;this rule won't fire when the else-part would be chosen?

(defthm set-field-of-set-field-both
  (equal (set-field ref1 pair1 value1
			   (set-field ref2 pair2 value2 heap))
	 (if (or (not (equal ref1 ref2))
		 (not (equal pair1 pair2)))
	     (set-field ref2 pair2 value2
			       (set-field ref1 pair1 value1 heap))
	   (set-field ref1 pair1 value1 heap)
	   ))
  :rule-classes ((:rewrite :loop-stopper ((ref1 ref2)
					  (pair1 pair2))))
  :hints (("Goal" :in-theory (enable get-field set-field))))


(defthm set-field-of-set-field-same
  (equal (set-field ref pair value1 (set-field ref pair value2 heap))
	 (set-field ref pair value1 heap))
  :hints (("Goal" :in-theory (enable get-field set-field))))


(defthm set-field-of-set-field-diff-2
  (implies (not (equal pair1 pair2))
	   (equal (set-field ref1 pair1 value1
				    (set-field ref2 pair2 value2  heap))
		  (set-field ref2 pair2 value2
                             (set-field ref1 pair1 value1 heap))))
  :rule-classes ((:rewrite :loop-stopper ((ref1 ref2)
					  (pair1 pair2)))))

;classes or fields or refs can differ.  here, refs differ
(defthm set-field-of-set-field-diff-1
  (implies (not (equal ref1 ref2))
	   (equal (set-field ref1 pair1 value1 (set-field ref2 pair2 value2 heap))
		  (set-field ref2 pair2 value2 (set-field ref1 pair1 value1 heap))))
  :rule-classes ((:rewrite :loop-stopper ((ref1 ref2)
					  (pair1 pair2)))))


;TTODO or consider sorting from high to low to aid in sharing (usually heap are filled from start to end, rather than from end to start)
;TTODO same applies to heaps - what about records?
(defthmd set-field-of-set-field-diff-1-constant-ads
  (implies (and (syntaxp (quotep ref1))
                (syntaxp (quotep ref2)) ;bbozo weaken
                (< ref2 ref1))
           (equal (set-field ref1 pair1 value1 (set-field ref2 pair2 value2 heap))
                  (set-field ref2 pair2 value2 (set-field ref1 pair1 value1 heap))))
  :rule-classes ((:rewrite :loop-stopper ((ref1 ref2) (pair1 pair2)))))
;;
;; clear-field
;;

(defund clear-field (ref pair heap)
  (set-field ref pair nil heap))

(defthm clear-field-of-nil
  (equal (clear-field ad pair nil)
         nil)
  :hints (("goal" :in-theory (enable clear-field))))

(defthm equal-set-field-destruct
  (equal (equal (set-field ref pair value1 heap1)
		(set-field ref pair value2 heap2))
	 (and (equal value1 value2)
	      (equal (clear-field ref pair heap1)
		     (clear-field ref pair heap2))))
  :hints (("Goal" :in-theory (enable clear-field set-field))))

(defthm clear-field-of-set-field-both
  (equal (clear-field ref1 pair1 (set-field ref2 pair2 value heap))
	 (if (and (equal ref1 ref2)
                  (equal pair1 pair2))
	     (clear-field ref1 pair1 heap)
	   (set-field ref2 pair2 value (clear-field ref1 pair1 heap))))
  :hints (("Goal" :in-theory (enable clear-field set-field ))))

(defthm clear-field-of-set-field-diff
  (implies (not (and (equal ref1 ref2)
		     (equal pair1 pair2))) ;distribute?
	   (equal (clear-field ref1 pair1
				      (set-field ref2 pair2 value heap))
		  (set-field ref2 pair2 value (clear-field ref1 pair1 heap))))
  :hints (("Goal" :in-theory (enable clear-field set-field ))))

(defthm clear-field-of-set-field-same
  (equal (clear-field ref pair (set-field ref pair value heap))
	 (clear-field ref pair heap))
  :hints (("Goal" :in-theory (enable clear-field set-field ))))

;more theorems needed about clr?


;; ;similar theorem for set-field?
;; (defthm reduce-claim-thatset-class-doesnt-change-heap
;;   (equal (equal (set-class-of-ref ref class-name heap)
;; 		heap)
;; 	 (equal (get-class-of-ref ref heap) class-name))
;;     :hints (("goal" :in-theory (enable set-class-of-ref get-class-of-ref))))


(defthm set-field-of-get-field-same-eric
  (implies (equal (get-field ref pair heap)
		  (get-field ref pair heap2))
	   (equal (set-field ref pair (get-field ref pair heap2) heap)
		  heap)))

(defthm set-field-of-get-field-same-eric-2
  (implies (equal value (get-field ref pair heap))
	   (equal (set-field ref pair value heap)
		  heap)))


;(in-theory (disable  MEMBERP-BECOMES-IN  MEMBERP-MEANS-IN))

;BOZO prove a thm about cardinality of difference?

;; (defthm bag::memberp-of-remove-all-irrel-rewrite
;;   (implies (not (equal x y))
;;            (equal (memberp x (bag::remove-all y lst))
;;                   (memberp x lst))))


;; (defthm new-ad-not-bound-helper2-better
;;   (implies (case-split (sets::setp ad-set))
;;            (equal (memberp (new-ad-aux ad-set current-try) ad-set)
;;                   nil))
;;   :hints (("subgoal *1/2"
;;            :use (:instance new-ad-not-bound-helper
;;                            (ad-set (sets::difference ad-set (sets::insert CURRENT-TRY nil)))
;;                            (current-try (+ 1 current-try))))
;;           ("Goal" :in-theory (enable new-ad-aux))))

;BOZO use in instead of memberp?
;move
;do we even need this?
;; (defthm not-memberp-dom-means-g-is-nil
;;   (implies (not (memberp ad (dom heap)))
;;            (equal (g ad heap)
;;                   nil)))


;; ;BOZO make a memberp version
;; (defthm new-ad-not-in-dom
;;   (equal (sets::in (new-ad ad-list) ad-list)
;;          nil)
;;   :hints (("Goal" :in-theory (enable new-ad
;;                                      new-ad-not-bound-helper2))))


;; (defthm new-ad-not-memberp-dom
;;   (equal (memberp (new-ad dom) dom)
;;          nil)
;;   :hints (("Goal" :in-theory (enable new-ad
;;                                      new-ad-not-bound-helper2-better))))

;; (defthm new-ad-not-memberp
;;   (implies (sublistp list (dom heap))
;;            (not (memberp (new-ad (dom heap))
;;                          list)))
;;   :hints (("Goal" :use   new-ad-not-memberp-dom
;;            :in-theory (e/d (IN-BECOMES-MEMBERP)
;;                            (memberp-becomes-in
;;                             new-ad-not-memberp-dom)))))

;bozo put this stuff back?
;; (thm
;;  (implies (not (set::in a (rkeys r)))
;;           (equal (g a r)
;;                  nil))
;;  :hints (("Goal" :in-theory (enable rkeys ACL2->RCD ifrp))))

;; ;drop? no?
;; (defthm g-of-new-ad
;;   (equal (g (new-ad (dom heap)) heap)
;;          nil))

;; ;can we get away with just one of these next 2?
;; (defthm new-ad-not-equal-something-in-dom
;;   (implies (sets::in xx (dom heap))
;;            (equal (equal xx (new-ad (dom heap)))
;;                   nil)))

;could be expensive?
;gen the (dom heap) to a variable?
(defthm new-ad-not-equal-something-in-dom-2
  (implies (set::in xx (dom heap))
           (equal (equal xx (new-ad (dom heap)))
                  nil))
  :hints (("goal" :in-theory (enable))))

;label the crucial property of new-ad

;will also have to fixup build-an-instance or whatever it's called now


;each member of the list BINDINGS is of the form: ((class-name . field-id) . value)
(defund set-fields (ad bindings heap)
  (declare (xargs :guard (alistp bindings)))
  (if (endp bindings)
      heap
    (let* ((first-binding (car bindings))
           (class-field-pair (car first-binding))
           (value (cdr first-binding)))
      (set-field ad class-field-pair value
                 (set-fields ad (cdr bindings) heap)
                 ))))

(defthm set-fields-of-nil
  (equal (set-fields ad nil heap)
         heap)
  :hints (("goal" :in-theory (enable set-fields))))

(defthm set-fields-of-non-cons
  (implies (not (consp bindings))
           (equal (set-fields ad bindings heap)
                  heap))
  :hints (("goal" :in-theory (enable set-fields))))

;loops with defn set-fields?
(defthmd set-fields-collect-1
  (equal (set-field ad pair value (set-field ad pair2 value2 heap))
         (set-fields ad (list (cons pair value)
                              (cons pair2 value2))
                     heap))
  :hints (("Goal" :in-theory (enable set-fields))))

;loops with defn set-fields!
(defthmd set-fields-collect-2
  (equal (set-field ad pair value (set-fields ad bindings heap))
         (set-fields ad (cons (cons pair value) bindings) heap))
  :hints (("Goal" :in-theory (enable set-fields))))

;fixme this is just lookup-equal!
;; (defund lookup-pair-in-bindings (pair bindings)
;;   (if (endp bindings)
;;       nil
;;     (if (equal pair (caar bindings))
;;         (cdar bindings)
;;       (lookup-pair-in-bindings pair (cdr bindings)))))

;; (defthm lookup-equal-of-cons
;;   (equal (lookup-equal pair (cons binding bindings))
;;          (if (equal pair (car binding))
;;              (cdr binding)
;;            (lookup-equal pair bindings)))
;;   :hints (("goal" :in-theory (enable lookup-equal))))

;;
;; clear-binding
;;

;remove all the bindings from BINDINGS whose keys match PAIR
(defund clear-binding (pair bindings)
  (if (endp bindings)
      nil
    (let ((binding (car bindings)))
      (if (equal (car binding) pair)
          (clear-binding pair (cdr bindings))
        (cons binding (clear-binding pair (cdr bindings)))))))

(defthm clear-binding-nil
  (equal (clear-binding pair nil)
         nil)
  :hints (("goal" :in-theory (enable clear-binding))))

(defthm clear-binding-of-not-consp
  (implies (not (consp x))
           (equal (clear-binding pair x)
                  nil))
  :hints (("goal" :in-theory (enable clear-binding))))

(defthm clear-binding-of-cons
  (equal (clear-binding pair (cons binding bindings))
         (if (equal pair (car binding))
             (clear-binding pair bindings)
           (cons binding (clear-binding pair bindings))))
  :hints (("Goal" :in-theory (enable clear-binding))))

(defthm clear-binding-of-clear-binding
  (equal (clear-binding pair (clear-binding pair bindings))
         (clear-binding pair bindings))
  :hints (("goal" :in-theory (enable clear-binding))))

(defthm acl2-count-clear-binding-decreases
  (implies (and (consp bindings) (true-listp bindings))
           (<= (acl2-count (clear-binding pair bindings))
               (acl2-count bindings)))
  :rule-classes :linear
  :hints (("goal" :do-not '(eliminate-destructors generalize)
           :in-theory (enable clear-binding acl2-count)))
  )

;; ;this removes duplicates from bindings.
;; ;a "duplicate binding" is a binding which binds a pair which has already been bound by an earlier binding.
;; ;could rewrite this to not call clear-field.  see my-remove-duplicates... no! would get the wrong one...
;; (defund remove-duplicate-bindings (bindings)
;;   (declare (xargs :hints (("Goal" :do-not '(eliminate-destructors)
;;                            :in-theory (disable; ACL2-COUNT-CDR
;;                                                acl2-count-clear-binding-decreases
;; ;                                               sets::consp-means-acl2-count-decreases-on-cdr
;;                                                )
;;                            :use ( ;(:instance acl2-count-cdr (x bindings))
;;                                   (:instance acl2-count-clear-binding-decreases
;;                                              (bindings (cdr bindings))
;;                                              (pair (caar bindings))))
;;                            :do-not-induct t))))
;;   (if (or (endp bindings)
;;           (not (true-listp bindings)) ;drop?
;;           )
;;       nil
;;     (cons (car bindings)
;;           (remove-duplicate-bindings (clear-binding (caar bindings) (cdr bindings))))))

;; (defthm REMOVE-DUPLICATE-BINDINGS-of-non-consp
;;   (IMPLIES
;;    (NOT (CONSP BINDINGS))
;;    (equal (REMOVE-DUPLICATE-BINDINGS BINDINGS)
;;           nil))
;;   :hints (("Goal" :in-theory (enable REMOVE-DUPLICATE-BINDINGS))))

;consider using insert instead of cons below
;fixme just use strip-cars?!
;; (defund pair-yield-of-bindings (bindings)
;;   (DECLARE (XARGS :GUARD (ALISTP bindings)))
;;   (if (endp bindings)
;;       nil
;;     (cons (caar bindings) (pair-yield-of-bindings (cdr bindings)))))

;; (defund pair-yield-of-bindings (bindings)
;;   (pair-yield-of-bindings-aux (remove-duplicate-bindings bindings)))

(defthm strip-cars-of-non-consp
  (implies (not (consp bindings))
           (equal (strip-cars bindings)
                  nil))
  :hints (("goal" :in-theory (enable strip-cars))))

(defthm strip-cars-of-cons-cons
  (equal (strip-cars (cons (cons pair value) bindings))
         (cons pair (strip-cars bindings)))
  :hints (("goal" :in-theory (enable strip-cars))))

;; Matches the version in books/std/alists/strip-cars.lisp
(defthm strip-cars-of-cons
  (equal (strip-cars (cons a x))
         (cons (car a)
               (strip-cars x))))

;; Matches the version in books/std/alists/strip-cars.lisp
(defthm strip-cdrs-of-cons
  (equal (strip-cdrs (cons a x))
         (cons (cdr a)
               (strip-cdrs x))))

(defthm set-to-nil-equal-clear-field
  (equal (set-field ad pair nil heap)
         (clear-field ad pair heap)
         )
  :hints (("goal" :in-theory (enable set-field clear-field)))
  )

(theory-invariant (incompatible (:rewrite SET-TO-NIL-EQUAL-CLEAR-FIELD)
                                (:definition clear-field)))

(defthm clear-field-of-clear-field
  (equal (clear-field ad pair (clear-field ad2 pair2 heap))
         (clear-field ad2 pair2 (clear-field ad pair heap)))
  :rule-classes ((:rewrite :loop-stopper ((ad ad2)
                                          (pair pair2))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (set-difference-theories
                       (enable clear-field)
                       '( SET-TO-NIL-EQUAL-CLEAR-FIELD)))))

;what if the ads differ?
(defthm clear-field-of-set-fields
  (equal (clear-field ad pair (set-fields ad bindings heap))
         (set-fields ad (clear-binding pair bindings)
                     (clear-field ad pair heap)))
  :hints (("goal"
           :in-theory (set-difference-theories
                       (enable set-fields clear-binding)
                       '(set-fields-collect-2))
           :do-not '(eliminate-destructors generalize))))

(defthm set-fields-of-clear-binding
  (implies (consp bindings)
           (equal (set-fields ad (cons (car bindings)
                                       (clear-binding (caar bindings) (cdr bindings)))
                              heap)
                  (set-fields ad bindings heap))
           )
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable set-fields)
                              '( SET-FIELDS-COLLECT-2))
           :do-not '(eliminate-destructors))))


;other cases?
(defthm clear-field-of-set-fields-diff
  (implies (not (equal ad ad2))
           (equal (CLEAR-FIELD ad pair (SET-FIELDS ad2 bindings heap))
                  (SET-FIELDS ad2 bindings (CLEAR-FIELD ad pair heap))))
  :hints (("Goal" :in-theory (e/d (set-fields)
                                  (set-fields-collect-2)))))

;; (defthm memberp-pair-yield-of-bindings-aux-remove-dups
;;   (implies (true-listp bindings)
;;            (equal (memberp pair (pair-yield-of-bindings-aux (remove-duplicate-bindings bindings)))
;;                   (memberp pair (pair-yield-of-bindings-aux bindings))))
;;   :hints (("goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable pair-yield-of-bindings-aux remove-duplicate-bindings))))



(encapsulate
 ()

 (local (defthm get-field-of-set-fields-1
          (implies (not (equal ad ad2))
                   (equal (get-field ad pair (set-fields ad2 bindings heap))
                          (get-field ad pair heap)))
          :hints (("goal" :in-theory (set-difference-theories
                                      (enable set-fields)
                                      '( set-fields-collect-2))))))

 (local (defthm get-field-of-set-fields-2
          (implies (memberp pair (strip-cars bindings))
                   (equal (get-field ad pair (set-fields ad bindings heap))
                          (lookup-equal pair bindings)))
          :hints (("goal" :do-not '(generalize eliminate-destructors)
;                   :expand(STRIP-CARS BINDINGS)
                   :in-theory (e/d (lookup-equal assoc-equal
                                    strip-cars
                                    set-fields
                                    )
                                   (set-fields-collect-2))))))

 (local (defthm GET-FIELD-of-SET-FIELDS-3
          (implies (not (memberp pair (strip-cars bindings)))
                   (equal (GET-FIELD ad pair (SET-FIELDS AD2 bindings HEAP))
                          (GET-FIELD ad pair HEAP)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (e/d (lookup-equal
                                    strip-cars
                                    set-fields
                                    )
                                   (set-fields-collect-2))))))

 (defthm get-field-of-set-fields
   (equal (get-field ad pair (set-fields ad2 bindings heap))
          (if (and (equal ad ad2)
                   (memberp pair (strip-cars bindings)))
              (lookup-equal pair bindings)
            (get-field ad pair heap)))))

;; ;Interesting!  set-field-many can set multiple adrs at a time!
;; ;BOZO is this the same as set-fields?
;; ;rename?
;; ;BOZO change the format of bindings!
;; (defund set-field-many (bindings heap)
;;   (if (endp bindings)
;;       heap
;;     (let* ((first-binding (car bindings))
;; 	   (adr (car first-binding))
;; 	   (class-name (cadr first-binding))
;; 	   (field-id (caddr first-binding))
;; 	   (value (cadddr first-binding)))
;;       (set-field adr (cons class-name field-id) value
;; 		 (set-field-many (cdr bindings) heap)))))

;; (defthm set-field-many-with-bindings-not-a-consp
;;   (implies (not (consp bindings))
;;            (equal (SET-FIELD-MANY BINDINGS HEAP)
;;                   heap))
;;   :hints (("Goal" :in-theory (enable set-field-many))))

;; (defthm set-field-many-opener-1
;;   (equal (set-field-many nil heap)
;; 	 heap)
;;   :hints (("Goal" :in-theory (enable set-field-many))))

;; ;so we open set-field-many but close up set-fields?  can we reconcile these two approaches?
;; (defthm set-field-many-opener-2
;;   (implies (and (and (syntaxp (equal 'cons (car bindings)))) ;why did i write it like this?
;; 		(consp bindings)
;; 		)
;; 	   (equal (set-field-many bindings heap)
;; 		  (let* ((first-binding (car bindings))
;; 			 (adr (car first-binding))
;; 			 (class-name (cadr first-binding))
;; 			 (field-id (caddr first-binding))
;; 			 (value (cadddr first-binding)))
;; 		    (set-field adr (cons class-name field-id) value
;; 			       (set-field-many (cdr bindings) heap)))))
;;   :hints (("Goal" :in-theory (enable set-field-many))))



;this one is in logic mode
;fixme use verify-termination here and elsewhere to lift functions to logic mode
;identical to >=-len
;; (defun my->=-len (x n)
;;   (declare (xargs :guard (and (integerp n) (<= 0 n))))
;;   (if (= n 0)
;;       t
;;       (if (atom x)
;;           nil (my->=-len (cdr x) (1- n)))))

;; ;this one is in logic mode
;; (defun my-all->=-len (lst n)
;;   (declare (xargs :guard (and (integerp n) (<= 0 n))))
;;   (if (atom lst)
;;       (eq lst nil)
;;       (and (>=-len (car lst) n)
;;            (my-all->=-len (cdr lst) n))))

;move
(defthm strip-caddrs-when-not-consp
  (implies (not (consp x))
           (equal (strip-caddrs x)
                  nil))
  :hints (("goal" :in-theory (enable strip-caddrs ))))

;STRIP-CADDRS-OF-CDR loops with defn STRIP-CADDRS
;move
;BOZO casues problems?
;disable?
;dup
(defthm strip-caddrs-of-cdr
  (equal (strip-caddrs (cdr x))
         (cdr (strip-caddrs x)))
  :hints (("goal" :in-theory (enable strip-caddrs))))

;bozo put back?
;; (defthmd strip-caddrs-of-hack
;;   (implies (all-nil (strip-caddrs bindings))
;;            (not (caddar bindings)))
;;   :rule-classes (:rewrite :type-prescription)
;;   :hints (("goal" :in-theory (enable strip-caddrs all-nil))))


;; (defthm get-field-of-set-field-many-diff-adr
;;   (implies (not (memberp adr (strip-cars bindings)))
;; 	   (equal (get-field adr pair (set-field-many bindings heap))
;; 		  (get-field adr pair heap)))
;;   :hints (("Goal" :in-theory (enable set-field-many memberp))))



;; (defthm get-field-of-set-field-many-diff-class-name
;;   (implies (not (memberp pair (strip-cadrs bindings)))
;; 	   (equal (get-field adr pair (set-field-many bindings heap))
;; 		  (get-field adr pair heap)))
;;   :hints (("Goal" :in-theory (enable set-field-many memberp))))















;; (defthm new-ad-ignores-extra-set-fields-of-the-same-adr
;;   (implies (and (not (equal value1 nil))
;; 		(not (equal value2 nil)))
;;   (equal (NEW-AD
;; 	  (SET-FIELD
;; 	   ref class-name1 field-id1 value1
;; 	   (SET-FIELD ref class-name2 field-id2 value2 heap)))
;; 	 (NEW-AD
;; 	  (SET-FIELD
;; 	   ref class-name1 field-id1 value1
;; 	   heap))))
;;   :hints (("Goal" :in-theory (enable new-ad new-ad-aux set-field))))

;; ...


;; (defthm s-of-set-field
;;   (equal (s ref value1 (set-field ref pair value2 heap))
;; 	 (s ref value1 heap))
;;   :hints (("goal" :in-theory (enable set-field))))

;; (defthm s-of-set-class
;;   (equal (s ref value1 (set-class-of-ref ref class-name heap))
;; 	 (s ref value1 heap))
;;   :hints (("goal" :in-theory (enable set-class-of-ref))))

;; ...

;; (defthm hack11
;;   (implies (g ref heap)
;; 	   (equal (unite (dom heap)
;; 			       (s1 ref))
;; 		  (dom heap)))
;;   :hints (("goal" :use (:instance in-dom-iff-g (a ref) (r heap))

;; 	   :in-theory (disable in-dom-iff-g))))

;; (defthm new-ad-s-already-bound-val
;;   (implies (and (g ref heap)
;; 		val)
;; 	   (equal (NEW-AD (S ref val HEAP))
;; 		  (new-ad heap)))
;;   :hints (("Goal" :in-theory (enable new-ad))))


;; ...

;;  bozo rephrase
;; (defthm get-field-of-not-bound
;;   (implies (not (bound-in-heap adr heap))
;; 	   (equal (get-field adr class-name field-id heap)
;; 		  nil))
;;   :hints (("Goal" :in-theory (enable bound-in-heap get-field))))

;; ...

;;  BOZO
;; (defthm get-field-of-new-ad
;;   (equal (get-field (new-ad heap) class-name field-id heap)
;; 	 nil)
;;   :hints (("goal" :in-theory (disable in-dom-iff-g)))
;;   )

;; ...


;; ;make a redux version which splits cases?
;; (defthm g-of-set-field
;;   (implies (case-split (not (equal ref1 ref2)))
;;   (equal
;;    (G ref1
;;       (SET-FIELD
;;        ref2 class-name2 field-id2 value2 heap2))
;;    (g ref1 heap2)))
;;   :hints (("Goal" :in-theory (enable set-field)))
;; )

;; (defthm g-of-set-field-2
;;   (implies (case-split value)
;; 	   (G ref (SET-FIELD
;; 		   ref class-name field-id value heap)))
;;   :hints (("Goal" :in-theory (enable set-field))))


;rename.
(defthm get-either-case
  (equal (get-field ref1 pair
		    (set-field ref2 pair
			       (get-field ref1 pair heap)
			       heap))
	 (get-field ref1 pair heap)
	 )
  :hints (("goal" :cases ((equal ref1 ref2)))))


;;  ...

;; (defthm get-field-non-nil-means-bound
;;   (implies (get-field adr pair heap)
;; 	   (bound-in-heap adr heap))
;;   :rule-classes ((:rewrite :match-free :all))
;;   :hints (("Goal" :in-theory (enable bound-in-heap get-field))))






;; ;kill?
;; (local (defthm new-ad-not-bound-helper3
;; 	  (implies (sets::subset bound-adrs bound-adrs2)
;; 		   (not (sets::in (new-ad-aux bound-adrs2 current-try) bound-adrs)))
;; 	  :hints (
;; 		  ("Goal" :in-theory (disable NEW-AD-NOT-BOUND-HELPER2)
;; 		   :use (:instance new-ad-not-bound-helper2
;; 					  (ad-set bound-adrs2))))))



;; (defthm bound-in-heap-of-set-field-same
;;  (implies val
;;           (BOUND-IN-HEAP
;;            ad
;;            (SET-FIELD  ad pair val heap)))

;; :hints (("Goal" :in-theory (enable BOUND-IN-HEAP set-field))))

;; (defthm bound-in-heap-of-set-field-diff
;;  (implies (not (equal ad ad2))
;;           (equal (BOUND-IN-HEAP
;;                   ad2
;;                   (SET-FIELD ad pair val heap))
;;                  (BOUND-IN-HEAP
;;                   ad2
;;                   heap)))

;; :hints (("Goal" :in-theory (enable BOUND-IN-HEAP set-field))))

;; (defthm bound-ad-isnt-new-ad
;;   (implies (bound-in-heap ad heap)
;;            (not (equal ad (new-ad (dom heap))))))









;; ;BOZO bad name
;; (defthm not-in-ad-list-means-not-equal-to-new-ad
;;   (implies (< a try)
;;            (not (equal (new-ad-aux ad-set try)
;;                        a)))
;;   :hints (("Goal" :in-theory (enable new-ad-aux))))


;; (defthm new-ad-not-in-dom-helper
;;   (implies (sets::setp x)
;;            (NOT (MEMBERP (NEW-AD-AUX x try)
;;                          x)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable  MEMBERP-BECOMES-IN
;;                                NEW-AD-AUX))))

;; (defthm nth-new-ad-not-bound
;;    (not (bound-in-heap (nth-new-ad n heap) heap))
;;    :hints (("Goal" :in-theory (enable nth-new-ad))))

;; ;BOZO  NEXT-ADR-OF-S-OF-NEXT-ADR loops with defn nth-new-ad?

;; ;generalize this!
;; (defthm next-adr-not-nth-adr
;;   (not (equal (next-adr heap)
;;               (nth-new-ad 2 heap)))
;;   :hints (("Goal" :in-theory (disable  NEXT-ADR-OF-S-OF-NEXT-ADR)
;;            :expand (NTH-NEW-AD 2 HEAP))))

;; ;make sure we deal completely with the different ways to say this...
;; (defthm not-bound-in-heap-means-g-is-nil
;;   (implies (not (bound-in-heap x heap))
;;            (equal (g x heap)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable BOUND-IN-HEAP))))


;do we have dom-of-s?
;s of set-field?

;; (theory-invariant (incompatible (:rewrite LEN-CDR-BOTH)
;;                                 (:definition len)))

;; (theory-invariant (incompatible (:rewrite LEN-CDR)
;;                                 (:definition len)))

;; (theory-invariant (incompatible (:rewrite true-listp-CDR)
;;                                 (:definition true-listp)))

(defthm get-field-of-clear-field-both
  (equal (get-field ad1 pair1 (clear-field ad2 pair2 heap))
         (if (and (equal ad1 ad2)
                  (equal pair1 pair2))
             nil
           (get-field ad1 pair1 heap)))
  :hints (("Goal" :in-theory (e/d (clear-field) (set-to-nil-equal-clear-field)))))

(defthm get-field-of-new-ad
  (equal (get-field (new-ad (rkeys heap)) pair heap)
         nil)
  :hints (("Goal" :in-theory (e/d (get-field) (G-IFF-GEN)))))

(defthm get-field-of-s-same
  (equal (get-field ad pair (s ad obj heap))
         (g pair obj))
  :hints (("Goal" :in-theory (enable get-field))))

(defthmd get-field-reassemble
  (equal (g class-field-pair (g ad heap))
         (get-field ad class-field-pair heap))
  :hints (("Goal" :in-theory (enable get-field))))

(theory-invariant (incompatible (:rewrite get-field-reassemble) (:definition get-field)))

(defthmd set-fields-opener
  (implies (not (endp bindings))
           (equal (set-fields ad bindings heap)
                  (let* ((first-binding (car bindings))
                         (class-field-pair (car first-binding))
                         (value (cdr first-binding)))
                        (set-field ad class-field-pair value
                                   (set-fields ad (cdr bindings) heap)))))
  :hints (("Goal" :in-theory (enable set-fields))))

(defthm set-fields-base-case
  (implies (endp bindings)
           (equal (set-fields ad bindings heap)
                  heap))
  :hints (("Goal" :in-theory (enable set-fields))))

(theory-invariant (incompatible (:rewrite set-fields-opener) (:rewrite SET-FIELDS-COLLECT-1)))

(defthm clr-of-set-field
  (equal (clr ad (set-field ad pair value heap))
         (clr ad heap))
  :hints (("Goal" :in-theory (enable set-field))))

(defthm clr-of-clear-field
  (equal (clr ad (clear-field ad value heap))
         (clr ad heap))
  :hints (("Goal" :in-theory (e/d (clear-field) (SET-TO-NIL-EQUAL-CLEAR-FIELD)))))

(defthm clr-of-set-fields
  (equal (clr ad (set-fields ad bindings heap))
         (clr ad heap))
  :hints (("Goal" :expand (SET-FIELDS AD BINDINGS HEAP)
           :in-theory (enable set-fields))))

;or should we open null-refp?
(defthm not-null-refp-of-new-ad
  (not (null-refp (new-ad dom))))

(defthm not-null-refp-of-nth-new-ad
  (not (null-refp (nth-new-ad n dom))))

;might loop in acl2? but in axe, equal-same will fire first (because of priorities)?
;fixme add an acl2 version with a syntaxp hyp?
;fixme can this interact with other rules that turn equal around (maybe based on term size?)
(defthmd equal-of-null-ref-turn-around
  (implies (syntaxp (not (quotep x))) ;fixme would also like to exclude x being a call to null-ref
           (equal (equal x (null-ref))
                  (equal (null-ref) x))))

(defthm equal-of-null-ref-and-new-ad
  (equal (equal (null-ref) (new-ad dom))
         nil))

(defthm equal-of-new-ad-and-null-ref
  (equal (equal (new-ad dom) (null-ref))
         nil))

(defthm equal-of-null-ref-and-nth-new-ad
  (equal (equal (null-ref) (nth-new-ad n dom))
         nil))

(defthm equal-of-nth-new-ad-and-null-ref
  (equal (equal (nth-new-ad n dom) (null-ref))
         nil))



;fixme make a "same" version
;is it bad that "g" is arising?
(defthm g-of-set-field-irrel
  (implies (not (equal ad ad2))
           (equal (g ad (set-field ad2 class-field-pair value heap))
                  (g ad heap)))
  :hints (("Goal" :in-theory (enable set-field))))

(defthm g-of-set-field-same
  (equal (g ad (set-field ad class-field-pair value heap))
         (s class-field-pair value (g ad heap)))
  :hints (("Goal" :in-theory (enable set-field))))

(defthm g-of-set-fields-irrel
  (implies (not (equal ad ad2))
           (equal (g ad (set-fields ad2 pairs heap))
                  (g ad heap)))
  :hints (("Goal" :in-theory (enable set-fields))))

(defthm in-rkeys-when-get-field-non-nil-main
  (implies (get-field ad pair heap)
           (set::in ad (rkeys heap)))
  :hints (("Goal" :use (:instance G-IFF-GEN (a ad) (r heap))
           :in-theory (e/d (GET-FIELD
                            ) (G-IFF-GEN GET-FIELD-REASSEMBLE)))))

;special case for when get-field is known equal to something
(defthm in-rkeys-when-get-field-non-nil
  (implies (and (equal (get-field ad pair heap) val) ;free vars
                val                                  ;is not nil
                )
           (set::in ad (rkeys heap))))

;special case for when get-field is known equal to something
;for axe (todo: we could build into axe that x is non-nil when it's equal to something non-nil)
(defthm in-rkeys-when-get-field-non-nil-alt
  (implies (and (equal val (get-field ad pair heap))
                val)
           (set::in ad (rkeys heap))))

(defthm clear-field-does-nothing
  (implies (not (get-field ad pair heap))
           (equal (clear-field ad pair heap)
                  heap))
  :hints (("Goal" :in-theory (e/d (clear-field) (set-to-nil-equal-clear-field)))))

(defthm get-field-of-s-diff
  (implies (not (equal ad ad2))
           (equal (get-field ad pair (s ad2 v heap))
                  (get-field ad pair heap)))
  :hints (("Goal" :in-theory (e/d (get-field) (GET-FIELD-REASSEMBLE)))))

(defthm all-addressp-of-n-new-ads
  (acl2::all-addressp (acl2::n-new-ads n ads))
  :hints (("Goal" :in-theory (e/d (acl2::all-addressp acl2::n-new-ads acl2::n-new-ads-aux) (N-NEW-ADS-BECOMES-N-NEW-ADS2)))))

(defthm heapp-of-set-fields
  (implies (and (jvm::heapp heap)
                (acl2::all-heap-object-keyp (strip-cars bindings))
                (addressp ad))
           (jvm::heapp (ACL2::SET-FIELDS ad bindings HEAP)))
  :hints (("Goal" :in-theory (enable ACL2::SET-FIELDS))))

(defthm strip-cars-of-append
  (equal (STRIP-CARS (APPEND x y))
         (append (strip-cars x) (strip-cars y)))
  :hints (("Goal" :in-theory (enable strip-cars append))))



(defthm addressfix-when-address-or-nullp-and-not-null-refp
  (implies (and (address-or-nullp x)
                (not (null-refp x)))
           (equal (addressfix x)
                  x)))


(defthm get-class-of-set-class-same
  (equal (get-class ad (set-class ad class heap))
         class)
  :hints (("Goal" :in-theory (enable get-class set-class))))

(defthm get-class-of-set-class-diff
  (implies (not (equal ad ad2))
           (equal (get-class ad (set-class ad2 class heap))
                  (get-class ad heap)))
  :hints (("Goal" :in-theory (enable get-class set-class))))

(defthm get-class-of-set-class-both
  (equal (get-class ad (set-class ad2 class heap))
         (if (equal ad ad2)
             class
           (get-class ad heap)))
  :hints (("Goal" :in-theory (enable get-class set-class))))


;why does this arise (as opposed to clear-field of set-field)?
(defthm clr-of-set-field-diff
  (implies (not (equal ad1 ad2))
           (equal (CLR ad1 (SET-FIELD AD2 CLASS-FIELD-PAIR VALUE HEAP))
                  (SET-FIELD AD2 CLASS-FIELD-PAIR VALUE (clr ad1 HEAP))))
  :hints (("Goal" :in-theory (enable set-field))))

(defthm get-class-of-set-field
  (equal (acl2::get-class ad1 (acl2::set-field ad2 pair val heap))
         (if (and (equal ad1 ad2)
                  (equal pair (acl2::class-pair)))
             val
           (acl2::get-class ad1 heap)))
  :hints (("Goal" :in-theory (enable acl2::get-class))))
