; Various rules about the jvm model
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize the material in this book

(include-book "jvm") ; for JVM::CALL-STACK, etc
(include-book "arrays")
(include-book "kestrel/arrays-2d/arrays-2d" :dir :system) ;todo drop? for set-row
(include-book "kestrel/lists-light/union-equal" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/bv-lists/all-all-unsigned-byte-p" :dir :system)
(include-book "kestrel/bv-lists/getbit-list" :dir :system)
(include-book "kestrel/lists-light/find-index" :dir :system)
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/memberp2" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ;for USB-PLUS-FROM-BOUNDS

;move
(defthm find-index-of-nth-self
  (implies (and (natp n)
                (< n (len lst))
                (no-duplicatesp-equal lst))
           (equal (find-index (nth n lst) lst)
                  n))
  :hints (("Goal" :in-theory (e/d (find-index (:i nth))
                                  ((:d nth))))))

;; (defthm inst-length-of-myif
;;   (equal (jvm::inst-length (cons (myif test a b) rest))
;;          (myif test (jvm::inst-length (cons a rest))
;;                (jvm::inst-length (cons b rest))))
;;   :hints (("Goal" :in-theory (e/d (myif) (jvm::inst-length)))))



;bozo loops with MYIF-OF-MAKE-FRAME
;; (defthmd make-frame-of-bvif-around-pc
;;   (equal (jvm::make-frame (bvif size test a b) jvm::locals jvm::stack jvm::program jvm::sync-flag jvm::method-designator)
;;          (myif test (jvm::make-frame (bvchop size a) jvm::locals jvm::stack jvm::program jvm::sync-flag jvm::method-designator)
;;                (jvm::make-frame (bvchop size b) jvm::locals jvm::stack jvm::program jvm::sync-flag jvm::method-designator)))
;;   :hints (("Goal" :in-theory (enable myif bvif))))

(defthm initialize-one-dim-array-of-myif
  (equal (jvm::initialize-one-dim-array (myif test a b) type count jvm::heap)
         (myif test (jvm::initialize-one-dim-array a type count jvm::heap)
               (jvm::initialize-one-dim-array b type count jvm::heap)))
  :hints (("Goal" :in-theory (enable myif))))



;This seemed to help a lot!  we were calling arith-term-order on huge terms of this form, which could be simplified a lot...
;BOZO think more about this?
;usually the lengths of the two call stacks will be equal...
;; (defthm len-of-call-stack-of-myif
;;   (equal (len (jvm::call-stack th (myif test state1 state2)))
;;          (myif test (len (jvm::call-stack th state1)) (len (jvm::call-stack th state2))))
;;   :hints (("Goal" :in-theory (enable myif))))

;BOZO do we ever want to go the other way?
;perhaps only do it if the call stacks are the same?
;or only if the states are calls to make-state?
(defthm call-stack-of-myif
  (equal (jvm::call-stack th (myif test state1 state2))
         (myif test (jvm::call-stack th state1) (jvm::call-stack th state2)))
  :hints (("Goal" :in-theory (enable myif))))

;but don;t I really want to push the myifs in?
;trying disabled Tue Jul  6 00:48:00 2010
(defthmd pc-of-nth-0-of-myif
  (equal (jvm::pc (nth 0 (myif test a b)))
         (myif test (jvm::pc (nth 0 a))
               (jvm::pc (nth 0 b))))
  :hints (("Goal" :in-theory (enable myif))))

;this version is in the ACL2 package (do I still need it?
(defun get-static-field (class-name field-id static-field-map)
  (jvm::get-static-field class-name field-id static-field-map))

(defthm clr-of-set-fields-diff
  (implies (not (equal ad1 ad2))
           (equal (clr ad1
                       (set-fields ad2 bindings heap))
                  (set-fields ad2
                             bindings (clr ad1 heap))))
  :hints (("Goal" :in-theory (enable set-fields))))

(in-theory (enable init-ref-in-heap))
(in-theory (enable gen-init-bindings))
(in-theory (enable gen-init-bindings-for-class))

(in-theory (disable JVM::GET-ARRAY-COMPONENT-TYPE))

(defun arraycontents (ref s)
  (array-contents ref (jvm::heap s)))

(defun arraycontents2 (ref s)
  (array-contents2 ref (jvm::heap s)))

(defthm in-of-insert-irrel
  (implies (not (equal a b))
           (equal (SET::IN a (SET::INSERT b x))
                  (SET::IN a x))))

(defthm jvm::myif-of-set-field-2
  (equal (myif test heap (SET-FIELD ad pair value heap)) ;requires the heaps to match
         (set-field ad pair (myif test (get-field ad pair heap) value) heap))
  :hints (("Goal" :in-theory (enable myif))))

(defthm jvm::myif-of-set-field-1
  (equal (myif test (SET-FIELD ad pair value heap) heap) ;requires the heaps to match
         (set-field ad pair (myif test value (get-field ad pair heap)) heap))
  :hints (("Goal" :in-theory (enable myif))))


;these seemed dangerous (e.g., for the des bouncy proof)
;this doubles the occurrences of heap2
;if both branches of the myif are set-fields, maybe we should make heap correspond to the smaller heap?
(defthm jvm::myif-of-set-field-1-strong
  (equal (myif test (set-field ad pair value heap) heap2)
         (set-field ad pair (myif test value (get-field ad pair heap2)) (myif test heap heap2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm jvm::myif-of-set-field-2-strong
  (equal (myif test heap2 (set-field ad pair value heap))
         (set-field ad pair (myif test (get-field ad pair heap2) value) (myif test heap2 heap)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm jvm::myif-of-set-field-and-set-field
  (equal (myif test
               (set-field AD CLASS-FIELD-PAIR VALUE1 HEAP1)
               (set-field AD CLASS-FIELD-PAIR VALUE2 HEAP2))
         (set-field ad CLASS-FIELD-PAIR
                    (myif test VALUE1 value2)
                    (myif test
                          HEAP1
                          HEAP2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthmd get-field-reassemble-array-contents
  (equal (g (array-contents-pair) (g ad heap))
         (get-field ad (array-contents-pair) heap))
  :hints (("Goal" :in-theory (enable get-field))))

(defthmd get-field-reassemble-class
  (equal (g (class-pair) (g ad heap))
         (get-field ad (class-pair) heap))
  :hints (("Goal" :in-theory (enable get-field))))

;used for example when the heap is an if where one branch creates a string object for interning and the other branch doesn't and the test is whether the string is already interned
(defthm get-field-of-myif
  (equal (get-field ad class-field-pair (myif test heap1 heap2))
         (myif test (get-field ad class-field-pair heap1)
               (get-field ad class-field-pair heap2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm get-field-of-myif2
  (equal (get-field (myif test ad1 ad2) class-field-pair heap)
         (myif test (get-field ad1 class-field-pair heap)
               (get-field ad2 class-field-pair heap)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm g-of-myif2
  (equal (g a (myif test r1 r2))
         (myif test (g a r1) (g a r2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm g-of-myif
  (equal (g (myif test a b) r)
         (myif test (g a r) (g b r)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm insert-of-myif
  (equal (SET::INSERT (myif test A1 a2) X)
         (myif test (set::insert a1 x)
               (set::insert a2 x)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm insert-of-myif2
  (equal (SET::INSERT X (myif test A1 a2))
         (myif test (set::insert x a1)
               (set::insert x a2)))
  :hints (("Goal" :in-theory (enable myif))))

;require items to be a constant?
(defthm first-non-member-when-member
  (implies (member-equal (car items) lst)
           (equal (FIRST-NON-MEMBER items lst)
                  (FIRST-NON-MEMBER (cdr items) lst))))

;crud. can't rewrite an IF expression...
(defthm if-hack-for-backchaining
 (implies (syntaxp (smaller-termp x y))
          (equal (myIF (EQUAL y x)
                      (EQUAL (array-length y
                                        (JVM::HEAP S0))
                             val)
                      val2)
                 (myIF (EQUAL y x)
                      (EQUAL (array-length x (JVM::HEAP S0))
                             val)
                      val2)))
 :hints (("Goal" :in-theory (enable myif))))


(in-theory (disable JVM::LOOKUP-METHOD-IN-CLASSES))
(in-theory (enable JVM::LOOKUP-METHOD))

(in-theory (disable s==r)) ;bozo

;disable?
(DEFTHM GET-FIELD-REASSEMBLE-safer
  (implies (syntaxp (and (consp heap)  ;perhaps allow vars named heap?
                         (equal 'jvm::heap (car heap))))
           (EQUAL (G CLASS-FIELD-PAIR (G AD HEAP))
                  (GET-FIELD AD CLASS-FIELD-PAIR HEAP)))
  :HINTS (("Goal" :IN-THEORY (ENABLE GET-FIELD))))

(defthm 2set-of-reverse
  (equal (LIST::|2SET| (REVERSE-LIST lst))
         (LIST::|2SET| lst))
  :hints (("Goal" :in-theory (enable LIST::|2SET| reverse-list append))))


(defthm initialize-one-dim-array-of-set-field
  (implies (not (equal ref1 ref2))
           (equal (jvm::initialize-one-dim-array ref1 type contents (set-field ref2 pair value heap))
                  (set-field ref2 pair value (jvm::initialize-one-dim-array ref1 type contents heap))
                  ))
  :rule-classes ((:rewrite :loop-stopper ((ref1 ref2))))
  :hints (("Goal" :in-theory (enable JVM::INITIALIZE-ONE-DIM-ARRAY))))

(defthm set-field-of-initialize-one-dim-array
  (implies (not (equal ref1 ref2))
           (equal (set-field ref1 pair value (jvm::initialize-one-dim-array ref2 type contents heap))
                  (jvm::initialize-one-dim-array ref2 type contents (set-field ref1 pair value heap))
                  ))
  :rule-classes
  ((:rewrite :loop-stopper ((ref1 ref2)))))

(in-theory (enable (:executable-counterpart s)))  ;BOZO think about this... when s is called to make a class info object it's nice to have it reduced to a constant?

(defthm array-contents-list-of-set-field-nth
  (implies (and (integerp n)
                (no-duplicatesp-equal ref-list)
                (<= 0 n)
                (< n (len ref-list)))
           (equal (array-contents-list ref-list (set-field (nth n ref-list) (array-contents-pair) value heap))
                  (set-row n value (array-contents-list ref-list heap))))
  :hints (("Goal":in-theory (enable (:I nth))
           :do-not '(generalize eliminate-destructors))))

(defthm array-contents-list-of-clear-field-nth
  (implies (and (integerp n)
                (no-duplicatesp-equal ref-list)
                (<= 0 n)
                (< n (len ref-list)))
           (equal (array-contents-list ref-list (clear-field (nth n ref-list) (array-contents-pair) heap))
                  (set-row n nil (array-contents-list ref-list heap))))
  :hints (("Goal" :in-theory (e/d (clear-field) (set-to-nil-equal-clear-field; LIST::UPDATE-NTH-BECOMES-CLEAR-NTH
                                                 )))))

(defthm array-contents-list-of-set-field-car
  (implies (and ;(integerp n) ;t;(not (zp n))
;(<= 0 n)
;(< n (len ref-list))
            (no-duplicatesp-equal ref-list)
            (not (endp ref-list))
            )
           (equal (array-contents-list ref-list (set-field (car ref-list) (array-contents-pair) value heap))
                  (set-row 0 value (array-contents-list ref-list heap))))
;  :hints (("Goal" :induct (myind n ref-list)))
  :hints (("Goal" :use (:instance array-contents-list-of-set-field-nth (n 0))
           :in-theory (e/d (;update-nth-of-0
                            ) ;prevents a loop
                           (array-contents-list-of-set-field-nth
                            SET-ROW)))))


;; (thm
;;  (equal (LIST::CLEAR-NTH n (ARRAY-CONTENTS-LIST REF-LIST heap))

;; (defthm array-contents-list-of-set-field-car
;;   (implies (not (endp ref-list))
;;	      (equal (array-contents-list ref-list (set-field (car ref-list) (array-contents-pair) value heap))
;;		     (set-row 0 value (array-contents-list ref-list heap)))))


;turns nth of 0 into car.  i think i prefer nth
;(in-theory (disable NTH-WHEN-N-IS-ZP))

;; (defund array-elem-2d (row col ref heap)
;;   (nth col
;;        (get-field (nth row
;;                        (get-field ref (array-contents-pair) heap))
;;                   (array-contents-pair)
;;                   heap)))

;; (defthm array-elem-2d-recollapse
;;   (equal (nth col
;;               (get-field (nth row
;;                               (get-field ref (array-contents-pair) heap))
;;                          (array-contents-pair)
;;                          heap))
;;          (array-elem-2d row col ref heap))
;;   :hints (("Goal" :in-theory (enable array-elem-2d))))

;; (theory-invariant (incompatible (:rewrite array-elem-2d-recollapse) (:definition array-elem-2d)))

(defthmd array-elem-2d-recollapse
  (implies (and (integerp row)
                (<= 0 row)
                (< row (len (get-field ref (array-contents-pair) heap))))
           (equal (nth col
                       (get-field (nth row
                                       (get-field ref (array-contents-pair) heap))
                                  (array-contents-pair)
                                  heap))
                  (array-elem-2d row col (array-contents2 ref heap))))
  :hints (("Goal" :in-theory (enable array-elem-2d))))

(theory-invariant (incompatible (:rewrite array-elem-2d-recollapse) (:definition array-elem-2d)))


(defthm not-equal-new-ad-when-some-field-is-non-nil
  (implies (and (EQUAL (GET-FIELD ad pair heap) val)
                val ;is not nil
                )
           (NOT (EQUAL ad (NEW-AD (RKEYS heap))))))

(in-theory (disable set-field-of-get-field-same-eric-2)) ;todo: enabled just below


;i don't know why the cars are getting introduced...
(defthm car-of-get-field-of-contents-hack
  (equal (CAR (GET-FIELD n (array-contents-pair) heap))
         (nth 0 (GET-FIELD n (array-contents-pair) heap)))
  :hints (("Goal" :in-theory (enable nth-of-0))))

(defthm not-all-nil-strip-cdrs-gen-init-bindings-for-class
  (implies (consp field-info-alist)
           (not (all-equal$ nil (strip-cdrs (gen-init-bindings-for-class field-info-alist class-name)))))
  :hints (("Goal" :in-theory (enable gen-init-bindings-for-class))))

(in-theory (enable set-field-of-get-field-same-eric-2)) ;bozo slow?

(defthmd set-field-recollapse
  (equal (S ad (S pair val (G ad heap)) heap)
         (set-field ad pair val heap))
  :hints (("Goal" :in-theory (enable set-field))))

(defthmd set-field-recollapse-strong
  (implies (equal obj (g ad heap))
           (equal (S ad (S pair val obj) heap)
                  (set-field ad pair val heap)))
  :hints (("Goal" :in-theory (enable set-field))))

(defthm s-of-s-becomes-set-field
  (equal (S ad (S pair val obj) heap)
         (set-field ad pair val (s ad obj heap)))
  :hints (("Goal" :in-theory (enable SET-FIELD))))

(defthm clear-field-reassemble-weak
  (equal (s ad (clr pair (g ad heap)) heap)
         (clear-field ad pair heap))
  :hints (("Goal" :in-theory (e/d (clear-field set-field) (set-to-nil-equal-clear-field)))))

(defthm clear-field-reassemble-strong
  (implies (equal val (g ad heap))
           (equal (s ad (clr pair val) heap)
                  (clear-field ad pair heap)))
  :hints (("Goal" :in-theory (e/d (clear-field) (set-to-nil-equal-clear-field)))))

(defthm s-of-clr
  (equal (s ad (clr pair val) heap)
         (clear-field ad pair (s ad val heap)))
  :hints (("Goal" :in-theory (e/d (clear-field) (set-to-nil-equal-clear-field)))))

(in-theory (disable CLEAR-FIELD-OF-S))

(in-theory (disable array-contents2))

(in-theory (enable array-elem-2d-recollapse))



(defthm array-row-recollapse
  (equal (get-field (nth n (get-field ref (array-contents-pair) heap)) (array-contents-pair) heap)
         (array-row n ref heap))
  :hints (("Goal" :in-theory (enable array-row))))

(theory-invariant (incompatible (:definition array-row) (:rewrite array-row-recollapse)))

(defthm nth-of-array-row
  (implies (and (INTEGERP N)
                (<= 0 N)
                (< N (LEN (array-contents ref heap))))
           (equal (nth m (array-row n ref heap))
                  (array-elem-2d n m (array-contents2 ref heap))))
  :hints (("Goal" :in-theory (e/d (array-elem-2d ARRAY-ROW ARRAY-CONTENTS2)
                                  (array-elem-2d-recollapse array-row-recollapse)))))


(defund array-elem-2d2 (row col ref heap)
  (array-elem-2d row col (array-contents2 ref heap)))

(defthm array-elem-2d2-recollapse
  (equal (array-elem-2d row col (array-contents2 ref heap))
         (array-elem-2d2 row col ref heap))
  :hints (("Goal" :in-theory (enable array-elem-2d2))))

(theory-invariant (incompatible (:definition array-elem-2d2 ) (:rewrite array-elem-2d2-recollapse)))

(in-theory (disable array-elem-2d))


(defthm nth-of-array-contents2
  (implies (and (natp row)
                (< row (len (array-contents ref heap))))
           (equal (NTH ROW (ARRAY-CONTENTS2 REF HEAP))
                  (array-row row ref heap)))
  :hints (("Goal" :in-theory (enable ARRAY-CONTENTS2))))

;; (defthm signed-byte-p-of-array-elem-2d2
;;   (implies (and (BYTE-P-LIST (ARRAY-ROW row ref heap))
;;                 (natp row)
;;                 (natp col)
;;                 (< col (len (ARRAY-ROW row ref heap)))
;;                 (< row (len (ARRAY-contents ref heap)))
;;                 )
;;            (signed-byte-p 8 (ARRAY-ELEM-2D2 row col ref heap)))
;;   :hints (("Goal" :in-theory (e/d (ARRAY-ELEM-2D2 ARRAY-ELEM-2D)
;;                                   (ARRAY-ELEM-2D2-RECOLLAPSE ARRAY-ELEM-2D-recollapse NTH-OF-ARRAY-ROW)))))

(defthm array-contents2-of-set-field-irrel
  (implies (and (not (memberp ad2 (array-contents ad heap)))
                (not (equal ad ad2)))
           (equal (array-contents2 ad (set-field ad2 pair val heap))
                  (array-contents2 ad heap)))
  :hints (("Goal" :in-theory (e/d (array-contents2) ()))))

(defthm array-contents2-of-set-field-irrel2
  (implies (not (equal pair (array-contents-pair)))
           (equal (array-contents2 ad (set-field ad2 pair val heap))
                  (array-contents2 ad heap)))
  :hints (("Goal" :in-theory (e/d (array-contents2) ()))))


(defthm array-elem-2d2-of-set-field-irrel
  (implies (and (not (memberp ad2 (array-contents ad heap)))
                (not (equal ad ad2)))
           (equal (ARRAY-ELEM-2D2 row col ad (SET-FIELD ad2 pair val heap))
                  (ARRAY-ELEM-2D2 row col ad heap)))
  :hints (("Goal" :in-theory (e/d (ARRAY-ELEM-2D2) (ARRAY-ELEM-2D2-recollapse)))))

(defthm array-elem-2d2-of-set-field-irrel2
  (implies (not (equal pair (array-contents-pair)))
           (equal (ARRAY-ELEM-2D2 row col ad (SET-FIELD ad2 pair val heap))
                  (ARRAY-ELEM-2D2 row col ad heap)))
  :hints (("Goal" :in-theory (e/d (ARRAY-ELEM-2D2) (ARRAY-ELEM-2D2-recollapse)))))

;(in-theory (disable JVM::INITIALIZE-ONE-DIM-ARRAY))

;(in-theory (disable store-array-2d))

;; ;nested induction
;; (defthm store-array-list-of-store-array-list
;;   (equal (store-array-list refs contents1 cols ':byte (store-array-list refs contents2 cols ':byte heap))
;;          (store-array-list refs contents1 cols ':byte heap))
;;   :hints (("Goal" :in-theory (enable store-array-list))))

;; (defthm store-array-2d-of-store-array-2d
;;   (implies (and (not (memberp ad (array-contents ad heap)))
;;                 (<= rows (len (array-contents ad heap))))
;;            (equal (STORE-ARRAY-2D ad contents1 rows cols ':BYTE (STORE-ARRAY-2D ad contents2 rows cols ':BYTE heap))
;;                   (STORE-ARRAY-2D ad contents1 rows cols ':BYTE heap)))
;;   :hints (("Goal" :in-theory (enable store-array-2d))))

                     ;; (ARRAY-CONTENTS2
;;                       (NEW-AD (RKEYS (JVM::HEAP S0)))
;;                       (STORE-ARRAY-2D
;;                        (NEW-AD (RKEYS (JVM::HEAP S0)))


(theory-invariant (incompatible (:definition set-field) (:rewrite S-OF-S-BECOMES-SET-FIELD)))

(in-theory (disable CLEAR-FIELD-REASSEMBLE-STRONG))

(in-theory (disable S-OF-S-BECOMES-SET-FIELD))

;; (defthm length-field-non-nil-when
;;   (implies (and (ARRAY-REF-LISTP ads (LIST NUMCOLS) type HEAP)
;;                 (memberp ad2 ads))
;;            (array-length AD2 HEAP))
;;   :hints (("Goal" :induct (true-listp ads)
;;            :expand (ARRAY-REFP (NTH 0 ADS)
;;                                (LIST NUMCOLS)
;;                                TYPE HEAP)
;;            :in-theory (enable array-ref-listp))))

;; (defthm type-field-non-nil-when
;;   (implies (and (array-ref-listp ads (list numcols) type heap)
;;                 (memberp type  '(:byte :int :boolean))
;;                 (memberp ad2 ads))
;;            (get-field ad2 (array-type-pair) heap))
;;   :hints (("Goal" :induct (true-listp ads)
;;            :expand (array-refp (nth 0 ads)
;;                                (list numcols)
;;                                type heap)
;;            :in-theory (enable))))

(defthm g-of-set-field-both
  (equal (G AD1 (SET-FIELD AD2 pair val heap))
         (if (equal ad1 ad2)
             (s pair val (g ad1 heap))
           (G AD1 heap))))

(defthm equal-set-field-destruct-gen
  (equal (equal (set-field ref pair value1 heap1) heap2)
         (and (equal value1 (get-field ref pair heap2))
              (equal (clear-field ref pair heap1)
                     (clear-field ref pair heap2))))
 :hints (("Goal" :use (:instance equal-set-field-destruct (value2 (get-field ref pair heap2)))
          :in-theory (disable equal-set-field-destruct))))

(defthm array-row-of-set-field-irrel
  (implies (and (not (equal ref ref2))
                (<= 0 n)
;               (< n (GET-FIELD REF '("ARRAY" . "length") HEAP))
                (< n (len (GET-FIELD REF (array-contents-pair) HEAP)))
                (not (memberp ref2 (array-contents ref heap))))
           (equal (ARRAY-ROW n ref (SET-FIELD ref2 pair val heap))
                  (ARRAY-ROW n ref heap)))
  :hints (("Goal" :in-theory (e/d (array-row) (ARRAY-ROW-RECOLLAPSE)))))

(in-theory (enable get-class))

(theory-invariant (incompatible (:definition ARRAY-ELEM-2D ) (:rewrite NTH-OF-ARRAY-ROW)))

;rename
(defthm sbp32-when-array-ref-listp
  (implies (and (array-ref-listp ref-list (list colcount) ':int heap)
                (memberp ref ref-list)
                (integerp col)
                (<= 0 col)
                (< col colcount))
           (unsigned-byte-p ;signed-byte-p
            32 (nth col (get-field ref (array-contents-pair) heap))))
  :hints (("Goal" :induct (true-listp ref-list)
           :in-theory (enable array-ref-listp ARRAY-REFP true-listp array-contents-okp))))

;rename
(defthm sbp32-when-array-refp
  (implies (and (array-refp ref (list rowcount colcount) ':int heap) ;free vars
                (integerp row)
                (integerp col)
                (<= 0 row)
                (< row rowcount)
                (<= 0 col)
                (< col colcount))
           (unSIGNED-BYTE-P ;SIGNED-BYTE-P
            32 (ARRAY-ELEM-2D2 row col ref heap)))
  :hints (("Goal" :expand (ARRAY-REFP REF (LIST ROWCOUNT COLCOUNT) ':INT HEAP)
           :in-theory (e/d (ARRAY-ELEM-2D2 ARRAY-ELEM-2D ;ARRAY-REFP
                                           ARRAY-CONTENTS2
                                           ARRAY-ROW
                                           )
                           (ARRAY-ELEM-2D2-RECOLLAPSE ARRAY-ELEM-2D-RECOLLAPSE
                                                      ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
                                                      ARRAY-ROW-RECOLLAPSE
                                                      ARRAY-ELEM-2D-OF-CONS ;bozo
                                                      NTH-OF-ARRAY-ROW
                                                      )))))

;trying...
;we're not yet ready for this...
;(in-theory (disable ARRAY-REFP-OPEN-FIRST-DIMENSION-WHEN-SMALL-CONSTANT))

;BOZO can this loop? what if colcount is just a call of len on array row (a common idiom: the colcount of an array is the length of its first row)
;bozo gen this and many other lemmas to arrays of any type
(defthm len-of-array-row-when-array-refp
  (implies (and (ARRAY-REFP ref (LIST rowcount colcount) type heap) ;free vars
                (integerp n)
                (integerp colcount)
                (<= 0 colcount)
                (<= 0 n)
                (< n rowcount))
           (equal (LEN (ARRAY-ROW n ref heap))
                  colcount))
  :hints (("Goal" :in-theory (e/d (ARRAY-ELEM-2D2 ARRAY-ELEM-2D ;ARRAY-REFP
                                                  ARRAY-CONTENTS2
                                                  ARRAY-ROW
                                                  )
                                  (ARRAY-ELEM-2D2-RECOLLAPSE ARRAY-ELEM-2D-RECOLLAPSE
                                                             ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
                                                             ARRAY-ROW-RECOLLAPSE
                                                             ARRAY-ELEM-2D-OF-CONS ;bozo
                                                             NTH-OF-ARRAY-ROW
                                                             ))
           :expand ((ARRAY-REFP REF (LIST ROWCOUNT COLCOUNT) TYPE HEAP)))))

(defthm consp-of-array-row-when-array-refp
  (implies (and (ARRAY-REFP ref (LIST rowcount colcount) type heap) ;free vars
                (integerp n)
                (integerp colcount)
                (<= 0 colcount)
                (<= 0 n)
                (< n rowcount))
           (equal (consp (ARRAY-ROW n ref heap))
                  (not (zp colcount))))
  :hints (("Goal" :in-theory (e/d (ARRAY-ELEM-2D2 ARRAY-ELEM-2D ;ARRAY-REFP
                                                  ARRAY-CONTENTS2
                                                  ARRAY-ROW
                                                  )
                                  (ARRAY-ELEM-2D2-RECOLLAPSE ARRAY-ELEM-2D-RECOLLAPSE
                                                             ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
                                                             ARRAY-ROW-RECOLLAPSE
                                                             ARRAY-ELEM-2D-OF-CONS ;bozo
                                                             NTH-OF-ARRAY-ROW
                                                             ))
           :expand ((ARRAY-REFP REF (LIST ROWCOUNT COLCOUNT) TYPE HEAP)))))

(defthm array-elem-2d-of-update-nth-diff
  (implies (and (not (equal row row2))
                (natp row)
                (natp row2))
           (equal (array-elem-2d row col (update-nth row2 val contents))
                  (array-elem-2d row col contents)))
  :hints (("Goal" :in-theory (e/d (array-elem-2d) (nth-of-array-row array-elem-2d-recollapse)))))

;; (EQUAL (LIST (ARRAY-ELEM-2D 1 0 A)
;;                       (ARRAY-ELEM-2D 1 1 A)
;;                       (ARRAY-ELEM-2D 1 2 A)
;;                       (ARRAY-ELEM-2D 1 3 A))
;;                 (NTH 1 A))

(defthm ARRAY-ELEM-2D-of-update-nth-same
  (implies (and ;(not (equal row row2))
                ;(natp row)
                ;(natp row2)
                )
           (equal (ARRAY-ELEM-2D row col (UPDATE-NTH row val contents))
                  (nth col val)))
  :hints (("Goal" :in-theory (e/d (array-elem-2d)
                                  (NTH-OF-ARRAY-ROW ARRAY-ELEM-2D-RECOLLAPSE)))))

;fixme rename
(defthm intp-list-list-of-array-contents-list
  (implies (array-ref-listp ref-list
                            (list numcols)
                            ':int
                            heap)
           (all-all-unsigned-byte-p 32; intp-list-list
            (array-contents-list ref-list heap)))
  :hints (("Goal" :in-theory (enable array-contents-list
                                     array-ref-listp
                                     array-refp
                                     ;;intp-list-list
                                     array-contents-okp
                                     ))))

;fixme rename
(defthm intp-list-list-of-array-contents2
  (implies (array-refp ref (list numrows numcols) ':int heap)
           (all-all-unsigned-byte-p 32 ;intp-list-list
                                      (array-contents2 ref heap)))
  :hints (("Goal" :expand ((ARRAY-REFP REF (LIST NUMROWS NUMCOLS) ':INT HEAP))
           :in-theory (enable ;array-refp
                       array-contents2))))

(defthm len-of-array-contents2
  (implies (array-refp ref (list numrows numcols) type ;':int
                       heap)
           (equal (len (array-contents2 ref heap))
                  numrows))
  :hints (("Goal" :in-theory (enable ;array-refp
                              array-contents2))))

;add int and other cases?
;move
(defthm byte-p-list-from-array-refp-one-dim
  (implies (array-refp ref (list dim) ':byte heap)
           (all-unsigned-byte-p 8 ;byte-p-list
            (get-field ref (array-contents-pair) heap)))
  :hints (("Goal" :in-theory (enable array-refp array-contents-okp))))

;not true..
;; (thm
;;  (equal (bvchop n (lognot x))
;;         (lognot (bvchop n x)))
;;  )


;; (defthm bvchop-of-s-shl-1
;;   (implies (and (natp n)
;;                 (< 0 n)
;;                 (< n 32) ;bozo
;;                 (integerp x)
;;                 (<= n m)
;;                 )
;;            (equal (BVCHOP n (JVM::S-SHL x m))
;;                   0))
;;   :hints (("Goal" :in-theory (e/d (JVM::S-SHL) (JVM::SBVMULT-RECOLLAPSE)))))

;bozo?
(in-theory (e/d (ARRAY-ELEM-2D2) (ARRAY-ELEM-2D2-RECOLLAPSE)))


(defthm byte-p-list-list-of-array-contents-list
  (implies (array-ref-listp ref-list
                            (list numcols)
                            ':byte
                            heap)
           (all-all-unsigned-byte-p 8 ;byte-p-list-list
            (array-contents-list ref-list heap)))
  :hints (("Goal" :in-theory (enable array-contents-list
                                     array-ref-listp
                                     array-refp
                                     ;;byte-p-list-list
                                     array-contents-okp
                                     ))))

(defthm byte-p-list-list-of-array-contents2
  (implies (array-refp ref
                       (list numrows numcols)
                       ':byte
                       heap)
           (all-all-unsigned-byte-p 8 ;byte-p-list-list
                                      (array-contents2 ref heap)))
  :hints
  (("Goal"
    :expand (ARRAY-REFP REF (LIST NUMROWS NUMCOLS) ':BYTE HEAP)
    :in-theory (enable ;array-refp
                       array-contents2))))

;(in-theory (disable ADD-BVCHOP-INSIDE-GETBIT)) ;bozo

(in-theory (disable ;ARRAY-REFP-OPEN-FIRST-DIMENSION-WHEN-SMALL-CONSTANT ;array-refp
                    ))

;; (defthm get-row-contents-of-2d-array
;;   (implies (and (array-refp ref (list numrows numcols) type heap)
;;                 (< n numrows)
;;                 (natp n))
;;            (equal (get-field (nth n (get-field ref (array-contents-pair) heap)) (array-type-pair) heap)
;;                   type))
;;   :hints (("Goal" :in-theory (disable ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
;;                               )
;;           :expand ((array-refp ref (list numrows numcols) type ;':byte
;;                                        heap)))))

(in-theory (disable UPDATE-SUBRANGE))

(defthm true-listp-of-array-row
  (implies (and (array-refp ref (list numrows numcols) type heap)
                (natp n)
                (< n numrows))
           (true-listp (array-row n ref heap)))
  :hints (("Goal" :in-theory (e/d (array-row) (array-row-recollapse
                                               ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
                                               ))
           :expand ((array-refp ref (list numrows numcols) type heap)))))



(defthm byte-p-list-of-get-field-contents-when-array-ref-listp
  (implies (and (array-ref-listp ref-list (list colcount) ':byte heap)
                (memberp ref ref-list))
           (all-unsigned-byte-p 8 ;byte-p-list
            (get-field ref (array-contents-pair) heap)))
  :hints
  (("Goal"
    :expand (array-refp ref (list rowcount colcount)
                        :int heap)
    :induct (true-listp ref-list)
    :in-theory
    (e/d
     (array-elem-2d2 array-elem-2d
                     true-listp
                     array-refp
                     array-ref-listp
                     array-contents2
                     array-row
                     array-contents-okp)
     (array-elem-2d2-recollapse array-elem-2d-recollapse
                                ;array-ref-listp-open-when-consp
                                array-row-recollapse
                                array-elem-2d-of-cons
                                nth-of-array-row)))))

(defthm byte-p-list-of-array-row
  (implies (and (ARRAY-REFP ref (list numrows numcols) ':BYTE heap)
                (natp n)
                (< n numrows))
           (all-unsigned-byte-p 8 ;BYTE-P-LIST
                                 (ARRAY-ROW n ref heap)))
  :hints (("Goal" :expand (ARRAY-REFP REF (LIST NUMROWS NUMCOLS)
                                      ':BYTE
                                      HEAP)
           :in-theory (e/d (ARRAY-ROW) (ARRAY-ROW-RECOLLAPSE
                                        ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
                                        )))))



;(in-theory (disable NTH1-WHEN-NOT-CDR))

;rename
(defthm intp-list-from-array-refp-one-dim
  (implies (array-refp ref (list dim) ':int heap)
           (all-unsigned-byte-p 32 ;jvm::intp-list
                                 (get-field ref (array-contents-pair) heap)))
  :hints (("Goal" :in-theory (enable array-refp array-contents-okp))))

(defthm integerp-nth-of-get-field-contents-when-array-refp
  (implies (and (ARRAY-REFP ref
                            (list len)
                            type
                            heap)
                (member-equal type '(:int :byte))
                (natp n)
                (< n len)
                )
           (integerp (NTH n (GET-FIELD ref (array-contents-pair) heap))))
  :hints (("Goal" :in-theory (enable memberp-of-cons-when-constant array-refp array-contents-okp))))


;make a set-row function
(defthm array-contents2-of-set-row
  (implies (and (natp n)
                (no-duplicatesp-equal (get-field ref (array-contents-pair) heap))
                (< n (len (get-field ref (array-contents-pair) heap)))
                (not (equal ref (nth n (get-field ref (array-contents-pair) heap)))))
           (equal (array-contents2 ref (set-field (nth n (get-field ref (array-contents-pair) heap)) (array-contents-pair) val heap))
                  (update-nth n val (array-contents2 ref heap))))
  :hints (("Goal" :in-theory (enable array-contents2))))


;; (thm
;;  (equal (CLEAR-FIELD ref pair (COPY-OBJECTS set heap1 heap2))
;;         (COPY-OBJECTS (set::delete ref set) heap1 (CLEAR-FIELD ref pair heap2)
(local (defun indh (m n lst)
         (if (endp lst)
             (list m n lst)
           (indh (+ -1 m) (+ -1 n) (cdr lst)))))

;move
(defthm not-memberp-nth-nthcdr
  (implies (and (< n m)
                (no-duplicatesp-equal lst) ;could be expensive?
                (natp n)
                (natp m)
                )
           (equal (memberp (nth n lst) (nthcdr m lst))
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (indh m n lst)
           :expand (NO-DUPLICATESP-EQUAL LST)
           :in-theory (e/d (nthcdr car-becomes-nth-of-0) ()))))

(local (defun indh22 (i) (if (zp i) i (indh22 (+ -1 i)))))

(defthm addresses-of-array-ref-list-one-dim
  (implies (and (natp len)
                (<= len (len ref-list)))
           (equal (addresses-of-array-ref-list ref-list len (list dim) heap)
                  (reverse-list (take len ref-list))))
  :hints (("Goal" :induct (indh22 len)
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (addresses-of-array-ref-list ;EQUAL-CONS-CASES2
                            take
                            ) (CAR-BECOMES-NTH-OF-0)))))

(defthmd non-nil-when-nth-is-non-nil-get-field
  (implies (and (equal free (nth n (get-field ad class-field-pair heap)))
                free)
           (iff (get-field ad class-field-pair heap)
                t)))

(defthmd hack11
  (IMPLIES (AND (EQUAL :ARRAY (NTH 0
                                   (GET-FIELD ad
                                              '(:SPECIAL-DATA . :CLASS)
                                              HEAP))))
           (CLR (array-contents-pair)
                (G ad HEAP)))
  :hints (("goal" :use ((:instance CLR-NON-NIL-WHEN-GET-FIELD-2 (a (array-contents-pair)) (pair '(:SPECIAL-DATA . :CLASS)))
                        (:instance NON-NIL-WHEN-NTH-IS-NON-NIL-GET-FIELD (n 0) (free :array) (class-field-pair '(:SPECIAL-DATA . :CLASS))))

           :in-theory (e/d ( ;-nil-when-nth-is-non-nil-get-field
                            ) ( CLR-NON-NIL-WHEN-GET-FIELD-2 CLR-NON-NIL-WHEN-GET-FIELD)))))

;BOZO make other versions?
(defthm array-ref-listp-of-set-field-both
  (implies (array-ref-listp reflist (list dim) ':int heap)
           (equal (array-ref-listp reflist (list dim) ':int (set-field ref (array-contents-pair) val heap))
                  (if (memberp ref reflist)
                      (and (true-listp val)
                           (equal dim (len val))
                           (all-unsigned-byte-p 32 val))
                    (array-ref-listp reflist (list dim) ':int heap))))
  :hints (;("subgoal *1/1.1" :use (:instance CLR-NON-NIL-WHEN-GET-FIELD-2 (a (array-contents-pair)) (ad (NTH 0 REFLIST)))                      :in-theory (e/d (non-nil-when-nth-is-non-nil-get-field) ( CLR-NON-NIL-WHEN-GET-FIELD-2 CLR-NON-NIL-WHEN-GET-FIELD)))

          ("Goal"
           :induct (len reflist)
           :in-theory (e/d ((:induction len)
                            ARRAY-REF-LISTP
                             hack11)
                           ( ;RKEYS-OF-SET-FIELD-BOTH
                            )))))

(defthmd split-list-hack
  (implies (and (consp x)
                (true-listp x))
           (equal (append (take (+ -1 (len x)) x) (list (nth (+ -1 (len x)) x)))
                  x))
  :hints (("Goal" :in-theory (enable equal-of-append))))

;              (EQUAL (LIST (NTH (+ -1 (LEN X)) X))
;                     (NTHCDR (+ -1 (LEN X)) X))

(defthm perm-cons-last-to-rest
  (implies (and (true-listp x)
                (consp x))
           (perm (cons (nth (+ -1 (len x)) x)
                            (take (+ -1 (len x)) x))
                      x))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance split-list-hack)
           :in-theory (e/d ( ;PERM-OF-CONS PERM-BECOMES-TWO-SUBBAGP-CLAIMS
                            ) (equal-of-append
                               )))))

;bozo handle other array types
;bozo heaps may not be the same
(defthm array-refp-of-set-row
  (implies (and (natp n)
                (< 0 dim2)
                (< n dim1)
                (array-refp ref (list dim1 dim2) ':int heap)
                (equal dim2 (len val))
                (true-listp val)
                (all-unsigned-byte-p 32 ;jvm::intp-list
                                      val)
;:bozo should this be part of array-refp?
                (no-duplicatesp-equal (addresses-of-array-ref ref (list dim1 dim2) heap))
                )
           (array-refp ref (list dim1 dim2) ':int (set-field (nth n (get-field ref (array-contents-pair) heap)) (array-contents-pair) val heap)))
  :otf-flg t
  :hints (("Goal" :expand ((ARRAY-REFP REF (LIST DIM1 (LEN VAL))
                                           ':INT
                                           HEAP)
                           (ARRAY-REFP REF (LIST DIM1 DIM2)
                                           ':INT
                                           (SET-FIELD (NTH N
                                                           (GET-FIELD REF (array-contents-pair)
                                                                      HEAP))
                                                      (array-contents-pair)
                                                      VAL HEAP))
                           (ARRAY-REFP REF (LIST DIM1 (LEN VAL))
                                           ':INT
                                           (SET-FIELD (NTH N
                                                           (GET-FIELD REF (array-contents-pair)
                                                                      HEAP))
                                                      (array-contents-pair)
                                                      VAL HEAP)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (array-contents2 ;array-refp
                            no-duplicatesp-equal
                            ;NO-DUPLICATESP-EQUAL-OF-CONS
                            not-equal-of-nth-when-not-memberp
                            )
                           (;CONS-EQUAL-REWRITE-CONSTANT-VERSION
                            array-elem-2d-of-cons             ;looped
                            SET::PICK-A-POINT-SUBSET-STRATEGY ;trying..
                            ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
                            ;NO-DUPLICATESP-EQUAL-OF-CONS
                            ;;addresses-of-array-ref
                            )))))



;lets the heap terms differ
(defthm array-refp-of-set-row-gen
  (implies (and (natp n)
                (< 0 dim2)
                (< n dim1)
                (equal (get-field ref (array-contents-pair) heap)
                       (get-field ref (array-contents-pair) heap2))
                (array-refp ref (list dim1 dim2) ':int heap)
                (equal dim2 (len val))
                (true-listp val)
                (all-unsigned-byte-p 32 ;jvm::intp-list
                                      val)
                ;bozo should this be part of array-refp?
                (no-duplicatesp-equal (addresses-of-array-ref ref (list dim1 dim2) heap))
                )
           (array-refp ref (list dim1 dim2) ':int (set-field (nth n (get-field ref (array-contents-pair) heap2)) (array-contents-pair) val heap)))
  :hints (("Goal" :use (:instance array-refp-of-set-row)
           :in-theory (disable array-refp-of-set-row
                               addresses-of-array-ref
                               ;array-refp
                               ))))


;better than the other rule...
(defthm length-field-when-array-ref-listp
  (implies (and (ARRAY-REF-LISTP ads (LIST NUMCOLS) type HEAP)
                (memberp ad ads))
           (equal (array-length AD HEAP)
                  numcols))
  :hints (("Goal" ;:induct (true-listp ads)
           :expand (ARRAY-REFP (NTH 0 ADS)
                               (LIST NUMCOLS)
                               TYPE HEAP)
           :in-theory (enable ;array-ref-listp
                       ))))

;todo: what is this all about?
;gen the type
(defthm ARRAY-REFP-of-set-field-both
  (implies (ARRAY-REFP ref1 (list dim) ':BYTE heap) ;bozo
           (equal (ARRAY-REFP ref1 (list dim) ':BYTE (SET-FIELD ref2 (array-contents-pair) newcontents heap))
                  (myif (equal ref1 ref2)
                        (AND (TRUE-LISTP NEWCONTENTS)
                             (EQUAL DIM (LEN NEWCONTENTS))
                             (all-unsigned-byte-p 8 ;BYTE-P-LIST
                                                   NEWCONTENTS))
                        t)))
  :hints (("Goal" :in-theory (e/d (myif get-field ;yuck
                                        ) (;IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO
                                          )))))

;this and several other things were needed when I included more than just the hacks book in the demo and arraydemo proofs - why did more rules break things?
;weird..
(defthm array-refp-of-size-0-means-contents-nil
  (implies (ARRAY-REFP ref '(0) type heap)
           (equal (GET-FIELD ref (array-contents-pair) heap)
                  nil))
  :hints (("Goal" :in-theory (enable array-refp))))


;seems needed for code which changes values of a 2d array but leaves the layout unchanged
(DEFTHM ARRAY-ELEM-2D-RECOLLAPSE-diff-but-agreeing-heaps
  (IMPLIES (AND (equal (GET-FIELD REF (array-contents-pair) HEAP)
                       (GET-FIELD REF (array-contents-pair) HEAP2))
                (INTEGERP ROW)
                (<= 0 ROW)
                (< ROW
                   (LEN (GET-FIELD REF (array-contents-pair)
                                   HEAP))))
           (EQUAL
            (NTH COL
                 (GET-FIELD (NTH ROW
                                 (GET-FIELD REF (array-contents-pair)
                                            HEAP))
                            (array-contents-pair)
                            HEAP2))
            (ARRAY-ELEM-2D ROW COL (ARRAY-CONTENTS2 REF HEAP2)))))

(defthm clr-of-clear-field-both
  (equal (clr ad (clear-field ad2 pair heap))
         (if (equal ad ad2)
             (clr ad heap)
           (clear-field ad2 pair (clr ad heap))))
  :hints
  (("Goal" :in-theory (e/d (clear-field)
                           (set-to-nil-equal-clear-field)))))

;; ;bozo why didn't the disables of this below work?
;; (local (in-theory (disable COPY-OBJECTS-EQUAL-REWRITE)))

;; (defthm COPY-OBJECTS-of-clear-field-irrel
;;   (implies (not (set::in ref refset))
;;            (equal (COPY-OBJECTS refset (CLEAR-FIELD REF PAIR HEAP1) HEAP2)
;;                   (COPY-OBJECTS refset HEAP1 HEAP2)))
;;   :hints (("subgoal *1/3" :cases ((SET::EMPTY REFSET)))
;;           ("Goal" :in-theory (e/d (COPY-OBJECTS HEAD-NOT) (COPY-OBJECTS-EQUAL-REWRITE)))))

(defthm set-field-of-s-irrel
  (implies (not (equal ref key))
           (equal (SET-FIELD REF PAIR val1 (S key val2 r))
                  (s key val2 (set-field ref pair val1 r))))
  :hints (("Goal" :in-theory (enable set-field))))

;; ;rename clear-field-of-copy-objects to -irrel?
;; (defthm clear-field-of-copy-objects-when-in
;;   (implies (set::in ref refset)
;;            (equal (clear-field ref pair (copy-objects refset heap1 heap2))
;;                   (copy-objects refset (clear-field ref pair heap1) heap2)))
;;   :hints (("subgoal *1/3" :cases ((equal ref (set::head refset))))
;;           ("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (copy-objects clear-field)
;;                            (copy-objects-equal-rewrite
;;                             SET-TO-NIL-EQUAL-CLEAR-FIELD
;;                             EQUAL-SET-FIELD-DESTRUCT-GEN ;looped?
;;                             EQUAL-SET-FIELD-DESTRUCT

;;                             )))))

;; (defthm clear-field-of-copy-objects-both
;;   (equal (clear-field ref pair (copy-objects refset heap1 heap2))
;;          (if (set::in ref refset)
;;              (copy-objects refset (clear-field ref pair heap1) heap2)
;;            (copy-objects refset heap1 (clear-field ref pair heap2))))
;;   :hints (("Goal" :in-theory (disable COPY-OBJECTS-EQUAL-REWRITE copy-objects
;;                                       ))))

(DEFTHM ARRAY-ROW-OF-SET-FIELD-IRREL-better
  (IMPLIES (AND (NOT (EQUAL REF REF2))
                (<= 0 N)
                (< N
                   (LEN (GET-FIELD REF (array-contents-pair)
                                   HEAP)))
                (NOT (equal ref2 (nth n (ARRAY-CONTENTS REF HEAP)))))
           (EQUAL (ARRAY-ROW N REF (SET-FIELD REF2 PAIR VAL HEAP))
                  (ARRAY-ROW N REF HEAP)))
  :HINTS (("Goal" :IN-THEORY (E/D (ARRAY-ROW)
                                  (ARRAY-ROW-RECOLLAPSE)))))




;; (defthm get-field-contents-of-store-array-list
;;   (implies (memberp ad ads)
;;            (equal (get-field ad (array-contents-pair) (store-array-list ads contents rowsize ':BYTE  ;gen?
;;                                                                           heap))
;;                   ;(byte-fix-list (take rowsize (nth (find-index ad ads) contents)))
;;                   (bvchop-list 8 (take rowsize (nth (find-index ad ads) contents)))
;;                   ))
;;   :hints (("Goal" :in-theory (enable store-array-list))))

;; (defthm get-field-of-store-array-2d-same-contents
;;   (implies (memberp ad2 (take numrows (array-contents ad heap)))
;;            (equal (GET-FIELD ad2 (array-contents-pair) (STORE-ARRAY-2D ad CONTENTS NUMROWS ROWSIZE ':byte ;gen?
;;                                                                          HEAP))
;;                   (bvchop-list 8 ;byte-fix-list
;;                    (take rowsize
;;                             (nth (find-index ad2 (take numrows (array-contents ad heap)))
;;                                  contents)))))
;;   :hints (("Goal" :in-theory (enable store-array-2d))))

(defthm array-contents-list-of-set-field-when-memberp
  (implies (no-duplicatesp-equal ref-list)
           (equal (array-contents-list ref-list (set-field ad (array-contents-pair) val heap))
                  (if (memberp ad ref-list)
                      (update-nth (find-index ad ref-list) val (array-contents-list ref-list heap))
                    (array-contents-list ref-list heap)
                    )))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (array-contents-list ;list::update-nth-equal-rewrite
                            ;LIST::NTH-0-BECOMES-CAR
                            MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP
                            ) (;ARRAY-CONTENTS
                               ARRAY-CONTENTS-LIST-OF-CLEAR-FIELD-NTH
                               CAR-BECOMES-NTH-OF-0
                               )))))

(defthm array-contents2-of-set-field-when-memberp
  (implies (and (memberp ad2 (array-contents ad heap))
                (no-duplicatesp-equal (array-contents ad heap))
                (not (equal ad ad2)))
           (equal (array-contents2 ad (set-field ad2 (array-contents-pair) val heap))
                  (update-nth (find-index ad2 (array-contents ad heap))
                              val
                              (array-contents2 ad heap))))
  :hints (("Goal" :in-theory (e/d (array-contents2 ;LIST::UPDATE-NTH-EQUAL-REWRITE
                                                   ) nil))))

(defthm array-contents2-of-set-field-both
  (implies (and (no-duplicatesp-equal (array-contents ad heap))
                (not (equal ad ad2)))
           (equal (array-contents2 ad (set-field ad2 (array-contents-pair) val heap))
                  (if (memberp ad2 (array-contents ad heap))
                      (update-nth (find-index ad2 (array-contents ad heap))
                                  val
                                  (array-contents2 ad heap))
                    (array-contents2 ad heap))))
  :hints (("Goal" :in-theory (e/d (array-contents2 ;LIST::UPDATE-NTH-EQUAL-REWRITE
                                   ) nil))))

(defthm array-refp-one-dim-of-s
  (implies (member-equal type '(:int :byte :boolean :short))
           (equal (array-refp ref (list x) type (s ref (g ref heap1) heap0))
                  (array-refp ref (list x) type heap1)))
  :hints (("Goal" :in-theory (enable; array-refp
                              GET-FIELD-REASSEMBLE
                              memberp-of-cons-when-constant
                              array-contents-okp
                              array-refp))))

(defthm array-refp-one-dim-of-s-irrel
  (implies (and (not (equal ref1 ref2))
                (member-equal type '(:int :byte :boolean :short)))
           (equal (array-refp ref1 (list x) type (s ref2 val heap))
                  (array-refp ref1 (list x) type heap)))
  :hints (("Goal" :in-theory (enable array-refp
                                     memberp-of-cons-when-constant
                                     array-contents-okp))))

;; (defthm array-refp-of-copy-objects-irrel
;;   (implies (and (not (set::in ref refs)) ;drat. this in about sets, but we often have bags
;;                 (member-equal type '(:int :byte :boolean :short)))
;;            (equal (array-refp ref
;;                               (cons dim nil)
;;                               type
;;                               (copy-objects refs heap1 heap0))
;;                   (array-refp ref
;;                               (cons dim nil)
;;                               type
;;                               heap0)))
;;   :hints (("Goal" :in-theory (enable copy-objects head-not))))

(defthm get-field-of-nth-when-array-ref-listp
  (implies (and (array-ref-listp ref-list (list dim) type heap)
                (< i (len ref-list))
                (natp i))
           (equal (array-length (nth i ref-list) heap)
                  dim))
  :hints (("Goal" :in-theory (e/d (;array-ref-listp
                                   ) (;array-ref-listp-open-when-consp
                                      )))))

(local
 (defthm list-of-car-and-cadr
  (implies (and (equal 2 (len dims))
                (true-listp dims))
           (equal (list (car dims) (cadr dims))
                  dims))))

(defthm get-dim2-when-array-refp
  (implies (and (array-refp ref (list dim1 dim2) type heap)
                (natp i)
                (< i dim1))
           (equal (array-length (nth i (get-field ref (array-contents-pair) heap)) heap)
                  dim2))
  :hints (("Goal" :in-theory (disable ;array-ref-listp-open-when-consp
                              ARRAY-ROW-RECOLLAPSE)
           :expand ((array-refp ref (list dim1 dim2) type heap)))))

(defthm len-of-get-field-contents-bound
  (implies (and (<= 2147483647 k)
                (array-refp ref (cons dim nil) type heap))
           (not (< k (LEN (GET-FIELD ref (array-contents-pair) heap)))))
  :hints (("Goal"
           :expand ((ARRAY-REFP REF (LIST DIM) TYPE HEAP))
           :in-theory (enable))))

;todo: drop the (equal .. t) phrasing.
(defthm len-of-get-field-contents-bound-other
  (implies (and (<= 2147483648 k)
                (array-refp ref (cons dim nil) type heap))
           (equal (< (len (get-field ref (array-contents-pair) heap)) k)
                  t))
  :hints (("Goal" :in-theory (enable array-refp))))

;BOZO now that we don't store the length field, delete some of these?
(defthm len-of-get-field-contents-bound-other2
  (implies (and (<= 2147483648 k)
                (array-refp ref (cons dim nil) type heap))
           (< (array-length ref heap) k))
  :hints (("Goal" :expand ((array-refp ref (cons dim nil) type heap)))))

;bozo whether we want this seems to depend on whether we are in the conclusion
;could add linear rules instead..
(defthm len-of-get-field-contents-bound-another
  (implies (array-refp ref (cons dim nil) type heap)
           (equal (< (LEN (GET-FIELD ref (array-contents-pair) heap)) 2147483647)
                  (not (equal (LEN (GET-FIELD ref (array-contents-pair) heap)) 2147483647))))
  :hints (("Goal"
           :expand ((ARRAY-REFP REF (LIST DIM) TYPE HEAP))
           :in-theory (enable ;array-refp
                              ))))

(defthm len-of-get-field-contents-bound-another2
  (implies (array-refp ref (cons dim nil) type heap)
           (equal (< (array-length ref heap) 2147483647)
                  (not (equal (array-length ref heap) 2147483647))))
  :hints (("Goal" :expand ((array-refp ref (cons dim nil) type heap))
           :in-theory (enable ;array-refp
                       ))))

;bozo flesh out this set, or don't explicitly store the length?
;or write one to the other
(defthm get-field-length-bound2
  (implies (and (<= 2147483647 k)
                (array-refp ref (cons dim nil) type heap))
           (not (< k (array-length ref heap))))
  :hints (("Goal" :expand (array-refp ref (cons dim nil) type heap)
           :in-theory (enable ;array-refp
                       ))))

(defthm len-of-get-fields-contents-impossible-value
  (implies (and (< 2147483647 k)
                (array-refp ref (cons dim nil) type heap))
           (equal (equal k (LEN (GET-FIELD ref (array-contents-pair) heap)))
                  nil))
  :hints (("Goal" :expand ((ARRAY-REFP REF (LIST DIM) TYPE HEAP)))))


;can lead to stack overflows..
;maybe it unifies (+ 1 x) with a constant
(defthmd logext-plus-1-when-usb-31-32
  (implies (unsigned-byte-p 31 x)
           (equal (LOGEXT 32 (+ 1 x))
                  (if (equal x (+ -1 2147483648))
                      -2147483648
                    (+ 1 x)))))

;seems to handle a common idiom:
(defthm logext-n+1-when-n-is-less-than-an-arrays-len
  (implies (and (< n (array-length ref heap)) ;free vars
                (ARRAY-REFP ref (cons dim nil) type heap)
                (UNSIGNED-BYTE-P 31 n))
           (equal (LOGEXT 32 (+ 1 n))
                  (+ 1 n)))
  :hints (("Goal" :expand (ARRAY-REFP REF (LIST DIM) TYPE HEAP)
           :in-theory (enable ;array-refp
                       logext-plus-1-when-usb-31-32))))


;it's a pity that i need both of these...
(defthm logext-n+1-when-n-is-less-than-an-arrays-len-2
  (implies (and (< n (LEN (GET-FIELD ref (array-contents-pair) heap))) ;free vars
                (ARRAY-REFP ref (cons dim nil) type heap)
                (UNSIGNED-BYTE-P 31 n))
           (equal (LOGEXT 32 (+ 1 n))
                  (+ 1 n)))
  :hints (("Goal" :expand (ARRAY-REFP REF (LIST DIM) TYPE HEAP)
           :in-theory (enable ;array-refp
                       logext-plus-1-when-usb-31-32))))

(defthm logext-n+1-when-n-is-less-than-an-arrays-dim
  (implies (and (ARRAY-REFP ref (cons dim nil) type heap)
                (< n dim) ;free var
                (UNSIGNED-BYTE-P 31 n))
           (equal (LOGEXT 32 (+ 1 n))
                  (+ 1 n)))
  :hints (("Goal" :expand (ARRAY-REFP REF (LIST DIM) TYPE HEAP)
           :in-theory (enable ;array-refp
                       logext-plus-1-when-usb-31-32))))

(defthm array-dim-is-integerp
  (implies (array-refp ref (cons dim dims) type heap)
           (integerp dim))
  :hints (("Goal" :expand (array-refp ref (cons dim dims) type heap))))

(defthm integerp-of-get-field-length-when-array-refp
  (implies (array-refp ref (cons dim dims) type heap)
           (INTEGERP (array-length ref heap)))
  :hints (("Goal" :expand ((ARRAY-REFP REF (CONS DIM DIMS)
                                       TYPE HEAP)))))

;special because val is a specific call to get
(DEFTHM ARRAY-REFP-ONE-DIM-OF-SL-both-special
  (IMPLIES (MEMBER-EQual TYPE '(:INT :BYTE :BOOLEAN :short))
           (EQUAL (ARRAY-REFP REF1 (LIST X) TYPE (S REF2 (G ref2 heap2) HEAP))
                  (if (EQUAL REF1 REF2)
                      (ARRAY-REFP REF1 (LIST X) TYPE HEAP2)
                    (ARRAY-REFP REF1 (LIST X) TYPE HEAP))))
  :HINTS (("Goal" :IN-THEORY (ENABLE ;ARRAY-REFP
                              get-field
                              ))))

;bozo more like this?
;trying with hyps reordered...
(defthm array-dim-bound
  (implies (and (array-refp ref (cons dim nil) type heap)
                (<= 2147483647 k))
           (not (< k dim)))
  :hints (("Goal" :expand (array-refp ref (cons dim nil) type heap)
           :in-theory (enable ;array-refp
                       ))))

;bozo too specific?
(defthm sbp-of-dim-minus-1
  (implies (array-refp ref (cons dim dims) type heap)
           (signed-byte-p 32 (+ -1 dim)))
  :hints (("Goal" :expand (array-refp ref (cons dim dims) type heap)
           :in-theory (enable ;array-refp
                       ))))

(defthm sbp-of-arraylen-minus-1
  (implies (array-refp ref (cons dim dims) type heap)
           (signed-byte-p 32 (+ -1 (array-length ref heap))))
  :hints (("Goal" :expand (array-refp ref (cons dim dims) type heap)
           :in-theory (enable ;array-refp
                       ))))

(defthm array-refp-fw-to-len
  (implies (array-refp ref (list dim) type heap)
           (equal dim (len (get-field ref (array-contents-pair) heap))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :expand ((array-refp ref (list dim) type heap)))))

(defthm array-refp-fw-to-len2
  (implies (array-refp ref (list dim) type heap)
           (equal dim (array-length ref heap)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :expand ((array-refp ref (list dim) type heap)))))


;; ;BOZO only for bytes!
;; (DEFTHM GET-FIELD-contents-OF-STORE-ARRAY-2D-both
;;   (EQUAL (GET-FIELD AD2 (array-contents-pair) (STORE-ARRAY-2D AD CONTENTS NUMROWS ROWSIZE ':byte HEAP))
;;          (if (MEMBERP AD2 (TAKE NUMROWS (ARRAY-CONTENTS AD HEAP)))
;;              (bvchop-list 8 ;BYTE-FIX-LIST
;;               (TAKE
;;                ROWSIZE
;;                (NTH
;;                 (FIND-INDEX AD2
;;                             (TAKE NUMROWS (ARRAY-CONTENTS AD HEAP)))
;;                 CONTENTS)))
;;            (GET-FIELD AD2 (array-contents-pair) HEAP)))
;;   :HINTS (("Goal" :IN-THEORY (ENABLE STORE-ARRAY-2D))))

;; ;BOZO gen!
;; (defthm array-refp-of-store-array-2d-when-member-of-contents
;;   (implies (and (memberp ref1 (array-contents ref2 heap))
;; ;                (equal 4 (len (array-contents ref2 heap))) ;BOZO new
;;                 (array-refp ref1 '(4) ':byte heap)
;;                 )
;;            (array-refp ref1 '(4) ':byte (store-array-2d ref2 vals 4 4 ':byte heap)))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (disable store-array-2d)
;;            :expand ((ARRAY-REFP REF1 '(4) ':BYTE HEAP)
;;                     (array-refp ref1 '(4)
;;                                        ':byte
;;                                        (store-array-2d ref2 vals 4 4 ':byte
;;                                                        heap))))))

;BOZO gen
(defthm array-length-when-a-row-of-a-2d-array
  (implies (and (memberp ref1 (GET-FIELD REF2 (array-contents-pair) HEAP)) ;binds the free variable ref2
                (array-refp ref2 (list dim1 dim2) type heap)
                )
           (equal (array-length ref1 heap)
                  dim2))
  :hints (("Goal" :in-theory (disable ;ARRAY-REF-LISTP
                              ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
                              )
           :expand ((ARRAY-REFP REF2 (LIST DIM1 DIM2)
                                type
                                HEAP)))))

(local (IN-THEORY (ENABLE ;COPY-GIVEN-OBJECTS-AND-NEW-ONES
                   MEMBERP-OF-CONS)))

;; ;BOZO replace the other one
;; (defthm array-refp-of-store-array-2d-irrel-better
;;   (implies (and (<= numrows (len (array-contents ref2 heap)))
;;                 (memberp type '(:byte :int :boolean :short)) ;BOZO
;;                 (not (zp numcols))
;;                 (not (memberp ref1 (array-contents ref2 heap))))
;;            (equal (array-refp ref1 (cons dim nil) type (store-array-2d ref2 contents numrows numcols type heap))
;;                   (array-refp ref1 (cons dim nil) type heap)))
;;   :hints (("Goal" :expand ()
;;            :in-theory (enable ;array-refp
;;                        ))))

(defthm true-listp-of-contents-contents-when-array-refp
  (implies (and (ARRAY-REFP ref (list dim1 dim2) type heap)
                (natp dim1)
                (natp n)
                (< n dim1))
           (true-listp (GET-FIELD (NTH n
                                       (GET-FIELD ref
                                                  (array-contents-pair)
                                                  heap))
                                  (array-contents-pair)
                                  heap)))
  :hints (("Goal" :in-theory (disable ;ARRAY-REF-LISTP-OPEN-WHEN-CONSP
                                      ARRAY-ROW-RECOLLAPSE)
           :expand (ARRAY-REFP ref (list dim1 dim2) type heap))))



(defthm usbp-31-array-refp-hack
  (IMPLIES (AND (< (+ n X)
                   (LEN (GET-FIELD REF (array-contents-pair)
                                   HEAP)))
                (<= k n)
                (natp n)
                (natp k)
                (ARRAY-REFP REF (list LEN) TYPE HEAP)
                (UNSIGNED-BYTE-P 31 X))
           (UNSIGNED-BYTE-P 31 (+ k X)))
  :hints (("Goal" :expand ((ARRAY-REFP REF (LIST LEN) TYPE HEAP)))))

;bozo genthese?
(defthm sbp-32-array-refp-hack
  (IMPLIES (AND (< (+ n X)
                   (LEN (GET-FIELD REF (array-contents-pair)
                                   HEAP)))
                (<= k n)
                (natp n)
                (natp k)
                (ARRAY-REFP REF (list LEN) TYPE HEAP)
                (UNSIGNED-BYTE-P 31 X))
           (SIGNED-BYTE-P 32 (+ k X)))
  :hints (("Goal" :expand ((ARRAY-REFP REF (LIST LEN) TYPE HEAP)))))

(local
 (defun hii (n lst)
   (if (zp n)
       (list n lst)
     (hii (+ -1 n) lst))))

;bozo i think the whole heap is irrelevant!
(defthm ADDRESSES-OF-ARRAY-REF-LIST-of-set-field-irrel
  (implies (and; (not (memberp ref ref-list))
                (natp items-left)
               ; (<= items-left (len item-list))
                )
           (equal (ADDRESSES-OF-ARRAY-REF-LIST item-list items-left '(4) (SET-FIELD ref pair val heap))
                  (ADDRESSES-OF-ARRAY-REF-LIST item-list items-left '(4) heap)))
  :hints (("Goal" :in-theory (enable true-listp ADDRESSES-OF-ARRAY-REF-LIST)
           :do-not '(generalize eliminate-destructors)
           :expand ((ADDRESSES-OF-ARRAY-REF-LIST ITEM-LIST ITEMS-LEFT '(4)
                                                 (SET-FIELD REF PAIR VAL HEAP)))
           :induct (hii items-left item-list)
           )))

;BOZO gen!
(defthm ARRAY-REFP-of-set-contents-and-set-contents
  (equal (ARRAY-REFP ref '(4) ':INT (SET-FIELD ref (array-contents-pair) vals (SET-FIELD ref2 (array-contents-pair) vals2 heap)))
         (ARRAY-REFP ref '(4) ':INT (SET-FIELD ref (array-contents-pair) vals heap)))
  :hints (("Goal" :in-theory (enable ARRAY-REFP))))


;vals and vals2 differ
;; (defthm ARRAY-REFP-of-set-contents-lemma
;;   (implies (and (ARRAY-REFP ref '(4) ':INT (SET-FIELD ref (array-contents-pair) vals heap))
;;                 (TRUE-LISTP VALS2)
;;                 (EQUAL 4 (LEN VALS2))
;;                 (JVM::INTP-LIST VALS2))
;;            (ARRAY-REFP ref '(4) ':INT (SET-FIELD ref (array-contents-pair) vals2 heap)))
;;   :hints (("Goal" :in-theory (enable ARRAY-REFP))))



(defthm sbp-from-less-than-array-bound
  (implies (and (< x (len (GET-FIELD ref (array-contents-pair) heap)))
                (ARRAY-REFP ref (LIST dim) type heap)
                (<= 0 x)
                (integerp x)
                )
           (SIGNED-BYTE-P 32 x))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P)
           :expand ((ARRAY-REFP REF (LIST DIM) TYPE HEAP)))))

(defthm sbp-from-less-than-array-bound2
  (implies (and (< (+ k x) (len (GET-FIELD ref (array-contents-pair) heap)))
                (<= 0 k)
                (ARRAY-REFP ref (LIST dim) type heap)
                (<= 0 x)
                (integerp x)
                )
           (SIGNED-BYTE-P 32 x))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P)
           :expand ((ARRAY-REFP REF (LIST DIM) TYPE HEAP)))))

(defthm sbp-from-less-than-array-bound3
  (implies (and (< (+ k2 x) (len (GET-FIELD ref (array-contents-pair) heap)))
                (<= k k2)
                (<= 0 k)
                (integerp k)
                (integerp k2)
                (ARRAY-REFP ref (LIST dim) type heap)
                (<= 0 x)
                (integerp x)
                )
           (SIGNED-BYTE-P 32 (+ k x)))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P SIGNED-BYTE-P)
           :expand ((ARRAY-REFP REF (LIST DIM) TYPE HEAP)))))

(defthm s-of-contents-not-nil-when-array-refp
  (implies (and (array-refp ad (cons len nil) type heap)
                type)
           (not (equal nil (s (array-contents-pair) new-contents (g ad heap)))))
  :hints (("Goal" ;:use (:instance GET-FIELD-TYPE-FROM-ARRAY-REFP (ref ad) (dim len))
           :expand ((ARRAY-REFP AD (LIST LEN) TYPE HEAP))
           :in-theory (e/d (get-field) ( ;GET-FIELD-TYPE-FROM-ARRAY-REFP
                                        G-IFF-GEN S-IFF)))))

(DEFTHM INTEGERP-NTH-OF-GET-FIELD-CONTENTS-WHEN-ARRAY-REFP2
  (IMPLIES (AND (ARRAY-REFP REF (LIST LEN) TYPE HEAP)
                (MEMBER-EQual TYPE '(:INT :BYTE))
                (NATP N)
                (< N LEN))
           (equal (INTEGERP (NTH N (GET-FIELD REF (array-contents-pair) HEAP)))
                  t)))

;; (len (GET-FIELD (NTH index (GET-FIELD 2 (array-contents-pair) HEAP-AT-LOOP-TOP)) (array-contents-pair) HEAP-AT-LOOP-TOP))
(defthm get-dim2-when-array-refp-dag
  (implies (and (equal (array-refp ref dims type heap) ;free vars
                       t)
                ;;dims may often be a constant
                (equal 2 (len dims))
                (true-listp dims)
                (natp i)
                (< i (car dims)))
           ;; was a call to the array-length macro
           (equal (LEN (GET-FIELD (NTH I
                                       (GET-FIELD REF (array-contents-pair)
                                                  HEAP))
                                  (array-contents-pair)
                                  HEAP))
                  (cadr dims)))
  :hints (("Goal" :use (:instance get-dim2-when-array-refp (dim1 (car dims)) (dim2 (cadr dims)))
           :in-theory (disable get-dim2-when-array-refp))))

(defthm array-row-of-set-field-irrel2
  (implies (not (equal pair (array-contents-pair)))
           (equal (array-row n ref (set-field ref2 pair val heap))
                  (array-row n ref heap)))
  :hints (("Goal" :in-theory (e/d (array-row)
                                  (array-row-recollapse)))))

(theory-invariant (incompatible (:definition clear-field) (:rewrite EQUAL-SET-FIELD-DESTRUCT-GEN)))
(theory-invariant (incompatible (:definition clear-field) (:rewrite EQUAL-SET-FIELD-DESTRUCT)))

(defthm clear-field-of-s-irrel
  (implies (not (equal ad ad2))
           (equal (CLEAR-FIELD ad field (S ad2 value heap))
                  (s ad2 value (CLEAR-FIELD ad field heap))))
  :hints (("Goal" :in-theory (e/d (CLEAR-FIELD) (SET-TO-NIL-EQUAL-CLEAR-FIELD
                                                 EQUAL-SET-FIELD-DESTRUCT-GEN
                                                 EQUAL-SET-FIELD-DESTRUCT)))))

;trying for efficiency
(in-theory (disable set-field-of-get-field-same-eric-2))

;; (defthm g-of-STORE-ARRAY-LIST
;;  (implies (memberp ad2 ads)
;;           (equal (G AD2 (STORE-ARRAY-LIST ads contents ROWSIZE ':BYTE HEAP))
;;                  (s (array-contents-pair)
;;                     (bvchop-list 8 ;byte-fix-list
;;                                   (take rowsize (nth (find-index ad2 ads) contents)))
;;                     (G AD2 HEAP))))
;;  :hints (("Goal" :in-theory (enable store-array-list))))

;; (defthm g-of-store-array-2d-same-contents
;;   (implies (and (memberp ad2 (array-contents ad heap))
;;                 (equal numrows (len (array-contents ad heap))))
;;            (equal (G ad2 (STORE-ARRAY-2D ad CONTENTS NUMROWS ROWSIZE ':byte HEAP))
;;                   (s (array-contents-pair)
;;                      (bvchop-list 8 ;byte-fix-list
;;                       (take rowsize
;;                                (nth (find-index ad2 (array-contents ad heap)) contents)))
;;                      (g ad2 heap))))
;;   :hints (("Goal" :in-theory (e/d (store-array-2d) (TAKE-WHEN-<=-OF-LEN)))))



;todo: move these:

;disabled Thu Apr 29 21:07:26 2010
;loops with BV-ARRAY-READ-OF-GETBIT-LIST
(defthmd getbit-of-bv-array-read-helper
  (implies (and (natp n)
                (< n element-size)
                (posp len)
                (natp element-size))
           (equal (getbit n (bv-array-read element-size len index data))
                  (bv-array-read 1 len index (getbit-list n data))))
  :hints (("Goal" :in-theory (e/d (getbit-list ;LIST::NTH-WITH-LARGE-INDEX
                                   natp posp bv-array-read GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                                  (; LIST::NTH-OF-CONS
                                   )))))

(defthmd getbit-of-bv-array-read
  (implies (and (syntaxp (and (quotep n)
                              (quotep data)))
                (natp n)
                (< n element-size)
                (posp len)
;                (equal len (len data))
                (natp element-size))
           (equal (getbit n (bv-array-read element-size len index data))
                  (bv-array-read 1 len index (getbit-list n data)))) ;the getbit-list gets computed
  :hints (("Goal" :use (:instance getbit-of-bv-array-read-helper)
           :in-theory (e/d (getbit-list) ( getbit-of-bv-array-read-helper)))))

;disable?
;compare to the regular
(DEFTHMd GETBIT-OF-BV-ARRAY-READ-gen
  (IMPLIES (AND ;(syntaxp (QUOTEP N))
;(syntaxp (QUOTEP DATA))
            (NATP N)
            (NATP INDEX)
            (< N (+ -1 ELEMENT-SIZE)) ; could have (< N ELEMENT-SIZE) but that seems to lead to loops
            (< INDEX LEN)
            (EQUAL LEN (LEN DATA))
            (NATP ELEMENT-SIZE))
           (EQUAL (GETBIT N (BV-ARRAY-READ ELEMENT-SIZE LEN INDEX DATA))
                  (BV-ARRAY-READ 1 LEN INDEX (GETBIT-LIST N DATA))))
  :HINTS (("Goal" :use (:instance getbit-of-bv-array-read)
           :IN-THEORY (E/D (GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER)
                           ()))))


;useful when get-field gets opened (e.g., for baload)
(defthm g-of-g-of-set-field-same
  (equal (g pair (g ref (set-field ref pair value heap)))
         value))

(DEFTHM g-of-g-of-set-field-when-pairs-different
  (IMPLIES (NOT (EQUAL PAIR1 PAIR2))
           (EQUAL (G PAIR1
                     (G REF1 (SET-FIELD REF2 PAIR2 VALUE HEAP)))
                  (GET-FIELD REF1 PAIR1 HEAP)))
  :hints (("Goal" :in-theory (enable set-field get-field))))

;bozo this takes advantage of behavior that should never happen in a real jvm run (but we found it hard to exclude such a case in triple des, since we don't fully handle ifs)
(defthm get-field-of-nth-new-ad-same-heap
  (equal (get-field (nth-new-ad n (rkeys heap)) pair heap)
         nil)
  :hints (("Goal" :in-theory (enable get-field g-when-not-in-rkeys))))


;doesn't have a hyphen in the name:
(defmacro newad (ad-set)
  `(new-ad ,ad-set))

;doesn't have a hyphen in the name:
(defmacro nthnewad (n ad-set)
  `(nth-new-ad ,n ,ad-set))

;move
(defthm new-ad-of-myif
  (equal (new-ad (myif test a b))
         (myif test (new-ad a)
               (new-ad b)))
  :hints (("Goal" :in-theory (enable myif))))

;move
(defthm rkeys-of-myif
  (equal (rkeys (myif test a b))
         (myif test (rkeys a)
               (rkeys b)))
  :hints (("Goal" :in-theory (enable myif))))

;because we disabled MYIF-WHEN-NOT-NIL -- add support for backchain limits and limit it?
;or use equivs somehow..
(defthm jvm::myif-of-nth-new-ad
  (equal (myif (nth-new-ad n dom) thenpart elsepart)
         thenpart))

(defthm jvm::myif-of-new-ad
  (equal (myif (new-ad dom) thenpart elsepart)
         thenpart))

(defthm unique-of-N-NEW-ADS2
  (implies (natp n)
           (NO-DUPLICATESP-EQUAL (N-NEW-ADS2 n ads)))
  :hints (("Goal" :in-theory (enable n-NEW-ADS2))))

(defthm null-refp-of-myif
  (equal (null-refp (myif test tp ep))
         (myif test (null-refp tp) (null-refp ep)))
  :hints (("Goal" :in-theory (enable myif))))

;;Standard hyps about the values in a Java array of ints:
(defun array-of-ints-hyps (var)
  `((all-unsigned-byte-p '32 ,var)
    (true-listp ,var)
    (unsigned-byte-p '31 (len ,var)) ;the len is short enough to fit in a JVM array
    ))

;helps with lifting programs with conditionals
(defthm stack-of-myif
  (equal (jvm::stack (myif test x y))
         (myif test (jvm::stack x) (jvm::stack y)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm thread-top-frame-of-myif
  (equal (jvm::thread-top-frame th (myif test s1 s2))
         (myif test (jvm::thread-top-frame th s1) (jvm::thread-top-frame th s2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm heap-of-myif
  (equal (jvm::heap (myif test s1 s2))
         (myif test (jvm::heap s1) (jvm::heap s2)))
  :hints (("Goal" :in-theory (enable myif))))

;; We need this form of the rule for Axe, I think?
;see S-NON-NIL-CANNOT-BE-NIL
(defthm not-equal-of-nil-and-s
  (implies (not (equal nil v))
           (not (equal nil (s a v r)))))

;; We need this form of the rule for Axe, I think?
(defthm not-equal-nil-when-array-refp
  (implies (and (ARRAY-REFP ad DIMS element-type HEAP)
                (member-eq element-type '(:int :byte :boolean :short))) ;gen
           (not (equal nil ad))))

(defthmd not-in-of-nil-when-all-addressp-of-2list
  (implies (all-addressp (set::2list set))
           (not (set::in nil set))))

(defthm get-field-of-nil-when-heapp
  (implies (jvm::heapp heap)
           (equal (get-field nil pair heap)
                  nil))
  :hints (("Goal" :in-theory (enable jvm::heapp get-field g-when-not-in-rkeys key-list
                                     not-in-of-nil-when-all-addressp-of-2list))))

(defthmd not-in-of-minus1-when-all-addressp-of-2list
  (implies (all-addressp (set::2list set))
           (not (set::in -1 set))))

(defthm get-field-of-minus1-when-heapp
  (implies (jvm::heapp heap)
           (equal (get-field -1 pair heap)
                  nil))
  :hints (("Goal" :in-theory (enable jvm::heapp get-field g-when-not-in-rkeys key-list
                                     not-in-of-minus1-when-all-addressp-of-2list))))

(defthm not-null-refp-when-equal-of-get-field
  (implies (and (equal val (get-field ad pair heap))
                val
                (jvm::heapp heap))
           (not (null-refp ad)))
  :hints (("Goal" :in-theory (enable jvm::heapp))))

(defthm not-null-refp-when-equal-of-get-field-alt
  (implies (and (equal (get-field ad pair heap) val)
                val
                (jvm::heapp heap))
           (not (null-refp ad))))

;move some of these to other libraries:

(defthm myif-of-cons-and-cons
  (equal (myif test (cons a1 b1) (cons a2 b2))
         (cons (myif test a1 a2) (myif test b1 b2)))
  :hints (("Goal" :in-theory (enable myif))))

;gross proof
(defthm bind-equal-same-rewrite
  (equal (equal (jvm::bind key val alist) alist)
         (equal (assoc-equal key alist) (cons key val)))
  :hints (("Goal" :in-theory (e/d (jvm::bind ASSOC-EQUAL) (CAR-BECOMES-NTH-OF-0)))))

(defthm car-of-assoc-equal2
  (equal (car (assoc-equal key alist))
         (if (assoc-equal key alist)
             key
           nil))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;a bit gross - using s and g would be better
(defthm bind-equal-same-rewrite2
  (implies (alistp alist)
           (equal (equal (jvm::bind key val alist) alist)
                  (and (assoc-equal key alist)
                       (equal (jvm::binding key alist) val))))
  :hints (("Goal" :in-theory (e/d (assoc-equal jvm::bind alistp jvm::binding)
                                  (car-becomes-nth-of-0)))))

(defthm heapref-table-of-myif
  (equal (jvm::heapref-table (myif test s1 s2))
         (myif test (jvm::heapref-table s1) (jvm::heapref-table s2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm monitor-table-of-myif
  (equal (jvm::monitor-table (myif test s1 s2))
         (myif test (jvm::monitor-table s1) (jvm::monitor-table s2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm class-table-of-myif
  (equal (jvm::class-table (myif test s1 s2))
         (myif test (jvm::class-table s1) (jvm::class-table s2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm intern-table-of-myif
  (equal (jvm::intern-table (myif test s1 s2))
         (myif test (jvm::intern-table s1) (jvm::intern-table s2)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm initialized-classes-of-myif
  (equal (jvm::initialized-classes (myif test s1 s2))
         (myif test (jvm::initialized-classes s1) (jvm::initialized-classes s2)))
  :hints (("Goal" :in-theory (enable myif))))
