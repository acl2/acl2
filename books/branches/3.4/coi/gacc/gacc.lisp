#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;; Keep this list of include-books in sync with the list in the .acl2 file:
;;
(include-book "ram")
(include-book "ordinals/e0-ordinal" :dir :system)

(local (include-book "top" :dir :bags)) ;would have the effect of disabling a bunch of expensive bag rules.

(local (in-theory (disable MAX-OFFSET)))

;for efficiency:
;(local (in-theory (disable BAG::DISJOINT-APPEND-REDUCTION)))

(in-theory (disable 
            (:REWRITE DEFAULT-<-2)
            (:REWRITE DEFAULT-<-1)
            (:REWRITE DEFAULT-+-2)
            (:REWRITE DEFAULT-+-1)
;            (:rewrite z*-wx-introduction)
            ))

; the next 4 events copied to gacc2, since this book is being deprecated (don't keep both copies forever).
(defun syntax-consp-or-quote (skel)
  (declare (type t skel))
  (or (quotep skel)
      (and (consp skel)
           (equal (car skel) 'cons))))

(defun syntax-consp-or-symbol (skel)
  (declare (type t skel))
  (or (symbolp skel)
      (and (consp skel)
           (or (equal (car skel) 'cons)
               (and (equal (car skel) 'quote)
                    (consp (cdr skel))
                    (not (null (cadr skel))))))))
      

(defun syntax-atom (m)
  (declare (type t m))
  (or (symbolp m)
      (quotep m)))




;;;
;;; Type reasoning
;;;

;bzo
(defthm integerp-+
  (implies
   (and 
    (integerp x)
    (integerp y))
   (integerp (+ x y))))

;bzo
(defthm integerp-implies-common-types
  (implies (integerp x)
           (and (rationalp x)
                (acl2-numberp x))))

(defun anything (x)
  (declare (type t x)
           (ignore x))
  t)

;bzo
(defun non-negative-integerp (n)
  (declare (type t n))
  (and (integerp n)
       (<= 0 n)))

(defthm non-negative-integerp-implies
  (implies (non-negative-integerp n)
           (and (integerp n)
                (<= 0 n)))
  :rule-classes (:forward-chaining))

(defthm implies-non-negative-integerp
  (implies (and (integerp n)
                (<= 0 n))
           (non-negative-integerp n)))

(in-theory (disable non-negative-integerp))

(defun positive-integerp (n)
  (declare (type t n))
  (and (integerp n)
       (< 0 n)))

(defthm positive-integerp-implies
  (implies (positive-integerp n)
           (and (integerp n)
                (< 0 n)))
  :rule-classes (:forward-chaining))

(defthm implies-positive-integerp
  (implies (and (integerp n)
                (< 0 n))
           (positive-integerp n)))

;;
;; skel type descriptors
;;

;; Ultimately I think we will want to adopt a notion of skel that
;; enables a skel to be used as a "ram" .. in other words, a skel that
;; supports a hierarcical decomposition of data description.  The
;; primary concern is whether we need to expose certain aspects of the
;; skel structure in order to do so .. ?
;; 
;; (if (consp skel)
;;   (let ((entry (car skel))
;;     (let ((key (car entry)))
;;       ...
;;       (s key value' (g* (cdr skel) ram))))



(defmacro skel-entry-body (entry &rest rst)
  `(let ((entry ,entry))
     (and (consp entry)
          (consp (cdr entry))
          (consp (cddr entry))
          (consp (cdddr entry))
          (consp (cddddr entry))
          (consp (cdddddr entry))
          (null  (cddddddr entry))
          (let ((akey (car entry))       ; abstract key
                (base (cadr entry))      ; base address of structure
                (indx (caddr entry))     ; index
                (size (cadddr entry))    ; size
                (ptr  (caddddr entry))   ; value/pointer
                (type (cadddddr entry))) ; type
            (and (anything akey)
                 (integerp base)
                 (non-negative-integerp indx)
                 (positive-integerp size)
                 (integerp ptr)
                 ,@rst)))))

;;
;; weak-skel
;;

(defun weak-skel (skel)
  (declare (type t skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (and (skel-entry-body entry (acl2::unsigned-byte-p (fix-size size) ;wintn 8 size 
                                                           ptr) (weak-skel type))
             (weak-skel (cdr skel))))
    (null skel)))
   
(defthm weak-skel-implies-true-listp
  (implies
   (weak-skel skel)
   (true-listp skel))
  :rule-classes (:forward-chaining))

(defthm open-weak-skel
  (implies (and (syntaxp (symbolp skel))
                (consp skel))
           (equal (weak-skel skel)
                  (let ((entry (car skel)))
                    (and (skel-entry-body entry (acl2::unsigned-byte-p (fix-size size) ;wintn 8 size 
                                                                       ptr) (weak-skel type))
                         (weak-skel (cdr skel)))))))


;;
;; Here we begin to introduce a weak notion of collect .. one that
;; collects only the "active" regions of the block.
;;

(defund blks (skel)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((ptr   (cadr entry))
              (index (caddr entry))
              (size  (cadddr entry)))
          (let ((blk (blk (+ (ifix ptr) index) (1+ (max-offset size)))))
            (append blk (blks (cdr skel))))))
    nil))

(defthm blks-of-cons
  (equal (blks (cons a skel))
         (append  (BLK (+ (IFIX (CADR a)) (CADDR a))
                       (1+ (MAX-OFFSET (CADDDR a)))) 
                  (blks skel)))
  :hints (("Goal" :in-theory (e/d (blks) (ifix)))))

(defthm blks-when-skel-is-not-a-consp
  (implies (not (consp skel))
           (not (blks skel)))
  :hints (("Goal" :in-theory (enable blks))))


(defthmd open-blks
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (blks skel)
           (LET ((ENTRY (CAR SKEL)))
                (LET ((PTR (CADR ENTRY))
                      (INDEX (CADDR ENTRY))
                      (SIZE (CADDDR ENTRY)))
                     (LET ((BLK (BLK (+ (IFIX PTR) INDEX)
                                     (1+ (MAX-OFFSET SIZE)))))
                          (APPEND BLK (BLKS (CDR SKEL))))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (blks skel) nil)))
  :hints (("Goal" :in-theory (enable blks))))

(defthm true-listp-blks
  (true-listp (blks skel)))

(defthm blks-append
  (equal (blks (append x y))
         (append (blks x)
                 (blks y)))
  :hints (("Goal" :in-theory (enable blks append))))

;(local (in-theory (enable append))) ;yuck.

;; Does this really improve performance?
;;
(in-theory (disable (:TYPE-PRESCRIPTION BLKS)))

(defund mesh (skel)
  (declare (type (satisfies weak-skel) skel)
           ;(xargs :verify-guards nil)
           )
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((type (cadddddr entry))) ; type
          (append (blks type)
                  (mesh type)
                  (mesh (cdr skel)))))
    nil))

(defthm mesh-of-cons
  (equal (mesh (cons entry skel))
         (APPEND (BLKS (CADDDDDR ENTRY))
                 (MESH (CADDDDDR ENTRY))
                 (MESH SKEL)))
  :hints (("Goal" :in-theory (enable mesh))))

(defthm mesh-when-skel-is-not-a-consp
  (implies (not (consp skel))
           (not (mesh skel)))
  :hints (("Goal" :in-theory (enable mesh))))
         
(defthmd open-mesh
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (mesh skel)
           (LET ((ENTRY (CAR SKEL)))
                (LET ((TYPE (CADDDDDR ENTRY)))
                     (APPEND (BLKS TYPE)
                             (MESH TYPE)
                             (MESH (CDR SKEL)))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (mesh skel) nil)))
  :hints (("Goal" :in-theory (enable mesh))))

(defthm true-listp-mesh
  (true-listp (mesh skel)))

(defthm mesh-append
  (equal (mesh (append x y))
         (append (mesh x)
                 (mesh y)))
  :hints (("Goal" :in-theory (enable mesh))))

;(verify-guards mesh)

(in-theory (disable (:TYPE-PRESCRIPTION MESH)))

(defun flatten (skel)
  (declare (type (satisfies weak-skel) skel))
  (append (blks skel) (mesh skel)))

;;
;; wf-skel
;;

(defun uniform-base (skel)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry1 (car skel)))
        (let ((base1 (cadr entry1)))
          (if (consp (cdr skel))
              (let ((entry2 (car (cdr skel))))
                (let ((base2 (cadr entry2)))
                  (and (equal base1 base2)
                       (uniform-base (cdr skel)))))
            t)))
    t))

(defun wf-skel (skel)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (and (skel-entry-body entry
                              (wf-skel type) 
                              (acl2::unsigned-byte-p (fix-size size) ptr) ;(wintn 8 size ptr) 
                              (unique (blks type))
                              (uniform-base type)
                              )
             (wf-skel (cdr skel))))
    (null skel)))
   
(defthm open-wf-skel
  (implies (and (syntaxp (syntax-consp-or-symbol skel))
                (consp skel))
           (equal (wf-skel skel)
                  (let ((entry (car skel)))
                    (and (skel-entry-body entry 
                                          (wf-skel type) 
                                          (acl2::unsigned-byte-p (fix-size size) ptr) ;(wintn 8 size ptr)
                                          (unique (blks type))
                                          (uniform-base type)
                                          )
                         (wf-skel (cdr skel)))))))

(defthm wf-skel-implies-weak-skel
  (implies (wf-skel skel)
           (weak-skel skel))
  :rule-classes (:forward-chaining))

;;
;; size-rec
;;

(defun size-rec (max skel)
  (declare (type integer max)
           (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((indx (caddr entry))
              (size (cadddr  entry)))
          (let ((max (max (nfix max) (+ 1 (nfix indx) (max-offset size)))))
            (size-rec max (cdr skel)))))
    (nfix max)))

(defthm open-size-rec
  (and
   (implies
    (consp skel)
    (equal (size-rec max skel)
           (let ((entry (car skel)))
             (let ((indx (caddr entry))
                   (size (cadddr  entry)))
               (let ((max (max (nfix max) (+ 1 (nfix indx) (max-offset size)))))
                 (size-rec max (cdr skel)))))))
   (implies
    (null skel)
    (equal (size-rec max skel) (nfix max)))))

(defthm non-negative-integerp-size-rec
  (and
   (non-negative-integerp (size-rec max skel))
   (integerp (size-rec max skel))
   (<= 0 (size-rec max skel))))

(defthm rmax-bound-rewrite
  (implies
   (and 
    (<= (size-rec max1 skel) rmax)
    (< (+ index (max-offset size)) (nfix max1)))
   (< (+ index (max-offset size)) rmax))
  :hints (("goal" :induct (size-rec max1 skel))))

(defthm size-rec-relation
  (implies
   (and
    (< rmax (size-rec max0 skel))
    (<= (size-rec max1 skel) rmax)
    (< (nfix max0) (nfix max1)))
   nil)
  :rule-classes (:forward-chaining))

(defthm size-rec-skel-prop
  (implies
   (wf-skel skel)
   (and
    (implies
     (< n (nfix max))
     (< n (size-rec max skel)))
    (implies
     (<= n (nfix max))
     (<= n (size-rec max skel)))))
  :hints (("goal" :induct (size-rec max skel))))


(defthm size-rec-relativity
  (implies
   (<= (nfix n1) (nfix n2))
   (<= (size-rec n1 skel) (size-rec n2 skel))))

;;
;; size
;;

(defun size (skel)
  (declare (type (satisfies weak-skel) skel))
  (size-rec 0 skel))

(defthm non-negative-integerp-size
  (non-negative-integerp (size skel)))

;;
;;
;; x* is a RAM _independent_ skeleton extraction function. I'm not
;; exactly sure how we would use this one .. perhaps if we had a
;; structure that was difficult to describe using g*, we would hand x*
;; a skeleton constructed in some other way.  Of course, this would
;; lead to problems when the constructor function was composed over
;; other functions that used g* .. hmm.
;;
;; Actually, I think we want to use x* in the following manner ..
;; 
;; (x* ptr (g* ptr dtype ram) (fn ram))
;; 
;; x* allows us to extract the functionality of fn as it applies to
;; the original structure (g* ..).
;;

(defun x* (skel ram)
  (declare (type (satisfies weak-skel) skel)
           (xargs :measure (acl2-count skel)
                  :guard-hints (("goal" :expand (wf-skel skel)))))
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((akey (car entry))       ; abstract key
              (base (cadr entry))
              (indx (caddr entry))      ; index
              (size (cadddr entry))     ; size
              ;(ptr  (caddddr entry))   ; pointer
              (type (cadddddr entry)))  ; type
          (let ((valu (rx size (+ indx base) ram)))
            (let ((type (x* type ram)))
              (cons `(,akey ,base ,indx ,size ,valu ,type)
                    (x* (cdr skel) ram))))))
    nil))

(defthm open-x*
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (x* skel ram)
           (let ((entry (car skel)))
             (let ((akey (car entry))       ; abstract key
                   (base (cadr entry))
                   (indx (caddr entry))      ; index
                   (size (cadddr entry))     ; size
                   (type (cadddddr entry)))  ; type
               (let ((valu (rx size (+ indx base) ram)))
                 (let ((type (x* type ram)))
                   (cons `(,akey ,base ,indx ,size ,valu ,type)
                         (x* (cdr skel) ram))))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (x* skel ram) nil))))

(defthm size-rec-x*
  (equal (size-rec min (x* skel ram))
         (size-rec min skel)))

(defthm size-x*
  (equal (size (x* skel ram))
         (size skel))
  :hints (("goal" :in-theory (enable size))))

(defthm blks-x*-reduction
  (equal (blks (x* rskel ram))
         (blks rskel)))

(defthm base-x*
  (implies
   (consp skel)
   (equal (cadar (x* skel ram))
          (cadar skel))))

(defthm uniform-base-x*
  (implies
   (uniform-base skel)
   (uniform-base (x* skel ram)))
  :hints (("goal" :induct (uniform-base skel))))

(defthm wf-skel-x*
  (implies
   (wf-skel skel)
   (wf-skel (x* skel ram))))

(defun relocate-block (rptr rskel)
  (declare (type (satisfies weak-skel) rskel))
  (if (consp rskel)
      (let ((entry (car rskel)))
        (let ((akey (car entry))        ; abstract key
              (indx (caddr entry))      ; index
              (size (cadddr entry))     ; size
              (valu (caddddr entry))    ; pointer/value
              (type (cadddddr entry)))  ; type
          (cons `(,akey ,rptr ,indx ,size ,valu ,type)
                (relocate-block rptr (cdr rskel)))))
    nil))

(defthm base-relocate-block
  (implies
   (consp rskel)
   (equal (cadar (relocate-block rptr rskel))
          rptr)))

(defthm consp-relocate-block
  (implies
   (consp (relocate-block rptr rskel))
   (consp rskel))
  :rule-classes (:forward-chaining))

(defthm uniform-base-relocate-block
  (uniform-base (relocate-block rptr rskel)))

;;
;;
;; g* is a RAM dependent skeleton extraction function
;;
;;

(defun g* (base skel ram)
  (declare (type (satisfies weak-skel) skel)
           (type (satisfies integerp) base)
           (xargs :measure (acl2-count skel)
                  :guard-hints (("goal" :expand (wf-skel skel)))))
  (let ((base (ifix base)))
    (if (and (consp skel) (not (zerop base)))
        (let ((entry (car skel)))
          (let ((akey (car entry))       ; abstract key
                (indx (caddr entry))      ; index
                (size (cadddr entry))     ; size
                ;(ptr  (caddddr entry))   ; pointer
                (type (cadddddr entry)))   ; type
            (let ((valu (rx size (+ indx base) ram)))
              (let ((type (g* valu type ram)))
                (cons `(,akey ,base ,indx ,size ,valu ,type)
                      (g* base (cdr skel) ram))))))
      nil)))

#|   now takes 3 args...
(defun g*-list (skel ram)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (let ((akey (car entry))       ; abstract key
              (base (cadr entry))
              (indx (caddr entry))      ; index
              (size (cadddr entry))     ; size
              ;(ptr  (caddddr entry))   ; pointer
              (type (cadddddr entry)))  ; type
          (let ((valu (rx size (+ indx base) ram)))
            (let ((type (g* valu type ram)))
              (cons `(,akey ,base ,indx ,size ,valu ,type)
                    (g*-list (cdr skel) ram))))))
    nil))
|#

(defthm open-g*
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (g* base skel ram)
           (let ((base (ifix base)))
             (if (zerop base) nil
               (let ((entry (car skel)))
                 (let ((akey (car entry))       ; abstract key
                       (indx (caddr entry))      ; index
                       (size (cadddr entry))     ; size
                       (type (cadddddr entry)))   ; type
                   (let ((valu (rx size (+ indx base) ram)))
                     (let ((type (g* valu type ram)))
                       (cons `(,akey ,base ,indx ,size ,valu ,type)
                             (g* base (cdr skel) ram))))))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (g* base skel ram) nil))
   (implies
    (and
     (syntaxp (syntax-atom base))
     (zerop base))
    (equal (g* base skel ram) nil))))

(defthm size-rec-g*-casesplit
  (equal (size-rec min (g* base skel ram))
         (if (zerop (ifix base)) (nfix min)
           (size-rec min skel))))

(defthm size-g*-casesplit
  (equal (size (g* base skel ram))
         (if (zerop (ifix base)) 0 (size skel)))
  :hints (("goal" :in-theory (enable size))))


(defthm blks-g*-reduction-casesplit
  (equal (blks (g* rptr rskel ram))
         (if (zerop (ifix rptr)) nil (blks (relocate-block rptr rskel)))))

(defthm base-g*
  (implies
   (and
    (consp rskel)
    (not (zerop (ifix rptr))))
   (equal (cadar (g* rptr rskel ram))
          (ifix rptr))))

(defthm consp-g*-forward
  (implies
   (consp (g* ptr skel ram))
   (and
    (not (zerop (ifix ptr)))
    (consp skel)))
  :rule-classes (:forward-chaining))

(defthm uniform-base-g*
  (uniform-base (g* rptr rskel ram)))

;;
;;
;; A little ground work on blks ..
;;
;;

(defun blks-ptr (ptr skel)
  (declare (type (satisfies weak-skel) skel)
           (type integer ptr))
  (if (consp skel)
      (let ((entry (car skel)))
        (let (;(ptr   (cadr entry))
              (index (caddr entry))
              (size  (cadddr entry)))
          (let ((blk (blk (+ (ifix ptr) index) (1+ (max-offset size)))))
            (append blk (blks-ptr ptr (cdr skel))))))
    nil))

(defthm uniform-base-blks-transformation
  (implies
   (uniform-base skel)
   (equal (blks skel)
          (blks-ptr (cadar skel) skel))))

;These next three just not true unless we're dealing with integers
(defthm disjoint-blk-ptr-blks-ptr-independent-of-ptr
  (implies
   (and
    (disjoint (blks-ptr ptr1 skel)
              (blk (+ ptr1 x) size))
    (wf-skel skel)
    (integerp ptr1)
    (integerp ptr2)
    (integerp x)
    )
   (disjoint (blks-ptr ptr2 skel)
             (blk (+ ptr2 x) size)))
  :hints (("goal" :in-theory (enable RELOCATE-BLK-OFFSET
                                     BAG::DISJOINT-APPEND-REDUCTION
                                     ))))

(defthm disjoint-blk-ptr-blks-ptr-independent-of-ptr-0-conclusion
  (implies
   (and
    (disjoint (blks-ptr ptr1 skel)
              (blk (+ ptr1 x) size))
    (wf-skel skel)
    (integerp ptr1)
    (integerp x)
    )
   (disjoint (blks-ptr 0 skel)
             (blk x size)))
  :hints (("Goal" :use (:instance  disjoint-blk-ptr-blks-ptr-independent-of-ptr (ptr2 0))
           :in-theory (disable  disjoint-blk-ptr-blks-ptr-independent-of-ptr))))

(defthm disjoint-blk-ptr-blks-ptr-independent-of-ptr-0-hyp
  (implies
   (and
    (disjoint (blks-ptr 0 skel)
              (blk x size))
    (wf-skel skel)
    (integerp ptr2)
    (integerp x)
    )
   (disjoint (blks-ptr ptr2 skel)
             (blk (+ ptr2 x) size)))
  :hints (("Goal" :use (:instance  disjoint-blk-ptr-blks-ptr-independent-of-ptr (ptr1 0))
           :in-theory (disable  disjoint-blk-ptr-blks-ptr-independent-of-ptr))))

(defthm blks-ptr-reduction
  (implies
   (not (integerp ptr1))
   (equal (blks-ptr ptr1 skel)
          (blks-ptr 0 skel))))

;; Perhaps this should be changed so that we know more about
;; relocate-blk (rather than leaving relocate-blk-offset off)

(defthm unique-blks-ptr-independent-of-ptr
  (implies
   (and
    (unique (blks-ptr ptr1 skel))
    (wf-skel skel))
   (unique (blks-ptr ptr2 skel)))
  :hints (("goal" :in-theory (enable bag::unique-of-append)  ;bzo
           :induct (blks-ptr ptr2 skel))))

(defthm blks-ptr-g*-reduction-casesplit
  (equal (blks-ptr addr (g* rptr rskel ram))
         (if (zerop (ifix rptr)) nil (blks-ptr addr rskel))))

(defthm integerp-cadar-g*
  (implies
   (consp (g* rptr skel ram))
   (integerp (cadar (g* rptr skel ram)))))

(defthm wf-skel-g*
  (implies
   (wf-skel skel)
   (wf-skel (g* ptr skel ram))))

;;
;;
;; s* takes a fleshed out skeleton and applies it to a memory.
;;
;;

(defun s* (skel ram)
  (declare (type (satisfies weak-skel) skel))
  (if (consp skel)
      (let ((entry (car skel)))
        (let (;(akey (car entry))        ; abstract key
              (base (cadr entry))         ; base address
              (indx (caddr entry))       ; index
              (size (cadddr entry))      ; size
              (valu (caddddr entry))     ; value
              (type (cadddddr entry)))   ; type
          (let ((ram (s* type ram)))
            (let ((ram (s* (cdr skel) ram)))
              (wx size (+ indx base) valu ram)))))
    ram))

(defthm open-s*
  (and
   (implies
    (and
     (syntaxp (syntax-consp-or-symbol skel))
     (consp skel))
    (equal (s* skel ram)
           (let ((entry (car skel)))
             (let (;(akey (car entry))        ; abstract key
                   (base (cadr entry))         ; base address
                   (indx (caddr entry))       ; index
                   (size (cadddr entry))      ; size
                   (valu (caddddr entry))     ; value
                   (type (cadddddr entry)))   ; type
               (let ((ram (s* type ram)))
                 (let ((ram (s* (cdr skel) ram)))
                   (wx size (+ indx base) valu ram)))))))
   (implies
    (and
     (syntaxp (syntax-atom skel))
     (not (consp skel)))
    (equal (s* skel ram) ram)))
  :hints (("goal" :in-theory '(s*))))

(defmacro spec-equal (s d)
  `(let ((s ,s)
         (d ,d))
     (and (equal (car s) (car d))          ; key
          ;(equal (cadr s) (cadr d))       ; base
            (equal (caddr s) (caddr d))      ; index
          (equal (cadddr s) (cadddr d))))) ; size

(set-well-founded-relation e0-ord-<)
(defun g*-instance (rptr rskel wskel)
  (declare (type integer rptr)
           (type (satisfies weak-skel) rskel wskel)
           (xargs :measure (cons (1+ (acl2-count rskel)) (acl2-count wskel))))
  (if (and (consp rskel) (not (zerop (ifix rptr))))
      (if (consp wskel)
          (let ((rentry (car rskel))
                (wentry (car wskel)))
            (let ((wbase (cadr wentry))
                  (wvalu (caddddr wentry))
                  (wtype (cadddddr wentry))
                  (rtype (cadddddr rentry)))
              (if (spec-equal rentry wentry)
                  (if (equal (ifix rptr) wbase)
                      (and (g*-instance (ifix rptr) (cdr rskel) (cdr wskel))
                           (g*-instance wvalu rtype wtype))
                    nil)
                nil)))
        nil)
    t))

(defthm g*-instance-g*
  (implies
   (wf-skel rskel)
   (g*-instance rptr rskel (g* rptr rskel ram)))
  :hints (("goal" :induct (g* rptr rskel ram))))

(defun g*-fix (rptr rskel wskel)
  (declare (type integer rptr)
           (type (satisfies weak-skel) rskel wskel)
           (xargs :measure (cons (1+ (acl2-count rskel)) (acl2-count wskel))))
  (if (and (consp rskel) (not (zerop (ifix rptr))))
      (if (consp wskel)
          (let ((rentry (car rskel))
                (wentry (car wskel)))
            (if (spec-equal rentry wentry)
                (let ((akey (car wentry))       ; abstract key
                      (base (cadr wentry))      ; base
                      (indx (caddr wentry))     ; index
                      (size (cadddr wentry))    ; size
                      (ptr  (caddddr wentry))   ; pointer
                      (wtype (cadddddr wentry)) ; type
                      (rtype (cadddddr rentry)))
                  (let ((type (g*-fix ptr rtype wtype)))
                    (cons `(,akey ,base ,indx ,size ,ptr ,type)
                          (g*-fix (ifix rptr) (cdr rskel) (cdr wskel)))))
              (g*-fix (ifix rptr) rskel (cdr wskel))))
        nil)
    nil))

(defthm g*-fix-g*
  (implies
   (wf-skel rskel)
   (equal (g*-fix rptr rskel (g* rptr rskel ram))
          (g* rptr rskel ram))))


(defun x*-instance (rskel wskel)
  (declare (type (satisfies weak-skel) rskel wskel)
           (xargs :measure (cons (1+ (acl2-count rskel)) (acl2-count wskel))))
  (if (consp rskel)
      (if (consp wskel)
          (let ((rentry (car rskel))
                (wentry (car wskel)))
            (let ((wbase (cadr wentry))
                  (rbase (cadr rentry))
                  (wtype (cadddddr wentry))
                  (rtype (cadddddr rentry)))
              (if (spec-equal rentry wentry)
                  (if (equal rbase wbase)
                      (and (x*-instance (cdr rskel) (cdr wskel))
                           (x*-instance rtype wtype))
                    nil)
                nil)))
        nil)
    t))


(defthm x*-instance-x*
  (implies
   (wf-skel rskel)
   (x*-instance rskel (x* rskel ram))))

(defun x*-fix (rskel wskel)
  (declare (type (satisfies weak-skel) rskel wskel)
           (xargs :measure (cons (1+ (acl2-count rskel)) (acl2-count wskel))))
  (if (consp rskel)
      (if (consp wskel)
          (let ((rentry (car rskel))
                (wentry (car wskel)))
            (if (spec-equal rentry wentry)
                (let ((akey (car wentry))       ; abstract key
                      (base (cadr wentry))     ; base
                      (indx (caddr wentry))     ; index
                      (size (cadddr wentry))    ; size
                      (ptr  (caddddr wentry))   ; pointer
                      (wtype (cadddddr wentry)) ; type
                      (rtype (cadddddr rentry)))
                  (let ((type (x*-fix rtype wtype)))
                    (cons `(,akey ,base ,indx ,size ,ptr ,type)
                          (x*-fix (cdr rskel) (cdr wskel)))))
              (x*-fix rskel (cdr wskel))))
        nil)
    nil))


(defthm x*-fix-x*
  (implies
   (wf-skel rskel)
   (equal (x*-fix rskel (x* rskel ram))
          (x* rskel ram))))

;;
;; rx/wx - x*/g*/s* rules
;;

(in-theory (disable DEFAULT-*-2 DEFAULT-*-1 
                    ACL2::INTEGERP-+-MINUS-* 
                    ACL2::INTEGERP-*-CONSTANT-MEANS-1 
;                    ACL2::TOP-BIT-MEANS-<
                    ACL2::INTEGERP-+-MINUS-*
                    ;DISJOINT-BLK-FREE-BACKCHAINING-1
                    ;DISJOINT-BLK-FREE-BACKCHAINING-2
                    ;DISJOINT-BLK-FREE-BACKCHAINING-2A
                    ;DISJOINT-BLK-FREE-BACKCHAINING-1A
                    ))

(in-theory (disable UNIFORM-BASE-BLKS-TRANSFORMATION))

(defthm s*-over-wx-mesh
  (implies
   (and
    (syntaxp (not (syntax-consp-or-quote rskel)))
    (disjoint (flatten rskel) (blk wptr (1+ (max-offset wsize))))
    (wf-skel rskel)
    )
  (equal (s* rskel (wx wsize wptr v ram))
         (wx wsize wptr v (s* rskel ram))))
  :hints (("goal" :in-theory (e/d (sblk) (fix ifix))
           :expand ((BLKS RSKEL)
                    (MESH RSKEL))
           :induct (s* rskel ram))))


(encapsulate
 ()

(local
  (defthm g*-over-wx-mesh-induction
    (implies
     (and
      (disjoint (flatten (g* rptr rskel ram))
                (blk wptr (1+ (max-offset wsize))))
      (wf-skel rskel)
      )
     (equal (g* rptr rskel (wx wsize wptr value ram))
            (g* rptr rskel ram)))
    :hints (("goal" :in-theory (e/d (sblk
                                     ) (
;disables for efficiency:
                                     fix
                                     ifix
                                     BAG::DISJOINT-APPEND-REDUCTION
                                     anything
                                     wf-skel))
             :induct (g* rptr rskel ram)))))


 (defthm g*-over-wx-mesh
   (implies
    (and
     (syntaxp (not (syntax-consp-or-quote rskel)))
     (equal v (g* rptr rskel ram)) ;; make it simplify this first ..
     (disjoint (flatten v) 
               (blk wptr (1+ (max-offset wsize))))
     (wf-skel rskel)
     )
    (equal (g* rptr rskel (wx wsize wptr value ram))
           v))))


(defthm x*-over-wx-mesh
  (implies
   (and
    (syntaxp (not (syntax-consp-or-quote rskel)))
    (disjoint (flatten rskel)
              (blk wptr (1+ (max-offset wsize))))
    (wf-skel rskel)
    )
   (equal (x* rskel (wx wsize wptr value ram))
          (x* rskel ram)))
  :hints (("goal" :in-theory (e/d (sblk) (WF-SKEL
                                          ;OPEN-WF-SKEL
                                          ;efficiency:
                                          BAG::DISJOINT-APPEND-REDUCTION
                                          ))

;efficiency:
           :expand  ((MESH RSKEL)
                     (BLKS RSKEL))
           :induct (x* rskel ram)))
  ) ; :rule-classes ((:rewrite :match-free :once)))

(defthm rx-over-s*-mesh
  (implies
   (and
    (disjoint (flatten wskel) 
              (blk rptr (1+ (max-offset rsize))))
    (wf-skel wskel)
    )
   (equal (rx rsize rptr (s* wskel ram))
          (rx rsize rptr ram)))
  :hints (("goal" :in-theory (enable sblk)
           :induct (s* wskel ram)))
  ) ; :rule-classes ((:rewrite :match-free :once)))

;;
;; x*/g*/s* rules
;;

;; (defthm flatten-of-cons
;;   (equal (flatten (cons a skel))
;;          (APPEND (BLKS (cons a SKEL)) (MESH (cons a SKEL)))))

(in-theory (disable mesh blks)) ;trying, now that we have blks-of-cons and mesh-of-cons...


(local (in-theory (disable BINARY-APPEND))) ;bzo why is append on?

(encapsulate
 ()

 (local
  (defthm g*-over-s*-mesh-induction
    (implies
     (and
      (disjoint (flatten (g* rptr rskel ram))
                (flatten wskel))
      (wf-skel rskel)
      (wf-skel wskel)
      )
     (equal (g* rptr rskel (s* wskel ram)) (g* rptr rskel ram)))

    :hints (("goal" :do-not '(generalize eliminate-destructors)
             :in-theory (e/d (bag::disjoint-of-append-one ;yuck
                              bag::disjoint-of-append-two
                              ) 
                             ( ;for efficiency:
                              wf-skel
                              mesh
                              blks
                              OPEN-BLKS
                              OPEN-MESH
                              fix
                              ifix))
             :induct (g* rptr rskel ram)))))

 (defthm g*-over-s*-mesh
   (implies
    (and
     (syntaxp (not (syntax-consp-or-quote rskel)))
     (equal v (g* rptr rskel ram)) ;; make it simplify this first ..
     (disjoint (flatten v)
               (flatten wskel))
     (wf-skel rskel)
     (wf-skel wskel)
     )
    (equal (g* rptr rskel (s* wskel ram)) v))))

(defthm x*-over-s*-mesh
  (implies
   (and
    (syntaxp (not (syntax-consp-or-quote rskel)))
    (disjoint (flatten rskel)
              (flatten wskel))
    (wf-skel rskel)
    (wf-skel wskel)
    )
   (equal (x* rskel (s* wskel ram))
          (x* rskel ram)))
  :hints (("goal" :in-theory (enable mesh)
           :induct (s* wskel ram))))

(defthm s*-over-s*
  (implies
   (and
    (syntaxp (not (syntax-consp-or-quote skel1)))
    (disjoint (flatten skel1)
              (flatten skel2))
    (wf-skel skel1)
    (wf-skel skel2)
    )
   (equal (s* skel1 (s* skel2 ram))
          (s* skel2 (s* skel1 ram))))
  :hints (("goal" :in-theory (enable mesh)
           :induct (s* skel2 ram)))
  :rule-classes ((:rewrite :loop-stopper ((skel2 skel1 s*)))))

(defthm g*-over-s*-s*
  (implies
   (and
    (and
     (disjoint (flatten skel1)
               (flatten skel2))
     (equal v (g* rptr rskel (s* skel1 ram)))
     (disjoint (flatten skel2)
               (flatten v))
     (wf-skel rskel)
     (wf-skel skel1)
     (wf-skel skel2)
     )
    )
   (equal (g* rptr rskel (s* skel1 (s* skel2 ram))) v)))



;; (defthm x*-x*
;;   (implies
;;    (equal ram1 ram2)
;;    (equal (x* (x* skel ram1) ram2)
;;           (x* skel ram2))))

;; (defthm x*-g*
;;   (implies
;;    (equal ram1 ram2)
;;    (equal (x* (g* ptr skel ram1) ram2)
;;           (g* ptr skel ram2))))


(defthm x*-x*
  (equal (x* (x* skel ram) ram)
         (x* skel ram)))

(defthm x*-g*
  (equal (x* (g* ptr skel ram) ram)
         (g* ptr skel ram)))

(defun s*-instance (skel ram)
  (declare (type t skel ram))
  (if (and (consp ram)
           (equal (car ram) 's*) ; (s* skel ram)
           (consp (cdr ram))
           (consp (cddr ram)))
      (if (equal skel (cadr ram))
          t
        (s*-instance skel (caddr ram)))
    nil))

;; #+joe
;; (defthm ram==s*
;;   (implies
;;    (and
;;     (syntaxp (not (s*-instance skel ram2)))
;;     (equal skel (x* skel ram2))
;;     (equal ram1 ram2)
;;     )
;;    (and (equal (equal (s* skel ram1) ram2)
;;                t)
;; ;        (equal (equal ram2 (s* skel ram1))
;;  ;              t)
;;         )))

;bzo an odd lemma. try disabled?
(defthm s*==s*
  (implies
   (and
    (equal skel1 skel2)
    (equal ram1 ram2)
    )
   (equal (equal (s* skel1 ram1) (s* skel2 ram2))
          t)))

(defthm disjoint-blks-from-x*-instance
  (implies
   (and
    (x*-instance a b)
    (disjoint (blks b) c))
   (disjoint (blks a) c))
  :hints (("Goal" :in-theory (enable BAG::DISJOINT-APPEND-REDUCTION))))

;nested inductions
(defthm disjoint-mesh-from-x*-instance
  (implies (and (x*-instance a b)
                (disjoint (mesh b) c))
           (disjoint (mesh a) c))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bag::disjoint-of-append-one ;yuck
                              mesh
                              blks
                              bag::disjoint-of-append-two) 
                           (ifix)))))

(defthm subbagp-blks-g*-fix-lemma
  (subbagp (BLKS (G*-FIX PTR C2 a))
           (BLKS a)))
     
(defthm disjoint-blks-g*-fix
  (implies (disjoint (blks a) b)
           (disjoint (blks (g*-fix ptr c a)) b))
  :hints (("Goal" :in-theory (e/d (BAG::SUBBAGP-DISJOINT) (g*-fix)))))

(defthm disjoint-g*-blks-g*-fix-2
  (implies (disjoint b (blks a))
           (disjoint b (blks (g*-fix ptr c a))))
  :hints (("Goal" :in-theory (e/d (BAG::SUBBAGP-DISJOINT) (g*-fix)))))

;; The world would be a lot better place if we could enable this rule
;; always ..

(local (in-theory (disable LIST::DISJOINT-BY-MULTIPLICITY)))

(defthm disjoint-mesh-g*-fix
  (implies
   (disjoint (mesh b) c)
   (disjoint (mesh (g*-fix ptr a b)) c))
;  :hints (("Goal" :in-theory (e/d (BAG::SUBBAGP-DISJOINT) (g*-fix))))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (enable bag::disjoint-of-append-one ;yuck
                              bag::disjoint-of-append-two))))

(defthm mesh-x*-g*
  (implies
   (wf-skel skel)
   (equal (mesh (x* (g* ptr skel ram1) ram2))
          (mesh (g* ptr skel ram1)))))

;; #+joe
;; (defthm s*-of-g*
;;   (equal (s* (g* ptr skel ram) ram)
;;          ram))

(defthm x*-fix-g*
  (equal (x*-fix (g* ptr skel ram)
                 (g* ptr skel ram))
         (g* ptr skel ram)))

(defthm x*-instance-g*
  (x*-instance (g* ptr skel ram)
               (g* ptr skel ram)))


(in-theory (disable 
            G*-OVER-S*-S*
            BLKS-G*-REDUCTION-CASESPLIT
            ))


;; ;bzo
;; #+joe
;; (defthm x*-of-s*
;;   (implies
;;    (and
;;     (syntaxp (not (syntax-consp-or-quote rskel)))
;;     (unique (flatten wskel))
;;     (x*-instance rskel wskel)
;;     (wf-skel rskel)
;;     (wf-skel wskel)
;;     )
;;    (equal (x* rskel (s* wskel ram))
;;           (x*-fix rskel wskel)))
;;   :hints (("goal" :in-theory '((:DEFINITION ANYTHING)
;;         (:DEFINITION BLKS)
;;         (:DEFINITION FIX)
;;         (:DEFINITION FLATTEN)
;;         (:DEFINITION IFIX)
;;         (:DEFINITION NOT)
;;         (:DEFINITION NULL)
;;         (:DEFINITION POSITIVE-INTEGERP)
;;         (:DEFINITION SYNP)
;;         (:DEFINITION WF-SKEL)
;;         (:DEFINITION WINTN)
;;         (:DEFINITION X*-FIX)
;;         (:DEFINITION X*-INSTANCE)
;;         (:ELIM CAR-CDR-ELIM)
;;         (:EXECUTABLE-COUNTERPART BLKS)
;;         (:EXECUTABLE-COUNTERPART CONSP)
;;         (:EXECUTABLE-COUNTERPART DISJOINT)
;;         (:EXECUTABLE-COUNTERPART EQUAL)
;;         (:EXECUTABLE-COUNTERPART MESH)
;;         (:EXECUTABLE-COUNTERPART SYNP)
;;         (:EXECUTABLE-COUNTERPART UNIQUE)
;;         (:EXECUTABLE-COUNTERPART X*-FIX)
;;         (:EXECUTABLE-COUNTERPART X*-INSTANCE)
;;         (:INDUCTION X*-FIX)
;;         (:FORWARD-CHAINING NON-NEGATIVE-INTEGERP-IMPLIES)
;;         (:FORWARD-CHAINING WEAK-SKEL-IMPLIES-TRUE-LISTP)
;;         (:FORWARD-CHAINING WF-SKEL-IMPLIES-WEAK-SKEL)
;;         (:REWRITE CAR-CONS)
;;         (:REWRITE CDR-CONS)
;;         (:REWRITE COMMUTATIVITY-OF-+)
;;         (:REWRITE DISJOINT-BLKS-FROM-X*-INSTANCE)
;;         (:REWRITE DISJOINT-COMMUTATIVE)
;;         (:REWRITE DISJOINT-of-APPEND-one)
;;         (:REWRITE DISJOINT-of-APPEND-two)
;;         (:REWRITE DISJOINT-MESH-FROM-X*-INSTANCE)
;;         (:REWRITE EQUAL-TRUE-LIST-CASES)
;;         (:REWRITE IMPLIES-NON-NEGATIVE-INTEGERP)
;;         (:REWRITE IMPLIES-POSITIVE-INTEGERP)
;;         (:REWRITE OPEN-BLKS)
;;         (:REWRITE OPEN-MESH)
;;         (:REWRITE OPEN-S*)
;;         (:REWRITE OPEN-WF-SKEL)
;;         (:REWRITE OPEN-X*)
;;         (:REWRITE REMOVE-LIST-UNIT)
;;         (:REWRITE RX-OF-WX)
;;         (:REWRITE S*-OVER-S*)
;;         (:REWRITE UNICITY-OF-0)
;;         (:REWRITE UNIQUE-of-APPEND)
;;         (:REWRITE UNIQUE-BLK)
;;         (:REWRITE X*-OVER-S*-MESH)
;;         (:REWRITE X*-OVER-WX-MESH)
;;         (:TYPE-PRESCRIPTION DISJOINT)
;;         (:TYPE-PRESCRIPTION NON-NEGATIVE-INTEGERP)
;;         (:TYPE-PRESCRIPTION UNIQUE)
;;         (:TYPE-PRESCRIPTION WEAK-SKEL)
;;         (:TYPE-PRESCRIPTION WF-SKEL)
;;         (:TYPE-PRESCRIPTION WFIXN)
;;         (:TYPE-PRESCRIPTION X*-FIX)
;;         (:TYPE-PRESCRIPTION X*-INSTANCE)))))

;; #+joe
;; (defthm g*-of-s*
;;   (implies
;;    (and
;;     (syntaxp (not (syntax-consp-or-quote rskel)))
;;     (unique (flatten wskel))
;;     (g*-instance ptr rskel wskel)
;;     (wf-skel wskel)
;;     (wf-skel rskel)
;;     )
;;    (equal (g* ptr rskel (s* wskel ram))
;;           (g*-fix ptr rskel wskel)))
;;   :hints (("goal" :in-theory '((:DEFINITION ANYTHING)
;;         (:DEFINITION BLKS)
;;         (:DEFINITION FIX)
;;         (:DEFINITION FLATTEN)
;;         (:DEFINITION G*)
;;         (:DEFINITION G*-FIX)
;;         (:DEFINITION G*-INSTANCE)
;;         (:DEFINITION IFIX)
;;         (:DEFINITION NOT)
;;         (:DEFINITION NULL)
;;         (:DEFINITION POSITIVE-INTEGERP)
;;         (:DEFINITION SYNP)
;;         (:DEFINITION WF-SKEL)
;;         (:DEFINITION WINTN)
;;         (:DEFINITION ZEROP)
;;         (:ELIM CAR-CDR-ELIM)
;;         (:EXECUTABLE-COUNTERPART BLKS)
;;         (:EXECUTABLE-COUNTERPART CONSP)
;;         (:EXECUTABLE-COUNTERPART DISJOINT)
;;         (:EXECUTABLE-COUNTERPART EQUAL)
;;         (:EXECUTABLE-COUNTERPART FLATTEN)
;;         (:EXECUTABLE-COUNTERPART IFIX)
;;         (:EXECUTABLE-COUNTERPART MESH)
;;         (:EXECUTABLE-COUNTERPART SYNP)
;;         (:EXECUTABLE-COUNTERPART UNIQUE)
;;         (:FORWARD-CHAINING NON-NEGATIVE-INTEGERP-IMPLIES)
;;         (:FORWARD-CHAINING WEAK-SKEL-IMPLIES-TRUE-LISTP)
;;         (:FORWARD-CHAINING WF-SKEL-IMPLIES-WEAK-SKEL)
;;         (:INDUCTION G*-FIX)
;;         (:REWRITE CAR-CONS)
;;         (:REWRITE CDR-CONS)
;;         (:REWRITE COMMUTATIVITY-OF-+)
;;         (:REWRITE DISJOINT-BLKS-G*-FIX)
;;         (:REWRITE DISJOINT-COMMUTATIVE)
;;         (:REWRITE DISJOINT-of-APPEND-one)
;;         (:REWRITE DISJOINT-of-APPEND-two)
;;         (:REWRITE DISJOINT-MESH-G*-FIX)
;;         (:REWRITE DISJOINT-NIL)
;;         (:REWRITE EQUAL-TRUE-LIST-CASES)
;;         (:REWRITE G*-OVER-S*-MESH)
;;         (:REWRITE G*-OVER-S*-S*)
;;         (:REWRITE G*-OVER-WX-MESH)
;;         (:REWRITE IMPLIES-NON-NEGATIVE-INTEGERP)
;;         (:REWRITE IMPLIES-POSITIVE-INTEGERP)
;;         (:REWRITE OPEN-BLKS)
;;         (:REWRITE OPEN-G*)
;;         (:REWRITE OPEN-MESH)
;;         (:REWRITE OPEN-S*)
;;         (:REWRITE OPEN-WF-SKEL)
;;         (:REWRITE REMOVE-LIST-UNIT)
;;         (:REWRITE RX-OF-WX)
;;         (:REWRITE S*-OVER-S*)
;;         (:REWRITE UNICITY-OF-0)
;;         (:REWRITE UNIQUE-of-APPEND)
;;         (:REWRITE UNIQUE-BLK)
;;         (:TYPE-PRESCRIPTION DISJOINT)
;;         (:TYPE-PRESCRIPTION G*-FIX)
;;         (:TYPE-PRESCRIPTION NON-NEGATIVE-INTEGERP)
;;         (:TYPE-PRESCRIPTION UNIQUE)
;;         (:TYPE-PRESCRIPTION WEAK-SKEL)
;;         (:TYPE-PRESCRIPTION WF-SKEL)
;;         (:TYPE-PRESCRIPTION WFIXN)))))
