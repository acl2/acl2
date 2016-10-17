(in-package "PROOF-CHECKER-ARRAY")

(include-book "farray")

(include-book "supplemental/sb60")
(include-book "supplemental/literal")
; (include-book "supplemental/clause")


;; ===================================================================



(defconst *s* 0)

(defconst *num-vars* 1)
(defconst *stack-end* 2)
(defconst *stack* 3)
(defconst *lookup* 4)



;; ===================================================================

;; (defun stack-memberp (e i st)
;;   (declare (xargs :guard (and (farrayp *s* st)
;;                               (fieldp *stack* *s* st)
;;                               (or (field-offsetp i *stack* *s* st)
;;                                   (equal i -1))
;;                               (literalp e))
;;                   :stobjs (st)))
;;   (field-memberp e i 0 *stack* *s* st))


(defun stack-contains-literalsp (i st)
  (declare (xargs :guard (and (farrayp *s* st)
                              (fieldp *stack* *s* st)
                              (or (field-offsetp i *stack* *s* st)
                                  (equal i -1)))
                  :stobjs (st)
                  :measure (nfix (1+ i))))
  (if (not (mbt (and (farrayp *s* st)
                     (fieldp *stack* *s* st)
                     (or (field-offsetp i *stack* *s* st)
                         (equal i -1)))))
      nil
    (if (equal i -1)
        t
      (and (literalp (fread *stack* i *s* st))
           (stack-contains-literalsp (1- i) st)))))

;; (defthm literalp-fread-*stack*
;;   (implies (and (stack-contains-literalsp j st)
;;                 (field-offsetp i *stack* *s* st)
;;                 (<= i j))
;;            (literalp (fread *stack* i *s* st))))


;; (defthm literalp-fread-*stack*
;;   (implies (and (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
;;                 (field-offsetp i *stack* *s* st)
;;                 (<= i (1- (fread *stack-end* 0 *s* st))))
;;            (literalp (fread *stack* i *s* st))))


(defun stack-uniquep (i st)
  (declare (xargs :guard (and (farrayp *s* st)
                              (fieldp *stack* *s* st)
                              (or (field-offsetp i *stack* *s* st)
                                  (equal i -1))
                              ;; (stack-contains-literalsp i st)
                              )
                  :stobjs (st)
                  :measure (nfix (1+ i))))
  (if (not (mbt (and (farrayp *s* st)
                     (fieldp *stack* *s* st)
                     (or (field-offsetp i *stack* *s* st)
                         (equal i -1))
                     ;; (stack-contains-literalsp i st)
                     )))
      nil
    (if (equal i -1)
        t
      (and (not (field-memberp (fread *stack* i *s* st)
                               (1- i) 0 *stack* *s* st))
           (stack-uniquep (1- i) st)))))


;; (defthm not-field-memberp-fread-*stack*
;;   (implies (and (stack-uniquep j st)
;;                 (field-offsetp i *stack* *s* st)
;;                 (<= i j))
;;            (not (field-memberp (fread *stack* i *s* st)
;;                                (1- i) 0 *stack* *s* st))))


(defun stack-not-conflictingp (i st)
  (declare (xargs :guard (and (farrayp *s* st)
                              (fieldp *stack* *s* st)
                              (or (field-offsetp i *stack* *s* st)
                                  (equal i -1))
                              (stack-contains-literalsp i st))
                  :stobjs (st)
                  :measure (nfix (1+ i))))
  (if (not (mbt (and (farrayp *s* st)
                     (fieldp *stack* *s* st)
                     (or (field-offsetp i *stack* *s* st)
                         (equal i -1))
                     (stack-contains-literalsp i st))))
      nil
    (if (equal i -1)
        t
      (and (not (field-memberp (negate (fread *stack* i *s* st))
                               (1- i) 0 *stack* *s* st))
           (stack-not-conflictingp (1- i) st)))))

;; (defthm not-field-memberp-negate-fread-*stack*
;;   (implies (and (stack-not-conflictingp j st)
;;                 (field-offsetp i *stack* *s* st)
;;                 (<= i j))
;;            (not (field-memberp (negate (fread *stack* i *s* st))
;;                                (1- i) 0 *stack* *s* st))))



(defthm integerp-+-2
  (implies (and (integerp i)
                (integerp j))
           (integerp (+ i j))))

(defthm integerp--
  (implies (integerp i)
           (integerp (- i))))

(defun lookup-corresponds-with-stackp (i st)
  (declare (xargs :guard (and (farrayp *s* st)
                              (fieldp *lookup* *s* st)
                              (fieldp *stack* *s* st)
                              (fieldp *stack-end* *s* st)
                              (or (field-offsetp i *lookup* *s* st)
                                  (equal i (flength *lookup* *s* st)))
                              (< 1 i)
                              (field-offsetp (fread *stack-end* 0 *s* st)
                                             *stack* *s* st))
                  :stobjs (st)
                  :measure (nfix (- (flength *lookup* *s* st) i))))
  (if (not (mbt (and (farrayp *s* st)
                     (fieldp *lookup* *s* st)
                     (fieldp *stack* *s* st)
                     (fieldp *stack-end* *s* st)
                     (or (field-offsetp i *lookup* *s* st)
                         (equal i (flength *lookup* *s* st)))
                     (< 1 i)
                     (field-offsetp (fread *stack-end* 0 *s* st)
                                    *stack* *s* st))))
      nil
    (if (equal i (flength *lookup* *s* st))
        t
      (and (or (not (equal (fread *lookup* i *s* st) 1))
               (field-memberp i
                              (1- (fread *stack-end* 0 *s* st))
                              0 *stack* *s* st))
           (lookup-corresponds-with-stackp (1+ i) st)))))


(defthm equal-fread-lookup-1-implies-field-memberp-*stack*
  (implies (and (lookup-corresponds-with-stackp i st)
                (field-offsetp lit *lookup* *s* st)
                (<= i lit)
                (equal (fread *lookup* lit *s* st) 1))
           (field-memberp lit
                          (1- (fread *stack-end* 0 *s* st))
                          0 *stack* *s* st)))

;; (defthm equal-fread-lookup-1-implies-field-memberp-*stack*-2
;;   (implies (and (lookup-corresponds-with-stackp 2 st)
;;                 (field-offsetp lit *lookup* *s* st)
;;                 (literalp lit)
;;                 (equal (fread *lookup* lit *s* st) 1))
;;            (field-memberp lit
;;                           (1- (fread *stack-end* 0 *s* st))
;;                           0 *stack* *s* st))
;;   :hints (("Goal" :use ((:instance
;;                          equal-fread-lookup-1-implies-field-memberp-*stack*
;;                          (i 2))))))

(in-theory (disable lookup-corresponds-with-stackp))

(defun stack-in-rangep (i st)
  (declare (xargs :guard (and (farrayp *s* st)
                              (fieldp *stack* *s* st)
                              (fieldp *lookup* *s* st)
                              (or (field-offsetp i *stack* *s* st)
                                  (equal i -1)))
                  :stobjs (st)
                  :measure (nfix (1+ i))))
  (if (not (mbt (and (farrayp *s* st)
                     (fieldp *stack* *s* st)
                     (fieldp *lookup* *s* st)
                     (or (field-offsetp i *stack* *s* st)
                         (equal i -1)))))
      nil
    (if (equal i -1)
        t
      (and (field-offsetp (fread *stack* i *s* st) *lookup* *s* st)
           (stack-in-rangep (1- i) st)))))


;; (defthm field-offsetp-fread-*stack*-*lookup*
;;   (implies (and (stack-in-rangep j st)
;;                 (field-offsetp i *stack* *s* st)
;;                 (<= i j))
;;            (field-offsetp (fread *stack* i *s* st) *lookup* *s* st)))


(defun stack-corresponds-with-lookup-p (i st)
  (declare (xargs :guard (and (farrayp *s* st)
                              (fieldp *stack* *s* st)
                              (fieldp *lookup* *s* st)
                              (or (field-offsetp i *stack* *s* st)
                                  (equal i -1))
                              (stack-in-rangep i st))
                  :stobjs (st)
                  :measure (nfix (1+ i))))
  (if (not (mbt (and (farrayp *s* st)
                     (fieldp *stack* *s* st)
                     (fieldp *lookup* *s* st)
                     (or (field-offsetp i *stack* *s* st)
                         (equal i -1))
                     (stack-in-rangep i st))))
      nil
    (if (equal i -1)
        t
      (and ;; (field-offsetp (fread *stack* i *s* st) *lookup* *s* st)
           (equal (fread *lookup* (fread *stack* i *s* st) *s* st) 1)
           (stack-corresponds-with-lookup-p (1- i) st)))))

;; (defthm equal-fread-*lookup*-fread-*stack*-1
;;   (implies (and (stack-corresponds-with-lookup-p j st)
;;                 (field-offsetp i *stack* *s* st)
;;                 (<= i j))
;;            (equal (fread *lookup* (fread *stack* i *s* st) *s* st)
;;                   1)))


;; ===================================================================

;; Some facts about evenp.

(defthm not-evenp-1+
  (implies (evenp i)
           (not (evenp (1+ i)))))


(defthm evenp-+-2
  (implies (evenp i)
           (evenp (+ 2 i))))

(defthm evenp-<-1+
  (implies (and (integerp i)
                (integerp j)
                (evenp i)
                (evenp j)
                (< i j))
           (< (1+ i) j)))


(defthm evenp-squeeze-equal-+-2
  (implies (and (integerp i)
                (integerp j)
                (evenp i)
                (evenp j)
                (< i j)
                (<= j (+ 2 i)))
           (equal (+ 2 i) j)))


(in-theory (disable evenp))

;; ===================================================================

(defthm evenp-implies-field-offsetp-1+
  (implies (and (field-offsetp i f start st)
                (evenp i)
                (farrayp start st)
                (fieldp f start st)
                (evenp (flength f start st)))
           (field-offsetp (1+ i) f start st))
  :hints (("Goal" :in-theory (enable field-offsetp))))

(defthm evenp-implies-field-offsetp-+-2
  (implies (and (field-offsetp i f start st)
                (evenp i)
                (farrayp start st)
                (fieldp f start st)
                (evenp (flength f start st))
                (not (equal (+ 2 i) (flength f start st))))
           (field-offsetp (+ 2 i) f start st))
  :hints (("Goal"
           :in-theory (enable field-offsetp)
           :use ((:instance evenp-squeeze-equal-+-2
                            (j (flength f start st)))))))

;; ===================================================================

(defun count-assigned (i st)
  (declare (xargs :guard (and (farrayp *s* st)
                              (fieldp *lookup* *s* st)
                              (or (field-offsetp i *lookup* *s* st)
                                  (equal i (flength *lookup* *s* st)))
                              (evenp (flength *lookup* *s* st))
                              (evenp i))
                  :stobjs (st)
                  :measure (nfix (- (flength *lookup* *s* st) i))))
  (if (not (mbt (and (farrayp *s* st)
                     (fieldp *lookup* *s* st)
                     (or (field-offsetp i *lookup* *s* st)
                         (equal i (flength *lookup* *s* st)))
                     (evenp (flength *lookup* *s* st))
                     (evenp i))))
      0
    (if (equal i (flength *lookup* *s* st))
        0
      (+ (if (equal (fread *lookup* i *s* st) 1) 1 0)
         (if (equal (fread *lookup* (1+ i) *s* st) 1) 1 0)
         (count-assigned (+ 2 i) st)))))


;; ===================================================================
;; ===================================================================
;; ===================================================================

(encapsulate
 ()
 (local (include-book "arithmetic/top-with-meta" :dir :system))
 (defthm evenp-flength-*lookup*
   (implies (integerp x)
            (evenp (+ 2 (* 2 x))))
   :hints (("Goal" :in-theory (enable evenp)))))

(defun assignment-stp (st)
  (declare (xargs :guard t
                  :guard-debug t
                  :stobjs (st)))                  
  (and
   ;; farray
   (farrayp *s* st)
   ;; Four fields in assignment
   (equal (num-fields *s* st)
          4)
   ;; num-vars is length 1 fieldp
   (fieldp *num-vars* *s* st)
   (equal (flength *num-vars* *s* st)
          1)
   ;; let n be num-vars
   (let ((n (fread *num-vars* 0 *s* st)))
     (and
      ;; num-vars is positive
      (<= 0 n)
      ;; stack-end is length 1 fieldp
      (fieldp *stack-end* *s* st)
      (equal (flength *stack-end* *s* st)
             1)
      ;; stack is length n fieldp
      (fieldp *stack* *s* st)
      (equal (flength *stack* *s* st)
             (1+ n))
      ;; lookup is length 2n+2 fieldp
      (fieldp *lookup* *s* st)
      (equal (flength *lookup* *s* st)
             (+ 2 (* 2 n)))
      ;; let se be stack-end
      (let ((se (fread *stack-end* 0 *s* st)))
        (and 
         ;; stack-end is field-offsetp
         (field-offsetp se *stack* *s* st)
         ;; (or (field-offsetp (1- se) *stack* *s* st)
         ;;     (equal se 0))
         ;; stack contains literals
         (stack-contains-literalsp (1- se) st)
         ;; stack unique
         (stack-uniquep (1- se) st)
         ;; stack not conflicting
         (stack-not-conflictingp (1- se) st)
         ;; lookup corresponds to stack
         (lookup-corresponds-with-stackp 2 st)
         ;; 
         (stack-in-rangep (1- se) st)
         ;; stack corresponds with lookup
         (stack-corresponds-with-lookup-p (1- se) st)
         ;;
         (equal (count-assigned 2 st)
                se)
         ))))))



;; ===================================================================

;; (defthm literalp-implies-integerp
;;   (implies (literalp x)
;;            (integerp x))
;;   :hints (("Goal" :in-theory (enable literalp)))
;;   :rule-classes :forward-chaining)


(defun lit-in-rangep (lit st)
  (declare (xargs :guard (and (assignment-stp st)
                              (literalp lit))
                  :stobjs (st)))
  (field-offsetp lit *lookup* *s* st))
  ;; (< lit (+ 2 (* 2 (fread *num-vars* 0 *s* st)))))




(defun assignedp (lit st)
  (declare (xargs :guard (and (assignment-stp st)
                              (literalp lit)
                              (lit-in-rangep lit st))
                  :stobjs (st)))                  
  (equal (fread *lookup* lit *s* st) 1))

(defthm assignedp-implies-field-memberp-*stack*
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st)
                (assignedp lit st))
           (field-memberp lit
                          (1- (fread *stack-end* 0 *s* st))
                          0 *stack* *s* st))
  :hints (("Goal"
           :use ((:instance equal-fread-lookup-1-implies-field-memberp-*stack*
                            (i 2))))))


(defthm field-memberp-*stack*-implies-equal-fread-*lookup*-1
  (implies (and (field-memberp lit i 0 *stack* *s* st)
                (stack-corresponds-with-lookup-p i st))
           (equal (fread *lookup* lit *s* st) 1)))




(defthm field-memberp-*stack*-implies-assignedp
  (implies (and (assignment-stp st)
                (field-memberp lit
                               (1- (fread *stack-end* 0 *s* st))
                               0 *stack* *s* st))
           (assignedp lit st)))



;; Most of the time stack membership is more useful than lookup.
(defthm equal-assignedp-field-memberp-*stack*
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st))
           (equal (assignedp lit st)
                  (field-memberp lit
                                 (1- (fread *stack-end* 0 *s* st))
                                 0 *stack* *s* st))))







;; ===================================================================
;; ===================================================================


;; ===================================================================

;; Some facts about field-offsetp and its interaction with literalp and evenp.


(defthm field-offsetp-implies-literalp
  (implies (and (field-offsetp lit f start st)
                (farrayp start st)
                (fieldp f start st)
                (< 1 lit))
           (literalp lit))
  :hints (("Goal"
           :in-theory (enable literalp)
           :use ((:instance sb60p-field-offsetp
                            (i lit))))))


(defthm evenp-field-offsetp-negate
  (implies (and (field-offsetp i f start st)
                (evenp i)
                (literalp i)
                (farrayp start st)
                (fieldp f start st)
                (evenp (flength f start st)))
           (field-offsetp (negate i) f start st))
  :hints (("Goal" :in-theory (enable equal-negate-1+))))




;; ===================================================================

;; correspondence between stack and lookup
;; ending in non-conflicting of lookup

(defthm field-memberp-*stack*-implies-not-field-memberp-negate-*stack*
  (implies (and (stack-not-conflictingp i st)
                (field-memberp lit i 0 *stack* *s* st))
           (not (field-memberp (negate lit) i 0 *stack* *s* st))))


(defthm not-field-memberp-*stack*-implies-not-equal-fread-*lookup*-1
  (implies (and (lookup-corresponds-with-stackp i st)
                (field-offsetp lit *lookup* *s* st)
                (<= i lit)
                (not (field-memberp lit
                                    (1- (fread *stack-end* 0 *s* st))
                                    0 *stack* *s* st)))
           (not (equal (fread *lookup* lit *s* st) 1))))

(defthm equal-fread-*lookup*-1-implies-not-equal-fread-*lookup*-negate-1
  (implies (and (lookup-corresponds-with-stackp i st)
                ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
                (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                ;; (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                (field-offsetp (negate lit) *lookup* *s* st)
                (<= i lit)
                (<= i (negate lit))
                (equal (fread *lookup* lit *s* st) 1))
           (not (equal (fread *lookup* (negate lit) *s* st) 1))) )


(defthm equal-fread-*lookup*-1-implies-not-equal-fread-*lookup*-1+-1
  (implies (and (lookup-corresponds-with-stackp i st)
                ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
                (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                ;; (literalp lit)
                (evenp lit)
                (< 1 i)
                (farrayp *s* st)
                (fieldp *lookup* *s* st)
                ;; (evenp (flength *lookup* *s* st))
                (field-offsetp lit *lookup* *s* st)
                (field-offsetp (1+ lit) *lookup* *s* st)
                (<= i lit)
                ;; (<= i (1+ lit))
                (equal (fread *lookup* lit *s* st) 1))
           (not (equal (fread *lookup* (1+ lit) *s* st) 1)))
  :hints (("Goal"
           :in-theory (enable equal-negate-1+)
           :use ((:instance
                  equal-fread-*lookup*-1-implies-not-equal-fread-*lookup*-negate-1)))))



;; ===================================================================

;; lookup-corresponds-with-stackp incrementing by two

(defthm lookup-corresponds-with-stackp-1+
  (implies (and (lookup-corresponds-with-stackp i st)
                (field-offsetp i *lookup* *s* st)
                ;; (<= (+ 2 i) (flength *lookup* *s* st))
                ;; (lookup-corresponds-with-stackp (+ 2 i) st)
                )
           (lookup-corresponds-with-stackp (+ 1 i) st))
  :hints (("Goal" :in-theory (enable lookup-corresponds-with-stackp))))



(encapsulate
 ()
 (local (include-book "arithmetic/top-with-meta" :dir :system))
 (defthm lookup-corresponds-with-stackp-+-2
   (implies (and (lookup-corresponds-with-stackp i st)
                 ;; (field-offsetp i *lookup* *s* st)
                 (<= (+ 2 i) (flength *lookup* *s* st))
                 )
            (lookup-corresponds-with-stackp (+ 2 i) st))
   :hints (("Goal"
            :in-theory (enable lookup-corresponds-with-stackp)) )))


;; ===================================================================

;; flength squeeze

(defthm <=-+-2-flength
  (implies (and (evenp i)
                (evenp (flength *lookup* *s* st))
                (integerp (flength *lookup* *s* st))
                ;; (not (equal i (flength *lookup* *s* st)))
                (field-offsetp i *lookup* *s* st))
           (<= (+ 2 i) (flength *lookup* *s* st)))
  :hints (("Goal" :in-theory (enable field-offsetp))))



;; ===================================================================

;; count-assigned and its relation to flength



(defthm <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *lookup* *s* st)
                (field-offsetp i *lookup* *s* st)
                (< 1 i)
                ;; (literalp i)
                ;; (evenp i)
                ;; (evenp (flength *lookup* *s* st))
                (lookup-corresponds-with-stackp i st)
                ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
                (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                )
           (<= (+ (count-assigned i st)
                  (count-assigned i st))
               (- (flength *lookup* *s* st)
                  i)))
  :hints (("Goal"
           :in-theory (disable stack-not-conflictingp
                               lookup-corresponds-with-stackp)
           :induct (count-assigned i st))))




;; (defthm squeeze1
;;   (implies (and (field-offsetp i f start st)
;;                 (field-offsetp j f start st)
;;                 (integerp (flength f start st))
;;                 (evenp i)
;;                 (evenp j)
;;                 (< i j))
;;            (field-offsetp (+ 2 i) f start st))
;;   :hints (("Goal" :in-theory (enable field-offsetp))))


(defthm <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i-2
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *lookup* *s* st)
                (field-offsetp i *lookup* *s* st)
                (< 1 i)
                ;; (literalp i)
                ;; (evenp i)
                ;; (evenp (flength *lookup* *s* st))
                (lookup-corresponds-with-stackp i st)
                ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
                (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                (field-offsetp j *lookup* *s* st)
                (evenp j)
                (<= i j)
                (not (equal (fread *lookup* j *s* st) 1))
                (not (equal (fread *lookup* (1+ j) *s* st) 1))
                ;; (literalp lit)
                ;; (<= i lit)
                ;; (not (field-memberp lit
                ;;                     (1- (fread *stack-end* 0 *s* st))
                ;;                     0 *stack* *s* st))
                ;; (not (field-memberp (negate lit)
                ;;                     (1- (fread *stack-end* 0 *s* st))
                ;;                     0 *stack* *s* st))
                )
           (< (+ (count-assigned i st)
                 (count-assigned i st))
              (- (flength *lookup* *s* st)
                 i)))
  :hints (("Goal"
           :in-theory (disable stack-not-conflictingp
                               lookup-corresponds-with-stackp)
           :induct (count-assigned i st))
          ("Subgoal *1/3"
           :cases ((equal i j)))
          ("Subgoal *1/3.1.1"
           :use ((:instance
                  <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i
                  (i (+ 2 i)))))))


(encapsulate
 ()
 (local (include-book "arithmetic/top-with-meta" :dir :system))

 (defthm <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i-3
   (implies (and ;; (farrayp *s* st)
                 ;; (fieldp *lookup* *s* st)
                 (field-offsetp i *lookup* *s* st)
                 (< 1 i)
                 ;; (literalp i)
                 ;; (evenp i)
                 ;; (evenp (flength *lookup* *s* st))
                 (lookup-corresponds-with-stackp i st)
                 ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
                 (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                 (field-offsetp j *lookup* *s* st)
                 (oddp j)
                 (< i j)
                 (not (equal (fread *lookup* j *s* st) 1))
                 (not (equal (fread *lookup* (1- j) *s* st) 1))
                 ;; (literalp lit)
                 ;; (<= i lit)
                 ;; (not (field-memberp lit
                 ;;                     (1- (fread *stack-end* 0 *s* st))
                 ;;                     0 *stack* *s* st))
                 ;; (not (field-memberp (negate lit)
                 ;;                     (1- (fread *stack-end* 0 *s* st))
                 ;;                     0 *stack* *s* st))
                 )
            (< (+ (count-assigned i st)
                  (count-assigned i st))
               (- (flength *lookup* *s* st)
                  i)))
   :hints (("Goal"
            :in-theory (disable stack-not-conflictingp
                                lookup-corresponds-with-stackp)
            :induct (count-assigned i st))
           ("Subgoal *1/3"
            :cases ((equal (1+ i) j)))
           ("Subgoal *1/3.1''"
            :use ((:instance
                   <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i
                   (i (+ 2 i)))))))
)


(defthm <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i-4
  (implies (and (farrayp *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp i *lookup* *s* st)
                (< 1 i)
                (evenp i)
                (evenp (flength *lookup* *s* st))
                (lookup-corresponds-with-stackp i st)
                (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                (field-offsetp j *lookup* *s* st)
                (<= i j)
                (not (equal (fread *lookup* j *s* st) 1))
                (not (equal (fread *lookup* (negate j) *s* st) 1))
                )
           (< (+ (count-assigned i st)
                 (count-assigned i st))
              (- (flength *lookup* *s* st)
                 i)))
  :hints (("Goal"
           :in-theory (e/d (equal-negate-1+
                            equal-negate-1-)
                           (count-assigned
                            stack-not-conflictingp
                            lookup-corresponds-with-stackp))
           :do-not-induct t
           :cases ((evenp j)))
          ("Subgoal 1"
           :use ((:instance
                  <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i-2)))
          ("Subgoal 2"
           :use ((:instance
                  <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i-3)))))


;; ===================================================================

;; Some dumb theorems to rearrange conclusion

(encapsulate
 ()
 (local (include-book "arithmetic/top-with-meta" :dir :system))
 (defthm count-assigned-<=-flength-/-2
   (implies (and ;; (farrayp *s* st)
             ;; (fieldp *lookup* *s* st)
             (field-offsetp i *lookup* *s* st)
             (< 1 i)
             ;; (literalp i)
             ;; (evenp i)
             ;; (evenp (flength *lookup* *s* st))
             (lookup-corresponds-with-stackp i st)
             ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
             (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
             (field-offsetp j *lookup* *s* st)
             (<= i j)
             (not (equal (fread *lookup* j *s* st) 1))
             (not (equal (fread *lookup* (negate j) *s* st) 1))
             )
            (< (count-assigned i st)
                (/ (- (flength *lookup* *s* st)
                      i)
                   2)))
   :hints (("Goal"
            ;; :do-not '(generalize fertilize eliminate-destructors)
            :in-theory (e/d ()
                            (stack-not-conflictingp
                             ;; stack-corresponds-with-lookup-p
                             lookup-corresponds-with-stackp))
            :do-not-induct t
            :use ((:instance
                   <=-+-count-assigned-count-assigned-flength-*lookup*-minus-i-4)))))

 (defthm count-assigned-<=-*num-vars*
   (implies (and ;; (farrayp *s* st)
             ;; (fieldp *lookup* *s* st)
             (field-offsetp i *lookup* *s* st)
             (< 1 i)
             ;; (literalp i)
             ;; (evenp i)
             ;; (evenp (flength *lookup* *s* st))
             (lookup-corresponds-with-stackp i st)
             ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
             (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
             (field-offsetp j *lookup* *s* st)
             (<= i j)
             (not (equal (fread *lookup* j *s* st) 1))
             (not (equal (fread *lookup* (negate j) *s* st) 1))
             (equal (flength *lookup* *s* st)
                    (+ 2 (* 2 (fread *num-vars* 0 *s* st))))
             )
            (< (count-assigned i st)
               (fread *num-vars* 0 *s* st)))
   :hints (("Goal"
            ;; :do-not '(generalize fertilize eliminate-destructors)
            :in-theory (e/d ()
                            (stack-not-conflictingp
                             ;; stack-corresponds-with-lookup-p
                             lookup-corresponds-with-stackp))
            :do-not-induct t
            :use ((:instance count-assigned-<=-flength-/-2)))))
 )



(defthm field-memberp-*stack*-implies-equal-fread-*lookup*-1-****
  (implies (and (not (equal (fread *lookup* lit *s* st) 1))
                (stack-corresponds-with-lookup-p i st))
           (not (field-memberp lit i 0 *stack* *s* st))))


(defthm evenp-field-offsetp-negate-2
  (implies (and (field-offsetp i f start st)
                (literalp i)
                (farrayp start st)
                (fieldp f start st)
                (evenp (flength f start st)))
           (field-offsetp (negate i) f start st))
  :hints (("Goal" :in-theory (enable field-offsetp equal-negate-1+))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm <-1-negate
   (implies (literalp lit)
            (< 1 (negate lit)))
   :hints (("Goal" :in-theory (enable literalp negate)))))


(defthm count-assigned-<=-*num-vars*-2
  (implies (and (farrayp *s* st)
                (fieldp *lookup* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                ;; (< 1 i)
                ;; (literalp i)
                ;; (evenp i)
                (evenp (flength *lookup* *s* st))
                (lookup-corresponds-with-stackp 2 st)
                ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
                (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                (literalp lit)
                (lit-in-rangep lit st)
                (not (field-memberp lit
                                    (1- (fread *stack-end* 0 *s* st))
                                    0 *stack* *s* st))
                (not (field-memberp (negate lit)
                                    (1- (fread *stack-end* 0 *s* st))
                                    0 *stack* *s* st))
                (equal (flength *lookup* *s* st)
                       (+ 2 (* 2 (fread *num-vars* 0 *s* st))))
                )
           (< (count-assigned 2 st)
              (fread *num-vars* 0 *s* st)))
  ;; :otf-flg t
  :hints (("Goal"
           ;; :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d ()
                           (count-assigned
                            stack-not-conflictingp
                            ;; stack-corresponds-with-lookup-p
                            lookup-corresponds-with-stackp
                            ;not-field-memberp-*stack*-implies-not-equal-fread-*lookup*-1
                            ))
           ;; :do-not-induct t
           :use ((:instance
                  not-field-memberp-*stack*-implies-not-equal-fread-*lookup*-1
                  (i 2)
                  (lit (negate lit)))))))


(defthm fread-*stack-end*-<-fread-*num-vars*
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st)
                (not (field-memberp lit
                                    (1- (fread *stack-end* 0 *s* st))
                                    0 *stack* *s* st))
                (not (field-memberp (negate lit)
                                    (1- (fread *stack-end* 0 *s* st))
                                    0 *stack* *s* st)))
           (< (fread *stack-end* 0 *s* st)
              (fread *num-vars* 0 *s* st)))
  :hints (("Goal"
           :use ((:instance count-assigned-<=-*num-vars*-2)))))


(defthm field-offsetp-1+-fread-*stack-end*-*stack*
  (implies (and (assignment-stp st)
                (literalp lit)
                (lit-in-rangep lit st)
                (not (field-memberp lit
                                    (1- (fread *stack-end* 0 *s* st))
                                    0 *stack* *s* st))
                (not (field-memberp (negate lit)
                                    (1- (fread *stack-end* 0 *s* st))
                                    0 *stack* *s* st)))
           (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st))
  :hints (("Goal"
           :in-theory (e/d (field-offsetp) (count-assigned))
           :use ((:instance fread-*stack-end*-<-fread-*num-vars*)))))

;; ===================================================================


;; Trying to prove that count-assigned is equal to end of stack
;; Won't work without induction that increases i and decreases stack-end...

;; (set-checkpoint-summary-limit (nil . nil))

;; (defthm count-assigned-equals-*stack-end*
;;   (implies (and (farrayp *s* st)
;;                 (fieldp *lookup* *s* st)
;;                 (field-offsetp i *lookup* *s* st)
;;                 (< 1 i)
;;                 ;; (literalp i)
;;                 (evenp i)
;;                 (evenp (flength *lookup* *s* st))
;;                 (lookup-corresponds-with-stackp i st)
;;                 (stack-uniquep (1- (fread *stack-end* 0 *s* st)) st)
;;                 (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
;;                 (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
;;                 )
;;            (equal (count-assigned i st)
;;                   (fread *stack-end* 0 *s* st)))
;;   :hints (("Goal"
;;            ;; :do-not '(generalize fertilize eliminate-destructors)
;;            :in-theory (e/d ();lookup-corresponds-with-stackp)
;;                            (stack-not-conflictingp
;;                             stack-corresponds-with-lookup-p
;;                             ));lookup-corresponds-with-stackp))
;;            :induct (count-assigned i st))))










;; ===================================================================

;; Possible replacement?
;; (defthm field-offsetp-even
;;   (implies (and (field-offsetp i f start st)
;;                 (integerp (flength f start st))
;;                 (not (equal i (flength f start st)))
;;                 (evenp i)
;;                 (evenp (flength f start st))
;;                 (not (field-offsetp (+ 2 i) f start st)))
;;            (equal (flength f start st) (+ 2 i)))
;;   :hints (("Goal" :in-theory (enable field-offsetp))))


;; Weaker theorem about count-assigned
;; (defthm count-assigned-<=-flength-*lookup*-minus-i
;;   (implies (and (farrayp *s* st)
;;                 (fieldp *lookup* *s* st)
;;                 (field-offsetp i *lookup* *s* st)
;;                 ;; (evenp i)
;;                 ;; (evenp (flength *lookup* *s* st))
;;                 )
;;            (<= (count-assigned i st)
;;                (- (flength *lookup* *s* st) i))) )








;; "Main" theorem
;; (defthm not-stack-memberp-implies-field-offsetp-1+
;;   (implies (and (assignment-stp st)
;;                 (literalp lit)
;;                 (lit-in-rangep lit st)
;;                 (not (field-memberp lit
;;                                     (1- (fread *stack-end* 0 *s* st))
;;                                     0 *stack* *s* st))
;;                 (not (field-memberp (negate lit)
;;                                     (1- (fread *stack-end* 0 *s* st))
;;                                     0 *stack* *s* st)))
;;            (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)))

;; ===================================================================


(defun assign-lit (lit st)
  (declare (xargs :guard (and (assignment-stp st)
                              (literalp lit)
                              (lit-in-rangep lit st)
                              (not (field-memberp lit
                                                  (1- (fread *stack-end* 0
                                                             *s* st))
                                                  0 *stack* *s* st))
                              (not (field-memberp (negate lit)
                                                  (1- (fread *stack-end* 0
                                                             *s* st))
                                                  0 *stack* *s* st)))
                  :stobjs (st)))
  (let* ((stack-end (fread *stack-end* 0 *s* st))
         (st (fwrite *lookup* lit 1 *s* st))
         (st (fwrite *stack* stack-end lit *s* st))
         (st (fwrite *stack-end* 0 (1+ stack-end) *s* st)))
    st))


;; ===================================================================

(defthm farrayp-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit))
           (farrayp *s* (assign-lit lit st))))

(defthm num-fields-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit))
           (equal (num-fields *s* (assign-lit lit st))
                  (num-fields *s* st))))


(defthm flength-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit)
                (fieldp f *s* st))
           (equal (flength f *s* (assign-lit lit st))
                  (flength f *s* st))))

(defthm fieldp-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit))
           (equal (fieldp f *s* (assign-lit lit st))
                  (fieldp f *s* st))))

(defthm field-offsetp-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit)
                (fieldp f *s* st))
           (equal (field-offsetp offset f *s* (assign-lit lit st))
                  (field-offsetp offset f *s* st))))

(defthm fread-*stack-end*-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit))
           (equal (fread *stack-end* 0 *s* (assign-lit lit st))
                  (1+ (fread *stack-end* 0 *s* st)))))


(defthm fread-*num-vars*-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *num-vars* *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit))
           (equal (fread *num-vars* 0 *s* (assign-lit lit st))
                  (fread *num-vars* 0 *s* st))))

;; ===================================================================

(defthm stack-contains-literalsp-fwrite-literal
  (implies (and (literalp v)
                (stack-contains-literalsp i st)
                ;; (farrayp *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                (field-offsetp offset *stack* *s* st))
           (stack-contains-literalsp i (fwrite *stack* offset v *s* st))))

(defthm stack-contains-literalsp-fwrite-diff-field
  (implies (and (not (equal f *stack*))
                (stack-contains-literalsp i st)
                ;; (farrayp *s* st)
                (fieldp f *s* st)
                (field-offsetp offset f *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                (sb60p v))
           (stack-contains-literalsp i (fwrite f offset v *s* st))))


(defthm stack-contains-literalsp-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit)
                (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st))
           (stack-contains-literalsp (fread *stack-end* 0 *s* st)
                                     (assign-lit lit st))))

(defthm stack-contains-literalsp-0-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit)
                (equal (fread *stack-end* 0 *s* st) 0))
           (stack-contains-literalsp 0 (assign-lit lit st)))
  :hints (("Goal"
           :use ((:instance stack-contains-literalsp
                            (i 0)
                            (st (assign-lit lit st)))))))

;; ===================================================================

  

(defthm stack-uniquep-fwrite-diff-field
  (implies (and (not (equal f *stack*))
                ;; (farrayp *s* st)
                (fieldp f *s* st)
                (field-offsetp offset f *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                (sb60p v)
                (stack-uniquep i st)
                ;; (stack-contains-literalsp i st)
                )
           (stack-uniquep i (fwrite f offset v *s* st))))


(defthm stack-uniquep-fwrite-out-of-bounds-high
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                ;; (<= 0 i)
                (field-offsetp j *stack* *s* st)
                (literalp lit)
                (stack-uniquep i st)
                (< i j)
                ;; (stack-contains-literalsp i st)
                )
           (stack-uniquep i (fwrite *stack* j lit *s* st))) )

(defthm stack-uniquep-fwrite-not-stack-memberp
  (implies (and (not (field-memberp lit (1- i) 0 *stack* *s* st))
                (farrayp *s* st)
                (fieldp *stack* *s* st)
                (field-offsetp i *stack* *s* st)
                ;; (field-offsetp (1- i) *stack* *s* st)
                (literalp lit)
                (stack-uniquep (1- i) st)
                (stack-contains-literalsp (1- i) st)
                )
           (stack-uniquep i (fwrite *stack* i lit *s* st))) )

(defthm stack-uniquep-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                (stack-uniquep (1- (fread *stack-end* 0 *s* st)) st)
                (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                (not (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0
                                    *stack* *s* st)))
           (stack-uniquep (fread *stack-end* 0 *s* st) (assign-lit lit st))) )

(defthm stack-uniquep-0-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit)
                (equal (fread *stack-end* 0 *s* st) 0))
           (stack-uniquep 0 (assign-lit lit st))))

;; ===================================================================


(defthm stack-not-conflictingp-fwrite-diff-field
  (implies (and (not (equal f *stack*))
                (farrayp *s* st)
                (fieldp f *s* st)
                (field-offsetp offset f *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                (sb60p v)
                (stack-not-conflictingp i st)
                ;; (stack-contains-literalsp i st)
                )
           (stack-not-conflictingp i (fwrite f offset v *s* st))) )


(defthm stack-not-conflictingp-fwrite-out-of-bounds-high
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                ;; (<= 0 i)
                (field-offsetp j *stack* *s* st)
                (literalp lit)
                (stack-not-conflictingp i st)
                (< i j)
                ;; (stack-contains-literalsp i st)
                )
           (stack-not-conflictingp i (fwrite *stack* j lit *s* st))))


(defthm stack-not-conflictingp-fwrite-not-stack-memberp
  (implies (and (not (field-memberp (negate lit) (1- i) 0 *stack* *s* st))
                (farrayp *s* st)
                (fieldp *stack* *s* st)
                (field-offsetp i *stack* *s* st)
                ;; (field-offsetp (1- i) *stack* *s* st)
                (literalp lit)
                (stack-not-conflictingp (1- i) st)
                (stack-contains-literalsp (1- i) st)
                )
           (stack-not-conflictingp i (fwrite *stack* i lit *s* st))))

(defthm stack-not-conflictingp-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                (not (field-memberp (negate lit) (1- (fread *stack-end* 0 *s*
                                                            st)) 0 *stack* *s* st)))
           (stack-not-conflictingp (fread *stack-end* 0 *s* st) (assign-lit lit
                                                                            st))) )


(defthm stack-not-conflictingp-0-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit)
                (equal (fread *stack-end* 0 *s* st) 0))
           (stack-not-conflictingp 0 (assign-lit lit st))))

;; ===================================================================


(defthm stack-in-rangep-fwrite-diff-field
  (implies (and (not (equal f *stack*))
                ;; (not (equal f *lookup*))
                ;; (farrayp *s* st)
                (fieldp f *s* st)
                (field-offsetp offset f *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                (sb60p v)
                (stack-in-rangep i st)
                ;; (stack-contains-literalsp i st)
                )
           (stack-in-rangep i (fwrite f offset v *s* st))))

(defthm stack-in-rangep-fwrite-out-of-bounds-high
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                ;; (<= 0 i)
                (field-offsetp j *stack* *s* st)
                (literalp lit)
                (stack-in-rangep i st)
                (< i j)
                ;; (stack-contains-literalsp i st)
                )
           (stack-in-rangep i (fwrite *stack* j lit *s* st))))


(defthm stack-in-rangep-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                ;; (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                ;; (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st)
                ;; (not (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st))
                )
           (stack-in-rangep (fread *stack-end* 0 *s* st)
                            (assign-lit lit st))) )

(defthm stack-in-rangep-0-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit)
                (equal (fread *stack-end* 0 *s* st) 0))
           (stack-in-rangep 0 (assign-lit lit st)))
  :hints (("Goal"
           :use ((:instance stack-in-rangep
                            (i 0)
                            (st (assign-lit lit st)))))))

;; ===================================================================

(defthm stack-corresponds-with-lookup-p-fwrite-diff-field
  (implies (and (not (equal f *stack*))
                (not (equal f *lookup*))
                ;; (farrayp *s* st)
                (fieldp f *s* st)
                (field-offsetp offset f *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                (sb60p v)
                (stack-corresponds-with-lookup-p i st)
                ;; (stack-contains-literalsp i st)
                )
           (stack-corresponds-with-lookup-p i (fwrite f offset v *s* st))))


(defthm stack-corresponds-with-lookup-p-fwrite-out-of-bounds-high
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                ;; (<= 0 i)
                (field-offsetp j *stack* *s* st)
                (literalp lit)
                (stack-corresponds-with-lookup-p i st)
                (< i j)
                ;; (stack-contains-literalsp i st)
                )
           (stack-corresponds-with-lookup-p i (fwrite *stack* j lit *s* st))))


(defthm stack-corresponds-with-lookup-p-fwrite-not-stack-memberp
  (implies (and ;; (not (stack-memberp lit i st))
                ;; (farrayp *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                ;; (fieldp *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                ;(field-offsetp (1- i) *stack* *s* st)
                ;; (literalp lit)
                ;; (lit-in-rangep lit st)
                ;; (stack-uniquep i st)
                (stack-corresponds-with-lookup-p i st)
                ;; (stack-contains-literalsp i st)
                )
           (stack-corresponds-with-lookup-p i (fwrite *lookup* lit 1 *s* st))) )

(defthm stack-corresponds-with-lookup-p-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                ;; (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                ;; (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s*
                                                            st)) st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st)
                ;; (not (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st))
                )
           (stack-corresponds-with-lookup-p (fread *stack-end* 0 *s* st) (assign-lit lit
                                                                            st))) )

(defthm stack-corresponds-with-lookup-p-0-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                (literalp lit)
                (equal (fread *stack-end* 0 *s* st) 0))
           (stack-corresponds-with-lookup-p 0 (assign-lit lit st)))
  :hints (("Goal"
           :use ((:instance stack-in-rangep-0-assign-lit)
                 (:instance stack-corresponds-with-lookup-p
                            (i 0)
                            (st (assign-lit lit st)))))))


;; ===================================================================

(in-theory (enable lookup-corresponds-with-stackp))

(defthm lookup-corresponds-with-stackp-fwrite-*lookup*
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *lookup* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *stack-end* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (literalp lit)
                ;; (lit-in-rangep lit st)
                ;; (literalp i)
                ;; (< 1 i)
                (lookup-corresponds-with-stackp i st)
                ;; (<= i lit)
                (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0 *stack* *s* st)
                )
           (lookup-corresponds-with-stackp i (fwrite *lookup* lit 1 *s* st))) )

(defthm field-memberp-fwrite-*stack*-fwrite-*stack-end*
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                ;; (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                ;; (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (literalp lit)
                ;; (field-offsetp lit *lookup* *s* st)
                )
           (field-memberp lit (fread *stack-end* 0 *s* st) 0 *stack* *s*
                          (fwrite *stack* (fread *stack-end* 0 *s* st) lit *s*
                                  (fwrite *stack-end* 0 (1+ (fread *stack-end*
                                                                   0 *s* st))
                                          *s* st)))))


(defthm integerp-implies-equal-+--1-1
  (implies (integerp x)
           (equal (+ -1 1 x)
                  x)))


(defthm lookup-corresponds-with-stackp-fwrite-*stack*-fwrite-*stack-end*
  (implies (and (farrayp *s* st)
                ;; (fieldp *lookup* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *stack-end* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (lit-in-rangep lit st)
                ;; (literalp i)
                ;; (< 1 i)
                (literalp lit)
                (lookup-corresponds-with-stackp i st)
                ;; (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st)
                )
           (lookup-corresponds-with-stackp i
                                           (fwrite *stack*
                                                   (fread *stack-end* 0 *s* st)
                                                   lit *s*
                                                   (fwrite *stack-end* 0
                                                           (1+ (fread
                                                                *stack-end*
                                                                0
                                                                *s*
                                                                st))
                                                           *s* st)))) )


(in-theory (disable lookup-corresponds-with-stackp))


(defthm lookup-corresponds-with-stackp-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                ;; (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                ;; (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                (lookup-corresponds-with-stackp 2 st)
                ;; (not (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st))
                )
           (lookup-corresponds-with-stackp 2 (assign-lit lit st))) )

;; ===================================================================


(defthm count-assigned-fwrite-*lookup*-low
  (implies (and (farrayp *s* st)
                (fieldp *lookup* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *stack-end* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (literalp lit)
                ;; (lit-in-rangep lit st)
                ;; (literalp i)
                ;; (< 1 i)
                ;; (evenp i)
                ;; (lookup-corresponds-with-stackp i st)
                (< lit i)
                ;; (not (equal (fread *lookup* lit *s* st) 1))
                ;; (not (equal (fread *lookup* (negate lit) *s* st) 1))
                ;; (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0 *stack* *s* st)
                )
           (equal (count-assigned i (fwrite *lookup* lit 1 *s* st))
                  (count-assigned i st))))


   

(defthm count-assigned-fwrite-*lookup*-high
  (implies (and (farrayp *s* st)
                (fieldp *lookup* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *stack-end* *s* st)
                (field-offsetp i *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (literalp lit)
                ;; (lit-in-rangep lit st)
                ;; (literalp i)
                (< 1 i)
                (evenp i)
                (evenp (flength *lookup* *s* st))
                ;; (lookup-corresponds-with-stackp i st)
                (<= i lit)
                (not (equal (fread *lookup* lit *s* st) 1))
                ;; (not (equal (fread *lookup* (negate lit) *s* st) 1))
                ;; (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0 *stack* *s* st)
                )
           (equal (count-assigned i (fwrite *lookup* lit 1 *s* st))
                  (1+ (count-assigned i st))))
  ;:otf-flg t
  :hints (("Subgoal *1/5"
           :cases ((equal lit i) (equal lit (1+ i))))
          ("Subgoal *1/2"
           :cases ((equal lit i) (equal lit (1+ i))))))

(defthm count-assigned-fwrite-*stack*-fwrite-*stack-end*
  (implies (and (farrayp *s* st)
                ;; (fieldp *lookup* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *stack-end* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                ;; (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (lit-in-rangep lit st)
                ;; (literalp i)
                ;; (< 1 i)
                (literalp lit)
                ;; (lookup-corresponds-with-stackp i st)
                ;; (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st)
                )
           (equal (count-assigned i
                                  (fwrite *stack*
                                          (fread *stack-end* 0 *s* st)
                                          lit *s*
                                          (fwrite *stack-end* 0
                                                  (1+ (fread
                                                       *stack-end*
                                                       0
                                                       *s*
                                                       st))
                                                  *s* st)))
                  (count-assigned i st))))


(defthm count-assigned-assign-lit
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                (not (equal (fread *lookup* lit *s* st) 1))
                (evenp (flength *lookup* *s* st))
                )
           (equal (count-assigned 2 (assign-lit lit st))
                  (1+ (count-assigned 2 st)))))


(defthm count-assigned-assign-lit-2
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                (not (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0
                                    *stack* *s* st))
                (evenp (flength *lookup* *s* st))
                (lookup-corresponds-with-stackp 2 st)
                )
           (equal (count-assigned 2 (assign-lit lit st))
                  (1+ (count-assigned 2 st)))) )



;; ===================================================================

;; (skip-proofs
;;  (defthm not-stack-memberp-implies-field-offsetp-1+
;;    (implies (and (assignment-stp st)
;;                  (literalp lit)
;;                  (field-offsetp lit *lookup* *s* st)
;;                  (not (stack-memberp lit
;;                                      (1- (fread *stack-end* 0 *s* st)) st))
;;                  (not (stack-memberp (negate lit)
;;                                      (1- (fread *stack-end* 0 *s* st)) st))
;;                  )
;;             (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)) ))
  ;; :hints (("Goal"
  ;;          :in-theory (disable lookup-corresponds-with-stackp
  ;;                              stack-corresponds-with-lookup-p))
  ;;         ("Subgoal 2'"
  ;;          :in-theory (enable field-offsetp)
  ;;          :cases ((equal (fread *num-vars* 0 *s* st) 0)))))



(defthm assignment-stp-assign-lit
  (implies (and (assignment-stp st)
                (literalp lit)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                ;; (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (field-offsetp lit *lookup* *s* st)
                ;(lit-in-rangep lit st)
                ;(not (stack-fullp st))
                (not (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0
                                    *stack* *s* st))
                (not (field-memberp (negate lit) (1- (fread *stack-end* 0 *s*
                                                            st)) 0 *stack* *s* st))
                )
           (assignment-stp (assign-lit lit st)))
  ;; :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           ;; :use ((:instance field-offsetp-1+-fread-*stack-end*-*stack*))
           ;; :use ((:instance not-stack-memberp-implies-field-offsetp-1+))
           :in-theory (disable assign-lit
                               stack-contains-literalsp
                               stack-uniquep
                               stack-not-conflictingp
                               stack-corresponds-with-lookup-p
                               stack-in-rangep
                               count-assigned)
           :use ((:instance count-assigned-assign-lit-2)
                 (:instance field-offsetp-1+-fread-*stack-end*-*stack*)))))





;; ===================================================================
;; ===================================================================
;; ===================================================================


(defun unassign-one (st)
  (declare (xargs :guard (and (assignment-stp st)
                              (not (equal (fread *stack-end* 0 *s* st) 0))
                              (sb60p (1- (fread *stack-end* 0 *s* st))))
                  :stobjs (st)))
  (let* ((1--stack-end (1- (fread *stack-end* 0 *s* st)))
         (lit (fread *stack* 1--stack-end *s* st))
         (st (fwrite *lookup* lit 0 *s* st))
         ;; (st (fwrite *stack* 1--stack-end 0 *s* st))
         (st (fwrite *stack-end* 0 1--stack-end *s* st)))
    st))


;; ===================================================================

;; (defthm field-offsetp-fread-*stack*-*lookup*
;;   (implies (and (farrayp *s* st)
;;                 (fieldp *stack* *s* st)
;;                 (fieldp *lookup* *s* st)
;;                 (field-offsetp i *stack* *s* st)
;;                 (stack-corresponds-with-lookup-p j st)
;;                 (<= i j))
;;            (field-offsetp (fread *stack* i *s* st) *lookup* *s* st)))

;; (defthm sb60p-field-offsetp
;;   (implies (and (field-offsetp i f start st)
;;                 (farrayp start st)
;;                 (fieldp f start st))
;;            (sb60p i))
;;   :hints (("Goal"
;;            :in-theory (enable field-offsetp farrayp fieldp)
;;            :use ((:instance sb60p-flength))))
;;   :rule-classes :forward-chaining)

(defthm field-offsetp-fread-*stack*-*lookup*
  (implies (and (stack-in-rangep j st)
                (field-offsetp i *stack* *s* st)
                (<= i j))
           (field-offsetp (fread *stack* i *s* st) *lookup* *s* st)))

(defthm farrayp-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (farrayp *s* (unassign-one st))))

(defthm num-fields-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (equal (num-fields *s* (unassign-one st))
                  (num-fields *s* st))))


(defthm flength-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st)
                (fieldp f *s* st))
           (equal (flength f *s* (unassign-one st))
                  (flength f *s* st))))

(defthm fieldp-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (equal (fieldp f *s* (unassign-one st))
                  (fieldp f *s* st))))

(defthm field-offsetp-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st)
                (fieldp f *s* st))
           (equal (field-offsetp offset f *s* (unassign-one st))
                  (field-offsetp offset f *s* st))))

(defthm fread-*stack-end*-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (equal (fread *stack-end* 0 *s* (unassign-one st))
                  (1- (fread *stack-end* 0 *s* st)))))


(defthm fread-*num-vars*-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *num-vars* *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (equal (fread *num-vars* 0 *s* (unassign-one st))
                  (fread *num-vars* 0 *s* st))))


;; ===================================================================

;; (defthm stack-contains-literalsp-1-
;;   (implies (and (stack-contains-literalsp i st)
;;                 (field-offsetp i *stack* *s* st))
;;            (stack-contains-literalsp (1- i) st)))

(defthm stack-contains-literalsp-unassign-one
  (implies (and ;; (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *lookup* *s* st)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (not (equal (fread *stack-end* 0 *s* st) 0))
                (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (stack-contains-literalsp (+ -2 (fread *stack-end* 0 *s* st))
                                     (unassign-one st))) )
  ;; :hints (("Goal"
  ;;          :use (;; (:instance stack-contains-literalsp-fwrite-diff-field
  ;;                ;;            (f 4)
  ;;                ;;            (i (+ -2 (fread 2 0 0 st)))
  ;;                ;;            (offset (fread 3 (+ -1 (fread 2 0 0 st)) 0 st))
  ;;                ;;            (v 0)
  ;;                ;;            (st (fwrite 2 0 (+ -1 (fread 2 0 0 st)) 0 st)))
  ;;                ;; (:instance stack-contains-literalsp-fwrite-diff-field
  ;;                ;;            (i (+ -2 (fread 2 0 0 st)))
  ;;                ;;            (f 2)
  ;;                ;;            (offset 0)
  ;;                ;;            (v (+ -1 (fread 2 0 0 st))))
  ;;                (:instance stack-contains-literalsp-1-
  ;;                           (i (+ -1 (fread 2 0 0 st))))))))


(defthm stack-uniquep-unassign-one
  (implies (and ;; (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *lookup* *s* st)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (not (equal (fread *stack-end* 0 *s* st) 0))
                (stack-uniquep (1- (fread *stack-end* 0 *s* st)) st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (stack-uniquep (+ -2 (fread *stack-end* 0 *s* st))
                          (unassign-one st))) )

(defthm stack-not-conflictingp-unassign-one
  (implies (and ;; (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *lookup* *s* st)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (not (equal (fread *stack-end* 0 *s* st) 0))
                (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (stack-not-conflictingp (+ -2 (fread *stack-end* 0 *s* st))
                                   (unassign-one st))) )



(defthm stack-in-rangep-unassign-one
  (implies (and ;; (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *lookup* *s* st)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (not (equal (fread *stack-end* 0 *s* st) 0))
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st))
           (stack-in-rangep (+ -2 (fread *stack-end* 0 *s* st))
                            (unassign-one st))) )


(defthm stack-corresponds-with-lookup-p-fwrite-not-stack-memberp-2
  (implies (and (not (field-memberp lit i 0 *stack* *s* st))
                ;; (farrayp *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (field-offsetp i *stack* *s* st)
                ;; (fieldp *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                ;; (field-offsetp (1- i) *stack* *s* st)
                ;; (literalp lit)
                ;; (lit-in-rangep lit st)
                ;; (stack-uniquep i st)
                (stack-corresponds-with-lookup-p i st)
                ;; (stack-contains-literalsp i st)
                )
           (stack-corresponds-with-lookup-p i (fwrite *lookup* lit 0 *s* st))) )

(defthm stack-corresponds-with-lookup-p-unassign-one
  (implies (and ;; (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *lookup* *s* st)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (not (equal (fread *stack-end* 0 *s* st) 0))
                (stack-uniquep 
                 (1- (fread *stack-end* 0 *s* st))
                 st)
                (stack-corresponds-with-lookup-p
                 (1- (fread *stack-end* 0 *s* st))
                 st))
           (stack-corresponds-with-lookup-p (+ -2 (fread *stack-end* 0 *s* st))
                                            (unassign-one st)))
  :hints (("Goal"
           :use ((:instance
                  stack-corresponds-with-lookup-p-fwrite-not-stack-memberp-2
                  (i (+ -2 (fread 2 0 0 st)))
                  (lit (fread 3 (+ -1 (fread 2 0 0 st)) 0 st))
                  (st (fwrite 2 0 (+ -1 (fread 2 0 0 st)) 0 st)))))))








(defthm lookup-corresponds-with-stackp-fwrite-*lookup*-0
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *lookup* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *stack-end* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                ;; (< 1 i)
                ;; (literalp lit)
                (field-offsetp lit *lookup* *s* st)
                (lookup-corresponds-with-stackp i st)
                ;; (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st)
                )
           (lookup-corresponds-with-stackp i
                                           (fwrite *lookup* lit 0 *s* st)))
  :hints (("Goal" :in-theory (enable lookup-corresponds-with-stackp))))


(defthm lookup-corresponds-with-stackp-fwrite-*stack-end*
  (implies (and ;; (farrayp *s* st)
                ;; (fieldp *lookup* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *stack-end* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                ;; (< 1 i)
                (field-offsetp (fread *stack* (1- (fread *stack-end* 0 *s* st))
                                      *s* st)
                               *lookup* *s* st)
                (lookup-corresponds-with-stackp i st)
                ;; (not (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st)
                )
           (lookup-corresponds-with-stackp
            i
            (fwrite *lookup*
                    (fread *stack* (1- (fread *stack-end* 0 *s* st)) *s* st)
                    0
                    *s*
                    (fwrite *stack-end*
                            0
                            (1- (fread *stack-end* 0 *s* st))
                            *s*
                            st))))
  :hints (("Goal" :in-theory (enable lookup-corresponds-with-stackp))))

;; (defthm lookup-corresponds-with-stackp-fwrite-*stack-end*-2
;;   (implies (and (farrayp *s* st)
;;                 ;; (fieldp *lookup* *s* st)
;;                 ;; (fieldp *stack* *s* st)
;;                 (fieldp *stack-end* *s* st)
;;                 ;; (field-offsetp i *lookup* *s* st)
;;                 (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
;;                 ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
;;                 ;; (< 1 i)
;;                 ;; (literalp lit)
;;                 ;; (field-offsetp lit *lookup* *s* st)
;;                 ;; (field-offsetp (fread *stack* (1- (fread *stack-end* 0 *s* st))
;;                 ;;                       *s* st)
;;                 ;;                *lookup* *s* st)
;;                 (lookup-corresponds-with-stackp i st)
;;                 (equal (fread *lookup*
;;                               (fread *stack* (1- (fread *stack-end* 0 *s* st))
;;                                      *s* st)
;;                               *s*
;;                               st)
;;                        0)
;;                 ;; (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st)
;;                 )
;;            (lookup-corresponds-with-stackp
;;             i
;;             (fwrite *stack-end* 0 (1- (fread *stack-end* 0 *s* st))
;;                     *s* st))))


;; !!!!!
(defthm lookup-corresponds-with-stackp-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                ;; (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                ;; (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (not (equal (fread *stack-end* 0 *s* st) 0))
                ;; (stack-uniquep (1- (fread *stack-end* 0 *s* st)) st)
                ;; (stack-not-conflictingp (1- (fread *stack-end* 0 *s* st)) st)
                ;; (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                ;; (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s*
                ;;                                             st)) st)
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st)
                (lookup-corresponds-with-stackp 2 st)
                ;; (field-offsetp (fread *stack* (1- (fread *stack-end* 0 *s* st))
                ;;                       *s* st)
                ;;                *lookup* *s* st)
                ;; (sb60p (1- (fread *stack-end* 0 *s* st)))
                ;; (not (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st))
                )
           (lookup-corresponds-with-stackp 2 (unassign-one st))) )
  ;; ;; :otf-flg t
  ;; :hints (("Goal"
  ;;          :do-not-induct t
  ;;          :in-theory (disable lookup-corresponds-with-stackp
  ;;                              lookup-corresponds-with-stackp-fwrite-*lookup*-0
  ;;                              lookup-corresponds-with-stackp-fwrite-*stack-end*)
  ;;          :use (;; (:instance lookup-corresponds-with-stackp-fwrite-*lookup*-0
  ;;                ;;            (i 2)
  ;;                ;;            (lit (fread *stack* (1- (fread *stack-end* 0 *s* st))
  ;;                ;;                        *s* st))
  ;;                ;;            (st (fwrite *stack-end* 0
  ;;                ;;                        (1- (fread *stack-end* 0 *s* st))
  ;;                ;;                        *s* st)))
  ;;                (:instance lookup-corresponds-with-stackp-fwrite-*stack-end*
  ;;                           (i 2))))))





(defthm count-assigned-fwrite-*lookup*-low-2
  (implies (and (farrayp *s* st)
                (fieldp *lookup* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *stack-end* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (literalp lit)
                ;; (lit-in-rangep lit st)
                ;; (literalp i)
                ;; (< 1 i)
                ;; (evenp i)
                ;; (lookup-corresponds-with-stackp i st)
                (< lit i)
                ;; (not (equal (fread *lookup* lit *s* st) 1))
                ;; (not (equal (fread *lookup* (negate lit) *s* st) 1))
                ;; (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0 *stack* *s* st)
                )
           (equal (count-assigned i (fwrite *lookup* lit 0 *s* st))
                  (count-assigned i st))))

(defthm count-assigned-fwrite-*lookup*-high-2
  (implies (and (farrayp *s* st)
                (fieldp *lookup* *s* st)
                ;; (fieldp *stack* *s* st)
                ;; (fieldp *stack-end* *s* st)
                (field-offsetp i *lookup* *s* st)
                (field-offsetp lit *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (literalp lit)
                ;; (lit-in-rangep lit st)
                ;; (literalp i)
                (< 1 i)
                (evenp i)
                (evenp (flength *lookup* *s* st))
                ;; (lookup-corresponds-with-stackp i st)
                (<= i lit)
                (equal (fread *lookup* lit *s* st) 1)
                ;; (not (equal (fread *lookup* (negate lit) *s* st) 1))
                ;; (field-memberp lit (1- (fread *stack-end* 0 *s* st)) 0 *stack* *s* st)
                )
           (equal (count-assigned i (fwrite *lookup* lit 0 *s* st))
                  (1- (count-assigned i st))))
  ;:otf-flg t
  :hints (("Subgoal *1/5"
           :cases ((equal lit i) (equal lit (1+ i))))
          ("Subgoal *1/2"
           :cases ((equal lit i) (equal lit (1+ i))))))





(defthm count-assigned-fwrite-*stack*-fwrite-*stack-end*-2
  (implies (and (farrayp *s* st)
                ;; (fieldp *lookup* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *stack-end* *s* st)
                ;; (field-offsetp i *lookup* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                ;; (field-offsetp (fread *stack* (1- (fread *stack-end* 0 *s* st))
                ;;                       *s* st)
                ;;                *lookup* *s* st)
                ;; (field-offsetp (1+ (fread *stack-end* 0 *s* st)) *stack* *s* st)
                ;; (lit-in-rangep lit st)
                ;; (literalp i)
                ;; (< 1 i)
                ;; (literalp lit)
                ;; (equal (fread *lookup* (fread *stack* (1- (fread *stack-end* 0 *s* st))
                ;;                       *s* st) *s* st) 1)
                ;; (lookup-corresponds-with-stackp i st)
                ;; (stack-memberp lit (1- (fread *stack-end* 0 *s* st)) st)
                )
           (equal (count-assigned
                   i
                   (fwrite *stack-end*
                           0
                           (1- (fread *stack-end* 0 *s* st))
                           *s*
                           st))
                  (count-assigned i st))))

(defthm literalp-fread-*stack*
  (implies (and (stack-contains-literalsp j st)
                (field-offsetp i *stack* *s* st)
                (<= i j))
           (literalp (fread *stack* i *s* st))))

(defthm literalp-fread-*stack*-2
  (implies (and (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                (field-offsetp i *stack* *s* st)
                (<= i (1- (fread *stack-end* 0 *s* st))))
           (literalp (fread *stack* i *s* st))))


(defthm count-assigned-unassign-one
  (implies (and (farrayp *s* st)
                (fieldp *stack-end* *s* st)
                (fieldp *stack* *s* st)
                (fieldp *lookup* *s* st)
                (field-offsetp (fread *stack-end* 0 *s* st) *stack* *s* st)
                ;; (field-offsetp (1- (fread *stack-end* 0 *s* st)) *stack* *s* st)
                (evenp (flength *lookup* *s* st))
                (stack-in-rangep (1- (fread *stack-end* 0 *s* st)) st)
                (stack-contains-literalsp (1- (fread *stack-end* 0 *s* st)) st)
                (stack-corresponds-with-lookup-p (1- (fread *stack-end* 0 *s* st)) st)
                (field-offsetp 2 *lookup* *s* st)
                (not (equal (fread *stack-end* 0 *s* st) 0))
                )
           (equal (count-assigned 2 (unassign-one st))
                  (1- (count-assigned 2 st))))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable count-assigned
                               count-assigned-fwrite-*stack*-fwrite-*stack-end*-2
                               count-assigned-fwrite-*lookup*-high-2
                               literalp-fread-*stack* literalp-fread-*stack*-2)
           :use ((:instance count-assigned-fwrite-*stack*-fwrite-*stack-end*-2
                            (i 2))
                 (:instance count-assigned-fwrite-*lookup*-high-2
                            (i 2)
                            (lit (fread *stack* (1- (fread *stack-end* 0 *s*
                                                           st)) *s* st))
                            (st (FWRITE *stack-end* 0 (+ -1 (FREAD *stack-end* 0 *s* ST))
                                        *s* ST)))
                 (:instance literalp-fread-*stack*-2
                            (i (1- (fread *stack-end* 0 *s* st))))))))

;; ===================================================================


(defthm assignment-stp-unassign-one
  (implies (and (assignment-stp st)
                (not (equal (fread *stack-end* 0 *s* st) 0)))
           (assignment-stp (unassign-one st)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable unassign-one
                               count-assigned
                               lookup-corresponds-with-stackp
                               stack-contains-literalsp
                               stack-corresponds-with-lookup-p
                               stack-uniquep
                               stack-not-conflictingp
                               stack-in-rangep
                               ;; field-offsetp-1--not-0
                               )
           )
          ("Subgoal 2"
           :use ((:instance count-assigned-unassign-one)))))



;; ===================================================================

(in-theory (disable unassign-one
                    stack-corresponds-with-lookup-p
                    stack-in-rangep
                    stack-not-conflictingp
                    stack-uniquep
                    stack-contains-literalsp
                    count-assigned))


(defun unassign-all (i st)
  (declare (xargs :guard (and (assignment-stp st)
                              ;; (sb60p (1- (fread *stack-end* 0 *s* st)))
                              (equal (fread *stack-end* 0 *s* st) i)
                              (or (field-offsetp i *stack* *s* st)
                                  (equal i 0))
                              )
                  :guard-debug t
                  :guard-hints (("Goal" :in-theory (disable
                                                    lookup-corresponds-with-stackp
                                                    )))
                  ;; :verify-guards nil
                  :stobjs (st)
                  :measure (nfix i)
                  ))
  (if (not (mbt (and (assignment-stp st)
                     ;; (sb60p (1- (fread *stack-end* 0 *s* st)))
                     (equal (fread *stack-end* 0 *s* st) i)
                     (or (field-offsetp i *stack* *s* st)
                         (equal i 0))
                     )))
      st
    (if (equal i 0)
        st
      (let* ((st (unassign-one st))
             (st (unassign-all (1- i) st)))
        st))))



(defthm assignment-stp-unassign-all
  (implies (and (assignment-stp st)
                )
           (assignment-stp (unassign-all i st)))
  ;; :otf-flg t
  :hints (("Goal"
           ;; :do-not-induct t
           :in-theory (disable unassign-one
                               lookup-corresponds-with-stackp ))))

;; (i-am-here)

;; ===================================================================


;; (defconst *a*
;;   '(4  ;  0 - num-fields
;;     6  ;  1 - num-vars offset
;;     7  ;  2 - stack-end offset
;;     8  ;  3 - stack offset
;;     13 ;  4 - lookup offset
;;     23 ;  5 - end offset
;;     4  ;  6 - 0 - num-vars
;;     3  ;  7 - 0 - stack-end
;;     2  ;  8 - 0 - stack bottom
;;     4  ;  9 - 1
;;     7  ; 10 - 2
;;     0  ; 11 - 3
;;     0  ; 12 - 4 - padding
;;     0  ; 13 - 0 - lookup
;;     0  ; 14 - 1
;;     1  ; 15 - 2
;;     0  ; 16 - 3
;;     1  ; 17 - 4
;;     0  ; 18 - 5
;;     0  ; 19 - 6
;;     1  ; 20 - 7
;;     0  ; 21 - 8
;;     0  ; 22 - 9
;;     0  ; 23 - end
;;     ))


;; (resize-mem 24 st)
;; (!memi 0 4 st)
;; (!memi 1 6 st)
;; (!memi 2 7 st)
;; (!memi 3 8 st)
;; (!memi 4 13 st)
;; (!memi 5 23 st)
;; (!memi 6 4 st)
;; (!memi 7 3 st)
;; (!memi 8 2 st)
;; (!memi 9 4 st)
;; (!memi 10 7 st)
;; (!memi 11 0 st)
;; (!memi 12 0 st)
;; (!memi 13 0 st)
;; (!memi 14 0 st)
;; (!memi 15 1 st)
;; (!memi 16 0 st)
;; (!memi 17 1 st)
;; (!memi 18 0 st)
;; (!memi 19 0 st)
;; (!memi 20 1 st)
;; (!memi 21 0 st)
;; (!memi 22 0 st)
;; (!memi 23 0 st)
;; (assignment-stp st)


;; (!memi 8 0 st)
;; (!memi 9 0 st)
;; (!memi 10 0 st)
;; (!memi 15 0 st)
;; (!memi 17 0 st)
;; (!memi 20 0 st)

;; (resize-mem 24 st)
;; (!memi 0 4 st)
;; (!memi 1 6 st)
;; (!memi 2 7 st)
;; (!memi 3 8 st)
;; (!memi 4 13 st)
;; (!memi 5 23 st)
;; (!memi 6 4 st)
;; (!memi 7 0 st)
;; (assignment-stp st)


;; ===================================================================

;; (defconst *st-4-empty*
;;   '(4  ;  0 - num-fields
;;     6  ;  1 - num-vars offset
;;     7  ;  2 - stack-end offset
;;     8  ;  3 - stack offset
;;     13 ;  4 - lookup offset
;;     23 ;  5 - end offset
;;     4  ;  6 - 0 - num-vars
;;     0  ;  7 - 0 - stack-end
;;     0  ;  8 - 0 - stack bottom
;;     0  ;  9 - 1
;;     0  ; 10 - 2
;;     0  ; 11 - 3
;;     0  ; 12 - 4 - padding
;;     0  ; 13 - 0 - lookup
;;     0  ; 14 - 1
;;     0  ; 15 - 2
;;     0  ; 16 - 3
;;     0  ; 17 - 4
;;     0  ; 18 - 5
;;     0  ; 19 - 6
;;     0  ; 20 - 7
;;     0  ; 21 - 8
;;     0  ; 22 - 9
;;     0  ; 23 - end
;;     ))


;; (resize-mem 24 st)
;; (!memi 0 4 st)
;; (!memi 1 6 st)
;; (!memi 2 7 st)
;; (!memi 3 8 st)
;; (!memi 4 13 st)
;; (!memi 5 23 st)
;; (!memi 6 4 st)
;; (!memi 7 0 st)
;; (!memi 8 0 st)
;; (!memi 9 0 st)
;; (!memi 10 0 st)
;; (!memi 11 0 st)
;; (!memi 12 0 st)
;; (!memi 13 0 st)
;; (!memi 14 0 st)
;; (!memi 15 0 st)
;; (!memi 16 0 st)
;; (!memi 17 0 st)
;; (!memi 18 0 st)
;; (!memi 19 0 st)
;; (!memi 20 0 st)
;; (!memi 21 0 st)
;; (!memi 22 0 st)
;; (!memi 23 0 st)
;; (assignment-stp st)



;; (memi 0 st)
;; (memi 1 st)
;; (memi 2 st)
;; (memi 3 st)
;; (memi 4 st)
;; (memi 5 st)
;; (memi 6 st)
;; (memi 7 st)
;; (memi 8 st)
;; (memi 9 st)
;; (memi 10 st)
;; (memi 11 st)
;; (memi 12 st)
;; (memi 13 st)
;; (memi 14 st)
;; (memi 15 st)
;; (memi 16 st)
;; (memi 17 st)
;; (memi 18 st)
;; (memi 19 st)
;; (memi 20 st)
;; (memi 21 st)
;; (memi 22 st)
;; (memi 23 st)


;; ===================================================================


;; (defun count-up (i j)
;;   (declare (xargs :guard (and (integerp i)
;;                               (integerp j)
;;                               (<= i (1+ j)))
;;                   :measure (nfix (- (1+ j) i))))
;;   (if (not (mbt (and (integerp i)
;;                      (integerp j)
;;                      (<= i (1+ j)))))
;;       nil
;;     (if (equal i (1+ j))
;;         nil
;;       (cons i
;;             (count-up (1+ i) j)))))

;; (defun count-down (j i)
;;   (declare (xargs :guard (and (integerp i)
;;                               (integerp j)
;;                               (<= (1- i) j))
;;                   :measure (nfix (- j (1- i)))))
;;   (if (not (mbt (and (integerp i)
;;                      (integerp j)
;;                      (<= (1- i) j))))
;;       nil
;;     (if (equal (1- i) j)
;;         nil
;;       (cons j (count-down (1- j) i)))))


;; (defun stack-contains-literalsp (i end st)
;;   (declare (xargs :guard (and (farrayp *s* st)
;;                               (fieldp *stack* *s* st)
;;                               (field-offsetp end *stack* *s* st)
;;                               (or (field-offsetp i *stack* *s* st)
;;                                   (equal i (1+ end)))
;;                               (<= i (1+ end)))
;;                   :guard-debug t
;;                   :stobjs (st)
;;                   :measure (nfix (- (1+ end) i))))
;;   (if (not (mbt (and (farrayp *s* st)
;;                      (fieldp *stack* *s* st)
;;                      (field-offsetp end *stack* *s* st)
;;                      (or (field-offsetp i *stack* *s* st)
;;                          (equal i (1+ end)))
;;                      (<= i (1+ end)))))
;;       nil
;;     (if (equal i (1+ end))
;;         t
;;       (and (literalp (fread *stack* i *s* st))
;;            (stack-contains-literalsp (1+ i) end st)))))


;; (defun stack-memberp (e st)
;;   (declare (xargs :guard (and (farrayp *s* st)
;;                               (fieldp *stack* *s* st)
;;                               (fieldp *stack-end* *s* st)
;;                               (field-offsetp 0 *stack-end* *s* st)
;;                               (field-offsetp (fread *stack-end* 0 *s* st)
;;                                              *stack* *s* st)
;;                               ;; (field-offsetp 0 *stack* *s* st)
;;                               (sb60p e))
;;                   :guard-hints (("Goal" :in-theory (enable field-offsetp)))
;;                   :stobjs (st)))
;;   (field-memberp e (fread *stack-end* 0 *s* st) 0 *stack* *s* st))



;; (defthm integerp-+-2
;;   (implies (and (integerp i)
;;                 (integerp j))
;;            (integerp (+ i j))))

;; (defthm integerp--
;;   (implies (and (integerp i))
;;            (integerp (- i))))


;; (encapsulate
;;  ()
;;  (local (include-book "arithmetic/top-with-meta" :dir :system))
;;  (defthm 1--<=-1-
;;    (implies (and (integerp x)
;;                  (integerp y)
;;                  (<= (1- y) x)
;;                  (not (equal x (1- y))))
;;             (<= (1- y) (1- x)))))


   
;; (defthm field-offsetp-1--squeeze
;;   (implies (and (field-offsetp x f start st)
;;                 (field-offsetp y f start st)
;;                 (< y x)
;;                 )
;;            (field-offsetp (1- x) f start st))
;;   :hints (("Goal"
;;            :in-theory (enable field-offsetp))))




;; ===================================================================


;; (defun-sk forall-literal-assigned (st)
;;   (forall lit (implies (and (literalp lit)
;;                             (lit-in-rangep lit st))
;;                        (or (assignedp lit st)
;;                            (assignedp (negate lit) st)))))
;; (in-theory (disable forall-literal-assigned
;;                     forall-literal-assigned-necc))


;; (defun-sk exists-unassigned-literal (st)
;;   (exists lit (and (literalp lit)
;;                    (lit-in-rangep lit st)
;;                    (not (assignedp lit st))
;;                    (not (assignedp (negate lit) st)))))
;; (in-theory (disable exists-unassigned-literal
;;                     exists-unassigned-literal-suff))



;; (defthm forall-literal-assigned-implies-equal-*stack-end*-*num-vars*
;;   (implies (and (assignment-stp st)
;;                 (< (fread *stack-end* 0 *s* st)
;;                    (fread *num-vars* 0 *s* st)))
;;            (exists-unassigned-literal

;; (defthm forall-literal-assigned-implies-equal-*stack-end*-*num-vars*
;;   (implies (and (assignment-stp st)
;;                 (forall-literal-assigned st))
;;            (equal (fread *stack-end* 0 *s* st)
;;                   (fread *num-vars* 0 *s* st))))

;; (defthm not-field-memberp-0-*stack*
;;   (implies (and (stack-contains-literalsp i st)
;;                 (field-offsetp i *stack* *s* st))
;;            (not (field-memberp 0 i 0 *stack* *s* st))))

;; (defthm not-field-memberp-1-*stack*
;;   (implies (and (stack-contains-literalsp i st)
;;                 (field-offsetp i *stack* *s* st))
;;            (not (field-memberp 1 i 0 *stack* *s* st))))


;; (defun-sk forall-lit-assigned (st)
;;   (forall lit (implies (field-offsetp lit *lookup* *s* st)
;;                        (equal (fread *lookup* lit *s* st) 1))))
;; (in-theory (disable forall-lit-assigned
;;                     forall-lit-assigned-necc))

;; (implies (forall-lit-assigned st)
;;          )
