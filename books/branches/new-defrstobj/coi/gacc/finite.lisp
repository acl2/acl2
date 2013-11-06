#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;; Keep this list of include-books in sync with the list in the .acl2 file:
(include-book "gax")

(in-theory (disable list::len-of-cdr)) ;might be nice to remove this eventually
(local (in-theory (disable ifix)))

(in-theory (disable (:executable-counterpart skel)))

;Added by Eric
(local (in-theory (disable memberp 
;                           acl2::MEMBERP-Subbagp-NOT-CONSP-VERSION
                           REMOVE-BAG
                           REMOVE-1)))


(local (in-theory (disable fix-slot)))

;(skipper
; (encapsulate ()

(defthm slot-p-implies-skel-p-slot-skel
  (implies
   (slot-p slot)
   (skel-p (slot-skel slot)))
  :hints (("goal" :in-theory (enable slot-p))))

#|
(defthm mv-nth-cons
  (equal (mv-nth i (cons a b))
         (if (zp i) a (mv-nth (1- i) b)))
  :hints (("goal" :in-theory (enable mv-nth))))
|#

;move these?
(defthm non-integerp-ifix
  (implies (not (integerp x))
           (equal (ifix x) 
                  0))
  :hints (("goal" :in-theory (enable ifix))))

(defthm integerp-ifix
  (implies (integerp x)
           (equal (ifix x) 
                  x))
  :hints (("goal" :in-theory (enable ifix))))

(in-theory 
 (enable 
  slot-p 
  slot-extensionality!!
  ))

;fix-size was defined here

(defun offset-size (n)
  (declare (type (integer 0 *) n))
  (if (zp n)
      (word-size)
    (+ (word-size) (offset-size (1- n)))))

(defthm fix-size-offset-size
  (equal (fix-size (offset-size n))
         (offset-size n))
  :hints (("goal" :in-theory (enable fix-size offset-size))))

(defthm offset-size-max-offset
  (equal (offset-size (max-offset size))
         (fix-size size))
  :hints (("Goal" :in-theory (enable max-offset fix-size))))

(defthm offset-size-max-offset-free
  (implies
   (equal len (1+ (max-offset size)))
   (equal (offset-size (+ -1 len))
          (fix-size size))))

(defthm offset-size-len-sblk
  (equal (offset-size (1- (len (sblk size ptr))))
         (fix-size size)))




(defthm unfixed-size-sblk
  (implies (syntaxp (syntax-unfixed-size size))
           (equal (sblk size ptr)
                  (sblk (fix-size size) ptr)))
  :hints (("goal" :in-theory (enable sblk))))

(defthm unfixed-size-max-offset
  (implies (syntaxp (syntax-unfixed-size size))
           (equal (max-offset size)
                  (max-offset (fix-size size)))))

(in-theory (disable max-offset-fix-size))

(theory-invariant 
 (incompatible 
  (:rewrite max-offset-fix-size)
  (:rewrite unfixed-size-max-offset)
  ))

(defun sblk-parms (base sblk)
  (declare (type t base sblk))
  (let ((size (offset-size (nfix (1- (len sblk))))))
    (let ((ptr (if (consp sblk) (car sblk) base)))
      (mv size (- (ifix ptr) (ifix base))))))

(defthm non-integerp-sblk-base
  (implies
   (not (integerp base))
   (equal (sblk-parms base sblk)
          (sblk-parms (ifix base) sblk)))
  :hints (("goal" :in-theory (enable ifix))))

;added by Eric.
(defthm integerp-of-v1-of-sblk-parms
  (integerp (v1 (sblk-parms base sblk)))
  :hints (("Goal" :in-theory (enable sblk-parms))))

;added by Eric.
(defthm integerp-of-v0-of-sblk-parms
  (integerp (v0 (sblk-parms base sblk)))
  :hints (("Goal" :in-theory (enable sblk-parms))))


(defun appears (base term)
  (declare (type t base term))
  (or (equal base term)
      (memberp base term)))

#|
(defun appears-ignore-package (base term)
  (declare (type t base term))
  (or (equal (symbol-name base) (symbol-name term))
      (memberp base term)))
|#

              
(defun syntax-ptr (base ptr woff wbase)
  (declare (type t base ptr))
  (if (and (consp ptr)
           (equal (car ptr) 'binary-+)
           (consp (cdr ptr))
           (consp (cddr ptr)))
      (if (appears base (cadr ptr))
          `((,woff  . ,(caddr ptr))
            (,wbase . ,(cadr ptr)))
        (if (appears base (caddr ptr))
            `((,woff  . ,(cadr  ptr))
              (,wbase . ,(caddr ptr)))
          nil))
    (if (appears base ptr)
        `((,woff  . (quote 0))
          (,wbase . ,ptr))
      `((,woff  . ,ptr)
        (,wbase . (quote 0))))))



(defthm sblk-parms-sblk
  (implies
   (and
    (bind-free (syntax-ptr base ptr 'woff 'wbase) (woff wbase))
    (equal wbase (ifix base))
    (equal ptr (+ wbase woff))
    (integerp wbase)
    (integerp woff)
    )
   (equal (sblk-parms base (sblk size ptr))
          (mv (fix-size size) woff)))
  :hints (("Goal" :in-theory (disable MAX-OFFSET-WHEN-MULTIPLE-OF-8 ;bzo
                                      ))))

(defthm sblk-parms-sblk-free
  (implies
   (and
    (equal (sblk size ptr) sblk)
    (bind-free (syntax-ptr base ptr 'woff 'wbase) (woff wbase))
    (equal wbase (ifix base))
    (equal ptr (+ wbase woff))
    (integerp wbase)
    (integerp woff)
    )
   (equal (sblk-parms base sblk)
          (mv (fix-size size) woff))))

(in-theory (disable sblk-parms))

(local (in-theory (disable MAX-OFFSET-WHEN-MULTIPLE-OF-8))) ;bzo

(defmacro compare (base s1 o1 s2 o2)
  `(equal (sblk ,s1 (+<> ,o1 ,base))
          (sblk ,s2 (+<> ,o2 ,base))))

;bzo 
(defthm open-len
  (implies (and (syntaxp (syntax-consp-or-symbol list))
                (consp list))
           (equal (len list)
                  (1+ (len (cdr list)))))
  :hints (("goal" :in-theory (enable len))))








(encapsulate
 ()
 
 (local
  (encapsulate
   ()
   
   (defthm zp-max-offset
     (equal (equal (max-offset s) 0)
            (equal (fix-size s) 8))
     :hints (("goal" :in-theory (e/d (max-offset fix-size)
                                     (unfixed-size-max-offset))
              :expand (fix-size s))))
   
   (defthm max-offset-offset-size
     (equal (max-offset (offset-size len))
            (nfix len))
     :hints (("goal" :in-theory (e/d (max-offset) ( unfixed-size-max-offset)))))
   
   (defthm max-offset-offset-size-free
     (implies
      (equal (fix-size s) (offset-size len))
      (equal (max-offset s)
             (nfix len))))
   
   ))
 
 (defun base-appears-shallow (ptr)
   (declare (type t ptr))
   (or (and (symbolp ptr)
            (equal (symbol-name ptr) "BASE"))
       (and (consp ptr)
            (consp (cdr ptr))
            (symbolp (cadr ptr))
            (equal (symbol-name (cadr ptr)) "BASE"))))
 
;if either is a 'base, then bind it to wbase, otherwise return nil
 (defun syntax-ptr-instance (ptr woff wbase)
   (declare (type t ptr))
   (if (and (consp ptr)
            (equal (car ptr) 'binary-+)
            (consp (cdr ptr))
            (consp (cddr ptr)))
       (if (base-appears-shallow (cadr ptr))
           `((,woff  . ,(caddr ptr))
             (,wbase . ,(cadr ptr)))
         (if (base-appears-shallow (caddr ptr))
             `((,woff  . ,(cadr  ptr))
               (,wbase . ,(caddr ptr)))
           nil))
     (if (base-appears-shallow ptr)
         `((,woff  . (quote 0))
           (,wbase . ,ptr))
       nil)))
 
;bzo try getting rid of the bind-free?
 
 (defthm equal-sblk-extensionality-2
   (implies (and (bind-free (syntax-ptr-instance ptr 'o1 'base) (o1 base))
                 (equal ptr (+ o1 base))
                 (integerp o1)
                 (integerp base))
            (equal (equal (sblk s1 ptr) x)
                   (met ((s2 o2) (sblk-parms base x))
                        (and (sblkp x)
                             (consp x)
                             (equal (fix-size s1)
                                    (fix-size s2))
                             (equal (ifix o1)
                                    (ifix o2))))))
   :hints (("goal" :in-theory (e/d (sblk blk sblk-parms sblkp len)
                                   (unfixed-size-max-offset relocate-blk-rec-offset)))))
 
 (defthm equal-sblk-extensionality
   (implies (and (bind-free (syntax-ptr 'base ptr 'o1 'base)
                            (o1 base))
                 (equal ptr (+ o1 base))
                 (integerp o1)
                 (integerp base))
            (equal (equal (sblk s1 ptr) x)
                   (met ((s2 o2)
                         (sblk-parms base x))
                        (and (sblkp x)
                             (consp x)
                             (equal (fix-size s1)
                                    (fix-size s2))
                             (equal (ifix o1)
                                    (ifix o2))))))
   :hints
   (("goal"
     :in-theory
     (e/d (sblk blk sblk-parms sblkp 
                len 
                )
          (unfixed-size-max-offset relocate-blk-rec-offset)))))
 
 )




(defun rs (size off base spec)
  (declare (type t size off spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (and (slot-p slot)
                 (equal :ptr (slot-type slot))
                 (compare base size off (slot-size slot) (slot-off slot)))
            (slot-skel slot)
          (rs size off base (cdr spec))))
    (skel 0 nil)))


(defthm rs-when-base-is-not-an-integerp
  (implies (not (integerp base))
           (equal (RS SIZE OFF BASE SPEC)
                  (RS SIZE OFF 0 SPEC)))
  :hints (("Goal" :in-theory (disable ;ZS-INTRODUCTION-LEFT ;bzo looped
                                      ))))

(defun rv (size off base spec)
  (declare (type t size off spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (and (slot-p slot)
                 (compare base size off (slot-size slot) (slot-off slot)))
            (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                   (ifix (slot-val slot)))
          (rv size off base (cdr spec))))
    0))

;was called positive-rv
(defthm rv-non-negative
  (<= 0 (rv size off base spec)))

(defun ws (size off base skel spec)
  (declare (type t size off skel spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (and (slot-p slot)
                 (equal :ptr (slot-type slot))
                 (compare base size off (slot-size slot) (slot-off slot)))
            (cons (update-slot slot :skel (fix-skel skel))
                  (cdr spec))
          (cons slot
                (ws size off base skel (cdr spec)))))
    spec))

(defthm ws-when-base-is-not-an-integerp
  (implies (not (integerp gacc::base))  
           (equal (ws size gacc::off gacc::base skel gacc::spec)
                  (ws size gacc::off 0 skel gacc::spec)))
  :hints (("Goal" :in-theory (enable ws))))


(defthm open-ws
  (and
   (implies
    (consp spec)
    (equal (ws size off base skel spec)
           (let ((slot (car spec)))
             (if (and (slot-p slot)
                      (equal :ptr (slot-type slot))
                      (compare base size off (slot-size slot) (slot-off slot)))
                 (cons (update-slot slot :skel (fix-skel skel))
                       (cdr spec))
               (cons slot
                     (ws size off base skel (cdr spec)))))))
   (implies
    (not (consp spec))
    (equal (ws size off base skel spec) spec))))

(in-theory
 (disable
  (:definition ws)
  ))

(defun wv (size off base val spec)
  (declare (type t size off val spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (and (slot-p slot)
                 (compare base size off (slot-size slot) (slot-off slot)))
            (cons (update-slot slot :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                (ifix val)))
                  (cdr spec))
          (cons slot
                (wv size off base val (cdr spec)))))
    spec))

(defthm open-wv
  (and
   (implies
    (consp spec)
    (equal (wv size off base val spec)
           (let ((slot (car spec)))
             (if (and (slot-p slot)
                      (compare base size off (slot-size slot) (slot-off slot)))
                 (cons (update-slot slot :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                     val))
                       (cdr spec))
               (cons slot
                     (wv size off base val (cdr spec)))))))
   (implies
    (not (consp spec))
    (equal (wv size off base skel spec) spec))))

(in-theory (disable (:definition wv)))

(defmacro keys-spec (w base spec)
  `(f*-spec (op ,w :x) ,base (v0 (split-blk (h*-spec (op :nil :z) ,spec)))))

(defthm rs-over-wv
  (equal (rs rsize roff base (wv wsize woff base value spec))
         (rs rsize roff base spec)))

(defthm rv-over-ws
  (equal (rv rsize roff base (ws wsize woff base value spec))
         (rv rsize roff base spec)))

(defthm rs-over-ws
  (implies
   (not (compare base rsize roff wsize woff))
   (equal (rs rsize roff base (ws wsize woff base value spec))
          (rs rsize roff base spec))))

(defthm rv-over-wv
  (implies
   (not (compare base rsize roff wsize woff))
   (equal (rv rsize roff base (wv wsize woff base value spec))
          (rv rsize roff base spec))))

(defthm rs-of-ws
  (implies
   (memberp (sblk size (+<> off base)) (keys-spec :ptr base spec))
   (equal (rs size off base (ws size off base value spec))
          (fix-skel value))))

(defthm rv-of-wv
  (implies
   (memberp (sblk size (+<> off base)) (keys-spec w base spec))
   (equal (rv size off base (wv size off base value spec))
          (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                 value))))

(defthm vanishing-ws
  (implies
   (not (memberp (sblk size (+<> off base)) (keys-spec :ptr base spec)))
   (equal (ws size off base value spec)
          spec))
  :hints (("goal" :induct (ws size off base value spec))))

(defthm vanishing-wv
  (implies
   (not (memberp (sblk size (+<> off base)) (keys-spec :all base spec)))
   (equal (wv size off base value spec)
          spec))
  :hints (("goal" :in-theory (enable fix-slot)
           :induct (wv size off base value spec))))

(defthm default-rs
  (implies
   (not (memberp (sblk size (+<> off base)) (keys-spec :ptr base spec)))
   (equal (rs size off base spec)
          (skel 0 nil))))

(defthm WEAK-SLOT-P-of-FIX-SLOT
  (WEAK-SLOT-P (FIX-SLOT slot))
  :hints (("Goal" :in-theory (enable fix-slot))))

(defthm default-rv
  (implies
   (not (memberp (sblk size (+<> off base)) (keys-spec :all base spec)))
                 (equal (rv size off base spec)
                        0))
  :hints (("Goal" :in-theory (enable fix-slot))))

(defthm ws-of-ws
  (implies
   (compare base s1 o1 s2 o2)
   (equal (ws s1 o1 base v1 (ws s2 o2 base v2 spec))
          (ws s1 o1 base v1 spec))))

(defthm wv-of-wv
  (implies
   (compare base s1 o1 s2 o2)
   (equal (wv s1 o1 base v1 (wv s2 o2 base v2 spec))
          (wv s1 o1 base v1 spec))))

(local
 (defthm ws-over-ws
   (implies
    (syntaxp (not (acl2::term-order p1 p2)))
    (equal (ws s1 p1 base v1 (ws s2 p2 base v2 spec))
           (if (compare base s1 p1 s2 p2)
               (ws s1 p1 base v1 spec)
             (ws s2 p2 base v2 (ws s1 p1 base v1 spec)))))))

(defthm wv-over-wv
  (implies
   (syntaxp (not (acl2::term-order p1 p2)))
   (equal (wv s1 p1 base v1 (wv s2 p2 base v2 spec))
          (if (compare base s1 p1 s2 p2)
              (wv s1 p1 base v1 spec)
            (wv s2 p2 base v2 (wv s1 p1 base v1 spec))))))

(defthm h*-spec-nil-wv
  (implies
   (equal hop (op :nil :z))
   (equal (h*-spec hop (wv size off base val spec))
          (h*-spec hop spec)))
  :hints (("goal" :induct (wv size off base val spec))))

(defthm h*-spec-of-ws
  (implies
   (not (g-op hop))
   (equal (h*-spec hop (ws size off base skel spec))
          (let ((skel (fix-skel skel)))
            (let ((wbase (skel-base skel)))
              (ws size off base (skel (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                             (op-base (op-how hop) :ptr wbase 0))
                                      (h*-spec hop (skel-spec (fix-skel skel))))
                  (h*-spec hop spec))))))
  :hints (("goal" :in-theory (enable ;unfixed-size-wfixn 
                                     g? fix-skel)
           :induct (ws size off base skel spec))))


(defun spec-spec-induction (spec1 spec2)
  (declare (type t spec1 spec2))
  (if (and (consp spec1)
           (consp spec2))
      (spec-spec-induction (cdr spec1) (cdr spec2))
    (cons spec1 spec2)))

(defthm consp-ws
  (equal (consp (ws size off base value spec))
         (consp spec)))

(defthm consp-wv
  (equal (consp (wv size off base value spec))
         (consp spec)))

(defthm non-integerp-wv
  (implies
   (not (integerp off))
   (equal (wv size off base value spec)
          (wv size 0 base value spec))))

(defthm non-integerp-ws
  (implies
   (not (integerp off))
   (equal (ws size off base value spec)
          (ws size 0 base value spec))))

(defthm unfixed-size-wv
  (implies
   (syntaxp (syntax-unfixed-size size))
   (equal (wv size off base value spec)
          (wv (fix-size size) off base value spec)))
  :hints (("Goal" :in-theory (enable ;UNFIXED-SIZE-WFIXN
                                     ))))

(defthm unfixed-size-rv
  (implies
   (syntaxp (syntax-unfixed-size wsize))
   (equal (rv wsize woff base spec)
          (rv (fix-size wsize) woff base spec)))
  :hints (("Goal" :in-theory (enable ;UNFIXED-SIZE-WFIXN
                                     ))))

(defthm unfixed-size-ws
  (implies
   (syntaxp (syntax-unfixed-size size))
   (equal (ws size off base value spec)
          (ws (fix-size size) off base value spec))))

(defthm unfixed-size-rs
  (implies
   (syntaxp (syntax-unfixed-size wsize))
   (equal (rs wsize woff base spec)
          (rs (fix-size wsize) woff base spec))))

;; ==============================================
;;
;; zv
;;
;; ==============================================

(defun zv (list base spec)
  (declare (type t list spec))
  (if (consp list)
      (let ((sblk (car list)))
        (if (and (sblkp sblk) (consp sblk))
            (met ((size off) (sblk-parms base sblk))
                 (let ((spec (wv size off base 0 spec)))
                   (zv (cdr list) base spec)))
          (zv (cdr list) base spec)))
    spec))

(defthm open-zv
  (and
   (implies
    (consp list)
    (equal (zv list base spec)
           (let ((sblk (car list)))
             (if (and (sblkp sblk) (consp sblk))
                 (met ((size off) (sblk-parms base sblk))
                      (let ((spec (wv size off base 0 spec)))
                        (zv (cdr list) base spec)))
               (zv (cdr list) base spec)))))
   (implies
    (not (consp list))
    (equal (zv list base spec) spec))))

(in-theory
 (disable
  (:definition zv)
  ))

(defthm zv-of-wv
  (implies
   (memberp (sblk wsize (+<> woff base)) list)
   (equal (zv list base (wv wsize woff base value spec1))
          (zv list base spec1)))
  :hints (("goal" :induct (zv list base spec1))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (enable ifix list::memberp 
                                            fix-skel)))))




(defthm skel-p-of-slot-skel-of-fix-slot
  (implies (SKEL-P (SLOT-SKEL slot))
           (SKEL-P (SLOT-SKEL (FIX-SLOT slot))))
  :hints (("Goal" :in-theory (enable fix-slot slot-skel SKEL-P slot))))

(defthm slot-p-of-fix-slot
  (implies (SLOT-p slot)
           (SLOT-p (FIX-SLOT slot)))
  :hints (("Goal" :in-theory (enable fix-slot slot-skel SKEL-P slot weak-slot-p))))

(defthm split-blk-when-spec-is-not-a-consp
  (implies (not (consp spec))
           (equal (split-blk spec)
                  (MV SPEC NIL))))

;bzo
(defthm rv-of-cons-one
  (implies (AND (GACC::SLOT-P GACC::SLOT)
                (GACC::COMPARE GACC::BASE GACC::SIZE
                               GACC::OFF (GACC::SLOT-SIZE GACC::SLOT)
                               (GACC::SLOT-OFF GACC::SLOT)))
           (equal (GACC::RV GACC::SIZE GACC::OFF GACC::BASE (cons gacc::slot GACC::SPEC))
                  (acl2::LOGHEAD (GACC::FIX-SIZE GACC::SIZE)
                                 (IFIX (GACC::SLOT-VAL GACC::SLOT)))))
  :hints (("Goal" :in-theory (enable gacc::rv))))

(defthm rv-of-cons-irrel-one
  (implies (not (GACC::SLOT-P GACC::SLOT))
           (equal (GACC::RV GACC::SIZE GACC::OFF GACC::BASE (cons gacc::slot GACC::SPEC))
                  (GACC::RV GACC::SIZE GACC::OFF GACC::BASE GACC::SPEC)))
  :hints (("Goal" :in-theory (enable gacc::rv))))

(defthm rv-of-cons-irrel-two
  (implies (not (GACC::COMPARE GACC::BASE GACC::SIZE
                               GACC::OFF (GACC::SLOT-SIZE GACC::SLOT)
                               (GACC::SLOT-OFF GACC::SLOT)))
           (equal (GACC::RV GACC::SIZE GACC::OFF GACC::BASE (cons gacc::slot GACC::SPEC))
                  (GACC::RV GACC::SIZE GACC::OFF GACC::BASE GACC::SPEC)))
  :hints (("Goal" :in-theory (enable gacc::rv))))
       
(defthm rv-of-cons-both
  (equal (GACC::RV GACC::SIZE GACC::OFF GACC::BASE (cons gacc::slot GACC::SPEC))
         (if  (AND (GACC::SLOT-P GACC::SLOT)
                   (GACC::COMPARE GACC::BASE GACC::SIZE
                                  GACC::OFF (GACC::SLOT-SIZE GACC::SLOT)
                                  (GACC::SLOT-OFF GACC::SLOT)))
             (acl2::LOGHEAD (GACC::FIX-SIZE GACC::SIZE)
                      (IFIX (GACC::SLOT-VAL GACC::SLOT)))
           (GACC::RV GACC::SIZE GACC::OFF GACC::BASE GACC::SPEC)))
  :hints (("Goal" :in-theory (enable gacc::rv))))

(defthm FIXED-SPEC-P-of-non-cons
  (implies (not (consp spec))
           (equal (FIXED-SPEC-P SPEC)
                  t)))

(defthm f*-spec-of-non-cons
  (implies (not (consp spec))
           (equal (F*-SPEC OP PTR SPEC)
                  nil)))

(defun start-of-f*-spec (op ptr slot)
  (IF
   (SLOT-P SLOT)
   (LET
    ((W (OP-WHICH OP)) (H (OP-HOW OP)))
    (LET
     ((OFF (SLOT-OFF SLOT))
      (SIZE (SLOT-SIZE SLOT))
      (TYPE (SLOT-TYPE SLOT))
      (SKEL (SLOT-SKEL SLOT))
      (VALUE (SLOT-VAL SLOT)))
     (LET
      ((READ VALUE))
      (LET
       ((BASE (SKEL-BASE SKEL)))
       (LET
        ((BASE
          (ACL2::LOGHEAD (FIX-SIZE SIZE)
                         (IFIX (OP-BASE H TYPE BASE READ)))))
        (LET
         ((BLK (IF (WHICHTYPE W TYPE)
                   (LIST (SBLK SIZE (|+<>| OFF PTR)))
                   NIL)))
         (LET ((REC (IF (PTR? TYPE)
                        (F*-SPEC OP BASE (SKEL-SPEC SKEL))
                        NIL)))
              (APPEND BLK
                      REC))))))))
   nil))

(defthm f*-spec-of-cons
  (equal (F*-SPEC OP PTR (cons slot SPEC))
         (append (start-of-f*-spec op ptr slot) (F*-SPEC OP PTR SPEC))))




(defthm zv-introduction-left
  (implies (fixed-spec-p spec2)
           (equal (equal (wv wsize woff base value spec1) spec2)
                  (let ((sblk (sblk wsize (+<> woff base))))
                    (and (equal (zv (list sblk) base spec1)
                                (zv (list sblk) base spec2))
                         (implies (memberp sblk (keys-spec :all base spec1))
                                  (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                                                        value) 
                                         (rv wsize woff base spec2)))))))
;  :otf-flg t
  :hints (("goal" ; :in-theory (enable acl2::memberp-of-cons)
           :expand ((RV (FIX-SIZE WSIZE) WOFF BASE SPEC2)
                    (H*-SPEC (OP :NIL :Z) SPEC1)
                    )
           :in-theory (e/d () (;split-blk ;bzo handle this
                              OPEN-H*-SPEC
                              OPEN-F*-SPEC
                               rv
                               slot-p
                               fix
                               SKEL-EXTENSIONALITY!
                               DEFS-SKEL-P-INCLUDES-WEAK-SKEL-P
                               OP-BASE
                               FIXED-SPEC-P
                               EQUAL-SBLK-EXTENSIONALITY
                               VANISHING-WV
                               ACL2::LOGHEAD-UPPER-BOUND
                               ACL2::LOGHEAD-NONNEGATIVE-LINEAR
;             SLOT-EXTENSIONALITY!!
;                       numtype
                               ))
           :induct (spec-spec-induction spec1 spec2)
           :do-not '(generalize eliminate-destructors ;fertilize 
                                eliminate-irrelevance)
           :do-not-induct t)))

;(in-theory (disable unfixed-size-wintn))




;bzo trying disabled. try removing altogether...
(defthmd zv-introduction-right
  (implies
   (fixed-spec-p spec2)
   (equal (equal spec2 (wv wsize woff base value spec1))
          (let ((sblk (sblk wsize (+<> woff base))))
            (and (equal (zv (list sblk) base spec2)
                        (zv (list sblk) base spec1))
                 (implies (memberp sblk (keys-spec :all base spec1))
                          (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                                        value) (rv wsize woff base spec2)))))))
  :hints (("goal" :in-theory (disable zv-introduction-left)

           :use ((:instance zv-introduction-left)))))

(defthm h*-spec-nil-zv
  (implies
   (equal hop (op :nil :z))
   (equal (h*-spec hop (zv list base spec))
          (h*-spec hop spec)))
  :hints (("goal" :induct (zv list base spec))))

(defthm keys-spec-zv
  (equal (keys-spec w base (zv list base spec))
         (keys-spec w base spec)))

(defthm fixed-spec-p-wv
  (implies
   (fixed-spec-p spec)
   (fixed-spec-p (wv size off base value spec)))
  :hints (("goal" :in-theory (enable ;unfixed-size-wintn
                                     ))))

(defthm fixed-spec-p-zv
  (implies
   (fixed-spec-p spec)
   (fixed-spec-p (zv list base spec))))

(defthm fixed-spec-p-ws
  (implies
   (and
    (fixed-spec-p spec)
    (acl2::unsigned-byte-p (gacc::fix-size size) ;wintn 8 size 
           (skel-base skel))
    (fixed-spec-p (skel-spec skel)))
   (fixed-spec-p (ws size off base skel spec)))
  :hints (("goal" 
           :in-theory (enable ;unfixed-size-wintn
                              fix-skel)
           :induct (ws size off base skel spec))))

(defthmd zv-over-wv
  (equal (zv list1 base (wv size off base 0 spec))
         (wv size off base 0 (zv list1 base spec)))
  :hints (("goal" :induct (zv list1 base spec)
           :in-theory (e/d (ifix)
                           (zv-introduction-right
                            zv-introduction-left)))))

;bzo move
;similar rule for wintn?
;; (defthm wfixn-of-fix-size
;;   (equal (acl2::loghead (gacc::fix-size (fix-size wsize)) ;wfixn 8 (fix-size wsize) 
;;                 value)
;;          (wfixn 8 wsize 
;;                 value))
;;   :hints (("Goal" :in-theory (enable unfixed-size-wfixn))))

;(theory-invariant (incompatible (:rewrite wfixn-of-fix-size) (:rewrite unfixed-size-wfixn)))

(encapsulate
 ()

;do we really want all this stuff to be local? 
 (local
  (encapsulate
   ()
   
   (in-theory
    (enable
     zv-over-wv
     ))
   
   (defthm zv-zv
     (equal (zv list1 base (zv list2 base spec))
            (zv list2 base (zv list1 base spec)))
     :hints (("goal" :in-theory (disable zv-introduction-right
                                         zv-introduction-left))))
   
   (defthm zv-concatenation
     (equal (zv list1 base (zv list2 base spec))
            (zv (append list1 list2) base spec))
     :hints (("goal" :in-theory (e/d (binary-append)
                                     (zv-introduction-left zv-introduction-right)))))
   
   (defthm wv-zv-wv
     (equal (wv wsize woff base v1 (zv list base (wv wsize woff base v2 spec)))
            (wv wsize woff base v1 (zv list base spec)))
     :hints (("goal" :induct (zv list base spec)
              :in-theory (e/d ( ;default-car default-cdr
                               )
                              (zv-introduction-left zv-introduction-right)))))
   
   (defthm rv-over-zv
     (implies
      (not (memberp (sblk rsize (+<> roff base)) list))
      (equal (rv rsize roff base (zv list base spec))
             (rv rsize roff base spec)))
     :hints (("goal" :do-not '(generalize eliminate-destructors)
              :in-theory (e/d (ifix memberp 
                                    )
                              ())
              :induct (zv list base spec))))
   
   (defthm wv-under-zv
     (implies
      (not (memberp (sblk wsize (+<> woff base)) list))
      (equal (zv list base (wv wsize woff base value spec))
             (wv wsize woff base value (zv list base spec))))
     :hints (("goal" :induct (zv list base spec)
              :in-theory (e/d (ifix ;default-car default-cdr
                               memberp 
;                               unfixed-size-wfixn
 ;                              unfixed-size-wintn
                               )
                              (zv-introduction-left zv-introduction-right)))))
   
   
   ))
 
;mine
 (defthm zv-induction
   (implies
    (and
     (fixed-spec-p spec2)
     (equal sblk (sblk wsize (+<> woff base)))
     (not (memberp sblk list)))
    (and (equal (equal (zv list base (wv wsize woff base value spec1))
                       (zv list base spec2))
                (and (equal (zv (cons sblk list) base spec1)
                            (zv (cons sblk list) base spec2))
                     (implies (memberp sblk (keys-spec :all base spec1))
                              (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                                            value) (rv wsize woff base spec2)))))
         ))
   :hints (("Goal" :in-theory (e/d (fixed-spec-p-zv wv-under-zv rv-over-zv
                                                    keys-spec-zv zv-introduction-left
                                                    zv-introduction-right
                                                    zv-concatenation 
                                                    list::append-of-cons) 
                                   (vanishing-wv
                                    zv-over-wv
                                    split-blk
                                    open-zv))))
   )



 
 ) ;end the encapsulate

(in-theory
 (disable
  zv-introduction-left
  zv-introduction-right
  zv-induction
  ))

;; ==============================================
;;
;; zs
;;
;; ==============================================

(defun zs (list base spec)
  (declare (type t list spec))
  (if (consp list)
      (let ((sblk (car list)))
        (if (and (sblkp sblk) (consp sblk))
            (met ((size off) (sblk-parms base sblk))
                 (let ((spec (ws size off base (skel 0 nil) spec)))
                   (zs (cdr list) base spec)))
          (zs (cdr list) base spec)))
    spec))

(defthm zs-when-base-is-not-an-integerp
  (implies (not (integerp base))
           (equal (ZS LIST BASE SPEC)
                  (ZS LIST 0 SPEC)))
  :hints (("Goal" :in-theory (disable ;ZS-INTRODUCTION-LEFT ;bzo looped (this lemma was lower down in the file)
                                      ))))
(defthm open-zs
  (and
   (implies
    (consp list)
    (equal (zs list base spec)
           (let ((sblk (car list)))
             (if (and (sblkp sblk) (consp sblk))
                 (met ((size off) (sblk-parms base sblk))
                      (let ((spec (ws size off base (skel 0 nil) spec)))
                        (zs (cdr list) base spec)))
               (zs (cdr list) base spec)))))
   (implies
    (not (consp list))
    (equal (zs list base spec) spec))))

(in-theory
 (disable
  (:definition zs)
  ))

(defthm zs-of-ws
  (implies
   (memberp (sblk wsize (+<> woff base)) list)
   (equal (zs list base (ws wsize woff base value spec1))
          (zs list base spec1)))
  :hints (("goal" :induct (zs list base spec1))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (enable ifix fix-skel memberp)))))

(local
 (defthm not-skel-p-ws
   (implies
    (not (skel-p value))
    (equal (ws size off base value spec)
           (ws size off base (skel 0 nil) spec)))
   :hints (("goal" :in-theory (enable fix-skel))))
 )


#|
;old, slow-proving version
(defthm zs-introduction-left
  (iff (equal (ws wsize woff base value spec1)
              spec2)
       (let ((sblk (sblk wsize (+<> woff base))))
         (and (equal (zs (list sblk) base spec1)
                     (zs (list sblk) base spec2))
              (implies (memberp sblk (keys-spec :ptr base spec1))
                       (equal (fix-skel value) (rs wsize woff base spec2))))))
  :hints (("goal" :induct (spec-spec-induction spec1 spec2))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (enable ;acl2::memberp-of-cons 
                                     slot-extensionality! 
                                     ifix 
                                     fix-skel)))))

|#

(defthm split-blk-when-spec-is-not-a-consp
  (implies (not (consp spec))
           (equal (SPLIT-BLK spec)
                  (mv spec nil))))

(defthm zs-introduction-left
  (equal (equal (ws wsize woff base value spec1) spec2)
         (let ((sblk (sblk wsize (+<> woff base))))
           (and (equal (zs (list sblk) base spec1)
                       (zs (list sblk) base spec2))
                (implies (memberp sblk (keys-spec :ptr base spec1))
                         (equal (fix-skel value) (rs wsize woff base spec2))))))
  :otf-flg t
  :hints (("goal" :induct (spec-spec-induction spec1 spec2))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :expand (;(H*-SPEC (OP :NIL :Z) SPEC1)
                                  )
                         :in-theory (e/d () 
                                         (FIX
                                          ;PTR?
                                          ;split-blk
                                          slot-p
                                          ;efficiency:
                                          ;RS
                                          ;whichtype
                                          ;OPEN-H*-SPEC
                                          VANISHING-WS
                                          op-base
                                          fix-slot
                                          SKEL-EXTENSIONALITY!
                                          DEFS-SKEL-P-INCLUDES-WEAK-SKEL-P
                                          ))))))

;bzo consider dropping (and renaming the -left rule since there'd be no -right rule)
(defthmd zs-introduction-right
  (equal (equal spec2 (ws wsize woff base value spec1))
         (let ((sblk (sblk wsize (+<> woff base))))
           (and (equal (zs (list sblk) base spec2)
                       (zs (list sblk) base spec1))
                (implies (memberp sblk (keys-spec :ptr base spec1))
                         (equal (fix-skel value) (rs wsize woff base spec2))))))
  :hints (("goal" :in-theory (disable zs-introduction-left)
           :use ((:instance zs-introduction-left)))))


(defthm open-split-blk
  (and
   (implies
    (consp spec)
    (equal (split-blk spec)
           (let ((slot (car spec)))
             (if (slot-p slot)
                 (let ((slot (fix-slot slot)))
                   (let ((type (slot-type slot))
                         (skel (slot-skel slot)))
                     (if (ptr? type)
                         (let ((base (skel-base skel)))
                           (let ((line (line base skel)))
                             (let ((slot (update-slot slot :skel (skel base nil))))
                               (met ((spec list) (split-blk (cdr spec)))
                                    (mv (cons slot spec)
                                        (cons line list))))))
                       (met ((spec list) (split-blk (cdr spec)))
                            (mv (cons slot spec) list)))))
               (met ((spec list) (split-blk (cdr spec)))
                    (mv (cons slot spec) list))))))
   (implies
    (not (consp spec))
    (equal (split-blk spec) (mv spec nil)))))

(in-theory
 (disable
  (:definition split-blk)
  ))

(defthm split-sblk-ws
  (equal (f*-spec op ptr (v0 (split-blk (ws size off base value spec))))
         (f*-spec op ptr (v0 (split-blk spec))))
  :hints (("goal" :induct (ws size off base value spec))))

(defthm keys-spec-zs
  (equal (keys-spec w base (zs list base spec))
         (keys-spec w base spec))
  :hints (("goal" :in-theory (enable ifix)
           :induct (zs list base spec))))

(defthm fixed-spec-p-zs
  (implies
   (fixed-spec-p spec)
   (fixed-spec-p (zs list base spec))))


(defthmd zs-over-ws
  (implies 
   (equal value (skel 0 nil))
   (equal (zs list1 base (ws size off base value spec))
          (ws size off base value (zs list1 base spec))))
  :hints (("goal" :induct (zs list1 base spec)
           :in-theory (e/d (ifix)
                           (zs-introduction-right
                            zs-introduction-left)))))

(encapsulate
 ()
 
 (local
  (encapsulate
   ()
   
   (in-theory
    (enable
     zs-over-ws
     ))
   
   (defthm zs-zs
     (equal (zs list1 base (zs list2 base spec))
            (zs list2 base (zs list1 base spec)))
     :hints (("goal" :in-theory (disable zs-introduction-right
                                         zs-introduction-left))))
   
   (defthm zs-concatenation
     (equal (zs list1 base (zs list2 base spec))
            (zs (append list1 list2) base spec))
     :hints (("goal" :in-theory (e/d (binary-append)
                                     (zs-introduction-left zs-introduction-right)))))
   
   (defthm ws-zs-ws
     (equal (ws wsize woff base v1 (zs list base (ws wsize woff base v2 spec)))
            (ws wsize woff base v1 (zs list base spec)))
     :hints (("goal" :induct (zs list base spec)
              :in-theory (e/d ( ;default-car default-cdr
                               )
                              (zs-introduction-left zs-introduction-right)))))




   (defthm rs-over-zs
     (implies
      (not (memberp (sblk rsize (+<> roff base)) list))
      (equal (rs rsize roff base (zs list base spec))
             (rs rsize roff base spec)))
     :hints (("goal" :do-not '(generalize eliminate-destructors)
              :in-theory (e/d (ifix ;SBLK-PARMS 
                               memberp) ( ;UNFIXED-SIZE-WS
;UNFIXED-SIZE-MAX-OFFSET
;UNFIXED-SIZE-SBLK
                               ))
              :induct (zs list base spec))))
   
   (defthm ws-under-zs
     (implies
      (not (memberp (sblk wsize (+<> woff base)) list))
      (equal (zs list base (ws wsize woff base value spec))
             (ws wsize woff base value (zs list base spec))))
     :hints (("goal" :induct (zs list base spec)
              :in-theory (e/d (ifix ;default-car default-cdr
                               memberp)
                              (zs-introduction-left zs-introduction-right)))))
   
   
   ))
 
 (defthm zs-induction
   (implies
    (and
     (equal sblk (sblk wsize (+<> woff base)))
     (not (memberp sblk list)))
    (equal (equal (zs list base (ws wsize woff base value spec1))
                  (zs list base spec2))
           (and (equal (zs (cons sblk list) base spec1)
                       (zs (cons sblk list) base spec2))
                (implies (memberp sblk (keys-spec :ptr base spec1))
                         (equal (fix-skel value) (rs wsize woff base spec2))))))
   :hints (("goal" :in-theory (e/d (fixed-spec-p-zs keys-spec-zs zs-introduction-left
                                                    zs-introduction-right
                                                    zs-concatenation) 
                                   (vanishing-wv
                                    open-zs)))))



 
 )


(in-theory
 (disable
  zs-introduction-left
  zs-introduction-right
  zs-induction
  ))

;; ==============================================
;;
;; zz
;;
;; ==============================================

(defun zz (vlist slist base spec)
  (declare (type t vlist slist spec))
  (let ((spec (zv vlist base spec)))
    (zs slist base spec)))


;I think the failed-location / tag-location stuff gives us debugging information in failed proofs.

(defund failed-location (key) 
  (declare (ignore key)) 
  nil) 

(in-theory (disable (:executable-counterpart failed-location)))
(in-theory (disable (:type-prescription failed-location)))

(defun tag-location (key bool)
  (implies (not bool) (failed-location key)))        

(defthm zz-wv-introduction
  (implies
   (fixed-spec-p spec2)
   (and (equal (equal (wv wsize woff base value spec1)
                      spec2)
               (let ((sblk (sblk wsize (+<> woff base))))
                 (and (equal (zz (list sblk) nil base spec1)
                             (zz (list sblk) nil base spec2))
                      (implies (memberp sblk (keys-spec :all base spec1))
                               (tag-location woff (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                                                                value) 
                                                         (rv wsize woff base spec2)))))))
        ))
  :hints (("goal" :in-theory '(tag-location failed-location zz zs 
                                            zv-introduction-left zv-introduction-right))))


(defthm zz-ws-introduction
  (and (equal (equal (ws wsize woff base value spec1)
                     spec2)
              (let ((sblk (sblk wsize (+<> woff base))))
                (and (equal (zz nil (list sblk) base spec1)
                            (zz nil (list sblk) base spec2))
                     (implies (memberp sblk (keys-spec :ptr base spec1))
                              (tag-location woff (equal (fix-skel value) 
                                                        (rs wsize woff base spec2)))))))
;;        (equal (equal spec2
;;                      (ws wsize woff base value spec1))
;;               (let ((sblk (sblk wsize (+<> woff base))))
;;                 (and (equal (zz nil (list sblk) base spec2)
;;                             (zz nil (list sblk) base spec1))
;;                      (implies (memberp sblk (keys-spec :ptr base spec1))
;;                               (tag-location woff (equal (rs wsize woff base spec2) 
;;                                                         (fix-skel value)))))))
       )
  :hints (("goal" :in-theory '(tag-location failed-location zz zv 
                                            zs-introduction-left zs-introduction-right))))

(in-theory
 (disable
  zz-wv-introduction
  zz-ws-introduction
  ))

(defthm ws-wv
  (equal (wv s1 o1 base v1 (ws s2 o2 base v2 spec))
         (ws s2 o2 base v2 (wv s1 o1 base v1 spec))))

(defthm zv-over-ws
  (equal (zv list base (ws wsize woff base value spec))
         (ws wsize woff base value (zv list base spec)))
  :hints (("goal" :induct (zv list base spec))))

(defthm zs-over-wv
  (equal (zs list base (wv wsize woff base value spec))
         (wv wsize woff base value (zs list base spec)))
  :hints (("goal" :induct (zs list base spec))))


(defthm rs-zv
  (equal (rs rsize roff base (zv list base spec))
         (rs rsize roff base spec))
  :hints (("goal" :induct (zv list base spec))))

(defthm rv-zs
  (equal (rv rsize roff base (zs list base spec))
         (rv rsize roff base spec))
  :hints (("goal" :induct (zs list base spec))))

(defthm zz-ws-induction
  (implies
   (and
    (equal sblk (sblk wsize (+<> woff base)))
    (not (memberp sblk slist)))
   (and (equal (equal (zz vlist slist base (ws wsize woff base value spec1))
                      (zz vlist slist base spec2))
               (and (equal (zz vlist (cons sblk slist) base spec1)
                           (zz vlist (cons sblk slist) base spec2))
                    (implies (memberp sblk (keys-spec :ptr base spec1))
                             (tag-location woff (equal (fix-skel value) 
                                                       (rs wsize woff base spec2))))))
;;         (equal (equal (zz vlist slist base spec2)
;;                       (zz vlist slist base (ws wsize woff base value spec1)))
;;                (and (equal (zz vlist (cons sblk slist) base spec2)
;;                            (zz vlist (cons sblk slist) base spec1))
;;                     (implies (memberp sblk (keys-spec :ptr base spec1))
;;                              (tag-location woff (equal (fix-skel value) 
;;                                                        (rs wsize woff base spec2))))))
        ))
  :hints (("goal" :in-theory '(tag-location failed-location zz 
                                            zv-over-ws zs-induction rs-zv keys-spec-zv))))

(defthm zs-over-zv
  (equal (zs slist base (zv vlist base spec))
         (zv vlist base (zs slist base spec))))

(defthm zv-over-zs
  (equal (zv vlist base (zs slist base spec))
         (zs slist base (zv vlist base spec))))

(in-theory
 (disable
  zv-over-zs
  ))

(theory-invariant 
 (incompatible 
  (:rewrite zs-over-zv)
  (:rewrite zv-over-zs)
  ))

(defthm zz-wv-induction
  (implies
   (and
    (equal sblk (sblk wsize (+<> woff base)))
    (fixed-spec-p spec2)
    (not (memberp sblk vlist)))
   (and (equal (equal (zz vlist slist base (wv wsize woff base value spec1))
                      (zz vlist slist base spec2))
               (and (equal (zz (cons sblk vlist) slist base spec1)
                           (zz (cons sblk vlist) slist base spec2))
                    (implies (memberp sblk (keys-spec :all base spec1))
                             (tag-location woff (equal (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                                                                      value
                                                                      )
                                                       (rv wsize woff base spec2))))))
        ))
  :hints (("goal" :in-theory '(tag-location failed-location zz 
                                            fixed-spec-p-zs
                                            zs-over-zv 
                                            zs-over-wv 
                                            zv-induction 
                                            rv-zs 
                                            keys-spec-zs))))

;              ))

(in-theory 
 (disable 
  failed-location
  (:type-prescription failed-location)
  (failed-location)
  ))

(in-theory
 (disable
  unfixed-size-wv
  unfixed-size-rv
  unfixed-size-ws
  unfixed-size-rs
  ))

(in-theory
 (disable
  open-wv
  open-ws
  rv-zs
  rs-zv
  zs-over-ws
  zv-over-ws
  vanishing-ws
  default-rs
  default-rv
  zz
  ))

;; For efficiency ..

(in-theory
 (disable
  wv-of-wv
  ws-of-ws
  ws-wv
  ))

(in-theory
 (enable
  zz-wv-introduction
  zz-ws-introduction
  zz-wv-induction
  zz-ws-induction
  ))

;;
;; f*/ws-wv
;;

(defmacro strip (spec)
  `(h*-spec (op :nil :x) ,spec))

(defthm f*-spec-wv
  (implies
   (not (memberp (sblk wsize (+<> woff base)) (keys-spec :ptr base spec)))
   (equal (f*-spec fop ptr (wv wsize woff base value spec))
          (f*-spec fop ptr spec)))
  :hints (("goal" :induct (wv wsize woff base value spec)
           :in-theory (enable open-wv memberp))))

;(in-theory (enable unfixed-size-wfixn))
;(in-theory (enable unfixed-size-wintn))

(defthm f*-spec-x-ws
  (implies
   (and
    (x? fop)
    (equal v (rs wsize woff base spec))
    (equal (f*-spec fop (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                               (skel-base (fix-skel skel))) (skel-spec (fix-skel skel)))
           (f*-spec fop (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                               (skel-base v)) (skel-spec v)))
    )
   (equal (f*-spec fop ptr (ws wsize woff base skel spec))
          (f*-spec fop ptr spec)))
  :hints (("goal'" :induct (ws wsize woff base skel spec)
           :in-theory (e/d (;unfixed-size-wfixn unfixed-size-wintn
                                               ) (;WFIXN-OF-FIX-SIZE
                                                  ))
           )
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (e/d (;unfixed-size-wfixn unfixed-size-wintn 
                                                             open-ws) (;WFIXN-OF-FIX-SIZE
                                                                       ))
                         ))))

;;
;; h*/ws-wx
;;

(defthm h*-spec-of-wv
  (implies
   (and
    (equal (op-which hop) :nil)
    (not (g-op hop)))
   (equal (h*-spec hop (wv wsize woff base value spec))
          (h*-spec hop spec)))
  :hints (("goal" :induct (wv wsize woff base value spec)
           :in-theory (e/d (g? open-wv) (zz-wv-introduction)))))

(defthm h*-spec-over-wv
  (implies
   (and
    (equal (op-which hop) :all)
    (not (g-op hop)))
   (equal (h*-spec hop (wv wsize woff base value spec))
          (wv wsize woff base (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                                             value) (h*-spec hop spec))))
  :hints (("goal" :induct (wv wsize woff base value spec)
           :in-theory (e/d (g? open-wv ;unfixed-size-wfixn
                               )
                           (zz-wv-introduction
;                            WFIXN-OF-FIX-SIZE
                            )))))

;;  ; was called wintn-rs for some reason
;; (defthm wintn-rv
;;   (wintn 8 size (rv size off base spec))
;;   :hints (("Goal" :in-theory (enable UNFIXED-SIZE-WINTN))))

(defthm fixed-spec-p-rs
  (implies
   (fixed-spec-p spec)
   (and (fixed-spec-p (skel-spec (rs size off base spec)))
        (acl2::unsigned-byte-p (gacc::fix-size size) ;wintn 8 size 
               (skel-base (rs size off base spec)))))
  :hints (("goal" :in-theory (enable ;UNFIXED-SIZE-WINTN
                                      )
           :induct (rs size off base spec))))

(in-theory (disable wv-over-wv))

;eric added the next 2. are they okay?
(defthm ws-of-rs-helper
  (equal (ws size off base (rs size off base spec) spec)
         spec))

(defthm wv-of-rv-helper
  (implies (fixed-spec-p spec);t; (WINTN 8 32 (SLOT-VAL (CAR SPEC)))
           (equal (wv size off base (rv size off base spec) spec)
                  spec)))
