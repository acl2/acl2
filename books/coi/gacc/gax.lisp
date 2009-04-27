#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;; Keep this list of include-books in sync with the list in the .acl2 file:

(include-book "gacc2")
(include-book "gacc")
(include-book "../util/mv-nth")

;(local (in-theory (disable bag::SUBBAGP-DISJOINT bag::SUBBAGP-DISJOINT-commute)))
(local (in-theory (disable acl2::S-EQUAL-DIFFERENTIAL)))

;try
(local (in-theory (disable RX-NON-NEGATIVE-LINEAR ACL2::LOGHEAD-UPPER-BOUND)))

(local (in-theory (disable 
;                   ACL2::LOGAND-WITH-MASK-ERIC
                   ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                   ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                   ACL2::LOGHEAD-LEQ
                   acl2::NOT-EVENP-FORWARD-TO-ODDP
                   ACL2::EVENP-FORWARD-TO-NOT-ODDP
  ;                 ACL2::LOGBITP-FORWARD-TO-LOGBIT-ONE
 ;                  ACL2::LOGBITP-FORWARD-TO-LOGBIT-zero
                   BAG::ZP-NFIX
                   )))

(in-theory (disable ifix))

(defmacro skipper (&rest args)
  `(progn
     ,@args
     ))

(defun which-covers (w1 w2)
  (declare (type t w1 w2))
  (let ((nw1 (numwhich w1))
        (nw2 (numwhich w2)))
    (equal nw2 (logand nw1 nw2))))

(defun wop-covers (op1 op2)
  (declare (type (satisfies op-p) op1 op2))
  (let ((w1 (op-which op1))
        (w2 (op-which op2)))
    (let ((nw1 (numwhich w1))
          (nw2 (numwhich w2)))
      (equal nw2 (logand nw1 nw2)))))

(local (in-theory (disable nfix))) ;trying...



;(in-theory (disable mv-nth))

;bzo
(in-theory
 (disable
  (:DEFINITION LOGBITP)
  (:DEFINITION ODDP)
  (:DEFINITION EVENP)
  (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT)
  (:DEFINITION ACL2::INTEGER-RANGE-P)
  (:DEFINITION ACL2::BINARY-LOGAND)
  (:DEFINITION FLOOR)
  (:DEFINITION ACL2::UNSIGNED-BYTE-P)
  ))

(in-theory
 (disable
  (:TYPE-PRESCRIPTION PERM)
  (:REWRITE bag::PERM-NIL-Y)
;  (:FORWARD-CHAINING bag::PERM-NOT-CONSP-NIL)
  ))

(in-theory (disable (op)))

(in-theory (enable slot-p))

(in-theory (enable skel-extensionality!))

(local (in-theory (disable skel-extensionality!)))

(in-theory (disable max-offset)) 
(local (in-theory (disable slot-p))) 

(defthm slot-extensionality!!
  (implies
   (skel-p skel)
   (and (equal (equal x (slot name off size val type skel))
               (and (slot-p x)
                    (equal (slot-name x) name)
                    (equal (slot-off  x) off)
                    (equal (slot-size x) size)
                    (equal (slot-val  x) val)
                    (equal (slot-type x) type)
                    (equal (slot-skel x) skel)))
;;         (equal (equal (slot name off size val type skel) x)
;;                (and (slot-p x)
;;                     (equal name (slot-name x) )
;;                     (equal off  (slot-off  x) )
;;                     (equal size (slot-size x) )
;;                     (equal val  (slot-val  x) )
;;                     (equal type (slot-type x) )
;;                     (equal skel (slot-skel x) )))
        ))
  :hints (("goal" :in-theory (enable ; slot-skel 
; slot-name 
;slot-off 
;slot-size 
;slot-val 
;slot-type 
;slot 
;slot-p
;weak-slot-p
                              ))))

(defthm h*-spec-g*-spec-track
  (and (implies (consp (h*-spec hop spec))
                (consp (g*-spec gop gptr spec ram)))
       (implies (not (consp (h*-spec hop spec)))
                (not (consp (g*-spec gop gptr spec ram)))))
  :hints (("goal" :induct (len spec) :in-theory (enable (:induction len)))))





(in-theory 
 (enable 
  (:induction g*-spec)
  (:induction f*-spec)
  (:induction h*-spec)
  (:induction s*-spec)
  ))

(in-theory 
 (enable 
;;  wx-of-rx 
  ))

(defun which-union (w1 w2)
  (let ((n1 (numwhich w1))
        (n2 (numwhich w2)))
    (let ((n (logand #x3 (logior n1 n2))))
      (case n
            (3 :all)
            (2 :ptr)
            (1 :val)
            (t :nil)))))

(defun how-which (op1)
  (if (equal (op-how op1) :x) :nil :ptr))

(defun f*-g* (op)
  (op (which-union (how-which op) (op-which op)) :x))

(defun g? (how)
  (and (not (equal how :x))
       (not (equal how :z))))

(defun g-op (op)
  (g? (op-how op)))

(defun x-op (op)
  (not (g? (op-how op))))

(defun g*-wx (op)
  (if (or (equal (op-how op) :x)
          (equal (op-how op) :z)) op
    (op (which-union (how-which op)
                     (op-which op))
        :x)))

(defthm numtype-when-not-pointer
  (implies (not (equal :ptr type))
           (equal (numtype type)
                  1)))

(defthm numtype-when-ptr
  (implies (ptr? type)
           (equal (numtype type)
                  2)))

(defthm g*-spec-over-wx
  (implies
   (and
    (disjoint
     (sblk wsize wptr)
     (flat (f*-spec (g*-wx gop) gptr (if (g-op gop) (g*-spec gop gptr gspec ram) gspec))))
    )
   (equal (g*-spec gop gptr gspec (wx wsize wptr wvalue ram))
          (g*-spec gop gptr gspec ram)))
  :hints (("goal" :induct (g*-spec gop gptr gspec ram)
           :in-theory (e/d (bag::flat-of-cons)
                           (numwhich
                            numtype
                            ;; which-union
                            ;; op-base
                            ))
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t)))



(defthm g*-spec-g-over-wx
  (implies
   (and
    (g-op gop)
    (equal v (g*-spec gop gptr gspec ram))
    (disjoint
     (sblk wsize wptr)
     (flat (f*-spec (g*-wx gop) gptr v)))
    )
   (equal (g*-spec gop gptr gspec (wx wsize wptr wvalue ram))
          v)))

(defthm g*-spec-x-over-wx
  (implies
   (and
    (x-op gop)
    (disjoint
     (sblk wsize wptr)
     (flat (f*-spec gop gptr gspec)))
    )
   (equal (g*-spec gop gptr gspec (wx wsize wptr wvalue ram))
          (g*-spec gop gptr gspec ram))))
  
;;
;; For efficiency, we usually want either x or g.
;;

(in-theory
 (disable
  g*-spec-over-wx
  ))

(defthm rx-over-s*-spec
  (implies
   (disjoint
    (sblk rsize rptr)
    (flat (f*-spec sop sptr sspec)))
   (equal (rx rsize rptr (s*-spec sop sptr sspec ram))
          (rx rsize rptr ram)))
  :hints (("goal" :in-theory (e/d (bag::flat-of-cons ;bzo
;                                   wx-of-rx
                                   ) 
                                  (numwhich
                                   numtype
                                   op-base
                                   whichtype
                                   ptr?
                                   ))
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :induct (s*-spec sop sptr sspec ram))
          ))

(defthm s*-spec-over-wx
  (implies
   (disjoint
    (sblk wsize wptr)
    (flat (f*-spec sop sptr sspec)))
   (equal (s*-spec sop sptr sspec (wx wsize wptr wvalue ram))
          (wx wsize wptr wvalue (s*-spec sop sptr sspec ram))))
  :hints (("goal" :in-theory (e/d (bag::flat-of-cons ;wx-of-rx
                                                     ) (numwhich numtype op-base whichtype ptr?))
           :induct (s*-spec sop sptr sspec ram)
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t)
          ))

(defthm s*-list-over-wx
  (implies
   (disjoint
    (sblk wsize wptr)
    (flat (f*-list sop sspec)))
   (equal (s*-list sop sspec (wx wsize wptr wvalue ram))
          (wx wsize wptr wvalue (s*-list sop sspec ram))))
  :hints (("goal" :in-theory (enable s*-list)
           :induct (s*-list sop sspec ram))))

(defthm s*-spec-over-s*-spec
  (implies
   (disjoint
    (flat (f*-spec sop1 sptr1 sspec1))
    (flat (f*-spec sop2 sptr2 sspec2)))
   (equal (s*-spec sop1 sptr1 sspec1 (s*-spec sop2 sptr2 sspec2 ram))
          (s*-spec sop2 sptr2 sspec2 (s*-spec sop1 sptr1 sspec1 ram))))
  :hints (("goal" :in-theory (e/d (bag::flat-of-cons ;bzo. prove a meta rule to handle this?
                                   ;wx-of-rx
                                     ) 
                                  (numwhich numtype op-base whichtype ptr?))
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :induct (s*-spec sop2 sptr2 sspec2 ram))
          ))

(defthm op-base-lemma-1
  (implies (not (EQUAL TYPE :PTR))
           (equal (OP-BASE H TYPE BASE VALU)
                  base)))

(defthm S*-SPEC-when-ptr-is-not-an-integerp
  (implies (not (integerp ptr))
           (equal (S*-SPEC OP PTR SPEC RAM)
                  (S*-SPEC OP 0 SPEC RAM)))
  :hints (("Goal" :in-theory (e/d (S*-SPEC ifix) (numwhich numtype op-base ptr? whichtype)))))

(defthm wx-when-v-is-not-an-integerp
  (implies (not (integerp v))
           (equal (WX SIZE A V RAM)
                  (WX SIZE A 0 RAM)))
  :hints (("Goal" :in-theory (enable wx))))

(defthm g*-spec-over-s*-spec
  (implies (and (g-op gop)
                (equal v (g*-spec gop gptr gspec ram))
                (disjoint (flat (f*-spec sop sptr sspec))
                          (flat (f*-spec (f*-g* gop) gptr v))))
           (equal (g*-spec gop gptr gspec (s*-spec sop sptr sspec ram))
                  v))
  :hints (("goal" :induct (s*-spec sop sptr sspec ram)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :expand ((F*-SPEC SOP 0 SSPEC)
                    (F*-SPEC SOP SPTR SSPEC))
           :in-theory (e/d (BAG::FLAT-OF-CONS) 
                           (ptr?
                            ;;g?
                            ;;whichtype
                            WHICH-UNION ;helped a lot
                            ;;G*-WX
                            numwhich ;this made a huge difference
                            NUMTYPE ;this made a big difference
                            HOW-WHICH ;did this hurt things?
                            op-base
                            ATOMIC-S*-OP-REPLACEMENT
                            ATOMIC-F*-OP-REPLACEMENT
                            ATOMIC-G*-OP-REPLACEMENT
                            OPEN-F*-SPEC
                            ;; bag::memberp-implies-subbagp-flat 
                            ;; bag::subbagp-disjoint-commute 
                            ;; s*-spec-over-wx 
                            ;; skel-extensionality! 
                            ;; bag::subbagp-implies-membership
                            ;; WX-OF-RX
                            ;; ACL2::LOGAND-WITH-MASK-ERIC
                            ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                            ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                            ACL2::LOGHEAD-LEQ
                            BINARY-APPEND  ;bzo
                            ;;disable more fwc rules?
                            acl2::NOT-EVENP-FORWARD-TO-ODDP
                            ACL2::EVENP-FORWARD-TO-NOT-ODDP
                            ;; ACL2::LOGBITP-FORWARD-TO-LOGBIT-ONE
                            ;; ACL2::LOGBITP-FORWARD-TO-LOGBIT-zero
                            BAG::ZP-NFIX
                            ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                            ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                            ACL2::LOGHEAD-LEQ
                            )))))


(defthm x*-spec-over-s*-spec
  (implies
   (and
    (x-op gop)
    (disjoint
     (flat (f*-spec sop sptr sspec))
     (flat (f*-spec gop gptr gspec))))
   (equal (g*-spec gop gptr gspec (s*-spec sop sptr sspec ram))
          (g*-spec gop gptr gspec ram)))
  :hints (("goal" :induct (s*-spec sop sptr sspec ram)
           :do-not-induct t
           :do-not '(generalize ;preprocess 
                     eliminate-destructors fertilize eliminate-irrelevance)
           :in-theory (e/d (bag::flat-of-cons) (;for efficiency:
                                                numwhich
                                                g?
                                                ;x-op
                                                ptr?
                                                whichtype
                                                numtype
                                                op-base)))))

(defun subwhich (w1 w2)
  (let ((n1 (numwhich w1))
        (n2 (numwhich w2)))
    (let ((n (logand n1 (lognot n2))))
      (whichnum n))))

(in-theory (disable g?))

(defun s*-g*-equal-induction (gop gptr gspec sop sptr sspec ram)
  (if (and (consp gspec)
           (consp sspec))
      (let ((gslot (car gspec))
            (sslot (car sspec)))
        (if (and (slot-p gslot)
                 (slot-p sslot))
            (let ((gw (op-which gop))
                  (gh (op-how   gop))
                  (sw (op-which sop))
                  (sh (op-how   sop)))
              (let ((goff   (slot-off  gslot))
                    (gsize  (slot-size gslot))
                    (gtype  (slot-type gslot))
                    (gskel  (slot-skel gslot))
                    (gvalue (slot-val  gslot))
                    (soff   (slot-off  sslot))
                    (ssize  (slot-size sslot))
                    (stype  (slot-type sslot))
                    (sskel  (slot-skel sslot))
                    (svalue (slot-val  sslot))
                    )
                (let ((gread (rx gsize (+<> goff gptr) ram))
                      (sread svalue))
                  (let ((gbase (skel-base gskel))
                        (sbase (skel-base sskel)))
                    (let ((gbase (acl2::loghead (gacc::fix-size gsize) ;wfixn 8 gsize 
                                        (op-base gh gtype gbase gread)))
                          (sbase (acl2::loghead (gacc::fix-size ssize) ;wfixn 8 ssize 
                                        (op-base sh stype sbase sread))))
                      (let ((gvalue (acl2::loghead (gacc::fix-size gsize) ;wfixn 8 gsize 
                                                   (if (whichtype gw gtype) gread gvalue)))
                            (svalue (acl2::loghead (gacc::fix-size ssize) ;wfixn 8 ssize 
                                                   (if (whichtype sw stype) svalue 
                                                     (rx ssize (+<> soff sptr) ram)))))
                        (let ((gskel (update-skel gskel :base gbase)))
                          (let ((ram (wx ssize (+<> soff sptr) svalue ram)))
                            (met ((gspex ramx) (s*-g*-equal-induction 
                                                gop gbase (skel-spec gskel)
                                                sop sbase (skel-spec sskel) ram))
                                 (let ((gskelx (skel gbase gspex)))
                                   (let ((gskel (if (ptr? gtype) gskelx gskel))
                                         (ram   (if (ptr? stype) ramx ram)))
                                     (met ((gspex sram) (s*-g*-equal-induction
                                                         gop gptr (cdr gspec)
                                                         sop sptr (cdr sspec) ram))
                                          (mv (cons (update-slot gslot
                                                                 :val  gvalue
                                                                 :skel gskel
                                                                 )
                                                    gspex)
                                              sram)))))))))))))
          (if (and (not (slot-p gslot))
                   (not (slot-p sslot)))
              (s*-g*-equal-induction gop gptr (cdr gspec)
                                     sop sptr (cdr sspec) ram)
            (mv nil (s*-spec sop sptr sspec ram)))))
    (if (consp sspec)
        (mv nil (s*-spec sop sptr sspec ram))
      (mv nil ram))))

(defthm mv-nth-s*-g*-equal-induction
  (equal (v1 (s*-g*-equal-induction gop gbase gspec sop sbase sspec ram))
         (s*-spec sop sbase sspec ram))
  :hints (("goal" :induct (s*-g*-equal-induction gop gbase gspec sop sbase sspec ram)
           :do-not-induct t
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :in-theory (disable ;efficiency:
                       numwhich numtype op-base ptr?))))



(defun f*-f*-induction (aop aptr aspec bop bptr bspec)
  (if (and (consp aspec)
           (consp bspec))
      (let ((aslot (car aspec))
            (bslot (car bspec)))
        (if (and (slot-p aslot)
                 (slot-p bslot))
            (let ((aw (op-which aop))
                  (ah (op-how   aop))
                  (bw (op-which bop))
                  (bh (op-how   bop)))
              (let ((aoff  (slot-off  aslot))
                    (asize (slot-size aslot))
                    (atype (slot-type aslot))
                    (askel (slot-skel aslot))
                    (avalue (slot-val aslot))
                    (boff  (slot-off  bslot))
                    (bsize (slot-size bslot))
                    (btype (slot-type bslot))
                    (bskel (slot-skel bslot))
                    (bvalue (slot-val bslot)))
                (let ((aread avalue)
                      (bread bvalue))
                  (let ((abase (skel-base askel))
                        (bbase (skel-base bskel)))
                    (let ((abase (acl2::loghead (gacc::fix-size asize) ;wfixn 8 asize 
                                                (op-base ah atype abase aread)))
                          (bbase (acl2::loghead (gacc::fix-size bsize) ;wfixn 8 bsize 
                                                (op-base bh btype bbase bread))))
                      (let ((ablk (if (whichtype aw atype) (sblk asize (+<> aoff aptr)) nil))
                            (bblk (if (whichtype bw btype) (sblk bsize (+<> boff bptr)) nil)))
                        (let ((recx (f*-f*-induction aop abase (skel-spec askel)
                                                     bop bbase (skel-spec bskel))))
                          (append ablk bblk
                                  recx
                                  (f*-f*-induction aop aptr (cdr aspec)
                                                   bop bptr (cdr bspec))))))))))
          (if (and (not (slot-p aslot))
                   (not (slot-p bslot)))
              (f*-f*-induction aop aptr (cdr aspec)
                               bop bptr (cdr bspec))
            (list aop aptr aspec
                  bop bptr bspec))))
    (list aop aptr aspec
          bop bptr bspec)))

(local (in-theory (disable LIST::LEN-OF-CDR)))
(local (in-theory (enable len))) 

(defthm len-f*-spec-under-h*-spec-equality
  (implies (equal (h*-spec hop fspec)
                  (h*-spec hop hspec))
           (equal (equal (len (f*-spec fop fptr fspec))
                         (len (f*-spec fop hptr hspec)))
                  t))
  :hints (("goal" :induct (f*-f*-induction fop fptr fspec fop hptr hspec)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :in-theory (disable ;for efficiency:
                       ptr? OP-BASE numwhich numtype whichtype
                       )
           :do-not-induct t)))


;causes a case-split.
(defthm logbitp-1-of-numwhich
  (equal (LOGBITP 1 (NUMWHICH which))
         (or (equal :all which)
             (equal :ptr which))))


(defthm f*-spec-under-h*-spec-equality
  (implies
   (and
    (x-op fop)
    (equal (h*-spec hop fspec)
           (h*-spec hop hspec))
    (syntaxp (not (acl2::term-order fspec hspec)))
    (x? hop)
    )
   (equal (f*-spec fop fptr fspec)
          (f*-spec fop fptr hspec)))
  :hints (("goal" :induct (f*-f*-induction fop fptr fspec fop fptr hspec)
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?
                            ) ( ;;for efficiency:
                            numwhich 
                            numtype
                            whichtype
                            ;;op-base
                            )))))

(defun w-not (w)
  (whichnum (logand #x3 (lognot (numwhich w)))))

(defun wop-not (op)
  (update-op op :which (w-not (op-which op))))

(defun wall (op)
  (update-op op :which :all))

;; (encapsulate
;;  ()
;;  (local (include-book "../super-ihs/logical-logops"))
;; ;bzo
;;  (DEFTHM ACL2::LOGAND-WITH-MASK-ERIC-constant-version
;;    (IMPLIES (and (syntaxp acl2::mask)
;;                  (ACL2::LOGMASKP ACL2::MASK))
;;             (EQUAL (LOGAND ACL2::MASK ACL2::I)
;;                    (ACL2::LOGHEAD (INTEGER-LENGTH ACL2::MASK)
;;                                   ACL2::I)))
;;    :hints (("Goal" :in-theory (enable ACL2::LOGAND-WITH-MASK-ERIC))))

;; ;Bbzo this has been replaced!
;; ;and now we're including all of super-ihs anyway?
;; ;try to not have this book rely on this...
;;  (DEFTHM
;;    ACL2::EQUAL-LOGAND-EXPT-REWRITE
;;    (IMPLIES (AND (SYNTAXP (QUOTEP ACL2::N))
;;                  (EQUAL (EXPT 2 (1- (INTEGER-LENGTH ACL2::N)))
;;                         ACL2::N)
;;                  (INTEGERP ACL2::N)
;;                  (INTEGERP ACL2::X)
;;                  (INTEGERP ACL2::K))
;;             (EQUAL (EQUAL (LOGAND ACL2::N ACL2::X) ACL2::K)
;;                    (IF (LOGBITP (1- (INTEGER-LENGTH ACL2::N))
;;                                 ACL2::X)
;;                        (EQUAL ACL2::K ACL2::N)
;;                        (EQUAL ACL2::K 0))))
;;    :HINTS
;;    (("goal"
;;      :IN-THEORY (ENABLE ACL2::LRDT)
;;      :USE (:INSTANCE ACL2::EQUAL-LOGAND-EXPT
;;                      (ACL2::N (1- (INTEGER-LENGTH ACL2::N))))))))


(defthm usb2-of-numwhich
  (ACL2::UNSIGNED-BYTE-P 2 (NUMWHICH which)))

(defthm usb2-of-numtype
  (ACL2::UNSIGNED-BYTE-P 2 (NUMtype which)))




(defthm logbitp-1-of-numtype
  (equal (LOGBITP 1 (NUMTYPE type))
         (equal :ptr type)))

;bzo gen
(defthm loghead-lognot-hack
  (implies (and (syntaxp (quotep k))
                (acl2::unsigned-byte-p 2 k)
                (integerp x)
;                (integerp n)
 ;               (<= 0 n)
                )
           (equal (EQUAL (ACL2::LOGHEAD 2 (LOGNOT x)) k)
                  (EQUAL (ACL2::LOGHEAD 2 x) (acl2::loghead 2 (lognot k)))))
  :hints (("Goal" :in-theory (enable acl2::loghead acl2::lognot))))

(defthm numtype-equal-own-logcar-rewrite
  (equal (EQUAL (NUMTYPE type) (ACL2::LOGCAR (NUMTYPE type)))
         (not (equal :ptr type))))

(defthm op-base-one
  (equal (OP-BASE :X :PTR base valu)
         base))

(defthm numwhich-cases
  (implies (and (NOT (EQUAL (NUMWHICH which) 0))
                (NOT (EQUAL (NUMWHICH which) 1))
                (NOT (EQUAL (NUMWHICH which) 2)))
           (equal (NUMWHICH which)
                  3))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 0)))
  )



(defthm loghead-of-op-base
  (equal (acl2::loghead n (OP-BASE H TYPE BASE VALU))
         (OP-BASE H TYPE (acl2::loghead n BASE) (acl2::loghead n VALU))))

(defthm whichtype-of-all
  (equal (whichtype :all type)
         t
         ))

(defthm whichnum-equal-all-rewrite
  (equal (EQUAL :ALL (WHICHNUM which))
         (equal 3 which)))

(defthm whichnum-equal-ptr-rewrite
  (equal (EQUAL :ptr (WHICHNUM which))
         (equal 2 which)))

(defthm numwhich-equal-0-rewrite
  (equal (EQUAL (NUMWHICH which) 0)
         (EQUAL which :NIL)))

(defthm numwhich-equal-2-rewrite
  (equal (EQUAL (NUMWHICH which) 2)
         (EQUAL which :ptr)))

(defthm numwhich-equal-3-rewrite
  (equal (EQUAL (NUMWHICH which) 3)
         (EQUAL which :all)))

(defthm numwhich-equal-1-rewrite
  (equal (EQUAL (NUMWHICH which) 1)
         (and (not (equal which :all))
              (not (equal which :ptr))
              (not (equal which :nil)))))
                   

;bzo
(defthm numwhich-of-whichnum
  (implies (acl2::unsigned-byte-p 2 n)
           (equal (numwhich (whichnum n))
                  n)))



(defthm evenp-of-numwhich
  (equal (evenp (numwhich which))
         (or (equal :nil which)
             (equal :ptr which))))

(defthm logcar-of-numwhich
  (equal (equal 0 (acl2::logcar (numwhich which)))
         (or (equal :nil which)
             (equal :ptr which))))

(defthm whichtype-of-nil
  (equal (WHICHTYPE :NIL type)
         nil))


(defthm w-not-equal-all-rewrite
  (equal (EQUAL :ALL (W-NOT w))
         (equal w :nil)))

(defthm w-not-equal-nil-rewrite
  (equal (EQUAL :nil (W-NOT w))
         (equal w :all)))

(defthm w-not-equal-ptr-rewrite
  (equal (EQUAL :ptr (W-NOT w))
         (and (not (EQUAL :val (W-NOT w)))
              (not (EQUAL :nil (W-NOT w)))
              (not (EQUAL :all (W-NOT w)))
              )))

(defthm w-not-equal-val-rewrite
  (equal (equal :val (w-not w))
         (equal :ptr w)))

;; (defthm slot-p-of-slot-forward-chaining
;;   (implies (SKEL-P SKEL)
;;            (slot-p (slot NAME OFF SIZE VAL TYPE SKEL)))
;;   :rule-classes ((:forward-chaining :trigger-terms ((slot NAME OFF SIZE VAL TYPE SKEL)))))

(defthm not-equal-slot-hack-cheap
  (implies (and (not (slot-p blah))
                (SKEL-P SKEL))
           (not (equal blah (slot NAME OFF SIZE VAL TYPE SKEL))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  )

;; (defun double-cdr-induct (a b)
;;   (if (endp a)
;;       (list a b)
;;     (double-cdr-induct (cdr a) (cdr b))))

(defthm subbagp-f*-spec-cdr-lemma
  (implies t ; (subbagp spec spec2)
           (subbagp (f*-spec op ptr (cdr spec)) (f*-spec op ptr spec)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;          :induct (double-cdr-induct spec spec2)
           :expand ((F*-SPEC OP PTR SPEC2))
           :in-theory (disable ATOMIC-F*-OP-REPLACEMENT NUMTYPE numwhich op-base))))


(defthm x*-spec-of-s*-spec
  (implies
   (and
    (x? gop)
    (equal sop gop)
    (equal gptr sptr)
    (unique (flat (f*-spec sop sptr sspec)))
    (equal (h*-spec (wop-not gop) gspec)
           (h*-spec (wop-not gop) sspec)))
   (equal (g*-spec gop gptr gspec (s*-spec sop sptr sspec ram))
          (h*-spec (wall gop) sspec)))
  :hints (("goal" :induct (s*-g*-equal-induction gop gptr gspec sop sptr sspec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :expand (;bzo
                    (F*-SPEC GOP GPTR SSPEC)
                    (:free (op) (H*-SPEC op GSPEC))
                    (:free (op) (H*-SPEC op sSPEC))
                    (S*-SPEC GOP GPTR SSPEC RAM))
           :do-not-induct t
           :in-theory (e/d (bag::flat-of-cons) 
                           ( ;mostly for efficiency:
                            OPEN-F*-SPEC
                            OPEN-G*-SPEC
                            OPEN-S*-SPEC ;didn't help much?
                            OPEN-H*-SPEC
                            ;f*-spec
                            FIXED-SPEC-P
                            ATOMIC-G*-OP-REPLACEMENT
                            ATOMIC-S*-OP-REPLACEMENT
                            ATOMIC-F*-OP-REPLACEMENT
                            numwhich
                            WHICHNUM
                            numtype 
                            op-base
                            which-union
                            binary-append
                            flat
                            w-not
                            ;SKEL-EXTENSIONALITY
                            ;;SLOT-EXTENSIONALITY
                            SLOT-EXTENSIONALITY!!
                            ;;x-op
                            ;;PTR?
                            )))))

(in-theory
 (disable
  f*-spec-under-h*-spec-equality
  len-f*-spec-under-h*-spec-equality
  ))

(defun f*-h*-op (fop hop)
  (if (x? fop)
      (update-op fop :how (op-how hop))
    fop))

(defun w-all? (op)
  (equal (op-which op) :all))

(defthm len-f*-spec-base
  (implies
   (syntaxp (not (quotep fptr)))
   (equal (len (f*-spec fop fptr fspec))
          (len (f*-spec fop 0 fspec)))))

(defun f*-h*-induction (fop fptr hop spec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((hh (op-how   hop))
                  (fh (op-how   fop)))
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((hbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                (op-base hh type base read))))
                      (let ((fbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                  (op-base fh type hbase read))))
                        (let ((skelx (skel fbase (f*-h*-induction fop fbase hop (skel-spec skel)))))
                          (let ((skel (update-skel skel :base fbase)))
                            (let ((skel (if (ptr? type) skelx skel)))
                              (let ((slot (update-slot slot :skel skel)))
                                (cons slot 
                                      (f*-h*-induction fop fptr hop (cdr spec)))))))))))))
          (cons slot
                (f*-h*-induction fop fptr hop (cdr spec)))))
    fptr))
  
(defthm len-f*-spec-of-h*-spec
  (implies
   (w-all? hop)
   (equal (len (f*-spec fop fptr (h*-spec hop spec)))
          (len (f*-spec (f*-h*-op fop hop) fptr spec))))
  :hints (("goal" :induct (f*-h*-induction fop fptr hop spec)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (;F*-H*-OP
                                 numwhich numtype op-base WHICHTYPE ptr? x?)))
          ))

(defthm f*-spec-of-h*-spec
  (implies
   (w-all? hop)
   (equal (f*-spec fop fptr (h*-spec hop spec))
          (f*-spec (f*-h*-op fop hop) fptr spec)))
  :hints (("goal" :induct (f*-h*-induction fop fptr hop spec)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich numtype)))))

(defthm g*-spec-to-h*-spec
  (implies
   (and
    (x? gop)
    (equal (op-which gop) :nil))
   (equal (g*-spec gop gptr gspec ram)
          (h*-spec (wall gop) gspec)))
  :hints (("goal" :induct (g*-spec gop gptr gspec ram))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         ))))

(defun which-intersect (op1 op2)
  (declare (type (satisfies op-p) op1 op2))
  (let ((nw1 (numwhich (op-which op1)))
        (nw2 (numwhich (op-which op2))))
    (let ((nw (logand nw1 nw2)))
      (whichnum nw))))

(defun h*-h*-op (op1 op2)
  (declare (type (satisfies op-p) op1 op2))
  (let ((op1 (if (x? op1) (update-op op1 :how (op-how op2)) op1)))
    (update-op op1 :which (which-intersect op1 op2))))

(defun h*-h*-hyp (op1 op2)
  (implies (or (g-op op1) (g-op op2)) (optype op2 :ptr)))

(defthm logand-equal-3-rewrite
  (implies (and (acl2::unsigned-byte-p 2 x)
                (acl2::unsigned-byte-p 2 y))
           (equal (EQUAL (LOGAND x y) 3)
                  (and (equal x 3)
                       (equal y 3)))))

(defthm h*-spec-of-h*-spec
  (implies
   (h*-h*-hyp op1 op2)
   (equal (h*-spec op1 (h*-spec op2 spec))
          (h*-spec (h*-h*-op op1 op2) spec)))
  :hints (("goal" :induct (h*-spec op2 spec)
           :do-not '(generalize eliminate-destructors 
                                fertilize eliminate-irrelevance)
           :do-not-induct t
           :expand ((H*-SPEC OP2 SPEC))
           :in-theory (e/d (g?) (;numwhich 
                                 ;numtype
                                 ;whichtype
                                 open-h*-spec
                                 ATOMIC-H*-OP-REPLACEMENT
                                 )))))

(defun s*-h*-induction (sop sptr hop spec sram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((sw (op-which sop))
                  (sh (op-how   sop))
                  (hh (op-how   hop)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((hbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                (op-base hh type base read))))
                      (let ((sbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                  (op-base sh type hbase read))))
                        (let ((svalue (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                     (if (whichtype sw type) value (rx size (+<> off sptr) sram)))))
                          (let ((sram (wx size (+<> off sptr) svalue sram)))
                            (let ((sram (if (ptr? type)
                                            (s*-h*-induction sop sbase hop (skel-spec skel) sram)
                                          sram)))
                              (s*-h*-induction sop sptr hop (cdr spec) sram))))))))))
          (s*-h*-induction sop sptr hop (cdr spec) sram)))
    sram))

(defthm s*-h*-induction-reduction
  (implies
   (and
    (x-op sop)
    (wop-covers hop sop))
   (equal (s*-h*-induction sop sptr hop spec sram)
          (s*-spec sop sptr (h*-spec hop spec) sram)))
  :hints (("goal" :induct (s*-h*-induction sop sptr hop spec sram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich
                                 numtype
                                 ;op-base
                                 ;whichtype
                                 )))))

(defthm s*-spec-with-h*-spec
  (implies
   (and
    (x-op sop)
    (wop-covers hop sop))
   (equal (s*-spec sop sptr (h*-spec hop spec) ram)
          (s*-spec (f*-h*-op sop hop) sptr spec ram)))
  :hints (("goal" :induct (s*-h*-induction sop sptr hop spec ram)
           :do-not '(generalize 
                     preprocess ;;
                     eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich ;numtype ;slowed things down?
                                          )))))

(defun g*-h*-induction (gop gptr hop spec ram)
  (if (consp spec)
      (let ((op gop)
            (ptr gptr))
        (let ((slot (car spec)))
          (if (slot-p slot)
              (let ((hh (op-how   hop))
                    (w  (op-which op))
                    (h  (op-how   op)))
                (let ((off   (slot-off  slot))
                      (size  (slot-size slot))
                      (type  (slot-type slot))
                      (skel  (slot-skel slot))
                      (value (slot-val  slot))
                      )
                  (let ((read (rx size (+<> off ptr) ram)))
                    (let ((base (skel-base skel)))
                      (let ((hbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                  (op-base hh type base read))))
                        (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                   (op-base h type hbase read))))
                          (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                      (if (whichtype w type) read value))))
                            (let ((skel (update-skel skel :base base)))
                              (let ((skelx (skel base (g*-h*-induction gop base hop (skel-spec skel) ram))))
                                (let ((skel (if (ptr? type) skelx skel)))
                                  (cons (update-slot slot
                                                     :val  value
                                                     :skel skel
                                                     )
                                        (g*-h*-induction gop gptr hop (cdr spec) ram))))))))))))
            (cons slot
                  (g*-h*-induction gop gptr hop (cdr spec) ram)))))
    nil))

(defthm g*-spec-with-h*-spec
  (implies
   (and
    (wop-covers hop (wop-not gop))
    (not (g? (op-how hop))))
   (equal (g*-spec gop gptr (h*-spec hop spec) ram)
          (g*-spec (f*-h*-op gop hop) gptr spec ram)))
  :hints (("goal" :induct (g*-h*-induction gop gptr hop spec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich numtype
                                          ;whichnum
                                          )))
          ))

(defun hop-not (op)
  (let ((w (numwhich (op-which op))))
    (let ((w (whichnum (logxor w #x3))))
      (op w (op-how op)))))

(defun hop- (op1 op2)
  (let ((w1 (numwhich (op-which op1)))
        (w2 (numwhich (op-which op2))))
    (let ((w (whichnum (logand (lognot w1) w2))))
      (op w (op-how op2)))))

(defthm h*-spec-over-g*-spec
  (implies
   (x? hop)
   (equal (h*-spec hop (g*-spec gop gptr gspec ram))
          (g*-spec (hop- (hop-not hop) gop) gptr (h*-spec (hop- gop hop) gspec) ram)))
  :hints (("goal" :induct (g*-spec gop gptr gspec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (disable ;numwhich numtype
                               ))))

(defun w-nill (op)
  (update-op op :which :nil))

(defun f*-g*-induction (fop fptr op ptr spec ram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op))
                  (fh (op-how   fop)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read (rx size (+<> off ptr) ram)))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                               (op-base h type base read))))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                  (if (whichtype w type) read value))))
                        (let ((fbase (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                    (op-base fh type base value))))
                          (let ((skel (update-skel skel :base base)))
                            (let ((skelx (skel base (f*-g*-induction fop fbase op base (skel-spec skel) ram))))
                              (let ((skel (if (ptr? type) skelx skel)))
                                (let ((slot (update-slot slot :skel skel)))
                                  (cons slot
                                        (f*-g*-induction fop fptr op ptr (cdr spec) ram)))))))))))))
          (cons slot
                (f*-g*-induction fop fptr op ptr (cdr spec) ram))))
    (list fop fptr)))

(defthm f*-spec-of-g*-spec-reduction
  (implies
   (and
    (not (equal (op-which gop) :nil))
    (x-op fop)
    )
   (equal (f*-spec fop fptr (g*-spec gop gptr spec ram))
          (f*-spec fop fptr (g*-spec (w-nill gop) gptr spec ram))))
  :hints (("goal" :induct (f*-g*-induction fop fptr gop gptr spec ram))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t
                         :in-theory (enable g?)
                         ))))

(defun op-which-subbagp-< (op1 op2)
  (let ((w1 (op-which op1))
        (w2 (op-which op2)))
    (let ((n1 (numwhich w1))
          (n2 (numwhich w2)))
      (equal n1 (logand n1 n2)))))

(defun g*-g*-induction (gop1 gptr1 ram1 op ptr spec ram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w  (op-which  op))
                  (h  (op-how    op))
                  (w1 (op-which gop1))
                  (h1 (op-how   gop1)))
              (let ((off   (slot-off  slot))
                    (size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (let ((read  (rx size (+<> off ptr) ram))
                      (read1 (rx size (+<> off gptr1) ram1)))
                  (let ((base (skel-base skel)))
                    (let ((base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                               (op-base h type base read))))
                      (let ((base1 (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                  (op-base h1 type base read1))))
                        (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                    (if (whichtype w type) read value))))
                          (let ((value1 (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                       (if (whichtype w1 type) read1 value))))
                            (let ((skel (update-skel skel :base base1)))
                              (let ((skelx (skel base1 (g*-g*-induction gop1 base1 ram1 op base (skel-spec skel) ram))))
                                (let ((skel (if (ptr? type) skelx skel)))
                                  (let ((slot (update-slot slot :val value1 :skel skel)))
                                    (cons slot
                                          (g*-g*-induction gop1 gptr1 ram1 op ptr (cdr spec) ram))))))))))))))
          (cons slot
                (g*-g*-induction gop1 gptr1 ram1 op ptr (cdr spec) ram))))
    nil))

(defthm g*-spec-with-x*-spec
  (implies
   (and
    (or (g-op gop1) (x? gop2))
    (op-which-subbagp-< gop2 gop1))
   (equal (g*-spec gop1 gptr1 (g*-spec gop2 gptr2 spec ram2) ram1)
          (g*-spec gop1 gptr1 spec ram1)))
  :hints (("goal" :induct (g*-g*-induction gop1 gptr1 ram1 gop2 gptr2 spec ram2)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (g?) (numwhich numtype)))
          ))

(defun w-nil? (op)
  (equal (op-which op) :nil))

(defthm h*-spec-of-g*-spec-reduction
  (implies
   (and
    (x-op hop)
    (w-nil? hop)
    (not (w-nil? gop))
    )
   (equal (h*-spec hop (g*-spec gop gptr spec ram))
          (h*-spec hop (g*-spec (update-op gop :which :nil) gptr spec ram))))
  :hints (("goal"  :induct (g*-spec gop gptr spec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (enable g?))
          ))

  
;; ====================================================
;;
;; split-blk
;;
;; ====================================================

(defun fix-slot (slot)
  (declare (type (satisfies slot-p) slot))
  (let ((size  (slot-size slot))
        (value (slot-val  slot))
        (type  (slot-type slot))
        (skel  (slot-skel slot)))
    (let ((skel (if (ptr? type)
                    (let ((base (skel-base skel)))
                      (update-skel skel :base (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                     (ifix base)
                                                     )))
                  skel)))
      (update-slot slot 
                   :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                               (ifix value)
                               )
                   :skel skel))))

;bzo will these let us disable fix-slot?
(defthm slot-type-of-fix-slot
 (equal (slot-type (fix-slot slot))
        (slot-type slot))
 :hints (("Goal" :in-theory (enable slot-type fix-slot slot))))

(defthm slot-size-of-fix-slot
 (equal (slot-size (fix-slot slot))
        (slot-size slot))
 :hints (("Goal" :in-theory (enable slot-size fix-slot slot))))

(defthm slot-off-of-fix-slot
 (equal (slot-off (fix-slot slot))
        (slot-off slot))
 :hints (("Goal" :in-theory (enable slot-off fix-slot slot))))


(defun split-blk (spec)
  (declare (type (satisfies wf-spec) spec))
  (if (consp spec)
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
               (mv (cons slot spec) list))))
    (mv spec nil)))

(defun join-blk (spec list)
  (declare (type (satisfies wf-spec) spec))
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((type (slot-type slot)))
              (if (and (ptr? type)
                       (consp list))
                  (let ((line (car list)))
                    (if (line-p line)
                        (let ((slot (update-slot slot :skel (line-skel line))))
                          (cons slot
                                (join-blk (cdr spec) (cdr list))))
                      (cons slot
                            (join-blk (cdr spec) list))))
                (cons slot
                      (join-blk (cdr spec) list))))
          (cons slot
                (join-blk (cdr spec) list))))
    spec))

(defthm join-blk-split-blk
  (implies
   (equal (h*-spec (op :all :x) spec)
          spec)
   (equal (join-blk (v0 (split-blk spec))
                    (v1 (split-blk spec)))
          spec))
  :hints (("goal" :in-theory (enable skel-extensionality!)
           :induct (split-blk spec))))

(defun f*-blk (fop ptr spec)
  (met ((spec list) (split-blk spec))
       (append (f*-spec fop ptr spec)
               (f*-list fop list))))


(defthm f*-blk-perm
  (implies
   (x? fop)
   (perm (f*-spec fop ptr spec)
         (f*-blk  fop ptr spec)))
  :hints (("goal'" :induct (split-blk spec))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t))))

(defthm f*-blk-perm?
  (implies (and (x? fop)
                (equal v (f*-blk  fop ptr spec)))
           (equal (perm (f*-spec fop ptr spec) v) t))
  :hints (("goal" :use (:instance f*-blk-perm)
           :in-theory nil)))

(defthm v0-split-blk-over-g*-spec
  (equal (v0 (split-blk (g*-spec gop ptr skel ram)))
         (g*-spec gop ptr (v0 (split-blk skel)) ram))
  :hints (("goal" :induct (split-blk skel))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t))))

(defthm v1-split-blk-over-g*-spec
  (implies
   (x? gop)
   (equal (v1 (split-blk (g*-spec gop ptr skel ram)))
          (g*-list gop (v1 (split-blk skel)) ram)))
  :hints (("goal" :induct (split-blk skel))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :do-not-induct t))))


(defun s*-blk (sop ptr spec ram)
  (met ((spec list) (split-blk spec))
       (let ((ram (s*-spec sop ptr spec ram)))
         (s*-list sop list ram))))

(defthm disjoint-f*-cdr-reduction
  (implies
   (x? fop)
   (and (equal (disjoint (flat (f*-spec fop fptr (cdr spec))) y)
               (disjoint (flat (f*-blk fop fptr (cdr spec))) y))
        ;(equal (disjoint y (flat (f*-spec fop fptr (cdr spec))))
        ;       (disjoint y (flat (f*-blk fop fptr (cdr spec)))))
        ))
  :hints (("goal" :in-theory (disable f*-blk x? bag::flat-append))))

(in-theory
 (disable
  f*-blk-perm
  ))

(defthm s*-blk-implements-s*-spec
  (implies
   (and
    (x? sop)
    (unique (flat (f*-blk sop sptr spec)))
    )
   (equal (s*-blk sop sptr spec ram)
          (s*-spec sop sptr spec ram)))
  :hints (("goal'" :in-theory (enable flat) 
           :induct (split-blk spec))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
                         :in-theory (disable numwhich)
                         :do-not-induct t))))
(in-theory
 (disable
  f*-blk-perm?
  s*-blk-implements-s*-spec
  disjoint-f*-cdr-reduction
  ))

;; ====================================================
;;
;; split-list
;;
;; ====================================================

(defun key-lst (list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (cons (line-key line)
                  (key-lst (cdr list)))
          (key-lst (cdr list))))
    nil))

(defun split-lst (key list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((ptr (line-key line)))
              (if (equal ptr key)
                  (let ((skel (line-skel line)))
                    (let ((line (update-line line :skel (skel (skel-base skel) nil))))
                      (mv skel (cons line (cdr list)))))
                (met ((skel list) (split-lst key (cdr list)))
                     (mv skel (cons line list)))))
          (met ((skel list) (split-lst key (cdr list)))
               (mv skel (cons line list)))))
    (mv nil list)))

(defun join-lst (key skel list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((ptr (line-key line)))
              (if (equal ptr key)
                  (let ((line (update-line line :skel skel)))
                    (cons line (cdr list)))
                (cons line (join-lst key skel (cdr list)))))
          (cons line
                (join-lst key skel (cdr list)))))
    list))

(defthm join-lst-split-lst
  (equal (join-lst key 
                   (v0 (split-lst key list))
                   (v1 (split-lst key list)))
         list))

(defun f*-lst (fop key list)
  (met ((skel list) (split-lst key list))
       (append (f*-spec fop (skel-base skel) (skel-spec skel))
               (f*-list fop list))))

(defthm f*-lst-perm
  (implies
   (x? fop)
   (perm (f*-lst fop key list)
         (f*-list fop list)))
  :hints (("goal'" :induct (split-lst key list))))

(defthm f*-lst-perm?
  (implies
   (and (x? fop)
        (bind-free (list (cons 'term v)) (term))
        (equal v term)
        (equal term (f*-lst fop key list)))
   (equal (perm (f*-list fop list) v)
          t))
  :hints (("goal" :in-theory (disable f*-lst))))

(defthm v0-split-lst-over-g*-spec
  (implies
   (memberp key (key-lst list))
   (equal (v0 (split-lst key (g*-list gop list ram)))
          (let ((skel (v0 (split-lst key list))))
            (let ((base (cond
                         ((equal (op-how gop) :z) 0)
                         ((equal (op-how gop) :x) (skel-base skel))
                         (t                       key))))
              (skel base (g*-spec gop base (skel-spec skel) ram))))))
  :hints (("goal" :induct (split-lst key list)
           :do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :expand  (G*-LIST GOP LIST RAM)
           :in-theory (enable memberp))
          ))

(defthm v1-split-lst-over-g*-spec
  (equal (v1 (split-lst key (g*-list gop list ram)))
         (g*-list gop (v1 (split-lst key list)) ram))
  :hints (("goal" :induct (split-lst key list))))

(defun s*-lst (sop key list ram)
  (met ((skel list) (split-lst key list))
       (let ((ram (s*-list sop list ram)))
         (s*-spec sop (skel-base skel) (skel-spec skel) ram))))

(in-theory
 (disable
  f*-lst-perm
  ))

(defthm s*-lst-implements-s*-list
  (implies
   (and
    (x? sop)
    (unique (flat (f*-lst sop key list)))
    )
   (equal (s*-lst sop key list ram)
          (s*-list sop list ram)))
  :hints (("goal'" :induct (split-lst key list))))

(defun which-disjoint (op1 op2)
  (declare (type (satisfies op-p) op1 op2))
  (let ((nw1 (numwhich (op-which op1)))
        (nw2 (numwhich (op-which op2))))
    (equal (logand nw1 nw2) 0)))

(defun h*-g*-op (op1 op2)
  (if (x? op1) (update-op op1 :how (op-how op2))
    (update-op op1)))
    
(defun h*-g*-hyp (hop gop)
  (and (which-disjoint hop gop)
       (implies (g-op gop) (and (or (not (optype hop :ptr))
                                    (not (optype gop :ptr)))
                                (equal (op-how hop) :z)))
       (implies (g-op hop) (not (optype gop :ptr)))))

(defthm min-self
  (equal (min x x)
         x)
  :hints (("Goal" :in-theory (enable min))))

(defthm min-known-1
  (implies (and (<=  x y)
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (min x y)
                  x))
  :hints (("Goal" :cases ((ACL2-NUMBERP X))
           :in-theory (enable min))))

(defthm min-known-2
  (implies (and (<= y x)
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (min x y)
                  y))
  :hints (("Goal" :cases ((ACL2-NUMBERP X))
           :in-theory (enable min))))

(defthm op-base-of-z-and-ptr
  (equal (OP-BASE :Z :PTR base valu)
         0))

(defthm op-base-equal-same-h-and-type-rewrite
  (equal (equal (OP-BASE H TYPE BASE1 VALU1) (OP-BASE H TYPE BASE2 VALU2))
         (if (or (not (equal type :ptr))
                 (equal h :x))
             (equal base1 base2)
           (if (equal h :z)
               t
             (equal valu1 valu2)))))

(defthm h*-spec-of-g*-spec
  (implies (h*-g*-hyp hop gop)
           (equal (h*-spec hop (g*-spec gop gptr spec ram))
                  (h*-spec (h*-g*-op hop gop) spec)))
  :hints (("subgoal *1/2" 
           :in-theory (e/d (g?) 
                           (OPEN-H*-SPEC
                            ;CAR-H*-SPEC
                            ;;NFIX
                            numwhich
                            op-base
                            whichnum
                            numtype
                            ATOMIC-H*-OP-REPLACEMENT
                            SLOT-EXTENSIONALITY!!
                            min
                            WX-OF-RX
                            ;; ACL2::LOGAND-WITH-MASK-ERIC
                            ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                            ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                            ACL2::LOGHEAD-LEQ
                            ;;g-op
                            ;;x?
                            )))
          ("goal" :induct (g*-spec gop gptr spec ram)
           :do-not '(generalize eliminate-destructors fertilize eliminate-irrelevance)
           :expand ((:free (x)  (H*-SPEC x SPEC)))
           :in-theory (e/d (g?) (OPEN-H*-SPEC
                                 FIXED-SPEC-P
                                 G*-SPEC-TO-H*-SPEC
                                 ATOMIC-G*-OP-REPLACEMENT
                                 ;;NFIX
                                 ;;numwhich
                                 ;;op-base
                                 whichnum
                                 numtype
                                 ATOMIC-H*-OP-REPLACEMENT
                                 SLOT-EXTENSIONALITY!!
                                 min
                                 WX-OF-RX
                                 ;; ACL2::LOGAND-WITH-MASK-ERIC
                                 ACL2::UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;bzo
                                 ACL2::LOGHEAD-NONNEGATIVE-LINEAR
                                 ACL2::LOGHEAD-LEQ
                                 ;;g-op
                                 ;;x?
                                 ))
           :do-not-induct t
           )))

