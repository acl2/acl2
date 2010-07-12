#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "GACC")

;; Keep this list of include-books in sync with the list in the .acl2 file:
;;
(include-book "finite")

;experiment:
(local (in-theory (disable numwhich numtype)))


;;bzo
;;
;;
;; z* stuff (moved to gacc3.lisp [was in ram.lisp]).
;;
;;

(defun z* (zlist ram)
  ;(declare (type t zlist ram))
  (if (consp zlist)
      (let ((ram (z*-rec (car zlist) ram)))
        (z* (cdr zlist) ram))
    ram))
 
;;
;; This may be helpful in extending the z*-rec lemmas to z*
;;
;bzo nested inductions

(defthmd z*-reduction 
  (equal (z* zlist ram) 
         (z*-rec (flat zlist) ram))
  :hints (("Goal" :in-theory (enable append  ;bzo why the enables?
                                     flat
                                     ))))

(defthmd z*-wx-introduction
  (equal (equal (wx size ptr value ram1)
                ram2) 
         (and (equal (z* (list (sblk size ptr)) ram1) 
                     (z* (list (sblk size ptr)) ram2)) 
              (tag-location ptr (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                                              value) 
                                       (rx size ptr ram2))))) 
  :hints (("Goal" :in-theory (e/d (blk sblk wx rx failed-location ;wfixn 
                                       wx==ram-rec)
                                  (
                                   open-rx-rec open-wx-rec z*-same-wx-rec-0)))))

;bzo WX==RAM-REC seemed to loop here when wx was disabled...
(defthm z*-of-wx 
  (implies 
   (any-subbagp (sblk size ptr) zlist)
   (equal (z* zlist (wx size ptr value ram1))
          (z* zlist ram1)))
  :hints (("Goal" :in-theory (e/d (blk sblk wx z*-reduction) (open-wx-rec)))))

(defun z*-induction-fn (ptr ram1 ram2 size value zlist)
  (if (consp zlist)
      (z*-induction-fn ptr (z*-rec (car zlist) ram1) (z*-rec (car zlist) ram2)
                    size value (cdr zlist))
    (list ptr ram1 ram2 size value)))

(defthm rx-rec-over-z*-disjoint
  (implies (disjoint-list (blk-rec ptr off size) zlist)
           (equal (rx-rec ptr off size (z* zlist ram))
                  (rx-rec ptr off size ram)))
  :hints (("Goal" :in-theory (enable z*-reduction))))



                      

(encapsulate
 ()

 (local
  (defthm wr-equality-to-value-equality
    (and (implies
          (equal ram1 (wr a v ram2))
          (equal (rd a ram1) (loghead8 v)))
         (implies
          (equal (wr a v ram2) ram1)
          (equal (loghead8 v) (rd a ram1))))
    :hints (("Goal" :in-theory (enable failed-location)))))
 
 (local
  (defthm wx-rec-equality-to-value-equality
    (and
     (implies
      (and
       (equal ram1 (wx-rec base off max value ram2))
       (integerp base)
       (integerp max)
       (integerp off)
       (< off max)
       (<= 0 off))
      (equal (rx-rec base off max ram1) ( ;wfixw 8 (- max off) 
                                         acl2::loghead (* 8 (nfix  (- max off)))
                                         value)))
     (implies
      (and
       (equal (wx-rec base off max value ram2) ram1)
       (integerp base)
       (integerp max)
       (integerp off)
       (< off max)
       (<= 0 off))
      (equal ( ;wfixw 8 (- max off) 
              acl2::loghead (* 8 (nfix  (- max off)))
              value) (rx-rec base off max ram1))))
    :hints (("goal" :in-theory (enable (:induction wx-rec))
             :induct (wx-rec base off max value ram2)))))

;bzo is this a good general theorem? 
;not used outside this book?
 (defthmd wx-equality-to-value-equality
   (and (implies (equal ram1 (wx size ptr value ram2))
                 (equal (rx size ptr ram1) (acl2::loghead (fix-size size) value)))
        (implies
         (equal (wx size ptr value ram2) ram1)
         (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                               value) (rx size ptr ram1))))
   :hints (("Goal" :in-theory (e/d ( failed-location) ()))))
 
 #+joe
 (local
  (defthm z*-rec-over-wx-rec
    (implies
     (and
      (integerp base)
      (integerp max)
      (integerp off)
      (< off max)
      (<= 0 off)
      (disjoint (blk-rec base off max) list))
     (equal (z*-rec list (wx-rec base off max value ram))
            (wx-rec base off max value (z*-rec list ram))))
    :hints (("goal" :in-theory (e/d (wx==ram-rec
                                     (:induction wx-rec))
                                    (Z*-REC-DISJOINT
                                     wr==ram
                                     z*-rec-of-wr
                                     z*-rec-over-wr 
                                     ))
             :induct (wx-rec base off max value ram2)))))
 
 (local
  (defthm rx-rec-over-z*-disjoint-flat
    (implies (disjoint (blk-rec ptr off size) (flat zlist))
             (equal (rx-rec ptr off size (z* zlist ram))
                    (rx-rec ptr off size ram)))))

;bzo 
 (local
  (defthm open-disjoint-list-x
    (and (implies (consp list)
                  (equal (disjoint-list term list)
                         (and (disjoint term (car list))
                              (disjoint-list term (cdr list)))))
         (implies (not (consp list))
                  (equal (disjoint-list term list) t)))
    :hints (("goal" :in-theory (enable disjoint-list 
                                       ;;append 
                                       flat
                                       ;;acl2::disjoint-of-cons-two
                                       )))))
  
 (defthm rx-over-z*-disjoint
   (implies (disjoint (sblk size ptr) (flat zlist))
    (equal (rx size ptr (z* zlist ram))
           (rx size ptr ram)))
   :hints (("goal" :in-theory '(rx-rec-over-z*-disjoint-flat 
                                blk rx sblk))))
 
 (local
  (defthm z*-rec-over-wx
    (implies
     (disjoint (sblk size ptr) list)
     (equal (z*-rec list (wx size ptr value ram))
            (wx size ptr value (z*-rec list ram))))
    :hints (("goal" :in-theory (enable wx sblk blk wx==ram-rec)))))
 
 (defthmd z*-over-wx-commute
   (implies (disjoint (sblk size ptr) (flat list))
            (equal (z* list (wx size ptr value ram))
                   (wx size ptr value (z* list ram))))
   :hints (("goal" :in-theory (enable z*-reduction))))
 
 )

(in-theory (disable bag::disjoint-list-reduction ;bzo why?
                    ))

(encapsulate
 ()

 (local
  (defthm read-equal-instance
    (implies (and (consp zlist)
                  (disjoint-list (blk-rec ptr off size)
                                 zlist)
                  (equal (z* zlist
                             (wx-rec ptr off size value ram1))
                         (z* zlist ram2))
                  (integerp size)
                  (integerp off)
                  (<= 0 off)
                  (<= off size)
                  (equal off 0))
             (equal (;wfixw 8 size
                     acl2::loghead (* 8 size)
                     value)
                    (rx-rec ptr off size ram2)))
    :hints (("Goal" :do-not-induct t
             :in-theory (disable z*-rec-over-append z*-reduction)
             :use ((:instance rx-rec-over-z*-disjoint 
                              (ram (wx-rec ptr off size value ram1)))))
            )
    :rule-classes nil))

 (local
  (encapsulate
   ()
  
   (local
    (defthm z*-helper-1-helper
      (implies 
       (and
        (disjoint (sblk size ptr) (flat zlist))
        (equal (z* zlist (wx size ptr value ram1)) 
               (z* zlist ram2)))
       (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                             value) 
              (rx size ptr ram2)))
      :hints (("goal" :in-theory '(z*-over-wx-commute ;bzo scary literal value for theory
                                   rx-over-z*-disjoint
                                   wx-equality-to-value-equality
                                   )))))

   (defthm z*-helper-1
     (implies 
      (and
       (disjoint-list (sblk size ptr) zlist) 
       (equal (z* zlist (wx size ptr value ram1)) 
              (z* zlist ram2)))
      (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                            value) 
             (rx size ptr ram2)))
     :hints (("goal" :in-theory '(z*-helper-1-helper 
                                  bag::disjoint-list-reduction))))
  
   ))
  
 (local
  (defthm z*-helper-2
    (implies (and
              (disjoint-list (sblk size ptr) zlist) 
              (equal (z* zlist (wx size ptr value ram1)) 
                     (z* zlist ram2)))
             (equal (z* (cons (sblk size ptr) zlist) ram1) 
                    (z* (cons (sblk size ptr) zlist) ram2)))
    :hints (("goal" :in-theory (e/d (wx blk sblk flat z*-reduction) (open-wx-rec open-rx-rec))))) )
 
 (local
  (defthm z*-helper-2a
    (implies 
     (and
      (disjoint-list (sblk size ptr) zlist) 
      (equal (z* zlist ram2) 
             (z* zlist (wx size ptr value ram1))))
     (equal (z* (cons (sblk size ptr) zlist) ram2) 
            (z* (cons (sblk size ptr) zlist) ram1)))
    :hints (("goal" :in-theory (e/d (wx blk sblk flat z*-reduction)
                                    (open-wx-rec open-rx-rec))))) )

 (local
  (defthm other-way-instance
    (implies (and (<= 0 off)
                  (< off size)
                  (integerp off)
                  (integerp size)
                  (disjoint-list (blk-rec ptr off size) list)
                  (equal (z*-rec (append (blk-rec ptr off size) 
                                         (flat list)) ram1)
                         (z*-rec (append (blk-rec ptr off size) 
                                         (flat list)) ram2))
                  (equal (;wfixw 8 (- size off)
                          acl2::loghead (* 8 (nfix  (- size off)))
                          value)
                         (rx-rec ptr off size ram2)))
             (equal (z*-rec (flat list) (wx-rec ptr off size value ram1))
                    (z*-rec (flat list) ram2)))
    :hints (("Goal" :in-theory (enable  z*-of-wx-rec
                                        WX==RAM-REC
                                        )))))

 (local
  (defthm z*-helper-3
    (implies 
     (and
      (disjoint-list (sblk size ptr) zlist) 
      (equal (z* (cons (sblk size ptr) zlist) ram1) 
             (z* (cons (sblk size ptr) zlist) ram2)) 
      (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                            value) 
             (rx size ptr ram2)))
     (equal (z* zlist (wx size ptr value ram1)) 
            (z* zlist ram2)))
    :hints (("goal" :in-theory (e/d (wx rx blk sblk flat ;wfixn 
                                        z*-reduction) (;wfixw 
                                                       z*-rec-over-append))))))

 (local
  (defthm z*-helper-3a
    (implies 
     (and
      (disjoint-list (sblk size ptr) zlist) 
      (equal (z* (cons (sblk size ptr) zlist) ram2) 
             (z* (cons (sblk size ptr) zlist) ram1)) 
      (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                            value) 
             (rx size ptr ram2)))
     (equal (z* zlist ram2) 
            (z* zlist (wx size ptr value ram1))))
    :hints (("goal" :use z*-helper-3))))

; Note the list-integer-listp zlist hypothesis.  To get rid of it,
; would need to know disjoint-list of sblk and an ifixed version of zlist
; since z*-rec ifixes the elements of the list.

 (defthm z*-wx-induction
   (implies 
    (disjoint-list (sblk size ptr) zlist)
    (equal (equal (z* zlist (wx size ptr value ram1)) 
                  (z* zlist ram2)) 
           (and (equal (z* (cons (sblk size ptr) zlist) ram1) 
                       (z* (cons (sblk size ptr) zlist) ram2)) 
                (tag-location ptr (equal (acl2::loghead (fix-size size) ;wfixn 8 size 
                                                        value) 
                                         (rx size ptr ram2))))))
   :hints (("goal" :in-theory (e/d (failed-location)
                                   ( z*-helper-1 z*-helper-2
                                                 z*-helper-2a z*-helper-3 z*-helper-3a))
            :use ((:instance z*-helper-1)
                  (:instance z*-helper-2)
                  (:instance z*-helper-2a)
                  (:instance z*-helper-3)
                  (:instance z*-helper-3a)))))) ;closes encapsulate


;; end of stuff from ram.lisp

;;
;; getx/sets, gets/sets
;;

(defun missing-key (key)
  (update-slot nil :name key :type :int :skel (skel 0 nil)))

(defthm slot-p-missing-key
  (slot-p (missing-key key)))

(in-theory (disable missing-key (missing-key)))

(defun get-slot (key spec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (if (equal key (slot-name slot))
                slot
              (get-slot key (cdr spec)))
          (missing-key key)))
    (missing-key key)))

(defun update-slot-value (value slot)
  (let ((size (slot-size slot)))
    (update-slot slot :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                  value))))

(defun update-slot-skel (skel slot)
  (update-slot slot :skel skel))

(defun set-slot-skel (key value skel)
  (if (consp skel)
      (let ((slot (car skel)))
        (if (slot-p slot)
            (if (equal key (slot-name slot))
                (cons (update-slot-skel value slot)
                      (cdr skel))
              (cons slot
                    (set-slot-skel key value (cdr skel))))
          (cons (missing-key key) skel)))
    (cons (missing-key key) skel)))

(defun set-slot-value (key value skel)
  (if (consp skel)
      (let ((slot (car skel)))
        (if (slot-p slot)
            (if (equal key (slot-name slot))
                (cons (update-slot-value value slot)
                      (cdr skel))
              (cons slot
                    (set-slot-value key value (cdr skel))))
          (cons (missing-key key) skel)))
    (cons (missing-key key) skel)))

;; If no :type key is provided, these functions expect "fun::type" 
;; to be bound in the context in which they are used.

(defmacro setx (key value skel &key (type 'nil))
  (let ((type (or type 'type)))
    `(let ((slot (get-slot ,key ,type))
           (base (skel-base ,skel)))
       (skel base (wv (slot-size slot) (slot-off slot) base ,value (skel-spec ,skel))))))

(defmacro getx (key skel &key (type 'nil))
  (let ((type (or type 'type)))
    `(let ((slot (get-slot ,key ,type))
           (base (skel-base ,skel)))
       (rv (slot-size slot) (slot-off slot) base (skel-spec ,skel)))))

(defmacro sets (key value skel &key (type 'nil))
  (let ((type (or type 'type)))
    `(let ((slot (get-slot ,key ,type)))
       (let ((base (skel-base ,skel))
             (size (slot-size slot))
             (off  (slot-off slot)))
         (skel base (ws size off base ,value (skel-spec ,skel)))))))

(defmacro gets (key skel &key (type 'nil))
  (let ((type (or type 'type)))
    `(let ((slot (get-slot ,key ,type)))
       (let ((base (skel-base ,skel))
             (size (slot-size slot))
             (off  (slot-off  slot)))
         (rs size off base (skel-spec ,skel))))))
  
(defun syntax-offset (woff wbase wptr rptr)
  (declare (type t woff wbase wptr rptr))
  (if (and (consp wptr)
           (equal (car wptr) 'binary-+)
           (consp (cdr wptr))
           (consp (cddr wptr))
           (equal (caddr wptr) rptr))
      `((,woff  . ,(cadr wptr))
        (,wbase . ,rptr))
    (if (equal wptr rptr)
        `((,woff  . (quote 0))
          (,wbase . ,rptr))
      nil)))

(defthmd unfixed-size-rx
  (implies (syntaxp (syntax-unfixed-size rsize))
           (equal (rx rsize rptr ram)
                  (rx (fix-size rsize) rptr ram)))
  :hints (("goal" :in-theory (enable rx))))

;move
(defthm unfixed-size-rx-constant-version
  (implies (syntaxp (and (quotep rsize)
                         (syntax-unfixed-size rsize)))
           (equal (rx rsize rptr ram)
                  (rx (fix-size rsize) rptr ram)))
  :hints (("goal" :use (:instance unfixed-size-rx)
           :in-theory (disable  unfixed-size-rx))))

(defthmd unfixed-size-wx
  (implies (syntaxp (syntax-unfixed-size wsize))
           (equal (wx wsize wptr value ram)
                  (wx (fix-size wsize) wptr value ram)))
  :hints (("goal" :in-theory (enable wx))))

(defthm split-blk-h*-spec
  (equal (f*-spec fop ptr (v0 (split-blk (h*-spec hop spec))))
         (f*-spec fop ptr (v0 (split-blk spec))))
  :hints (("goal" ;:induct (len spec) :in-theory (enable len)
           )))

(defthm f*-spec-g*-spec-v0-split-blk
  (equal (f*-spec fop fptr (g*-spec gop gptr (v0 (split-blk spec)) ram))
         (f*-spec fop fptr (v0 (split-blk spec))))
  :hints (("goal" :induct (split-blk spec))))


;; ==========================================
;;
;; deeper perm/unique/remove-list meta-rules
;;
;; ==========================================


(defun bind-fn-template-args (temp args)
  (declare (type t temp args))
  (if (consp temp)
      (if (consp args)
          (if (consp (car temp))
              (if (and (consp (car args))
                       (equal (caar temp) (caar args)))
                  (met ((hit alist) (bind-fn-template-args (cdar temp) (cdar args)))
                       (if hit
                           (met ((hit rst) (bind-fn-template-args (cdr temp) (cdr args)))
                                (if hit
                                    (mv hit (append alist rst))
                                  (mv nil nil)))
                         (mv nil nil)))
                (mv nil nil))
            (met ((hit alist) (bind-fn-template-args (cdr temp) (cdr args)))
                 (if hit
                     (mv hit (cons (cons (car temp) (car args)) alist))
                   (mv nil nil))))
        (mv nil nil))
    (mv t nil)))

(defun find-fn-template-args-rec (fn args term)
  (declare (type t fn args term))
  (and (consp term)
       (or (and (consp (car term))
                (and (equal (caar term) fn)
                     (met ((hit alist) (bind-fn-template-args args (cdar term)))
                          (and hit alist)))
                (find-fn-template-args-rec fn args (cdar term)))
           (find-fn-template-args-rec fn args (cdr term)))))

(defun find-fn-template-args (fncall term)
  (declare (type t fncall term))
  (and (consp term)
       (consp fncall)
       (or (and (equal (car term) (car fncall))
                (met ((hit alist) (bind-fn-template-args (cdr fncall) (cdr term)))
                     (and hit alist)))
           (find-fn-template-args-rec (car fncall) (cdr fncall) (cdr term)))))

(defun template-keys (template)
  (declare (type t template))
  (if (consp template)
      (if (consp (car template))
          (append (template-keys (cdar template))
                  (template-keys (cdr template)))
        (cons (car template) (template-keys (cdr template))))
    nil))

(defmacro find-fn-template (template term)
  `(bind-free (find-fn-template-args ',template ,term) ,(template-keys (cdr template))))

(defun ptr! (op)
  (if (whichtype (op-which op) :ptr) 
      (update-op op :which :ptr)
    (update-op op :which :nil)))

(defun val! (op)
  (if (whichtype (op-which op) :val)
      (update-op op :which :val)
    (update-op op :which :nil)))

(defun f*-vp (fop fptr spec)
  (append (f*-spec (val! fop) fptr spec)
          (f*-spec (ptr! fop) fptr spec)))


;;
;; We might want to define a meta-unique as well to feed this
;; function.
;;


(defun concrete-pv (which)
  (declare (type t which))
  (and (consp which)
       (consp (cdr which))
       (if (equal (car which) 'quote)
           (let ((which (cadr which)))
             (or (equal which ':nil)
                 (equal which ':ptr)
                 (equal which ':val)))
         (not (equal (car which) 'op-which)))))

(defthmd f*-spec-vp-perm
  (implies
   (and
    (equal which (op-which fop))
    (syntaxp (not (concrete-pv which))))
   (perm (f*-spec fop fptr spec)
         (f*-vp fop fptr spec)))
  :hints (("goal" :induct (f*-spec fop fptr spec)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;acl2::perm-free-substitution
                       ))))



(defthm g*-spec-v0-split-blk-of-wx-helper
  (implies
   (and
    (equal (op-how gop) :x)
    (equal (op-which gop) :val)
    (equal wbase base)
    (equal wptr (+ (ifix woff) (ifix wbase)))
     
    (unique (flat (f*-spec (update-op gop :which :all) base (v0 (split-blk spec)))))
     
    (memberp (sblk wsize (+<> woff wbase))
             (f*-spec gop base (v0 (split-blk spec))))
     
    (subbagp (sblk wsize (+<> woff wbase))
             (flat (f*-spec gop base (v0 (split-blk spec)))))
     
    )
   (equal (g*-spec gop base (v0 (split-blk spec)) (wx wsize wptr value ram))
          (wv wsize woff wbase (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                                      value) 
              (g*-spec gop base (v0 (split-blk spec)) ram))))
  :otf-flg t
  :rule-classes nil
  :hints (("goal" :induct (len spec) 
           :do-not '(generalize ;preprocess 
                                eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (open-wv
                            ;len 
                            bag::flat-of-cons
;                            (:REWRITE ACL2::DISJOINT-COMMUTATIVE)
;                           (:REWRITE ACL2::MEMBERP-COMPUTATION)
                            (:REWRITE BAG::UNIQUE-of-APPEND) 
                            bag::disjoint-of-append-one 
                            bag::disjoint-of-append-two 
                            LIST::memberp-of-cons 
                            bag::disjoint-of-flat-helper-2
                            bag::disjoint-of-flat-helper
                            BAG::SUBBAGP-MEANS-RARELY-DISJOINT
                            BAG::SUBBAGP-MEANS-RARELY-DISJOINT-two
                            g*-spec-over-wx 
                            f*-spec-vp-perm
;                            unfixed-size-wfixn
                            unfixed-size-rx
                            unfixed-size-wx
                            )
                           (fix-slot
                            slot-p
                            ;;whichtype
                            ;;START-OF-F*-SPEC
                            ;;wfixn-of-fix-size
                            ;;subbagp-membership-fwd 
                            ;;subbagp-membership-free 
                            ;;bag::memberp-implies-subbagp-flat 
                            zz-wv-introduction)))))

(defthm rv-over-g*-spec-helper
  (implies
   (and
    (memberp (sblk wsize (+<> woff base))
             (f*-spec gop base (v0 (split-blk spec))))
    (subbagp (sblk wsize (+<> woff base))
             (flat (f*-spec gop base (v0 (split-blk spec)))))
    (unique (flat (f*-spec (update-op gop :which :all) base (v0 (split-blk spec)))))
    )
   (equal (rv wsize woff base (g*-spec gop base spec ram))
          (rx wsize (+<> woff base) ram)))
  :rule-classes nil
  :hints (("goal" :induct (len spec)
           :do-not '(generalize preprocess
                                eliminate-destructors fertilize eliminate-irrelevance)
           :do-not-induct t
           :in-theory (e/d (bag::flat-of-cons
                            bag::disjoint-of-append-one
                            bag::disjoint-of-append-two
                            LIST::memberp-of-cons
                            bag::disjoint-of-flat-helper-2
                            bag::unique-of-append 
                            F*-SPEC-VP-PERM
                            UNFIXED-SIZE-RX
;                                          UNFIXED-SIZE-WFIXN
                            LIST::MEMBERP-of-APPEND
                            BAG::MEMBERP-SUBBAGP
;                                           BAG::NOT-MEMBERP-OF-CDR-CHEAP
                            BAG::SUBBAGP-IMPLIES-SUBBAGP-APPEND-CAR
                            ) 
                           ( ;wfixn-of-fix-size
                            ;;ptr!
                            ;;F*-SPEC-VP-PERM
                            numwhich
                            numtype
                            op-base
                            )))))

;(local (in-theory (disable wfixn-of-fix-size)));bzo

;; Of course, we could have faster (evaluating) versions of these
;; combinations of functions that would improve proof times ..

(defthm g*-spec-v0-split-blk-of-wx
  (implies
   (and
    (equal (op-how gop) :x)
    (equal (op-which gop) :val)
    (bind-free (syntax-offset 'woff 'wbase wptr base) (woff wbase))
    (equal wbase base)
    (equal wptr (+<> woff wbase))
    (memberp (sblk wsize (+<> woff wbase))
            (f*-spec (update-op gop :which :val) base (v0 (split-blk spec))))
    (unique (flat (f*-spec (update-op gop :which :all) base (v0 (split-blk spec)))))
    )
   (equal (g*-spec gop base (v0 (split-blk spec)) (wx wsize wptr value ram))
          (wv wsize woff wbase (acl2::loghead (gacc::fix-size wsize) ;wfixn 8 wsize 
                                              value)
              (g*-spec gop base (v0 (split-blk spec)) ram))))
  :hints (("goal" :use (:instance g*-spec-v0-split-blk-of-wx-helper)
           :in-theory (e/d (;unfixed-size-wfixn
                            unfixed-size-rx
                            unfixed-size-wx
                            f*-spec-vp-perm)
                           (zz-wv-introduction)))))

(defthm rv-over-g*-spec
   (implies
    (and
     (memberp (sblk wsize (+<> woff base))
             (f*-spec gop base (v0 (split-blk spec))))
     (unique (flat (f*-spec (update-op gop :which :all) base (v0 (split-blk spec)))))
     )
    (equal (rv wsize woff base (g*-spec gop base spec ram))
           (rx wsize (+<> woff base) ram)))
   :hints (("goal" :use (:instance rv-over-g*-spec-helper)
            :in-theory `(bag::subbagp-membership-fwd f*-spec-vp-perm))))

;;
;; Next for GACC is the Z* stuff for s* .. should be fun.
;;

(defthm z*-of-s*
  (implies
   (any-subbagp (flat (f*-spec sop sptr spec)) list)
   (equal (z* list (s*-spec sop sptr spec ram))
          (z* list ram)))
  :hints (("Goal" :in-theory (enable flat))))

(defthm z*-nil-reduction
  (equal (z* '(nil) ram) ram))

(defthm z*-list-append-reduction
  (equal (z* (list (append x y)) ram)
         (z* (list x y) ram))
  :hints (("goal" :in-theory (enable z*-reduction flat))))


;;
;; This is an example of how to split/join
;;

(defun split-list (list)
  (if (consp list)
      (let ((entry (car list)))
        (if (consp entry)
            (cons (car entry)
                  (append (split-list (cdr entry))
                          (split-list (cdr list))))
          (cons entry
                (split-list (cdr list)))))
    list))

(defun join-list (list flat)
  (if (and (consp list) (consp flat))
      (let ((entry (car list))
            (line  (car flat))
            (flat  (cdr flat)))
        (if (consp entry)
            (met ((cdrline flat hit1) (join-list (cdr entry) flat))
                 (met ((list flat hit2) (join-list (cdr list) flat))
                      (mv (cons (cons line cdrline) list) flat (and hit1 hit2))))
          (met ((list flat hit) (join-list (cdr list) flat))
               (mv (cons line list) flat hit))))
    (mv list flat (not (consp list)))))

(defthm open-join-list
  (and
   (implies
    (consp list)
    (equal (join-list list flat)
           (if (and (consp list) (consp flat))
      (let ((entry (car list))
            (line  (car flat))
            (flat  (cdr flat)))
        (if (consp entry)
            (met ((cdrline flat hit1) (join-list (cdr entry) flat))
                 (met ((list flat hit2) (join-list (cdr list) flat))
                      (mv (cons (cons line cdrline) list) flat (and hit1 hit2))))
          (met ((list flat hit) (join-list (cdr list) flat))
               (mv (cons line list) flat hit))))
    (mv list flat (not (consp list))))))
   (implies
    (not (consp list))
    (equal (join-list list flat) (mv list flat (not (consp list)))))
   (implies
    (not (consp flat))
    (equal (join-list list flat) (mv list flat (not (consp list)))))))


(defthm join-list-append-reduction
  (implies
   (v2 (join-list list x))
   (and (v2 (join-list list (append x y)))
        (equal (v0 (join-list list (append x y)))
               (v0 (join-list list x)))
        (equal (v1 (join-list list (append x y)))
               (append (v1 (join-list list x)) y)))) 
  :hints (("goal" :in-theory (enable default-car default-cdr))))

(defthm join-list-split-list
  (and (v2 (join-list list (split-list list)))
       (equal (v0 (join-list list (split-list list)))
              list)
       (not (consp (v1 (join-list list (split-list list))))))
  :hints (("goal" :induct (split-list list))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors fertilize eliminate-irrelevance)
                         :in-theory (enable binary-append)
                         :do-not-induct t))))

;;
;; Here is the real thing ..
;;

(defun f*-rec (spec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((size (slot-size slot))
                  (off  (slot-off  slot)))
              (cons (sblk size off)
                    (f*-rec (cdr spec))))
          (f*-rec (cdr spec))))
    nil))

(defun s*-rec (spec ram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((off  (slot-off  slot))
                  (size (slot-size slot))
                  (value (slot-val slot)))
              (let ((ram (wx size off value ram)))
                (s*-rec (cdr spec) ram)))
          (s*-rec (cdr spec) ram)))
    ram))

(defun g*-rec (spec ram)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((off   (slot-off  slot))
                  (size  (slot-size slot)))
              (cons (update-slot slot :val (rx size off ram))
                    (g*-rec (cdr spec) ram)))
          (cons slot
                (g*-rec (cdr spec) ram))))
    spec))

(defthm true-listp-g*-rec
  (equal (true-listp (g*-rec rec ram))
         (true-listp rec)))

(defthm len-g*-rec
  (equal (len (g*-rec rec ram))
         (len rec)))

(defthm g*-rec-append
  (equal (g*-rec (append x y) ram)
         (append (g*-rec x ram) (g*-rec y ram))))

(defun spec->rec (op ptr spec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((off  (slot-off  slot))
                    (size (slot-size slot))
                    (type (slot-type slot))
                    (skel (slot-skel slot))
                    (value (slot-val slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (if (ptr? type) (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                       (op-base h type base read))
                                  base)))
                      (let ((slot (update-slot slot
                                               :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                           value)
                                               :off (+<> off ptr)
                                               :skel (skel base nil))))
                        (let ((blk (if (whichtype w type) (list slot) nil)))
                          (let ((rec (if (ptr? type) (spec->rec op base (skel-spec skel)) nil)))
                            (append blk
                                    rec
                                    (spec->rec op ptr (cdr spec)))))))))))
          (spec->rec op ptr (cdr spec))))
    nil))

(defthm open-spec->rec
  (implies
   (consp spec)
   (equal (spec->rec op ptr spec)
          (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how op)))
              (let ((off  (slot-off  slot))
                    (size (slot-size slot))
                    (type (slot-type slot))
                    (skel (slot-skel slot))
                    (value (slot-val slot)))
                (let ((read value))
                  (let ((base (skel-base skel)))
                    (let ((base (if (ptr? type) (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                       (op-base h type base read))
                                  base)))
                      (let ((slot (update-slot slot
                                               :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                           value)
                                               :off (+<> off ptr)
                                               :skel (skel base nil))))
                        (let ((blk (if (whichtype w type) (list slot) nil)))
                          (let ((rec (if (ptr? type) (spec->rec op base (skel-spec skel)) nil)))
                            (append blk
                                    rec
                                    (spec->rec op ptr (cdr spec)))))))))))
          (spec->rec op ptr (cdr spec))))))
  :hints (("goal" :in-theory '(spec->rec))))

(defthm true-listp-spec->rec
  (true-listp (spec->rec op ptr spec)))

(defthm atomic-spec->rec-replacement
  (implies
   (syntaxp (symbolp op))
   (equal (spec->rec op ptr spec)
          (spec->rec (xop op) ptr spec))))

(defthm len-spec->rec-reduction
  (implies
   (syntaxp (not (quotep ptr)))
   (equal (len (spec->rec op ptr spec))
          (len (spec->rec op 0 spec)))))

(defthm len-spec->rec-g*-spec-reduction
  (equal (len (spec->rec op ptr (g*-spec op ptr spec ram)))
         (len (spec->rec op ptr spec)))
  :hints (("goal" :in-theory (enable len))))

(defthm len-spec->rec-h*-spec-reduction
  (equal (len (spec->rec op ptr (h*-spec op spec)))
         (len (spec->rec op ptr spec)))
  :hints (("goal" :in-theory (enable len))))

(defthm s*-rec-append
  (equal (s*-rec (append x y) ram)
         (s*-rec y (s*-rec x ram)))
  :hints (("goal" :in-theory (enable binary-append)
           :induct (s*-rec x ram))))

(defthmd s*-spec-s*-rec-reduction
  (equal (s*-spec op ptr spec ram)
         (s*-rec (spec->rec op ptr spec) ram)))

(defun rec->spec (op spec rec)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (if (and (whichtype w type) (not (consp rec))) (mv spec rec nil)
                  (let ((read (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                             (slot-val (car rec))))
                        (rec  (if (whichtype w type) (cdr rec) rec)))
                    (let ((base (if (ptr? type) (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                               (skel-base skel)) (skel-base skel))))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                          (if (whichtype w type) read value))))
                        (let ((base (op-base h type base value)))
                          (let ((skel-spec (skel-spec skel)))
                            (met ((skel-spec rec hit1) (if (ptr? type)
                                                           (rec->spec op skel-spec rec) 
                                                         (mv skel-spec rec t)))
                                 (let ((skel (skel base skel-spec)))
                                   (met ((spec rec hit2) (rec->spec op (cdr spec) rec))
                                        (mv (cons (update-slot slot :val value :skel skel) spec) 
                                            rec (and hit1 hit2)))))))))))))
          (met ((spec rec hit) (rec->spec op (cdr spec) rec))
               (mv (cons slot spec) rec hit))))
    (mv spec rec t)))

(defthm open-rec->spec
  (and
   (implies
    (consp spec)
    (equal (rec->spec op spec rec)
           (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((w (op-which op))
                  (h (op-how   op)))
              (let ((size  (slot-size slot))
                    (type  (slot-type slot))
                    (skel  (slot-skel slot))
                    (value (slot-val  slot))
                    )
                (if (and (whichtype w type) (not (consp rec))) (mv spec rec nil)
                  (let ((read (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                             (slot-val (car rec))))
                        (rec  (if (whichtype w type) (cdr rec) rec)))
                    (let ((base (if (ptr? type) (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                               (skel-base skel)) (skel-base skel))))
                      (let ((value (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                  (if (whichtype w type) read value))))
                        (let ((base (op-base h type base value)))
                          (let ((skel-spec (skel-spec skel)))
                            (met ((skel-spec rec hit1) (if (ptr? type)
                                                           (rec->spec op skel-spec rec) 
                                                         (mv skel-spec rec t)))
                                 (let ((skel (skel base skel-spec)))
                                   (met ((spec rec hit2) (rec->spec op (cdr spec) rec))
                                        (mv (cons (update-slot slot :val value :skel skel) spec) 
                                            rec (and hit1 hit2)))))))))))))
          (met ((spec rec hit) (rec->spec op (cdr spec) rec))
               (mv (cons slot spec) rec hit))))
    (mv spec rec t))))
   (implies
    (not (consp spec))
    (equal (rec->spec op spec rec) (mv spec rec t)))
   )
  :hints (("goal" :in-theory '(rec->spec))))

(defthm atomic-rec->spec-replacement
  (implies (syntaxp (symbolp op))
           (equal (rec->spec op spec rec)
                  (rec->spec (xop op) spec rec)))
  :hints (("Goal" :in-theory (disable numwhich 
                                      numtype
                                      op-base
                                      ptr?
                                      WHICHTYPE
                                      slot-p
                                      SLOT-EXTENSIONALITY!!
                                      SKEL-EXTENSIONALITY
                                      SKEL-EXTENSIONALITY!
                                      SLOT-EXTENSIONALITY
                                      ))))

(in-theory (disable (:definition rec->spec)))

(defthm rec->spec-append-reduction
  (implies (v2 (rec->spec op spec x))
           (and (v2 (rec->spec op spec (append x y)))
                (equal (v0 (rec->spec op spec (append x y)))
                       (v0 (rec->spec op spec x)))
                (equal (v1 (rec->spec op spec (append x y)))
                       (append (v1 (rec->spec op spec x)) y))))
  :hints (("goal" :do-not '(generalize eliminate-destructors
                                       fertilize eliminate-irrelevance)
           :in-theory (e/d (LIST::CDR-APPEND
                            LIST::CAR-APPEND
                                        ;binary-append
                            SLOT-EXTENSIONALITY
                            SKEL-EXTENSIONALITY
                            )
                           (;for efficiency:
                            ATOMIC-REC->SPEC-REPLACEMENT
                            BINARY-APPEND
                            SLOT-P
                            skel-extensionality! 
                            SLOT-EXTENSIONALITY!!
                            default-car 
                            numwhich
                            numtype
                            ptr?
                            op-base
                            whichtype
                            ;OPEN-REC->SPEC
                            ;; non-integer-size-wfixn
                            ))
           :do-not-induct t
           :induct (rec->spec op spec x))
          ))

(defun not-which (op)
  (let ((which (op-which op)))
    (let ((nwhich (numwhich which)))
      (let ((not-nwhich (logxor #x3 nwhich)))
        (update-op op :which (whichnum not-nwhich))))))

(defthm op-base-of-op-base
  (equal (OP-BASE h
                  type
                  (OP-BASE h
                           type
                           base
                           valu)
                  valu)
         (OP-BASE h
                  type
                  base
                  valu)))

(defthm rec->spec-of-spec->rec-h*-spec-helper
  (let ((template (h*-spec (not-which op) spec)))
    (and (v2 (rec->spec op template (spec->rec op ptr spec)))
         (equal (v0 (rec->spec op template (spec->rec op ptr spec)))
                (h*-spec (update-op op :which :all) spec))
         (not (consp (v1 (rec->spec op template (spec->rec op ptr spec)))))))
  :rule-classes nil
  :hints (("goal" :induct (spec->rec op ptr spec)
           :do-not '(generalize eliminate-destructors 
                                fertilize eliminate-irrelevance)
           :in-theory (e/d (binary-append) (numwhich 
                                            numtype
                                            op-base
                                            ;;whichtype
                                            ;;ptr?
                                            ;;not-which
                                            whichnum
                                            slot-p
                                            ))
           :do-not-induct t)
          ))

(defthm rec->spec-of-spec->rec-h*-spec-raw
  (and (v2 (rec->spec op spec (spec->rec op ptr spec)))
       (equal (v0 (rec->spec op spec (spec->rec op ptr spec)))
              (h*-spec (update-op op :which :all) spec))
       (not (consp (v1 (rec->spec op spec (spec->rec op ptr spec))))))
  :hints (("goal" :induct (spec->rec op ptr spec))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors 
                                      fertilize eliminate-irrelevance)
                         :in-theory (e/d (binary-append) 
                                         (numwhich numtype 
                                                   SLOT-EXTENSIONALITY
                                                   ;ptr?
                                                   op-base
                                                   whichtype
                                                   slot-p
                                                   ))
                         :do-not-induct t))))


(defthm rec->spec-of-spec->rec-h*-spec
  (implies
   (equal template (h*-spec (not-which op) spec))
   (and (v2 (rec->spec op template (spec->rec op ptr spec)))
        (equal (v0 (rec->spec op template (spec->rec op ptr spec)))
               (h*-spec (update-op op :which :all) spec))
        (not (consp (v1 (rec->spec op template (spec->rec op ptr spec)))))))
  :hints (("goal" :in-theory nil
           :use (:instance rec->spec-of-spec->rec-h*-spec-helper))))

(defthmd rec->spec-h*-spec-not-which-introduction-1
  (implies (and (x? op)
                (syntaxp (not (and (consp spec) (equal (car spec) 'h*-spec)))))
           (implies
            (v2 (rec->spec op (h*-spec (not-which op) spec) rec))
            (equal (v1 (rec->spec op spec rec))
                   (v1 (rec->spec op (h*-spec (not-which op) spec) rec)))))
  :otf-flg t
  :hints (("goal" :do-not '(generalize preprocess eliminate-destructors
                                       fertilize eliminate-irrelevance)
           :in-theory (e/d (g? binary-append) 
                           (SKEL-EXTENSIONALITY!
                            ;;GACC::ATOMIC-REC->SPEC-REPLACEMENT ;made things worse...
                            numwhich
                            op-base
                            slot-p
                            ;; numtype
                            whichnum
                            whichtype
                            x?
                            ptr?
                            not-which
                            ))
           :do-not-induct t
           :induct (rec->spec op spec rec))
          ))

(defthmd rec->spec-h*-spec-not-which-introduction-2
  (implies (and (x? op)
                (syntaxp (not (and (consp spec) (equal (car spec) 'h*-spec)))))
           (implies
            (v2 (rec->spec op (h*-spec (not-which op) spec) rec))
            (equal (v0 (rec->spec op spec rec))
                   (v0 (rec->spec op (h*-spec (not-which op) spec) rec)))))
;  :otf-flg t
  :hints (("goal" :do-not '(generalize preprocess eliminate-destructors
                                       fertilize eliminate-irrelevance)
           :in-theory (e/d (g? rec->spec-h*-spec-not-which-introduction-1) 
                           (SKEL-EXTENSIONALITY!
                            SLOT-EXTENSIONALITY!!
                            SLOT-EXTENSIONALITY
                            ;;GACC::ATOMIC-REC->SPEC-REPLACEMENT ;made things worse...
;                            numwhich
;                            op-base
                            ;; numtype
 ;                           whichnum
                            ;;whichtype
                            ;; ;x?
              ;              ptr?
               ;             not-which
                            ))
           :do-not-induct t
           :induct (rec->spec op spec rec))
          ))

(defthmd rec->spec-h*-spec-not-which-introduction-3
  (implies (and (x? op)
                (syntaxp (not (and (consp spec) (equal (car spec) 'h*-spec)))))
           (equal (v2 (rec->spec op spec rec))
                  (v2 (rec->spec op (h*-spec (not-which op) spec) rec))))
  :hints (("goal" :do-not '(generalize preprocess eliminate-destructors
                                       fertilize eliminate-irrelevance)
           :in-theory (e/d (g? rec->spec-h*-spec-not-which-introduction-1) 
                           (SKEL-EXTENSIONALITY!
                            ;;GACC::ATOMIC-REC->SPEC-REPLACEMENT ;made things worse...
                            numwhich
                            numtype
                            whichnum
                             op-base
                            ;; whichtype
                            ;;x?
                            ptr?
                            ;; not-which
                            ))
           :do-not-induct t
           :induct (rec->spec op spec rec))
          ))
 
(defun rec->spec-of-spec->rec-hyp (op template spec)
  (equal (h*-spec (not-which op) template)
         (h*-spec (not-which op) spec)))
 
(defthmd rec->spec-of-spec->rec
  (implies
   (and
    (x? op)
    (force (rec->spec-of-spec->rec-hyp op template spec)))
   (equal (v0 (rec->spec op template (spec->rec op ptr spec)))
          (h*-spec (update-op op :which :all) spec)))
  :hints (("goal" :in-theory (enable rec->spec-of-spec->rec-hyp
                                     rec->spec-h*-spec-not-which-introduction-1
                                     rec->spec-h*-spec-not-which-introduction-2
                                     rec->spec-h*-spec-not-which-introduction-3
                                     rec->spec-of-spec->rec-h*-spec
                                     ))))
 


(defthm g*-rec-g*-spec-commute
  (implies
   (x? op)
   (equal (g*-rec (spec->rec op ptr spec) ram)
          (spec->rec op ptr (g*-spec op ptr spec ram))))
  :hints (("goal" :in-theory (disable; WFIXN-DOES-NOTHING-REWRITE
                                      ;UNFIXED-SIZE-WFIXN-0-TO-8 ;why?
                                      )
           :induct (g*-spec op ptr spec ram))))

(defthm g*-spec-default-which
  (implies
   (and (syntaxp (not (quotep w)))
        (not (equal w :all))
        (not (equal w :ptr))
        (not (equal w :nil)))
   (equal (g*-spec (op w h) ptr spec ram)
          (g*-spec (op :val h) ptr spec ram)))
  :hints (("Goal" :in-theory (disable ACL2::LOGAND-EXPT-CONSTANT-VERSION ;why?
                                      ))))

(defthmd g*-spec-g*-rec-reduction
  (implies
   (x? op)
   (equal (g*-spec op ptr spec ram)
          (v0 (rec->spec op spec (g*-rec (spec->rec op ptr spec) ram)))))
  :hints (("goal" :in-theory (enable rec->spec-of-spec->rec acl2::logbit))))

(defthm f*-rec-append
  (equal (f*-rec (append x y))
         (append (f*-rec x) (f*-rec y))))

(defthmd f*-spec-f*-rec-reduction
  (equal (f*-spec op ptr spec)
         (f*-rec (spec->rec op ptr spec))))

(defun h*-rec (rec)
  (if (consp rec)
      (let ((slot (car rec)))
        (if (slot-p slot)
            (let ((size  (slot-size slot))
                  (value (slot-val  slot)))
              (let ((slot (update-slot slot :val (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                                                value))))
                (cons slot (h*-rec (cdr rec)))))
          (cons slot
                (h*-rec (cdr rec)))))
    rec))

(defthm true-listp-h*-rec
  (equal (true-listp (h*-rec rec))
         (true-listp rec)))

(defthm len-h*-rec
  (equal (len (h*-rec rec))
         (len rec)))

(defthm h*-rec-append
  (equal (h*-rec (append x y))
         (append (h*-rec x) (h*-rec y))))

(defthm h*-spec-h*-spec-commute
  (implies
   (implies (g-op op) (optype op :ptr))
   (equal (h*-rec (spec->rec op ptr spec))
          (spec->rec op ptr (h*-spec op spec))))
  :hints (("goal" :in-theory (enable g?))))


(encapsulate
 ()

 (local
  (defthm h*-spec-op-reduction
    (implies
     (syntaxp (symbolp op))
     (equal (h*-spec op spec)
            (h*-spec (op (op-which op) (op-how op)) spec)))))

 (defthm spec-rec-h*-spec-reduction
   (implies
    (x? op)
    (equal 
     (spec->rec op ptr (h*-spec op spec))
     (spec->rec op ptr spec))))

 (defthmd h*-spec-h*-rec-reduction
   (implies
    (and
     (x? op) 
     (equal (op-which op) :all))
    (equal (h*-spec op spec)
           (v0 (rec->spec op spec (h*-rec (spec->rec op ptr spec))))))
   :hints (("goal" :in-theory (disable h*-spec-op-reduction))
           ("goal''" :in-theory (enable h*-spec-op-reduction))))

 )

;; ===============================================
;;
;; z* rules
;;
;; ===============================================

(in-theory (disable z*))

(defthm s*-rec-over-wx
  (implies
   (disjoint (sblk size off) (flat (f*-rec spec)))
   (equal (s*-rec spec (wx size off value ram))
          (wx size off value (s*-rec spec ram))))
  :hints (("goal" :in-theory (enable ;my-wx-over-wx
                                     flat))))

;; We are beginning to see a weakness in our representation. There 
;; is no good reason for (f*-rec rec) to be unique in the following
;; theorem, except that it makes it convenient to prove the result.
;; Our use of s*-rec type functions should have gone all the way down
;; to rd/wr.  There should be generic r*/w* functions that take an
;; association list of _atomic_ addresses and updates/inserts that
;; list.  These association lists could then have been lifted into
;; rx/wx and, ultimately, into g*/s*.  The fact that rx/wx is our
;; atomic operation is a weakness in expressing the sorts of things
;; we want to say.


(defthm s*-rec-over-z*
  (implies
   (and
    (unique (flat (f*-rec rec)))
    (disjoint-list (flat (f*-rec rec)) zlist))
   (equal (z* zlist (s*-rec rec ram))
          (s*-rec rec (z* zlist ram))))
  :hints (("goal" :in-theory (enable
                              flat
                              z*-over-wx-commute
                              bag::disjoint-list-reduction
                              ))))


(defthm z*-s*-rec-introduction
  (implies (unique (flat (f*-rec rec)))
           (equal (equal ram1 (s*-rec rec ram2))
                  (and (equal (z* (list (flat (f*-rec rec))) ram1)
                              (z* (list (flat (f*-rec rec))) ram2))
                       (equal (g*-rec rec ram1)
                              (h*-rec rec)))))
  :hints (("Goal" :in-theory (enable flat))))

(defthmd z*-cons-reduction
  (implies
   (syntaxp (not (quotep b)))
   (equal (z* (cons a b) ram)
          (z* b (z* (list a) ram))))
  :hints (("goal" :in-theory (enable z*))))

(defthm z*-commute
  (equal (z* a (z* b ram))
         (z* b (z* a ram)))
  :hints (("goal" :in-theory (enable z*-reduction)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm g*-rec-over-z*
  (implies
   (disjoint-list (flat (f*-rec rec)) zlist)
   (equal (g*-rec rec (z* zlist ram))
          (g*-rec rec ram)))
  :hints (("goal" :in-theory (enable flat bag::disjoint-list-reduction))))


(defthm z*-s*-rec-induction
  (implies (and (unique (flat (f*-rec rec)))
                (disjoint-list (flat (f*-rec rec)) zlist))
           (equal (equal (z* zlist (s*-rec rec ram1))
                         (z* zlist ram2))
                  (and (equal (z* (cons (flat (f*-rec rec)) zlist) ram1)
                              (z* (cons (flat (f*-rec rec)) zlist) ram2))
                       (equal (h*-rec rec)
                              (g*-rec rec ram2)))))
  :hints (("goal" :in-theory `(g*-rec-over-z*
                               z*-commute
                               z*-cons-reduction
                               s*-rec-over-z*
                               z*-s*-rec-introduction))))

(defthm z*-s*-rec-elimination
  (implies
   (and
    (unique (flat (f*-rec rec)))
    (any-subbagp (flat (f*-rec rec)) zlist))
   (equal (z* zlist (s*-rec rec ram))
          (z* zlist ram))))

(defthmd g*-spec-h*-spec-equality-reduction
  (implies
   (x? op)
   (equal (equal (g*-spec op ptr spec ram)
                 (h*-spec (op :all :x) spec))
          (equal (g*-rec (spec->rec op ptr spec) ram)
                 (h*-rec (spec->rec op ptr spec)))))
  :hints (("goal" :induct (spec->rec op ptr spec) :in-theory (disable
                                                              ;UNFIXED-SIZE-WFIXN-0-TO-8 ;bzo think about this
                                                              ))))

(defthm z*-s*-spec-introduction
  (implies
   (and
    (x? op)
    (unique (flat (f*-spec op ptr spec))))
   (equal (equal ram1 (s*-spec op ptr spec ram2))
          (and (equal (z* (list (flat (f*-spec op ptr spec))) ram1)
                      (z* (list (flat (f*-spec op ptr spec))) ram2))
               (equal (g*-spec op ptr spec ram1)
                      (h*-spec (op :all :x) spec)))))
  :hints (("goal" :in-theory '(z*-s*-rec-introduction
                               s*-spec-s*-rec-reduction
                               f*-spec-f*-rec-reduction
                               g*-spec-h*-spec-equality-reduction
                               ))))

(defthm z*-s*-spec-induction
  (implies
   (and
    (x? op)
    (unique (flat (f*-spec op ptr spec)))
    (disjoint-list (flat (f*-spec op ptr spec)) zlist))
   (equal (equal (z* zlist (s*-spec op ptr spec ram1))
                      (z* zlist ram2))
               (and (equal (z* (cons (flat (f*-spec op ptr spec)) zlist) ram1)
                           (z* (cons (flat (f*-spec op ptr spec)) zlist) ram2))
                    (equal (h*-spec (op :all :x) spec)
                           (g*-spec op ptr spec ram2)))))
  :hints (("goal" :in-theory '(z*-s*-rec-induction
                               s*-spec-s*-rec-reduction
                               f*-spec-f*-rec-reduction
                               g*-spec-h*-spec-equality-reduction
                               ))))


(defthm z*-s*-spec-elimination
  (implies
   (and
    (unique (flat (f*-spec op ptr spec)))
    (any-subbagp (flat (f*-spec op ptr spec)) zlist))
   (equal (z* zlist (s*-spec op ptr spec ram))
          (z* zlist ram)))
  :hints (("goal" :in-theory '(s*-spec-s*-rec-reduction
                               f*-spec-f*-rec-reduction
                               z*-s*-rec-elimination
                               ))))

(defthm s*-spec-over-z*
  (implies
   (and
    (unique (flat (f*-spec op ptr spec)))
    (disjoint-list (flat (f*-spec op ptr spec)) zlist))
   (equal (z* zlist (s*-spec op ptr spec ram))
          (s*-spec op ptr spec (z* zlist ram))))
  :hints (("goal" :in-theory '(s*-rec-over-z*
                               s*-spec-s*-rec-reduction
                               f*-spec-f*-rec-reduction
                               ))))

(defthm g*-spec-over-z*
  (implies
   (and
    (x? op)
    (disjoint-list (flat (f*-spec op ptr spec)) zlist))
   (equal (g*-spec op ptr spec (z* zlist ram))
          (g*-spec op ptr spec ram)))
  :hints (("goal" :in-theory '(g*-spec-g*-rec-reduction
                               f*-spec-f*-rec-reduction
                               g*-rec-over-z*
                               ))))

(defthm s*-list-over-z*
  (implies
   (and
    (x? op)
    (unique (flat (f*-list op spec)))
    (disjoint-list (flat (f*-list op spec)) zlist))
   (equal (z* zlist (s*-list op spec ram))
          (s*-list op spec (z* zlist ram))))
  :hints (("goal" :in-theory (e/d ((:induction s*-list)) (
                                                          ;(:META BAG::*META*-SUBBAGP-LIST)
                                                          ))
;           :do-not '(generalize eliminate-destructors)
           :induct (s*-list op spec ram))))

(defthm z*-s*-list-elimination
  (implies
   (and
    (unique (flat (f*-list op spec)))
    (any-subbagp (flat (f*-list op spec)) zlist))
   (equal (z* zlist (s*-list op spec ram))
          (z* zlist ram)))
  :hints (("goal" :in-theory (enable (:induction s*-list)))))


(defthm rs-of-h*-spec
  (implies
   (not (g-op op))
   (equal (rs size off base (h*-spec op spec))
          (skel (if (equal (op-how op) :z) 0
                  (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                 (skel-base (rs size off base spec))))
                (h*-spec op (skel-spec (rs size off base spec))))))
  :hints (("goal" :in-theory (enable g? ;unfixed-size-wfixn
                                     )
           :induct (rs size off base spec))))

(defthm zz-of-ws
  (implies
   (memberp (sblk wsize (+<> woff base)) slist)
   (equal (zz vlist slist base (ws wsize woff base v spec))
          (zz vlist slist base spec)))
  :hints (("goal" :in-theory (enable zs-over-ws zz))))

(defthm zz-of-wv
  (implies
   (memberp (sblk wsize (+<> woff base)) vlist)
   (equal (zz vlist slist base (wv wsize woff base v spec))
          (zz vlist slist base spec)))
  :hints (("goal" :in-theory (enable zv-over-wv zz))))

;;
;;
;; Spec type
;;
;;

(defun spec-type (spec type)
  (equal (h*-spec (op :nil :z) spec) type))

(defthm spec-type-nil-reduction
  (equal (spec-type list nil)
         (equal list nil))
  :hints (("goal" :in-theory (enable spec-type))))

(defthm spec-type-h*-spec-reduction
  (implies
   (and
    (equal hspec (h*-spec (op :nil :z) spec))
    (syntaxp (not (equal hspec spec)))
    )
   (equal (spec-type spec type)
          (spec-type (h*-spec (op :nil :z) spec) type)))
  :hints (("goal" :in-theory (enable spec-type))))

(defthm spec-type-free
  (implies
   (spec-type (h*-spec (op :nil :z) spec) type)
   (equal (h*-spec (op :nil :z) spec)
          type)))

(defthm spec-type-equality
  (implies
   (and
    (equal hspec (h*-spec (op :nil :z) spec))
    (syntaxp (equal hspec type))
    (equal hspec type)
    )
   (spec-type spec type)))

(in-theory (disable spec-type))

(defthm rv-of-wv-all
  (implies (memberp (sblk size (|+<>| off base))
                   (keys-spec :all base spec))
           (equal (rv size
                      off base (wv size off base value spec))
                  (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                 value
                         )))
  :hints (("goal" :in-theory nil
           :use ((:instance rv-of-wv (w :all))))))

(defmacro shape-list (list)
  `(h*-list (op :all :x) ,list))

(defmacro shape-spec (spec)
  `(h*-spec (op :all :x) ,spec))

(defmacro shape-skel (skel)
  `(skel (skel-base ,skel) (h*-spec (op :all :x) (skel-spec ,skel))))

(defmacro skel-type (skel type)
  `(spec-type (skel-spec ,skel) ,type))

(defmacro struc (op skel)
  `(h*-spec ,op (skel-spec ,skel)))

(defmacro flat-skel (w ptr skel)
  `(f*-spec (op ,w :x) ,ptr (skel-spec ,skel)))

(defmacro struc-list (op skels)
  `(h*-list ,op ,skels))

(defmacro flat-list (h skels)
  `(f*-list (op ,h :x) ,skels))

(defmacro fixed-skel-spec (skel)
  `(fixed-spec-p (skel-spec ,skel)))

;;
;; Some useful bind-free stuff ..
;;

(defun fn-instance-rec (arglist fname term)
  (declare (type t arglist fname term))
  (if (consp term)
      (if arglist
          (or (fn-instance-rec nil fname (car term))
              (fn-instance-rec t   fname (cdr term)))
        (let ((fn (car term)))
          (if (equal fn fname)
              (cdr term)
            (fn-instance-rec t fname (cdr term)))))
    nil))

(defun bind-keys (args term)
  (declare (type t args term))
  (if (and (consp args)
           (consp term))
      (cons (cons (car args) (car term))
            (bind-keys (cdr args) (cdr term)))
    nil))

(defun fn-instance-fn (fname args arglist term)
  (declare (type t fname args term))
  (let ((term (fn-instance-rec arglist fname term)))
    (bind-keys args term)))


(defun fn-instance-wrapper (fname args term hyps mfc acl2::state)
  (declare (xargs :stobjs (acl2::state)
                  :verify-guards t)
           (ignore acl2::state))
  (let ((hit (fn-instance-fn fname args nil term)))
    (or hit
        (and hyps
             (let ((hyps (acl2::mfc-clause mfc)))
               (fn-instance-fn fname args t hyps))))))

(defmacro fn-instance (fname args term &key (hyps 'nil))
  `(fn-instance-wrapper ,fname ,args ,term ,hyps acl2::mfc acl2::state))

(defmacro bind-fn-instance (fn term &key (hyps 'nil))
  `(bind-free (fn-instance (quote ,(car fn)) (quote ,(cdr fn)) ,term :hyps ,hyps) ,(cdr fn)))

(defmacro bind-fn-instance-equal (fn term &key (hyps 'nil))
  `(and (bind-fn-instance ,fn ,term :hyps ,hyps)
        (equal ,term ,fn)))

;(in-theory (disable acl2::LEN-REDUCTION))

(defun split-blk-fix-slot (slot)
  (if (slot-p slot)
      (let ((slot (fix-slot slot)))
        (let ((type (slot-type slot))
              (skel (slot-skel slot)))
          (if (ptr? type)
              (let ((base (skel-base skel)))
                (let ((slot (update-slot slot :skel (skel base nil))))
                  slot))
            slot)))
    slot))
  
(defthm v0-split-blk
  (equal (v0 (split-blk (cons slot list)))
         (cons (split-blk-fix-slot slot) (v0 (split-blk list)))))

(in-theory (disable open-split-blk))

(defthm h*-spec-wv-val
  (implies
   (and
    (not (optype hop :val))
    (not (memberp (sblk wsize (+<> woff base)) (keys-spec :ptr base spec))))
   (equal (h*-spec hop (wv wsize woff base value spec))
          (h*-spec hop spec)))
  :hints (("goal" :induct (wv wsize woff base value spec)
           :in-theory (enable open-split-blk open-wv memberp))))

(defthm h*-spec-wv-val-2
  (implies (and (not (optype hop :val))
                (equal v (h*-spec hop spec))
                (not (memberp (sblk wsize (|+<>| woff base))
                              (keys-spec :ptr base v))))
           (equal (h*-spec hop (wv wsize woff base value spec))
                  v))
  :hints (("goal" :in-theory '(h*-spec-wv-val split-blk-h*-spec))))

(in-theory
 (disable
  h*-spec-wv-val
  h*-spec-wv-val-2
  ))

(defthm f*-spec-h*-spec-introduction
  (implies
   (and
    (x? fop)
    (equal hspec (h*-spec (op :nil :x) spec))
    (syntaxp (not (equal hspec spec))))
   (equal (f*-spec fop base spec)
          (f*-spec fop base hspec)))
  :hints (("goal''" :induct (f*-spec fop base spec))))

(defthm f*-list-h*-list-introduction
  (implies
   (and
    (x? fop)
    (equal hlist (h*-list (op :nil :x) list))
    (syntaxp (not (equal hlist list))))
   (equal (f*-list fop list)
          (f*-list fop hlist)))
  :hints (("goal''" :induct (f*-list fop list))))

(in-theory
 (disable
  f*-spec-h*-spec-introduction
  f*-list-h*-list-introduction
  ))

(defthm f*-spec-h*-spec-reduction
  (implies
   (and
    (x? fop)
    (x? hop))
   (equal (f*-spec fop base (h*-spec hop spec))
          (f*-spec fop base spec))))

(theory-invariant
 (incompatible
  (:rewrite f*-spec-h*-spec-reduction)
  (:rewrite f*-spec-h*-spec-introduction)
  ))

(in-theory
 (disable
  g*-spec-default-which
  ))



;;
;; blog
;;

(defthm f*-spec-of-g*-spec
  (implies
   (and
    (x? fop)
    (equal (op-how gop) :x))
   (equal (f*-spec fop fptr (g*-spec gop gptr spec ram))
          (f*-spec fop fptr spec)))
  :hints (("goal" :induct (F*-G*-INDUCTION FOP FPTR GOP GPTR SPEC RAM))))

(defthm f*-list-of-g*-list
  (implies
   (and
    (x? fop)
    (equal (op-how gop) :x))
   (equal (f*-list fop (g*-list gop list ram))
          (f*-list fop list)))
  :hints (("goal" :induct (g*-list gop list ram)
           :in-theory (enable (:induction g*-list))
           )))


(defun rd-spec (list ram)
  (if (consp list)
      (cons (rd-list (car list) ram)
            (rd-spec (cdr list) ram))
    nil))

(defun wr-spec (list value ram)
  (if (and (consp list)
           (consp value))
      (let ((ram (wr-list (car list) (enlistw (len (car list)) (car value)) ram)))
        (wr-spec (cdr list) (cdr value) ram))
    ram))

(defun g*-rd (spec list)
  (if (consp spec)
      (let ((slot (car spec)))
        (if (slot-p slot)
            (let ((value (wintlist (car list))))
              (cons (update-slot (car spec) :val value)
                    (g*-rd (cdr spec) (cdr list))))
          (cons slot
                (g*-rd (cdr spec) list))))
    spec))

(defun v*-rec (spec)
  (if (consp spec)
      (let ((slot (car spec)))
           (if (slot-p slot)
               (let ((size (slot-size slot))
                     (value (slot-val slot)))
                    (cons (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                         value)
                          (v*-rec (cdr spec))))
               (v*-rec (cdr spec))))
      nil))

(defthm s*-rec-reduction
  (equal (s*-rec spec ram)
         (wr-spec (f*-rec spec) (v*-rec spec) ram))
  :hints (("goal" :in-theory (e/d (WX-TO-WR-LIST-REDUCTION) (UNFIXED-SIZE-SBLK)))))

(defun list->rec (op list)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((key  (line-key  line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (append (spec->rec op base (skel-spec skel))
                        (list->rec op (cdr list)))))
          (list->rec op (cdr list))))
    nil))

(defun rec->list (op list rec)
  (if (consp list)
      (let ((line (car list)))
        (if (line-p line)
            (let ((key  (line-key  line))
                  (skel (line-skel line)))
              (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                (met ((spec rec hit) (rec->spec op (skel-spec skel) rec))
                     (if (not hit) (mv list rec nil)
                       (met ((list rec hit) (rec->list op (cdr list) rec))
                            (mv (cons (update-line line :skel (skel base spec))
                                      list)
                                rec
                                hit))))))
          (met ((list rec hit) (rec->list op (cdr list) rec))
               (mv (cons line list) rec hit))))
    (mv list rec t)))


(defthm open-rec->list
  (and
   (implies
    (consp list)
    (equal (rec->list op list rec)
           (let ((line (car list)))
             (if (line-p line)
                 (let ((key  (line-key  line))
                       (skel (line-skel line)))
                   (let ((base (op-base (op-how op) :ptr (skel-base skel) key)))
                     (met ((spec rec hit) (rec->spec op (skel-spec skel) rec))
                          (if (not hit) (mv list rec nil)
                            (met ((list rec hit) (rec->list op (cdr list) rec))
                                 (mv (cons (update-line line :skel (skel base spec))
                                           list)
                                     rec
                                     hit))))))
               (met ((list rec hit) (rec->list op (cdr list) rec))
                    (mv (cons line list) rec hit))))))
   (implies
    (not (consp list))
    (equal (rec->list op list rec)
           (mv list rec t))))
  :hints (("goal" :in-theory '(rec->list))))

(defthm atomic-rec->list-replacement
  (implies
   (syntaxp (symbolp op))
   (equal (rec->list op list rec)
          (rec->list (xop op) list rec))))

(defthm rec->list-append-reduction
  (implies
   (v2 (rec->list op list x))
   (and (v2 (rec->list op list (append x y)))
        (equal (v0 (rec->list op list (append x y)))
               (v0 (rec->list op list x)))
        (equal (v1 (rec->list op list (append x y)))
               (append (v1 (rec->list op list x)) y))))
  :hints (("goal" :induct (rec->list op list x))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors
                                      fertilize eliminate-irrelevance)
                         :in-theory (enable binary-append)
                         :do-not-induct t))))


(defthm rec->list-of-list->rec-h*-list-helper
  (let ((template (h*-list (not-which op) list)))
    (and (v2 (rec->list op template (list->rec op list)))
         (equal (v0 (rec->list op template (list->rec op list)))
                (h*-list (update-op op :which :all) list))
         (not (consp (v1 (rec->list op template (list->rec op list)))))))
  :rule-classes nil
  :hints (("goal" :induct (list->rec op list))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors 
                                      fertilize eliminate-irrelevance)
                         :in-theory (enable binary-append)
                         :do-not-induct t))))

(defthm rec->list-of-list->rec-h*-list-raw
  (and (v2 (rec->list op list (list->rec op list)))
       (equal (v0 (rec->list op list (list->rec op list)))
              (h*-list (update-op op :which :all) list))
       (not (consp (v1 (rec->list op list (list->rec op list))))))
  :hints (("goal" :induct (list->rec op list))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors 
                                      fertilize eliminate-irrelevance)
                         :in-theory (enable binary-append)
                         :do-not-induct t))))

(defthm rec->list-of-list->rec-h*-list
  (implies
   (equal template (h*-list (not-which op) list))
   (and (v2 (rec->list op template (list->rec op list)))
        (equal (v0 (rec->list op template (list->rec op list)))
               (h*-list (update-op op :which :all) list))
        (not (consp (v1 (rec->list op template (list->rec op list)))))))
  :hints (("goal" :in-theory nil
           :use (:instance rec->list-of-list->rec-h*-list-helper))))

(defthm rec->list-h*-list-not-which-introduction
  (implies
   (and (x? op)
        (syntaxp (not (and (consp list) (equal (car list) 'h*-list))))
        (v2 (rec->list op (h*-list (not-which op) list) rec)))
   (and (iff (v2 (rec->list op list rec))
             (v2 (rec->list op (h*-list (not-which op) list) rec)))
        (implies
         (v2 (rec->list op (h*-list (not-which op) list) rec))
         (and (equal (v1 (rec->list op list rec))
                     (v1 (rec->list op (h*-list (not-which op) list) rec)))
              (equal (v0 (rec->list op list rec))
                     (v0 (rec->list op (h*-list (not-which op) list) rec)))))))
  :hints (("goal" :induct (rec->list op list rec))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors
                                      fertilize eliminate-irrelevance)
                         :in-theory (e/d (rec->spec-h*-spec-not-which-introduction-1
                                            rec->spec-h*-spec-not-which-introduction-2
                                            rec->spec-h*-spec-not-which-introduction-3
                                            g? ;binary-append
                                            ) 
                                         (numwhich
                                          whichnum
                                          op-base
                                          ;not-which
                                          ))
                         :do-not-induct t))))

(in-theory
 (disable
  rec->list-h*-list-not-which-introduction
  ))


(defun rec->list-of-list->rec-hyp (op template list)
   (equal (h*-list (not-which op) template)
          (h*-list (not-which op) list)))

(defthm rec->list-of-list->rec
  (implies
   (and
    (x? op)
    (rec->list-of-list->rec-hyp op template list))
   (equal (v0 (rec->list op template (list->rec op list)))
          (h*-list (update-op op :which :all) list)))
  :hints (("goal" :in-theory `(rec->list-of-list->rec-hyp
                               rec->list-h*-list-not-which-introduction
                               rec->list-of-list->rec-h*-list
                               ))))

(defthm g*-rec-g*-list-commute
  (implies (x? op)
           (equal (g*-rec (list->rec op list) ram)
                  (list->rec op (g*-list op list ram))))
  :hints (("goal" :induct (g*-list op list ram)
           :do-not '(generalize preprocess eliminate-destructors 
                                fertilize eliminate-irrelevance)
           :in-theory (enable g? open-g*-list (:induction g*-list))
           :do-not-induct t)))

(defthmd g*-list-g*-rec-commute
  (implies
   (x? op)
   (equal (list->rec op (g*-list op list ram))
          (g*-rec (list->rec op list) ram))))

(theory-invariant
 (incompatible
  (:rewrite g*-list-g*-rec-commute)
  (:rewrite g*-rec-g*-list-commute)
  ))

(defthm g*-list-default-which
  (implies
   (and (syntaxp (not (quotep w)))
        (not (equal w :all))
        (not (equal w :ptr))
        (not (equal w :nil)))
   (equal (g*-list (op w h) list ram)
          (g*-list (op :val h) list ram)))
  :hints (("goal" :in-theory (enable g*-list g*-spec-default-which))))

(defthmd g*-rec-reduction
  (equal (g*-rec spec ram)
         (g*-rd spec (rd-spec (f*-rec spec) ram)))
  :hints (("Goal" :in-theory (enable RX-TO-RD-LIST-REDUCTION))))

;(local (in-theory (enable LEN))) 

(defthm len-v1-rec->spec
  (implies (x? op)
           (equal (len (v1 (rec->spec op spec rec)))
                  (nfix (- (len rec) (len (f*-spec op 0 spec))))))
  :hints (("goal" :in-theory (disable numwhich numtype whichtype ptr? slot-p op-base len x? whichtype
                                      ATOMIC-F*-OP-REPLACEMENT ;looped!
                                      ATOMIC-REC->SPEC-REPLACEMENT
                                      )
           :induct (rec->spec op spec rec))))

(defthm v2-rec->spec-reduction
  (implies (x? op)
           (iff (v2 (rec->spec op spec rec))
                (<= (len (f*-spec op ptr spec)) (len rec))))
  :hints (("goal" :in-theory (disable numwhich numtype op-base ptr? whichtype)
           :induct (rec->spec op spec rec))))

(defthm len-spec->rec
  (equal (len (spec->rec op ptr spec))
         (len (f*-spec op ptr spec)))
  :hints (("Goal" :in-theory (disable numwhich numtype whichtype ptr? slot-p op-base len))))

;bzo
(defthmd append-len0
  (implies (equal (len x) 0)
           (equal (append x y) y))
  :hints (("goal" :in-theory (enable binary-append))))

(defthmd g*-list-g*-rec-reduction
  (implies
   (x? op)
   (equal (g*-list op list ram)
          (v0 (rec->list op list (g*-rec (list->rec op list) ram)))))
  :hints (("goal" :induct (list->rec op list)
           :in-theory (e/d (APPEND-LEN0 ;bzo
                              rec->spec-h*-spec-not-which-introduction-1
                              rec->spec-h*-spec-not-which-introduction-2
                              rec->spec-h*-spec-not-which-introduction-3
                              g*-spec-default-which
                              rec->list-of-list->rec
                              rec->spec-of-spec->rec) 
                           (;numwhich
                            )))))

(defthmd f*-list-f*-rec-reduction
  (equal (f*-list op list)
         (f*-rec (list->rec op list)))
  :hints (("goal" :in-theory (enable f*-spec-f*-rec-reduction))))

(defthm h*-rec-h*-list-commute
  (implies
   (implies (g-op op) (optype op :ptr))
   (equal (h*-rec (list->rec op list))
          (list->rec op (h*-list op list))))
  :hints (("goal" :in-theory (enable g?))))

(defthm list-rec-h*-list-reduction
   (implies
    (x? op)
    (equal 
     (list->rec op (h*-list op list))
     (list->rec op list))))

(defthm atomic-list->rec-op-replacement
  (implies
   (syntaxp (symbolp op))
   (equal (list->rec op list)
          (list->rec (xop op) list))))

(defthm h*-list-h*-rec-reduction
  (implies
   (and
    (x? op)
    (equal (op-which op) :all))
   (equal (h*-list op list)
          (v0 (rec->list op list (h*-rec (list->rec op list)))))))

(in-theory
 (disable
  h*-list-h*-rec-reduction
  ))

(in-theory
 (disable
  s*-rec-reduction
  ))

(defthm s*-rec-over-s*-rec
  (implies
   (and
    (unique (flat (f*-rec list2)))
    (disjoint (flat (f*-rec list1)) (flat (f*-rec list2))))
   (equal (s*-rec list1 (s*-rec list2 ram))
          (s*-rec list2 (s*-rec list1 ram))))
  :hints (("goal" 
           :in-theory (e/d (flat) ( Z*-S*-REC-INTRODUCTION))
           :induct (s*-rec list2 ram))))


(encapsulate
 ()

 (local
  (encapsulate
   ()

   (defun rewrite= (x y)
     (equal x y))
   
   (defthm true-rewrite=
     (implies
      (equal x y)
      (rewrite= x y)))
   
   (defthm false-rewrite=
     (implies
      (not (equal x y))
      (not (rewrite= x y))))
   
   (defthm rewrite=-free
     (implies
      (rewrite= (s*-list op list ram) y)
      (equal (s*-list op list ram) y)))
   
   (in-theory
    (disable
     rewrite=
     ))
   
   (defthm s*-list-s*-rec-reduction-helper
     (implies
      (unique (flat (f*-list op list)))
      (rewrite= (s*-list op list ram)
                (s*-rec (list->rec op list) ram)))
     :hints (("goal" :in-theory (enable s*-spec-s*-rec-reduction
                                        f*-list-f*-rec-reduction))))

   ))

 (defthm s*-list-s*-rec-reduction
   (implies
    (unique (flat (f*-list op list)))
    (equal (s*-list op list ram)
           (s*-rec (list->rec op list) ram)))
   :hints (("goal" :in-theory `(rewrite=)
            :use ((:instance s*-list-s*-rec-reduction-helper)))))
 ) ;encap

(in-theory (disable s*-list-s*-rec-reduction))

(defun flattenlistw (addr vals)
  (if (and (consp addr)
           (consp vals))
      (append (enlistw (len (car addr)) (car vals))
              (flattenlistw (cdr addr) (cdr vals)))
    nil))

(defthm wr-spec-wr-rec-reduction
  (implies (and (equal (len addr) (len vals)) ;hyp added by Eric after changing wr-list..
                (unique (flat addr)))
           (equal (wr-spec addr vals ram)
                  (wr-list (flat addr) (flattenlistw addr vals) ram)))
  :hints (("Goal" :in-theory (enable flat))))

(defthm rd-spec-rd-rec-reduction
  (equal (flat (rd-spec addrs ram))
         (rd-list (flat addrs) ram))
  :hints (("Goal" ; :do-not '(generalize eliminate-destructors)
           :in-theory (enable flat append))))

(defun slot-p-list (list)
  (if (consp list)
      (and (slot-p (car list))
           (slot-p-list (cdr list)))
    t))

(defthm OFFSET-SIZE-expanded-max-offset
  (EQUAL (OFFSET-SIZE (+ -1 (* 1/8 (FIX-SIZE SIZE))))
         (FIX-SIZE SIZE))
  :hints (("Goal" :use (:instance OFFSET-SIZE-MAX-OFFSET)
           :in-theory (disable OFFSET-SIZE-MAX-OFFSET))))

(defthm v0-sblk-parms
  (equal (v0 (sblk-parms base (sblk size off)))
         (fix-size size))
  :hints (("goal" :in-theory (enable sblk-parms))))


;move?
(defthm max-offset-offset-size
  (equal (max-offset (offset-size n))
         (nfix n))
  :hints (("goal" :induct (offset-size n)
           :in-theory (e/d (max-offset)
                           ( 
                        unfixed-size-max-offset
                        offset-size-max-offset-free
                       )))))

(defthm len-sblkp
  (implies
   (and
    (sblkp sblk)
    (consp sblk))
   (equal (len sblk)
          (1+ (max-offset (v0 (sblk-parms 0 sblk))))))
  :hints (("goal" :in-theory (enable sblk-parms))))

(defun sblkp-list (list)
  (if (consp list)
      (and (sblkp (car list))
           (consp (car list))
           (sblkp-list (cdr list)))
    t))

(defun h*-rd (flat list)
  (if (consp flat)
      (let ((value (wintlist (car list))))
        (met ((size base) (sblk-parms 0 (car flat)))
             (declare (ignore base))
             (cons (acl2::loghead (gacc::fix-size size) ;wfixn 8 size 
                                  value)
                   (h*-rd (cdr flat) (cdr list)))))
    nil))

(defthm slot-p-append
  (equal (slot-p-list (append x y))
         (and (slot-p-list x)
              (slot-p-list y))))

(defthm slot-p-list-spec->rec
  (slot-p-list (spec->rec op ptr spec)))

(defthm slot-p-list-list->rec
  (slot-p-list (list->rec op list)))

(defthm v*-rec-g*-rd
  (implies
   (and
    (equal (len slist)
           (len vals))
    (slot-p-list slist))
   (equal (v*-rec (g*-rd slist vals))
          (h*-rd (f*-rec slist) vals)))
  :hints (("goal" :in-theory (enable ;unfixed-size-wfixn
                                     ))))

(defthm len-rd-spec
  (equal (len (rd-spec list ram))
         (len list)))

(defthm len-f*-rec
  (implies
   (slot-p-list list)
   (equal (len (f*-rec list))
          (len list))))

(defthm f*-rec-g*-rd
  (equal (f*-rec (g*-rd slist vals))
         (f*-rec slist)))

(defun fixlistw (f list)
  (if (consp list)
      (append (enlistw (len (car f)) (wintlist (car list)))
              (fixlistw (cdr f) (cdr list)))
    nil))

(defthm fixlistw-rd-spec
  (equal (fixlistw f (rd-spec f ram))
         (rd-list (flat f) ram))
  :hints (("Goal" :in-theory (enable flat))))

(defthm sblkp-list-f*-rec
  (sblkp-list (f*-rec rec)))

(defthm flattenlistw-h*-rd
  (implies
   (and
    (sblkp-list f)
    (equal (len f)
           (len list)))
   (equal (flattenlistw f (h*-rd f list))
          (fixlistw f list)))
  :hints (("goal" :in-theory (e/d (unfixed-size-max-offset)
                                  (wintlist enlistw)))))

(defthm true-listp-v1-rec->spec
  (implies
   (true-listp rec)
   (true-listp (v1 (rec->spec op spec rec)))))

;; ;bzo
;; (defthm nthcdr-nthcdr
;;   (equal (nthcdr n (nthcdr m list))
;;          (nthcdr (+ (nfix n) (nfix m)) list))
;;   :hints (("Goal" :in-theory (enable nthcdr))))



(local (in-theory (enable nthcdr))) ;bzo


;bzo
(defthmd nthcdr-of-one-more
  (implies (and (integerp n)
                (<= 0 n))
           (equal (NTHCDR (+ 1 n) l)
                  (nthcdr n (cdr l)))))

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (defun rewrite= (x y)
     (equal x y))
   
   (defthm true-rewrite=
     (implies
      (equal x y)
      (rewrite= x y)))
   
   (defthm false-rewrite=
     (implies
      (not (equal x y))
      (not (rewrite= x y))))
   
   (defthm rewrite=-v1
     (implies
      (rewrite= (v1 x) y)
      (equal (v1 x) y)))
   
   (in-theory
    (disable
     rewrite=
     ))

   (defthm v1-rec->spec-helper
     (implies
      (and
       (true-listp rec)
       (x? op))
      (rewrite= (v1 (rec->spec op spec rec))
                (nthcdr (len (f*-spec op 0 spec)) rec)))
     :hints (("goal" :in-theory (e/d (acl2::default-cdr nthcdr-of-one-more) (op-base numwhich numtype nthcdr ptr? whichtype slot-p)))))))

 (defthm v1-rec->spec
   (implies
    (and
     (true-listp rec)
     (x? op))
    (equal (v1 (rec->spec op spec rec))
           (nthcdr (len (f*-spec op 0 spec)) rec)))
   :hints (("goal" :in-theory `(rewrite=)
            :use ((:instance v1-rec->spec-helper)))))

 )



(in-theory
 (disable
  acl2::s-equal-differential
  ))

(defthm atomic-g*-list-op-replacment
  (implies
   (syntaxp (symbolp gop))
   (equal (g*-list gop list ram)
          (g*-list (xop gop) list ram)))
  :hints (("Goal" :in-theory (enable g*-list))))

;tried replacing iff with equal, but the proof broke..
(defthm g*-list-h*-list-equality-reduction
  (implies
   (x? op)
   (iff (equal (g*-list op list ram) (h*-list (op :all :x) list))
        (equal (g*-rec (list->rec op list) ram) (h*-rec (list->rec op list)))))
  :hints (("goal" :induct (list->rec op list))
          (and (consp (cadr acl2::id))
               `(:do-not '(generalize preprocess eliminate-destructors 
                                      fertilize eliminate-irrelevance)
                         :in-theory (enable g? 
                                            g*-spec-h*-spec-equality-reduction)
                         :do-not-induct t))))

(defthm z*-s*-list-introduction
  (implies
   (and
    (x? op)
    (unique (flat (f*-list op list))))
   (equal (equal ram1 (s*-list op list ram2))
          (and (equal (z* (list (flat (f*-list op list))) ram1)
                      (z* (list (flat (f*-list op list))) ram2))
               (equal (g*-list op list ram1)
                      (h*-list (op :all :x) list)))))
  :hints (("goal" :in-theory '(z*-s*-rec-introduction
                               s*-list-s*-rec-reduction
                               f*-list-f*-rec-reduction
                               g*-list-h*-list-equality-reduction
                               ))))

(defthm z*-s*-list-induction
  (implies
   (and
    (x? op)
    (unique (flat (f*-list op list)))
    (disjoint-list (flat (f*-list op list)) zlist))
   (equal (equal (z* zlist (s*-list op list ram1))
                 (z* zlist ram2))
          (and (equal (z* (cons (flat (f*-list op list)) zlist) ram1)
                      (z* (cons (flat (f*-list op list)) zlist) ram2))
               (equal (h*-list (op :all :x) list)
                      (g*-list op list ram2)))))
  :hints (("goal" :in-theory '(z*-s*-rec-induction
                               s*-list-s*-rec-reduction
                               f*-list-f*-rec-reduction
                               g*-list-h*-list-equality-reduction
                               ))))


(in-theory (disable g*-list-default-which len-sblkp g*-list-h*-list-equality-reduction))

;;
;; Ray's theorem
;;

(defun fix-memory (skels ram)
  (s*-list (op :val :x) (g*-list (op :val :x) skels ram) nil))

(defun fix-memory-list (a-list ram)
   (if (consp a-list)
      (wr 
         (car a-list) 
         (rd (car a-list) ram) 
         (fix-memory-list (cdr a-list) ram))
      nil))

(defthm fix-memory-list-reduction
  (equal (fix-memory-list list ram)
         (wr-list list (rd-list list ram) nil)))

(defthm len-of-h*-rd
  (equal (len (H*-RD FLAT LIST))
         (len FLAT)))
        

;bzo gross hints
(defthm fix-memory-list-fix-memory-equiv
  (implies
   (and
    (equal list (flat (f*-list (op :val :x) skels)))
    (unique list))
   (equal (fix-memory skels ram)
          (fix-memory-list list ram)))
  :hints (("goal" :in-theory nil)
          ("goal'" :in-theory `((x?)
                                (op)
                                (op-how)
                                fix-memory
                                fix-memory-list-reduction
                                s*-list-s*-rec-reduction
                                f*-list-of-g*-list
                                ))
          ("goal'''" :in-theory `(len-of-h*-rd
                                  (x?)
                                  (op)
                                  (op-how)
                                  len-f*-rec
                                  len-rd-spec
                                  flattenlistw-h*-rd
                                  fixlistw-rd-spec
                                  slot-p-list-list->rec
                                  sblkp-list-f*-rec
                                  fix-memory
                                  fix-memory-list-reduction
                                  g*-list-g*-rec-commute
                                  f*-list-f*-rec-reduction
                                  s*-rec-reduction
                                  g*-rec-reduction
                                  wr-spec-wr-rec-reduction
                                  rd-spec-rd-rec-reduction
                                  f*-rec-g*-rd
                                  v*-rec-g*-rd
                                  ))))

;(in-theory (disable wfix wint)) 


;; begin stuff from push-gacc:


(in-theory (disable ;sblk 
                    (sblk) ;move up?
                    ))

(in-theory
 (disable
  (:CONGRUENCE BAG::PERM-IMPLIES-equal-MEMBERp-2)
  (:CONGRUENCE BAG::PERM-IMPLIES-PERM-APPEND-2)
  (:CONGRUENCE BAG::PERM-IMPLIES-PERM-CONS-2)
  ))

(in-theory (enable acl2::default-car))

(in-theory (enable skel-extensionality!))

(in-theory (disable open-split-blk))



;;  in gacc
;; (defthm f*-spec-h*-spec-introduction
;;   (implies
;;    (and
;;     (x? fop)
;;     (equal hspec (h*-spec (op :nil :x) spec))
;;     (syntaxp (not (equal hspec spec))))
;;    (equal (f*-spec fop base spec)
;;           (f*-spec fop base hspec)))
;;   :hints (("goal''" :induct (f*-spec fop base spec))))

;; (defthm f*-list-h*-list-introduction
;;   (implies
;;    (and
;;     (x? fop)
;;     (equal hlist (h*-list (op :nil :x) list))
;;     (syntaxp (not (equal hlist list))))
;;    (equal (f*-list fop list)
;;           (f*-list fop hlist)))
;;   :hints (("goal''" :induct (f*-list fop list))))

;; (in-theory
;;  (disable
;;   f*-spec-h*-spec-introduction
;;   f*-list-h*-list-introduction
;;   ))

;; (defthm f*-spec-h*-spec-reduction
;;   (implies
;;    (and
;;     (x? fop)
;;     (x? hop))
;;    (equal (f*-spec fop base (h*-spec hop spec))
;;           (f*-spec fop base spec))))

;; (theory-invariant
;;  (incompatible
;;   (:rewrite f*-spec-h*-spec-reduction)
;;   (:rewrite f*-spec-h*-spec-introduction)
;;   ))



(defthm h*-spec-over-rs
  (equal (h*-spec (op :nil :z) (skel-spec (rs size off base spec)))
         (skel-spec (rs size off base (h*-spec (op :nil :z) spec)))))

(in-theory 
 (disable 
  rs-of-h*-spec
  ))

(theory-invariant 
 (incompatible 
  (:rewrite h*-spec-over-rs)
  (:rewrite rs-of-h*-spec)
  ))

(defthm f*-spec-v0-split-blk-h*-spec-introduction
  (implies
   (and
    (equal hspec (h*-spec (op :nil :z) spec))
    (syntaxp (not (equal hspec spec))))
   (equal (f*-spec fop fptr (v0 (split-blk spec)))
          (f*-spec fop fptr (v0 (split-blk hspec)))))
  :hints (("goal''" :in-theory (enable open-split-blk open-wv)
           :induct (split-blk spec))))

(in-theory
 (disable
  SPLIT-BLK-H*-SPEC
  ))

(theory-invariant 
 (incompatible 
  (:rewrite f*-spec-v0-split-blk-h*-spec-introduction)
  (:rewrite SPLIT-BLK-H*-SPEC)
  ))


(defthm h*-spec-v0-split-blk
  (equal (h*-spec op (v0 (split-blk spec)))
         (v0 (split-blk (h*-spec op spec))))
  :hints (("goal" :in-theory (enable open-split-blk))))

(defthm skel-p-rs
  (skel-p (rs size off base spec)))

(defthm fixed-spec-p-skel-base-rs
  (implies
   (fixed-spec-p spec)
   (acl2::unsigned-byte-p (fix-size size) ;wintn 8 size 
          (skel-base (rs size off base spec))))
  :hints (("goal" :in-theory (enable ;unfixed-size-wintn
                                     )
           :induct (rs size off base spec))))



(defun syntax-unfixed-int (n)
  (declare (type t n))
  (or (not (consp n))
      (and (not (equal (car n) 'quote))
           (not (equal (car n) 'ifix)))))
      
(defthmd unfixed-int-sblk-parms
  (implies (syntaxp (syntax-unfixed-int base))
           (equal (sblk-parms base sblk)
                  (sblk-parms (ifix base) sblk)))
  :hints (("goal" :in-theory (enable sblk-parms))))

(defthmd unfixed-int-ws
  (implies (syntaxp (syntax-unfixed-int off))
           (equal (ws size off base v spec)
                  (ws size (ifix off) base v spec)))
  :hints (("goal" :in-theory (e/d (ws) (zz-ws-introduction)))))



;bzo

(defthmd len-0-not-consp-fwd
  (implies (equal (len list) 0)
           (not (consp list)))
  :rule-classes (:forward-chaining))




;(in-theory (disable consp-h*-spec))



