(in-package "DJVM")
(include-book "consistent-state-obj-init")
(include-book "consistent-state-properties2") 
(include-book "INST/base-locals")
(include-book "djvm-frame-manipulation-primitives")
(include-book "djvm-heap")

(include-book "INST/base-bind-free")
;;
;; version 2 of the consistent-state-properties!!
;;

(in-theory (disable thread-set-call-stack make-thread make-frame
                    locals operand-stack method-ptr
                    state-set-local-at
                    local-at
                    pushStack
                    consistent-state
                    topStack-guard-strong
                    type-size
                    topStack
                    state-set-pc
                    value-of
                    wff-tagged-value
                    frame-set-locals
                    consistent-state push pop top
                    initialized-ref
                    tag-of
                    NULLp
                    frame-set-operand-stack
                    primitive-type?
                    frame-obj-init-map
                    heap-init-map
                    frame-aux))


(defthm consistent-state-obj-init-state-set-thread-table
  (implies (and (consistent-state-obj-init s)
                (consistent-thread-table-obj-init tt (heap-init-map (aux s))))
           (consistent-state-obj-init (state-set-thread-table tt s)))
  :hints (("Goal" :in-theory (enable consistent-state-obj-init))))


(defthm consistent-thread-table-obj-init-consistent-thread-table-obj-init
  (implies (and (consistent-thread-entry-obj-init new-thread hp-init)
                (consistent-thread-table-obj-init tt hp-init))
           (consistent-thread-table-obj-init (replace-thread-table-entry 
                                              old new-thread tt)
                                             hp-init))
  :hints (("Goal" :in-theory (e/d (consistent-thread-table-obj-init) 
                                  ()))))


(defthm thread-call-stack-thread-set-call-stack-obj-init
  (equal (thread-call-stack (thread-set-call-stack cs th))
         cs)
  :hints (("Goal" :in-theory (e/d (thread-set-call-stack) (make-thread)))))


(defthm wff-thread-thread-set-call-stack
  (implies (wff-thread th)
           (wff-thread (thread-set-call-stack cs th)))
  :hints (("Goal" :in-theory (e/d (wff-thread make-thread thread-set-call-stack)))))

(defthm consistent-thread-entry-obj-init-set-call-stack
  (implies (and (consistent-call-stack-obj-init cs hp-init)
                (consistent-thread-entry-obj-init th hp-init))
           (consistent-thread-entry-obj-init (thread-set-call-stack cs th)
                                             hp-init))
  :hints (("Goal" :in-theory (enable consistent-thread-entry-obj-init))))



(defthm consistent-state-if-bound-then-consistent-thread-entry-obj-init
  (implies (and (consistent-thread-table-obj-init tt hp-init)
                (thread-by-id id tt))
           (consistent-thread-entry-obj-init (thread-by-id id tt) hp-init))
  :hints (("Goal" :in-theory (enable consistent-thread-table-obj-init))))


(defthm consistent-thread-entry-obj-init-consistent-thread-entry-obj-init-push-stack
  (implies (and (consistent-thread-entry-obj-init thread hp-init)
                (consistent-frame-obj-init frame hp-init)
                (wff-call-frame frame))
           (consistent-thread-entry-obj-init 
            (thread-set-call-stack (push frame 
                                         (pop (thread-call-stack thread))) thread)
            hp-init))
  :hints (("Goal" :in-theory (enable  consistent-thread-entry-obj-init
                                      push pop top
                                      consistent-call-stack-obj-init))))


(defthm frame-aux-frame-set-operand-stack-no-change
  (equal (FRAME-AUX (FRAME-SET-OPERAND-STACK OPSTACK FRAME))
         (frame-aux frame))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack))))


(defthm operand-stack-frame-set-operand-stack-is-opstack
  (equal (operand-stack  (FRAME-SET-OPERAND-STACK OPSTACK FRAME))
         opstack)
  :hints (("Goal" :in-theory (enable frame-set-operand-stack))))


(defthm locals-frame-set-operand-stack-no-change
  (equal (locals (FRAME-SET-OPERAND-STACK OPSTACK FRAME))
         (locals frame))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack))))


(defthm method-ptr-frame-set-operand-stack-no-change
  (equal (method-ptr (FRAME-SET-OPERAND-STACK OPSTACK FRAME))
         (method-ptr frame))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack))))


(defthm frame-obj-init-map-frame-set-operand-stack-no-change
  (equal (frame-obj-init-map  (FRAME-SET-OPERAND-STACK OPSTACK FRAME))
         (frame-obj-init-map  frame))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack frame-obj-init-map))))



(defthm consistent-frame-obj-init-if-pop-opstack-1
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (not (equal (method-ptr-methodname (method-ptr frame)) "<init>")))
                (consistent-opstack-obj-init opstack hp-init (collect-values
                                                              (frame-obj-init-map frame))))
           (consistent-frame-obj-init (frame-set-operand-stack
                                       opstack frame) hp-init))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init)
                                  (frame-set-operand-stack)))))



(defthm consistent-frame-obj-init-if-pop-opstack-2
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (equal (method-ptr-methodname (method-ptr frame)) "<init>"))
                (consistent-opstack-obj-init opstack hp-init
                                             (cons (acl2::g 'this (frame-aux frame))
                                                   (collect-values
                                                    (frame-obj-init-map frame)))))
           (consistent-frame-obj-init (frame-set-operand-stack 
                                       opstack frame) hp-init))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init)
                                  (frame-set-operand-stack)))))




(defthm consistent-frame-obj-init-consistent-opstack-1
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (equal (method-ptr-methodname (method-ptr frame)) "<init>")))
           (consistent-opstack-obj-init (operand-stack frame) hp-init
                                        (cons (acl2::g 'this (frame-aux frame))
                                              (collect-values
                                               (frame-obj-init-map frame)))))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init) ()))))



(defthm consistent-frame-obj-init-consistent-opstack-2
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (not (equal (method-ptr-methodname (method-ptr frame)) "<init>"))))
           (consistent-opstack-obj-init (operand-stack frame) hp-init
                                        (collect-values
                                         (frame-obj-init-map frame))))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init) ()))))


(defthm consistent-thread-entry-obj-init-implies-consistent-call-stack
  (implies (consistent-thread-entry-obj-init th hp-init)
           (consistent-call-stack-obj-init (thread-call-stack th) hp-init))
  :hints (("Goal" :in-theory (enable consistent-thread-entry-obj-init))))


(defthm consistent-thread-entry-obj-init-implies
  (implies (and (consistent-call-stack-obj-init cs hp-init)
                (consp cs))
           (CONSISTENT-FRAME-OBJ-INIT 
            (TOP cs) hp-init))
  :hints (("Goal" :in-theory (e/d (consistent-call-stack-obj-init top) 
                                  (consistent-frame-obj-init)))))



(defthm true-listp-implies-pop-true-listp
  (implies (true-listp l)
           (true-listp (pop l)))
  :hints (("Goal" :in-theory (enable pop))))


(defthm wff-call-frame-true-listp-opstack
  (implies (wff-call-frame frame)
           (true-listp (operand-stack frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame locals operand-stack))))




(defthm wff-call-frame-frame-set-opstack
  (implies (and (wff-call-frame frame)
                (true-listp any))
           (WFF-CALL-FRAME
            (FRAME-SET-OPERAND-STACK any frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame locals 
                                     operand-stack
                                     make-frame
                                     method-ptr
                                     frame-set-operand-stack))))


;; Thu Aug  4 17:41:39 2005

(defthm consistent-state-obj-init-implies-consistent-thread-table-obj-init
  (implies (consistent-state-obj-init s)
           (consistent-thread-table-obj-init (thread-table s)
                                             (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (enable consistent-state-obj-init))))



(defthm consistent-opstack-obj-init-pop-stack-consistent-opstack-obj-init
  (implies (consistent-opstack-obj-init stack hp-init valid-sync-refs)
           (consistent-opstack-obj-init (pop stack) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-opstack-obj-init 
                                     canPopCategory2  push
                                     popcategory2 popcategory1
                                     tag-of value-of top
                                     category1 category2
                                     canPopCategory1
                                     pop))))

;;
;; (defthm frame-aux-frame-set-operand-stack-no-change
;;   (equal (frame-aux (frame-set-operand-stack stack frame))
;;          (frame-aux frame)))


(defthm consistent-thread-entry-obj-init-implies-wff-call-frame
  (implies (and (consistent-call-stack-obj-init cs hp-init)
                (consp cs))
           (wff-call-frame (top cs)))
  :hints (("Goal" :in-theory (e/d (consistent-call-stack-obj-init top) 
                                  (consistent-frame-obj-init)))))




(defthm consistent-thread-entry-obj-init-implies-wff-call-frame-specific
  (implies (and (syntaxp (acl2::found-symbol 's cs))
                (bind-free (acl2::default-bind-free 's 's
                                                    (acl2::pkg-witness "DJVM")))
                (consistent-call-stack-obj-init cs (heap-init-map (aux s)))
                (consp cs))
           (wff-call-frame (top cs)))
  :hints (("Goal" :in-theory (e/d (consistent-call-stack-obj-init top) 
                                  (consistent-frame-obj-init)))))


;;; this above is difficult to apply. may need syntaxp and bind-free!! 


(defthm consistent-state-obj-init-preserved-by-popStack 
  (implies (and (consistent-state-obj-init s)
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s) (thread-table s)))))
           (consistent-state-obj-init (popStack s)))
  :hints (("Goal" :in-theory (e/d (popStack popstack-of-thread)
                                  (consistent-state)))))

;;;
;;; Thu Aug  4 18:16:07 2005
;;;
;;; We probably is only interested in exporting this fact about popStack out! 
;;;
;;; Maybe some time about popCategory2 

;;;
;;; push is more difficult!! 
;;;


(defthm push-consp
  (consp (push v stack))
  :hints (("Goal" :in-theory (enable push))))


(defthm top-push-is
  (equal (top (push v stack))
         v)
  :hints (("Goal" :in-theory (enable push top))))



(defthm car-push-is
  (equal (car (push v stack))
         v)
  :hints (("Goal" :in-theory (enable push top))))


(defthm cdr-push-is
  (equal (cdr (push v stack))
         stack)
  :hints (("Goal" :in-theory (enable push top))))

(defthm consistent-opstack-obj-init-push-stack-consistent-opstack-obj-init-1
  (implies (and (consistent-opstack-obj-init stack hp-init valid-sync-refs)
                (wff-tagged-value v)
                (case-split (not (equal (tag-of v) 'REF))))
           (consistent-opstack-obj-init (push v stack) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-opstack-obj-init)
           :do-not-induct t)))



(defthm true-listp-implies-push-true-listp
  (implies (true-listp l)
           (true-listp (push v  l)))
  :hints (("Goal" :in-theory (enable push))))


(defthm consistent-state-obj-init-preserved-by-pushStack-1
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (not (equal (tag-of v) 'REF)))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s) (thread-table s)))))                
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state)))))



(defthm consistent-opstack-obj-init-push-stack-consistent-opstack-obj-init-2
  (implies (and (consistent-opstack-obj-init stack hp-init valid-sync-refs)
                (wff-tagged-value v)
                (case-split (equal (tag-of v) 'REF))
                (case-split (NULLp v)))
           (consistent-opstack-obj-init (push v stack) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-opstack-obj-init)
           :do-not-induct t)))


(defthm consistent-state-obj-init-preserved-by-pushStack-2
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (equal (tag-of v) 'REF))
                (case-split (NULLp v))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state)))))


(defthm consistent-opstack-obj-init-push-stack-consistent-opstack-obj-init-3
  (implies (and (consistent-opstack-obj-init stack hp-init valid-sync-refs)
                (wff-tagged-value v)
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (initialized-ref (value-of v) hp-init)))
           (consistent-opstack-obj-init (push v stack) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-opstack-obj-init)
           :do-not-induct t)))

;
; Thu Aug  4 18:54:49 2005
;

(defthm consistent-state-obj-init-preserved-by-pushStack-3
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (initialized-ref (value-of v)
                                             (heap-init-map (aux s))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state)))))
;
; this above is the common cases!! 
;



(defthm consistent-opstack-obj-init-push-stack-consistent-opstack-obj-init-4
  (implies (and (consistent-opstack-obj-init stack hp-init valid-sync-refs)
                (wff-tagged-value v)
                (case-split (equal (tag-of v) 'REF))
                (case-split (mem (value-of v) valid-sync-refs))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) hp-init))))
           (consistent-opstack-obj-init (push v stack) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-opstack-obj-init)
           :do-not-induct t)))



;; (defthm mem-value-of-cons-x-list-1
;;   (implies (equal (value-of v) x)
;;            (mem (value-of v) (cons x l))))


;; (defthm mem-value-of-cons-x-list-2
;;   (implies (mem (value-of v) l)
;;            (mem (value-of v) (cons x l))))




(defthm consistent-frame-obj-init-if-pop-opstack-2-g
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (equal (method-ptr-methodname (method-ptr frame))
                                   "<init>"))
                (equal (acl2::g 'this (frame-aux frame)) x)
                (consistent-opstack-obj-init opstack hp-init
                                             (cons x 
                                                   (collect-values
                                                    (frame-obj-init-map frame)))))
           (consistent-frame-obj-init (frame-set-operand-stack 
                                       opstack frame) hp-init))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init)
                                  (frame-set-operand-stack)))))




(defthm consistent-frame-obj-init-consistent-opstack-1-g
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (equal (method-ptr-methodname (method-ptr frame))
                                   "<init>"))
                (equal (acl2::g 'this (frame-aux frame)) x))
           (consistent-opstack-obj-init (operand-stack frame) hp-init
                                        (cons x
                                              (collect-values
                                               (frame-obj-init-map frame)))))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init) ()))))


                     
          

(defthm consistent-state-obj-init-preserved-by-pushStack-4
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (equal (method-ptr-methodname
                                    (method-ptr (current-frame s)))
                                   "<init>"))
                (or (equal (value-of v)
                           (acl2::g 'this (frame-aux (current-frame s))))
                    (mem (value-of v)
                         (collect-values (frame-obj-init-map (current-frame s)))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v)
                                                  (heap-init-map (aux s)))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state))
           :expand (current-frame s)
           :do-not '(fertilize))))



(defthm consistent-state-obj-init-preserved-by-pushStack-5
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr (current-frame s)))
                                        "<init>")))
                (mem (value-of v)
                     (collect-values (frame-obj-init-map (current-frame s))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v)
                                                  (heap-init-map (aux s)))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (pushStack v s)))
  :hints (("Goal" :in-theory (e/d (pushStack push-stack-of-thread)
                                  (consistent-state))
           :do-not '(fertilize))))


;; note that we haven't deal with size 2 objects!!! 


;----------------------------------------------------------------------
;
; well this is the theorem that we will export!! 
;
;
;;;
;;; Maybe we will prove a more commonly used fact, copying values between
;;; 
;;; locals and operand stack, does not matter. 
;;;
;;; loading from ARRAY or GETFIELD does not matter, because we proved that
;;; their content are initialized!!! 
;;; 

; the only way to set a local variable is to go through the operand stack
; 

;----------------------------------------------------------------------

; similiarly for manipulating locals!! 

(defthm frame-obj-init-map-frame-set-locals-reduce
  (equal (FRAME-OBJ-INIT-MAP (FRAME-SET-LOCALS LOCALS FRAME))
         (frame-obj-init-map frame))
  :hints (("Goal" :in-theory (enable frame-set-locals frame-obj-init-map))))


(defthm method-ptr-frame-set-locals-reduce
  (equal (method-ptr (FRAME-SET-LOCALS LOCALS FRAME))
         (method-ptr frame))
  :hints (("Goal" :in-theory (enable frame-set-locals frame-obj-init-map))))


(defthm operand-stack-frame-set-locals-reduce
  (equal (operand-stack  (FRAME-SET-LOCALS LOCALS FRAME))
         (operand-stack frame))
  :hints (("Goal" :in-theory (enable frame-set-locals frame-obj-init-map))))


(defthm locals-frame-set-locals-reduce
  (equal (locals  (FRAME-SET-LOCALS LOCALS FRAME))
         locals)
  :hints (("Goal" :in-theory (enable frame-set-locals frame-obj-init-map))))


(defthm frame-aux-frame-set-locals-reduce
  (equal (frame-aux (FRAME-SET-LOCALS LOCALS FRAME))
         (frame-aux frame))
  :hints (("Goal" :in-theory (enable frame-set-locals frame-obj-init-map))))


(defthm consistent-frame-obj-init-if-set-locals-1
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (not (equal (method-ptr-methodname (method-ptr frame)) "<init>")))
                (consistent-locals-obj-init locals hp-init (collect-values
                                                            (frame-obj-init-map frame))))
           (consistent-frame-obj-init (frame-set-locals
                                       locals frame) hp-init))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init)
                                  (frame-set-locals)))))



(defthm consistent-frame-obj-init-if-set-locals-2
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (equal (method-ptr-methodname (method-ptr frame)) "<init>"))
                (consistent-locals-obj-init locals hp-init
                                             (cons (acl2::g 'this (frame-aux frame))
                                                   (collect-values
                                                    (frame-obj-init-map frame)))))
           (consistent-frame-obj-init (frame-set-locals
                                       locals frame) hp-init))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init)
                                  (frame-set-locals)))))



;----------------------------------------------------------------------



(defthm consistent-locals-obj-init-push-stack-consistent-locals-obj-init-1
  (implies (and (consistent-locals-obj-init locals hp-init valid-sync-refs)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len locals))
                (case-split (not (equal (tag-of v) 'REF))))
           (consistent-locals-obj-init (update-nth i v locals) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init))))



;;; I don't to include base-locals.lisp, because it includes base.lisp!!! 
;;; which may change quite some things!! 

;; (defun invalidate-category2-value (index s)
;;     (declare (xargs :guard (and (integerp index)
;;                                 (current-frame-guard s)
;;                                 (wff-call-frame (current-frame s))
;;                                 (<= -1 index)
;;                                 (< index (- (len (locals (current-frame s))) 1))
;;                                 (or (< index 0)
;;                                     (wff-tagged-value (local-at index s))))))
;;     (if (< index 0) s
;;       (if (equal (type-size (tag-of (local-at index s))) 1) s
;;         (state-set-local-at index '(topx . topx) s)))))




(defthm consistent-frame-obj-init-consistent-locals-1
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (equal (method-ptr-methodname (method-ptr frame)) "<init>")))
           (consistent-locals-obj-init (locals frame) hp-init
                                        (cons (acl2::g 'this (frame-aux frame))
                                              (collect-values
                                               (frame-obj-init-map frame)))))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init) ()))))



(defthm consistent-frame-obj-init-consistent-locals-2
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (not (equal (method-ptr-methodname (method-ptr frame)) "<init>"))))
           (consistent-locals-obj-init (locals frame) hp-init
                                        (collect-values
                                         (frame-obj-init-map frame))))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init) ()))))


(defthm wff-call-frame-frame-set-locals
  (implies (and (wff-call-frame frame)
                (true-listp any))
           (WFF-CALL-FRAME
            (FRAME-SET-LOCALS  any frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame locals 
                                     operand-stack
                                     make-frame
                                     method-ptr
                                     frame-set-locals))))


(defthm wff-call-frame-true-listp-locals
  (implies (wff-call-frame frame)
           (true-listp (locals frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame locals 
                                     make-frame
                                     method-ptr
                                     frame-set-locals))))


(defthm true-listp-update-nth-true-listp
  (implies (true-listp l)
           (true-listp (update-nth i v l))))


(defthm consistent-state-obj-init-preserved-by-state-set-local-at-1
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (not (equal (tag-of v) 'REF)))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at 
                                   set-local-at-of-thread) (consistent-state))
           :do-not-induct t)))


;----------------------------------------------------------------------



(defthm consistent-locals-obj-init-push-stack-consistent-locals-obj-init-2
  (implies (and (consistent-locals-obj-init locals hp-init valid-sync-refs)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len locals))
                (case-split (equal (tag-of v) 'REF))
                (case-split (NULLp v)))
           (consistent-locals-obj-init (update-nth i v locals) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init))))



(defthm consistent-state-obj-init-preserved-by-state-set-local-at-2
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (NULLp v))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread
                                   state-set-local-at)
                                  (consistent-state))
           :do-not-induct t)))




(defthm consistent-local-obj-init-push-stack-consistent-locals-obj-init-3
  (implies (and (consistent-locals-obj-init locals hp-init valid-sync-refs)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len locals))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (initialized-ref (value-of v) hp-init)))
           (consistent-locals-obj-init (update-nth i v locals) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init))))


(defthm consistent-state-obj-init-preserved-by-state-set-local-at-3
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (initialized-ref (value-of v) (heap-init-map (aux
                                                                          s))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at
                                   set-local-at-of-thread) 
                                  (consistent-state))
           :do-not-induct t)))




(defthm consistent-locals-obj-init-set-local-at-consistent-locals-obj-init-4
  (implies (and (consistent-locals-obj-init locals hp-init valid-sync-refs)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len locals))
                (mem (value-of v) valid-sync-refs)
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) hp-init))))
           (consistent-locals-obj-init (update-nth i v locals) hp-init valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init))))




(defthm consistent-frame-obj-init-if-set-local-2-g
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (equal (method-ptr-methodname (method-ptr frame))
                                   "<init>"))
                (equal (acl2::g 'this (frame-aux frame)) x)
                (consistent-locals-obj-init locals hp-init
                                             (cons x 
                                                   (collect-values
                                                    (frame-obj-init-map frame)))))
           (consistent-frame-obj-init (frame-set-locals 
                                       locals frame) hp-init))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init)
                                  (frame-set-locals)))))




(defthm consistent-frame-obj-init-consistent-locals-1-g
  (implies (and (consistent-frame-obj-init frame hp-init)
                (case-split (equal (method-ptr-methodname (method-ptr frame))
                                   "<init>"))
                (equal (acl2::g 'this (frame-aux frame)) x))
           (consistent-locals-obj-init (locals frame) hp-init
                                        (cons x
                                              (collect-values
                                               (frame-obj-init-map frame)))))
  :hints (("Goal" :in-theory (e/d (consistent-frame-obj-init) ()))))





(defthm consistent-state-obj-init-preserved-by-state-set-local-at-4
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (equal (method-ptr-methodname
                                    (method-ptr (current-frame s)))
                                   "<init>"))
                (or (equal (value-of v)
                           (acl2::g 'this (frame-aux (current-frame s))))
                    (mem (value-of v)
                         (collect-values (frame-obj-init-map (current-frame s)))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) (heap-init-map (aux s)))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at 
                                   set-local-at-of-thread) (consistent-state))
           :do-not-induct t)))



(defthm consistent-state-obj-init-preserved-by-state-set-local-at-5
  (implies (and (consistent-state-obj-init s)
                (wff-tagged-value v)
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr (current-frame s)))
                                        "<init>")))
                (mem (value-of v)
                     (collect-values (frame-obj-init-map (current-frame s))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) (heap-init-map (aux s)))))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at
                                   set-local-at-of-thread) (consistent-state))
           :do-not-induct t)))


;----------------------------------------------------------------------
;
; Now I will need to prove the "commonly used lemma" 
; 
; copy between opstack and locals preserve the consistent-state-obj-init!! 
; 
; The argument is this: 
;  
;   if the value being copied is not 'REF, easy
;   if it is NULL, easy
;   if it is initialized-ref, easy
;   if it is uninitialized, because it is from opstack (or local)
;      we know, it is mem of the (collect-values (frame-obj-init-map
;      (current-frame s)))
; 
; Maybe I shall let the ALOAD, ASTORE proof drives the lemma development. 
; Thu Aug  4 23:41:02 2005

;----------------------------------------------------------------------

(defthm thread-table-state-set-pc-reduce
  (equal (thread-table (state-set-pc any s))
         (thread-table s))
  :hints (("Goal" :in-theory (enable state-set-pc))))


(defthm aux-state-set-pc-reduce
  (equal (aux  (state-set-pc any s))
         (aux  s))
  :hints (("Goal" :in-theory (enable state-set-pc))))


(defthm consistent-state-obj-init-reduce
  (implies (and (syntaxp (and (acl2::found-symbol 's s2)
                              (not (equal s2 's))))
                (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness "DJVM")))
                (equal (thread-table s2) (thread-table s))
                (equal (heap-init-map (aux s2)) (heap-init-map (aux s))))
          (equal (consistent-state-obj-init s2)
                 (consistent-state-obj-init s)))
  :hints (("Goal" :in-theory (enable consistent-state-obj-init))))





(defthm consistent-state-obj-init-preserved-by-state-set-pc
  (equal (consistent-state-obj-init (state-set-pc any s))
         (consistent-state-obj-init s)))
         
(defthm wff-tagged-value-topx-topx
  (wff-tagged-value '(topx . topx)))


(defthm consistent-state-obj-init-invalidate-category2
  (implies (and (consistent-state-obj-init s)
                (<= -1 i)
                (< i (len (locals (current-frame s))))
                (integerp i)
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))                
           (consistent-state-obj-init (invalidate-category2-value i s)))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

;
; we replaced all reference to consistent-state in above lemmas to only assert
; current-thread exists and the the thread-call-stack has at least one
; frame. because update-nth will introduce a call frame, of which, we could not
; prove its locals are consistent-locals-obj-init.
;
; Fri Aug  5 15:42:50 2005

;----------------------------------------------------------------------
;; (i-am-here) 

(local 
 (defthm non-nil-implies-mem
   (implies (WFF-TAGGED-VALUE (top l))
            (mem (top l) l))
   :hints (("Goal" :in-theory (enable top wff-tagged-value)))))

(defthm topStack-guard-strong-implies-mem-topStack-opstack
  (implies (topStack-guard-strong s)
           (mem (topStack s) (operand-stack 
                              (top (thread-call-stack 
                                    (thread-by-id (current-thread s)
                                                  (thread-table s)))))))
  :hints (("Goal" :in-theory (enable topStack
                                     topStack-guard-strong))))


(defthm mem-consistent-opstack-obj-init-implies-mem-valid-obj-reference
  (implies (and (mem v opstack)
                (equal (tag-of v) 'REF)
                (not (NULLp v))
                (not (initialized-ref (value-of v) hp-init))
                (consistent-opstack-obj-init opstack hp-init valid-sync-refs))
           (mem (value-of v) valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-opstack-obj-init)
           :do-not '(generalize))))




;; (defthm consistent-opstack-obj-init-consistent-opstack-ref
;;   (implies (and (equal frame2 frame1)
;;                 (consistent-opstack-obj-init (operand-stack frame1)
;;                                              hp-init
;;                                              (collect-values
;;                                               (frame-obj-init-map frame1))))
;;            (CONSISTENT-OPSTACK-OBJ-INIT
;;             (OPERAND-STACK frame2) hp-init (collect-values 
;;                                             (frame-obj-init-map frame1)))))



(defthm consistent-state-obj-init-topStack-guard-strong-1
   (implies (and (topStack-guard-strong s)
                 (consistent-state-obj-init s)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s))))
                 (case-split (equal (tag-of (topStack s)) 'REF))
                 (case-split (not (NULLp (topStack s))))
                 (case-split (not (initialized-ref (value-of (topStack s))
                                                   (heap-init-map (aux s)))))
                 (case-split (not (equal (method-ptr-methodname
                                          (method-ptr frame))
                                         "<init>")))
                 (equal (current-frame s) frame))
            (mem (value-of (topStack s))
                 (collect-values 
                  (frame-obj-init-map frame))))
   :hints (("Goal" :restrict
            ((mem-consistent-opstack-obj-init-implies-mem-valid-obj-reference
              ((opstack (operand-stack (top (thread-call-stack 
                                             (thread-by-id (current-thread s)
                                                           (thread-table s))))))
               (hp-init (heap-init-map (aux s)))))))))

(in-theory (disable JVM::MEM-BASE-TYPES-IMPLIES-NOT-EQUAL))
                  

(defthm consistent-state-obj-init-topStack-guard-strong-2-lemma
  (implies (and (topStack-guard-strong s)
                 (consistent-state-obj-init s)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s))))
                 (case-split (equal (tag-of (topStack s)) 'REF))
                 (case-split (not (NULLp (topStack s))))
                 (case-split (not (initialized-ref (value-of (topStack s))
                                                   (heap-init-map (aux s)))))
                 (case-split (equal (method-ptr-methodname
                                     (method-ptr frame))
                                    "<init>"))
                 (equal (current-frame s) frame))
            (mem  (value-of (topStack s))
                  (cons (acl2::g 'this (frame-aux frame))
                        (collect-values 
                         (frame-obj-init-map frame)))))
   :hints (("Goal"    :in-theory (disable mem)
            :restrict
            ((mem-consistent-opstack-obj-init-implies-mem-valid-obj-reference
              ((opstack (operand-stack (top (thread-call-stack 
                                             (thread-by-id (current-thread s)
                                                           (thread-table s))))))
               (hp-init (heap-init-map (aux s)))))))))





(defthm consistent-state-obj-init-topStack-guard-strong-2
  (implies (and (topStack-guard-strong s)
                 (consistent-state-obj-init s)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s))))
                 (case-split (equal (tag-of (topStack s)) 'REF))
                 (case-split (not (NULLp (topStack s))))
                 (case-split (not (initialized-ref (value-of (topStack s))
                                                   (heap-init-map (aux s)))))
                 (case-split (equal (method-ptr-methodname
                                     (method-ptr frame))
                                    "<init>"))
                 (case-split (not (equal (value-of (topStack s))
                                         (acl2::g 'this (frame-aux frame)))))
                 (equal (current-frame s) frame))
            (mem  (value-of (topStack s))
                  (collect-values 
                   (frame-obj-init-map frame))))
  :hints (("Goal" :use ((:instance consistent-state-obj-init-topStack-guard-strong-2-lemma)))))




(defthm consistent-state-obj-init-state-set-local-at
  (implies (and (consistent-state-obj-init s)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (integerp i)
                (topStack-guard-strong s)
                (wff-tagged-value (topStack s))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-state-obj-init (state-set-local-at i (topStack s) s)))
  :hints (("Goal" :in-theory (disable state-set-local-at))))


;;; instead of referring to (consistent-state s) 
;;; we only assert that topStack is wff-tagged-value and the thread-exists.
;;;
;;; because later we will deal with the case that we set 
;;;
;;; (topStack s) then '(topx . topx) as part of the 
;;;
;;;  storing size 2 value!! 
;;;
;;; Fri Aug  5 16:24:43 2005

;----------------------------------------------------------------------


;; (defthm mem-consistent-opstack-obj-init-implies-mem-valid-obj-reference
;;   (implies (and (mem v opstack)
;;                 (equal (tag-of v) 'REF)
;;                 (not (NULLp v))
;;                 (not (initialized-ref (value-of v) hp-init))
;;                 (consistent-opstack-obj-init opstack hp-init valid-sync-refs))
;;            (mem (value-of v) valid-sync-refs))
;;   :hints (("Goal" :in-theory (enable consistent-opstack-obj-init)
;;            :do-not '(generalize))))


(defthm update-nth-i-remain-consistent-implies-value-seen
  (implies (and (consistent-locals-obj-init (update-nth i v locals)
                                            hp-init
                                            valid-sync-refs)
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) hp-init))))
           (mem (value-of v) valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init))))



(defthm update-nth-i-remain-consistent-implies-value-seen-specific-1-lemma
  (implies (and (syntaxp (acl2::found-symbol 's1 frame))
                (bind-free (acl2::default-bind-free 's1 's1 (acl2::pkg-witness
                                                             "DJVM")))
                (bind-free (acl2::default-bind-free 'i 'i (acl2::pkg-witness "DJVM")))
                (case-split (equal (method-ptr-methodname
                                    (method-ptr frame))
                                   "<init>"))
                (consistent-locals-obj-init (update-nth i v (locals frame))
                                            (heap-init-map (aux s1))
                                            (cons (acl2::g 'this
                                                           (frame-aux frame))
                                                  (collect-values (frame-obj-init-map frame))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) (heap-init-map
                                                                (aux s1))))))
           (mem (value-of v) (cons (acl2::g 'this
                                            (frame-aux frame))
                                   (collect-values (frame-obj-init-map frame)))))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init))))




(defthm update-nth-i-remain-consistent-implies-value-seen-specific-1
  (implies (and (syntaxp (acl2::found-symbol 's1 frame))
                (bind-free (acl2::default-bind-free 's1 's1 (acl2::pkg-witness
                                                             "DJVM")))
                (bind-free (acl2::default-bind-free 'i 'i (acl2::pkg-witness "DJVM")))
                (case-split (equal (method-ptr-methodname
                                    (method-ptr frame))
                                   "<init>"))
                (consistent-locals-obj-init (update-nth i v (locals frame))
                                            (heap-init-map (aux s1))
                                            (cons (acl2::g 'this
                                                           (frame-aux frame))
                                                  (collect-values (frame-obj-init-map frame))))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) (heap-init-map
                                                                (aux s1)))))
                (case-split (not (equal (value-of v)
                                        (acl2::g 'this
                                                 (frame-aux frame))))))
           (mem (value-of v) (collect-values (frame-obj-init-map frame))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable
                       update-nth-i-remain-consistent-implies-value-seen-specific-1-lemma
                       UPDATE-NTH-I-REMAIN-CONSISTENT-IMPLIES-VALUE-SEEN)
           :use ((:instance update-nth-i-remain-consistent-implies-value-seen-specific-1-lemma)))))



(defthm update-nth-i-remain-consistent-implies-value-seen-specific-2
  (implies (and (syntaxp (acl2::found-symbol 's1 frame))
                (bind-free (acl2::default-bind-free 's1 's1 (acl2::pkg-witness
                                                             "DJVM")))
                (bind-free (acl2::default-bind-free 'i 'i (acl2::pkg-witness "DJVM")))
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr frame))
                                        "<init>")))
                (consistent-locals-obj-init (update-nth i v (locals frame))
                                            (heap-init-map (aux s1))
                                            (collect-values (frame-obj-init-map frame)))
                (case-split (equal (tag-of v) 'REF))
                (case-split (not (NULLp v)))
                (case-split (not (initialized-ref (value-of v) (heap-init-map
                                                                (aux s1))))))
           (mem (value-of v) (collect-values (frame-obj-init-map frame))))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init))))


;----------------------------------------------------------------------

(defthm consistent-state-implies-consistent-locals-obj-init-1-lemma
  (implies (and (consistent-state-obj-init s)
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr 
                                          (top (thread-call-stack 
                                                (thread-by-id (current-thread s)
                                                              (thread-table s))))))
                                        "<init>")))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-locals-obj-init 
            (locals (top (thread-call-stack 
                          (thread-by-id (current-thread s)
                                        (thread-table s)))))
            (heap-init-map (aux s))
            (collect-values (frame-obj-init-map 
                             (top (thread-call-stack 
                                   (thread-by-id (current-thread s)
                                                 (thread-table s)))))))))

;----------------------------------------------------------------------

(local 
 (defthm thread-by-id-implies-mem
   (implies (thread-by-id id tt)
            (mem (thread-by-id id tt) tt))))

(local 
 (defthm replace-thread-by-new-thead
   (implies (thread-by-id id tt)
            (mem (thread-by-id id tt) tt))))


(local 
 (defthm thread-by-id-after-replace
   (implies (and (mem old tt)
                 (equal (thread-by-id id tt) old)
                 (equal (thread-id new) id))
            (equal (thread-by-id id 
                                 (replace-thread-table-entry 
                                  old 
                                  new tt))
                   new))))

(local 
 (defthm thread-id-thread-set-call-stack
   (equal (thread-id (thread-set-call-stack cs thread))
          (thread-id thread))))

(local 
 (defthm wff-thread-id-thread-by-id
   (implies (wff-thread (thread-by-id id tt))
            (equal (thread-id (thread-by-id id tt))
                   id))))



(local 
 (defthm locals-state-set-local-at-is
   (implies (and (thread-by-id (current-thread s) (thread-table s))
                 (wff-thread (thread-by-id (current-thread s) (thread-table s)))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s)))))
           (equal (locals (top (thread-call-stack
                                (thread-by-id (current-thread s)
                                              (thread-table (state-set-local-at i v s))))))
                  (update-nth i v (locals (top (thread-call-stack 
                                                (thread-by-id (current-thread s)
                                                              (thread-table
                                                               s))))))))
   :hints (("Goal" :in-theory (e/d (state-set-local-at
                                    set-local-at-of-thread)
                                   (wff-thread))
            :do-not '(generalize)))))
                  
;----------------------------------------------------------------------

(local (in-theory (disable wff-thread)))

(local 
 (defthm current-thread-state-set-local-at 
   (equal (CURRENT-THREAD (STATE-SET-LOCAL-AT I V S))
          (current-thread s))
   :hints (("Goal" :in-theory (enable state-set-local-at)))))

(local 
 (defthm thread-exist-thread-exists-after-replace-thread
   (implies (and (thread-by-id id tt)
                 (wff-thread new)
                 (wff-thread-table tt)
                 (equal (thread-id new) (thread-id old)))
            (THREAD-BY-ID id (replace-thread-table-entry old new tt)))
   :hints (("Goal" :in-theory (enable thread-by-id)))))


;; (local 
;;  (defthm thread-exist-thread-exists-after-state-set-local
;;    (implies (thread-by-id id (thread-table s))
;;             (THREAD-BY-ID id (THREAD-TABLE (STATE-SET-LOCAL-AT I V S))))
;;    :hints (("Goal" :in-theory (enable state-set-local-at)))))


(local 
 (defthm thread-by-id-is-after-state-set-local-at
   (implies (and (thread-by-id (current-thread s) (thread-table s))
                 (wff-thread (thread-by-id (current-thread s) (thread-table s))))
            (equal (THREAD-BY-ID (current-thread s) (THREAD-TABLE (STATE-SET-LOCAL-AT I V S)))
                   (set-local-at-of-thread i v (thread-by-id (current-thread s)
                                                             (thread-table s)))))
   :hints (("Goal" :in-theory (enable state-set-local-at)))))


(local 
 (defthm top-thread-call-stack-set-local-at-thread-is
   (equal (top (thread-call-stack (set-local-at-of-thread i v th)))
          (frame-set-locals (update-nth i v (locals (top (thread-call-stack
                                                          th))))
                            (top (thread-call-stack
                                  th))))
   :hints (("Goal" :in-theory (enable set-local-at-of-thread)))))

(local 
 (defthm consp-thread-call-stack-set-local-at-of-thread
   (consp (thread-call-stack (set-local-at-of-thread i v th)))
   :hints (("Goal" :in-theory (enable set-local-at-of-thread)))))
   
(local 
 (defthm aux-state-set-local-at
   (equal (aux (state-set-local-at i v s))
          (aux s))
   :hints (("Goal" :in-theory (enable state-set-local-at)))))

(local 
 (defthm wff-thread-implies-not-null
   (implies (wff-thread th)
            th)
   :rule-classes :forward-chaining))


(defthm consistent-state-implies-consistent-locals-obj-init-1
  (implies (and (consistent-state-obj-init (state-set-local-at i v s))
                (wff-thread (thread-by-id (current-thread s) (thread-table s)))
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr 
                                          (top (thread-call-stack 
                                                (thread-by-id (current-thread s)
                                                              (thread-table s))))))
                                        "<init>"))))
           (consistent-locals-obj-init 
            (update-nth i v (locals (top (thread-call-stack 
                                          (thread-by-id (current-thread s)
                                                        (thread-table s))))))
            (heap-init-map (aux s))
            (collect-values (frame-obj-init-map 
                             (top (thread-call-stack 
                                   (thread-by-id (current-thread s)
                                                 (thread-table s))))))))
  :hints (("Goal" :use ((:instance
                         consistent-state-implies-consistent-locals-obj-init-1-lemma
                         (s (state-set-local-at i v s))))
           :do-not-induct t)))


;----------------------------------------------------------------------


(defthm consistent-state-implies-consistent-locals-obj-init-2-lemma
  (implies (and (consistent-state-obj-init s)
                (case-split (equal (method-ptr-methodname
                                    (method-ptr 
                                     (top (thread-call-stack 
                                           (thread-by-id (current-thread s)
                                                         (thread-table s))))))
                                   "<init>"))
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s)))))
           (consistent-locals-obj-init 
            (locals (top (thread-call-stack 
                          (thread-by-id (current-thread s)
                                        (thread-table s)))))
            (heap-init-map (aux s))
            (cons (acl2::g 'this (frame-aux 
                                  (top (thread-call-stack 
                                        (thread-by-id (current-thread s)
                                                      (thread-table s))))))
                  (collect-values (frame-obj-init-map 
                                   (top (thread-call-stack 
                                         (thread-by-id (current-thread s)
                                                       (thread-table s))))))))))

(defthm consistent-state-implies-consistent-locals-obj-init-2
   (implies (and (consistent-state-obj-init (state-set-local-at i v s))
                 (wff-thread (thread-by-id (current-thread s) (thread-table s)))                 
                 (case-split (equal (method-ptr-methodname
                                     (method-ptr 
                                      (top (thread-call-stack 
                                            (thread-by-id (current-thread s)
                                                          (thread-table s))))))
                                    "<init>")))
            (consistent-locals-obj-init 
             (update-nth i v (locals (top (thread-call-stack 
                                           (thread-by-id (current-thread s)
                                                         (thread-table s))))))
             (heap-init-map (aux s))
             (cons (acl2::g 'this (frame-aux 
                                       (top (thread-call-stack 
                                            (thread-by-id (current-thread s)
                                                          (thread-table s))))))
                   (collect-values (frame-obj-init-map 
                                    (top (thread-call-stack 
                                          (thread-by-id (current-thread s)
                                                        (thread-table
                                                         s)))))))))
   :hints (("Goal" :use ((:instance
                          consistent-state-implies-consistent-locals-obj-init-2-lemma
                          (s (state-set-local-at i v s)))))))



(defthm consistent-state-obj-init-state-set-local-at-general-lemma
  (implies (and (consistent-state-obj-init (state-set-local-at i v s1))
                (wff-thread (thread-by-id (current-thread s1) (thread-table s1)))
                (equal (frame-obj-init-map (current-frame s2))
                       (frame-obj-init-map (current-frame s1)))
                (equal (acl2::g 'this (frame-aux (current-frame s2)))
                       (acl2::g 'this (frame-aux (current-frame s1))))
                (equal (method-ptr (current-frame s2))
                       (method-ptr (current-frame s1)))
                (equal (heap-init-map (aux s2))
                       (heap-init-map (aux s1)))
                (equal (len (locals (current-frame s2)))
                       (len (locals (current-frame s1))))
                (wff-tagged-value v)
                (thread-by-id (current-thread s2) (thread-table s2))
                (consp (thread-call-stack 
                        (thread-by-id (current-thread s2) (thread-table s2))))
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s1))))
                (consistent-state-obj-init s2))
            (consistent-state-obj-init (state-set-local-at i v s2)))
  :hints (("Goal" :do-not '(generalize fertilize))))




;; (defthm consistent-state-obj-init-state-set-local-at
;;   (implies (and (consistent-state-obj-init s)
;;                 (<= 0 i)
;;                 (< i (len (locals (current-frame s))))
;;                 (integerp i)
;;                 (topStack-guard-strong s)
;;                 (wff-tagged-value (topStack s))
;;                 (thread-by-id (current-thread s) (thread-table s))
;;                 (consp (thread-call-stack (thread-by-id (current-thread s)
;;                                                         (thread-table s)))))
;;            (consistent-state-obj-init (state-set-local-at i (topStack s) s)))
;;   :hints (("Goal" :in-theory (disable state-set-local-at))))

;; Shall I merge this above with the lemma
;; so ACL2 don't have to backward chain to prove 
;;
;; (consistent-state-obj-init (state-set-local-at i (topStack s1) s1))


(defthm consistent-state-obj-init-state-set-local-at-general-specific
  (implies (and (consistent-state-obj-init (state-set-local-at i (topStack s1) s1))
                (wff-thread (thread-by-id (current-thread s1) (thread-table s1)))
                (equal (frame-obj-init-map (current-frame s2))
                       (frame-obj-init-map (current-frame s1)))
                (equal (acl2::g 'this (frame-aux (current-frame s2)))
                       (acl2::g 'this (frame-aux (current-frame s1))))
                (equal (method-ptr (current-frame s2))
                       (method-ptr (current-frame s1)))
                (equal (heap-init-map (aux s2))
                       (heap-init-map (aux s1)))
                (equal (len (locals (current-frame s2)))
                       (len (locals (current-frame s1))))
                (wff-tagged-value (topStack s1))
                (thread-by-id (current-thread s2) (thread-table s2))
                (consp (thread-call-stack 
                        (thread-by-id (current-thread s2) (thread-table s2))))
                (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s1))))
                (consistent-state-obj-init s2))
            (consistent-state-obj-init (state-set-local-at i (topStack s1) s2)))
  :hints (("Goal" :do-not '(generalize fertilize)
           :use ((:instance
                  consistent-state-obj-init-state-set-local-at-general-lemma
                  (v (topStack s1)))))))

;----------------------------------------------------------------------




;; (defthm consistent-state-obj-init-state-set-local-at
;;   (implies (and (consistent-state-obj-init s)
;;                 (<= 0 i)
;;                 (< i (len (locals (current-frame s))))
;;                 (integerp i)
;;                 (topStack-guard-strong s)
;;                 (wff-tagged-value (topStack s))
;;                 (thread-by-id (current-thread s) (thread-table s))
;;                 (consp (thread-call-stack (thread-by-id (current-thread s)
;;                                                         (thread-table s)))))
;;            (consistent-state-obj-init (state-set-local-at i (topStack s) s)))
;;   :hints (("Goal" :in-theory (disable state-set-local-at))))


;; need to show (local-at i s) is a member of locals!

(defthm nth-i-mem
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len l)))
           (mem (nth i l) l)))


(defthm mem-local-at-locals
   (implies (and (integerp i)
                 (<= 0 i)
                 (< i (len (locals (current-frame s))))
                 (equal (current-frame s) frame))
            (mem (local-at i s)
                 (locals frame)))
   :hints (("Goal" :in-theory (enable local-at
                                      current-frame))))



(defthm mem-consistent-locals-obj-init-implies-mem-valid-obj-reference
  (implies (and (mem v locals)
                (equal (tag-of v) 'REF)
                (not (NULLp v))
                (not (initialized-ref (value-of v) hp-init))
                (consistent-locals-obj-init locals hp-init valid-sync-refs))
           (mem (value-of v) valid-sync-refs))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init)
           :do-not '(generalize))))


(defthm consistent-state-obj-init-local-at-i-1
   (implies (and (integerp i)
                 (<= 0 i)
                 (< i (len (locals (current-frame s))))
                 (consistent-state-obj-init s)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s))))
                 (case-split (equal (tag-of (local-at i s)) 'REF))
                 (case-split (not (NULLp (local-at i s))))
                 (case-split (not (initialized-ref (value-of (local-at i s))
                                                   (heap-init-map (aux s)))))
                 (case-split (not (equal (method-ptr-methodname
                                          (method-ptr frame))
                                         "<init>")))
                 (equal (current-frame s) frame))
            (mem (value-of (local-at i s))
                 (collect-values 
                  (frame-obj-init-map frame))))
   :hints (("Goal" :restrict
            ((mem-consistent-locals-obj-init-implies-mem-valid-obj-reference
              ((locals (locals (top (thread-call-stack 
                                     (thread-by-id (current-thread s)
                                                   (thread-table s))))))
               (hp-init (heap-init-map (aux s)))))))))


(defthm consistent-state-obj-init-local-at-i-2-lemma
  (implies (and  (integerp i)
                 (<= 0 i)
                 (< i (len (locals (current-frame s))))
                 (consistent-state-obj-init s)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s))))
                 (case-split (equal (tag-of (local-at i s)) 'REF))
                 (case-split (not (NULLp (local-at i s))))
                 (case-split (not (initialized-ref (value-of (local-at i s))
                                                   (heap-init-map (aux s)))))
                 (case-split (equal (method-ptr-methodname
                                     (method-ptr frame))
                                    "<init>"))
                 (equal (current-frame s) frame))
            (mem  (value-of (local-at i s))
                  (cons (acl2::g 'this (frame-aux frame))
                        (collect-values 
                         (frame-obj-init-map frame)))))
   :hints (("Goal"    :in-theory (disable mem)
            :restrict
            ((mem-consistent-locals-obj-init-implies-mem-valid-obj-reference
              ((locals (locals (top (thread-call-stack 
                                     (thread-by-id (current-thread s)
                                                   (thread-table s))))))
               (hp-init (heap-init-map (aux s)))))))))



(defthm consistent-state-obj-init-local-at-2
  (implies (and  (integerp i)
                 (<= 0 i)
                 (< i (len (locals (current-frame s))))
                 (consistent-state-obj-init s)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s))))
                 (case-split (equal (tag-of (local-at i s)) 'REF))
                 (case-split (not (NULLp (local-at i s))))
                 (case-split (not (initialized-ref (value-of (local-at i s))
                                                   (heap-init-map (aux s)))))
                 (case-split (equal (method-ptr-methodname
                                     (method-ptr frame))
                                    "<init>"))
                 (equal (current-frame s) frame)
                 (case-split (not (equal (value-of (local-at i s))
                                         (acl2::g 'this (frame-aux frame)))))
                 (equal (current-frame s) frame))
            (mem  (value-of (local-at i s))
                  (collect-values 
                   (frame-obj-init-map frame))))
  :hints (("Goal" :use ((:instance consistent-state-obj-init-local-at-i-2-lemma)))))


(defthm consistent-state-obj-init-wff-tagged-value
  (implies (and (mem v locals)
                (consistent-locals-obj-init locals hp-init valid-sync-refs))
           (wff-tagged-value v))
  :hints (("Goal" :in-theory (enable consistent-locals-obj-init))))



(defthm consistent-state-obj-init-wff-tagged-value-specific-1
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (equal (method-ptr-methodname
                                    (method-ptr (current-frame s)))
                                   "<init>"))
                (case-split (consistent-locals-obj-init (locals (current-frame s))
                                                        (heap-init-map (aux s))
                                                        (cons (acl2::g 'this 
                                                                       (frame-aux (current-frame s)))
                                                              (collect-values 
                                                               (frame-obj-init-map 
                                                                (current-frame s)))))))
           (wff-tagged-value (local-at i s)))
  :hints (("Goal" :in-theory (disable current-frame  mem-local-at-locals)
           :use ((:instance mem-local-at-locals
                            (frame (current-frame s)))
                 (:instance consistent-state-obj-init-wff-tagged-value
                                   (v (local-at i s))
                                   (locals (current-frame s))
                                   (hp-init (heap-init-map (aux s)))
                                   (valid-sync-refs (cons (acl2::g 'this 
                                                                   (frame-aux (current-frame s)))
                                                          (collect-values 
                                                           (frame-obj-init-map 
                                                            (current-frame s))))))))))



(defthm consistent-state-obj-init-wff-tagged-value-specific-2
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len (locals (current-frame s))))
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr (current-frame s)))
                                        "<init>")))
                (case-split (consistent-locals-obj-init (locals (current-frame s))
                                                        (heap-init-map (aux s))
                                                        (collect-values 
                                                         (frame-obj-init-map 
                                                          (current-frame s))))))
           (wff-tagged-value (local-at i s)))
  :hints (("Goal" :in-theory (disable current-frame mem-local-at-locals)
           :use ((:instance mem-local-at-locals
                            (frame (current-frame s)))
                 (:instance consistent-state-obj-init-wff-tagged-value
                                   (v (local-at i s))
                                   (locals (current-frame s))
                                   (hp-init (heap-init-map (aux s)))
                                   (valid-sync-refs (collect-values 
                                                     (frame-obj-init-map 
                                                      (current-frame s)))))))))


;;; Sat Aug  6 00:33:29 2005
;;; prove a lemma to shortern the reasoning


(defthm consistent-state-obj-init-implies-consistent-locals-obj-init-1
  (implies (and (consistent-state-obj-init s)
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s))))
                (case-split (not (equal (method-ptr-methodname
                                         (method-ptr (current-frame s)))
                                        "<init>")))
                (equal (current-frame s) frame))
           (consistent-locals-obj-init (locals frame)
                                       (heap-init-map (aux s))
                                       (collect-values 
                                        (frame-obj-init-map 
                                         frame)))))




(defthm consistent-state-obj-init-implies-consistent-locals-obj-init-2
  (implies (and (consistent-state-obj-init s)
                (thread-by-id (current-thread s) (thread-table s))
                (consp (thread-call-stack (thread-by-id (current-thread s)
                                                        (thread-table s))))
                (case-split (equal (method-ptr-methodname
                                    (method-ptr (current-frame s)))
                                   "<init>"))
                (equal (acl2::g 'this (frame-aux frame)) x)
                (equal (current-frame s) frame))
           (consistent-locals-obj-init (locals frame)
                                       (heap-init-map (aux s))
                                       (cons x 
                                             (collect-values 
                                              (frame-obj-init-map 
                                               frame))))))



(defthm consistent-state-obj-init-pushStack
   (implies (and (consistent-state-obj-init s)
                 (<= 0 i)
                 (< i (len (locals (current-frame s))))
                 (integerp i)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s)))))
            (consistent-state-obj-init (pushStack (local-at i s) s))))


;----------------------------------------------------------------------


;----------------------------------------------------------------------


;; some fact about initialized-ref
;;(include-book "djvm-heap")

(defthm not-consp-deref2-init-implies-initialized-ref
  (implies (not (consp (deref2-init (tag-REF v) hp-init)))
           (initialized-ref v hp-init))
  :hints (("Goal" :in-theory (enable initialized-ref))))
  
;----------------------------------------------------------------------

(defthm consistent-value-implies-wff-tagged-value
  (implies (consistent-value v type cl hp)
           (wff-tagged-value v)))

;----------------------------------------------------------------------



;; (i-am-here) 
(defthm thread-table-state-set-heap-reduce
  (equal (thread-table (state-set-heap any s))
         (thread-table s))
  :hints (("Goal" :in-theory (enable state-set-pc))))


(defthm aux-state-set-heap-reduce
  (equal (aux  (state-set-heap any s))
         (aux  s))
  :hints (("Goal" :in-theory (enable state-set-pc))))


(defthm consistent-state-obj-init-preserved-by-state-set-heap
  (equal (consistent-state-obj-init (state-set-heap any s))
         (consistent-state-obj-init s)))

;----------------------------------------------------------------------

;;(i-am-here) ;; Sun Aug  7 09:58:15 2005

(encapsulate () 
  (local (include-book "INST/base-load-class-normalize"))

  (defthm getArrayClass-reduce
    (and (equal (PC (GETARRAYCLASS any s))
                (pc s))
         (equal (current-thread (getarrayclass any s))
                (current-thread s))
         (equal (thread-table (getarrayclass any s))
                (thread-table s))
         (equal (current-frame (getarrayclass any s))
                (current-frame s))
         (equal (heap-init-map (aux (getarrayclass any s)))
                (heap-init-map (aux s))))
    :hints (("Goal" :in-theory (enable getarrayclass))))


  (defthm resolveClassReference-reduce
    (and (equal (PC (resolveClassReference any s))
                (pc s))
         (equal (current-thread (resolveClassReference any s))
                (current-thread s))
         (equal (thread-table (resolveClassReference any s))
                (thread-table s))
         (equal (heap-init-map (aux (resolveClassReference any s)))
                (heap-init-map (aux s)))
         (equal (current-frame (resolveClassReference any s))
                (current-frame s)))
    :hints (("Goal" :in-theory (enable resolveClassReference)))))


(defthm consistent-state-obj-init-preserved-by-resolveClassReference
  (equal (consistent-state-obj-init (resolveClassReference any s))
         (consistent-state-obj-init s))
  :hints (("Goal" :in-theory (disable resolveClassReference))))


(defthm consistent-state-obj-init-preserved-by-getArrayClass
  (equal (consistent-state-obj-init (getArrayClass any s))
         (consistent-state-obj-init s))
  :hints (("Goal" :in-theory (disable getArrayClass))))



(defthm consistent-state-obj-init-preserved-by-make-state
  (implies (equal (heap-init-map (aux s)) (heap-init-map aux))
           (equal (consistent-state-obj-init (make-state pc cid 
                                                         hp 
                                                         (thread-table s)
                                                         cl 
                                                         env
                                                         ef
                                                         aux))
                  (consistent-state-obj-init s)))
  :hints (("Goal" :in-theory (enable consistent-state-obj-init)))) 
;----------------------------------------------------------------------


(defthm consistent-state-obj-init-pushStack-topx-topx
   (implies (and (consistent-state-obj-init s)
                 (thread-by-id (current-thread s) (thread-table s))
                 (consp (thread-call-stack (thread-by-id (current-thread s)
                                                         (thread-table s)))))
            (consistent-state-obj-init (pushStack '(topx . topx) s))))


;----------------------------------------------------------------------

(defthm thread-table-update-trace-is
  (equal (thread-table (update-trace any s))
         (thread-table s))
  :hints (("Goal" :in-theory (enable update-trace))))



(defthm heap-init-map-update-trace-is
  (equal (heap-init-map (aux (update-trace any s)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable update-trace 
                                     aux-set-trace
                                     heap-init-map))))



(defthm consistent-state-obj-init-update-trace
  (equal    (consistent-state-obj-init (update-trace any s))
            (consistent-state-obj-init s))
   :hints (("Goal" :in-theory (disable update-trace))))
