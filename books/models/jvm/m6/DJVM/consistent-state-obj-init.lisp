(in-package "DJVM")
(include-book "../DJVM/consistent-state")


;; (include-book "../DJVM/djvm-env")
;; (include-book "../DJVM/djvm-class-table")
;; (include-book "../DJVM/djvm-thread")
;; (include-book "../DJVM/djvm-obj")
;; (include-book "../DJVM/djvm-type-value")
;; (include-book "../DJVM/djvm-linker")


;;; The predicate defined in this section: asserts that if local or operand
;;; stack contains uninitialized reference, then, these references should be
;;; kept tracked of in frame-obj-init-map.
;;; 
;;; Mon Oct 24 13:52:01 2005

(acl2::set-verify-guards-eagerness 2)

(defun frame-obj-init-map (frame) 
  (declare (xargs :guard (wff-call-frame frame)))
  (acl2::g 'frame-obj-init-map (frame-aux frame)))

(defun collect-keys (obj-init-map) 
  (declare (xargs :guard (alistp obj-init-map)))
  (if (endp obj-init-map) nil
    (cons (car (car obj-init-map))
          (collect-keys (cdr obj-init-map)))))

(defun collect-values (obj-init-map)
  (declare (xargs :guard (and (alistp obj-init-map)
                              (nodup-set (collect-keys obj-init-map)))))
  (if (endp obj-init-map) nil
    (cons (cdr (car obj-init-map))
          (collect-values (cdr obj-init-map)))))


(defun initialized-ref (ref hp-init)
  (declare (xargs :guard (wff-heap-init-map-strong hp-init)))
  (or (not (bound? ref hp-init))
      (not (consp (binding ref hp-init)))))


;; (defun consistent-locals-obj-init (locals hp-init valid-obj-refs)
;;   (declare (xargs :guard (and (wff-heap-init-map-strong hp-init)
;;                               (true-listp valid-obj-refs))))
;;   (if (not (consp locals)) t
;;     (cond ((category1loc locals)
;;            (and (or (not (equal (tag-of (car locals)) 'REF)) 
;;                     ;; not a reference value! 
;;                     (NULLp (car locals))
;;                     (initialized-ref (value-of (car locals)) hp-init)
;;                     (mem (value-of (car locals)) valid-obj-refs))
;;                 (consistent-locals-obj-init (shift1slot locals) hp-init 
;;                                             valid-obj-refs)))
;;           ((category2loc locals)
;;            (consistent-locals-obj-init (shift2slot locals) hp-init valid-obj-refs)))))
      

;; (defun wff-tagged-locals (l)
;;   (if (not (consp l)) t
;;     (and (wff-tagged-value (car l))
;;          (wff-tagged-locals (cdr l)))))

;; ;;;
;; ;;; this will make the guard verification for consistent-state-strong 
;; ;;; a bit complicated! 
;; ;;; 
;; ;;; the benefit is that we can have some nice lemma about pushStack and
;; ;;; popStack without thinking too much about the guard! --- by ignoring the
;; ;;; difference between size two value and size one value!! 
;; ;;; 
;;;;;; 

(defun consistent-locals-obj-init (locals hp-init valid-obj-refs)
   (declare (xargs :guard (and (wff-heap-init-map-strong hp-init)
                               (true-listp valid-obj-refs))))
   (if (not (consp locals)) t
     (and (wff-tagged-value (car locals))
          (or (not (equal (tag-of (car locals)) 'REF))
              (NULLp (car locals))
              (initialized-ref (value-of (car locals)) hp-init)
              (mem (value-of (car locals)) valid-obj-refs))
          (consistent-locals-obj-init (cdr locals) hp-init valid-obj-refs))))


;; (defun consistent-opstack-obj-init (stack hp-init valid-obj-refs)
;;   (declare (xargs :guard (and (wff-heap-init-map-strong hp-init)
;;                               (true-listp valid-obj-refs))))
;;   (if (not (consp stack)) t
;;     (cond ((canPopCategory1 stack)
;;            (and (or (not (equal (tag-of (topCategory1 stack)) 'REF))
;;                     ;; not a reference value! 
;;                     (NULLp (topCategory1 stack))
;;                     (initialized-ref (value-of (topCategory1 stack)) hp-init)
;;                     (mem (value-of (topCategory1 stack)) valid-obj-refs))
;;                 (consistent-opstack-obj-init (popCategory1 stack) hp-init 
;;                                             valid-obj-refs)))
;;           ((canPopCategory2 stack)
;;            (consistent-opstack-obj-init (popCategory2 stack) hp-init valid-obj-refs)))))

(defun consistent-opstack-obj-init (stack hp-init valid-obj-refs)
  (declare (xargs :guard (and (wff-heap-init-map-strong hp-init)
                              (true-listp valid-obj-refs))))
  (if (not (consp stack)) t
    (and (wff-tagged-value (car stack))
         (or (not (equal (tag-of (car stack)) 'REF))
             (NULLp (car stack))
             (initialized-ref (value-of (car stack)) hp-init)
             (mem (value-of (car stack)) valid-obj-refs))
         (consistent-opstack-obj-init (cdr stack) hp-init 
                                      valid-obj-refs))))

      
(defun isConstructorFrame (frame)
  (declare (xargs :guard (wff-call-frame frame)
                  :guard-hints (("Goal" :in-theory (enable wff-call-frame)))))
  (equal (method-ptr-methodname (method-ptr frame))
         "<init>"))
          
(defun consistent-frame-obj-init (frame hp-init)
  (declare (xargs :guard (and (wff-call-frame frame)
                              (wff-heap-init-map-strong hp-init))))
  (mylet* ((obj-refs  (collect-values (frame-obj-init-map frame)))
           (this      (acl2::g 'this (frame-aux frame)))
           (vars      (locals frame))
           (stack     (operand-stack frame)))
    (and (alistp (frame-obj-init-map frame))
       (nodup-set (collect-keys (frame-obj-init-map frame)))
       (cond ((isConstructorFrame frame)
               (and (consistent-locals-obj-init vars hp-init (cons this obj-refs))
                    (consistent-opstack-obj-init stack hp-init (cons this obj-refs))))
             (t (and (consistent-locals-obj-init vars hp-init obj-refs)
                     (consistent-opstack-obj-init stack hp-init obj-refs)))))))


          
(defun consistent-call-stack-obj-init (call-stack hp-init)
  (declare (xargs :guard (wff-heap-init-map-strong hp-init)))
  (if (not (consp call-stack)) t
    (and (wff-call-frame (car call-stack))
         (consistent-frame-obj-init (car call-stack) hp-init)
         (consistent-call-stack-obj-init (cdr call-stack) hp-init))))

          
(defun consistent-thread-entry-obj-init (thread-entry hp-init)
  (declare (xargs :guard (wff-heap-init-map-strong hp-init)))
  (and (wff-thread thread-entry)
       (consistent-call-stack-obj-init (thread-call-stack thread-entry)
                                       hp-init)))


(defun consistent-thread-table-obj-init (tt hp-init)
  (declare (xargs :guard (wff-heap-init-map-strong hp-init)))
  (if (not (consp tt)) t
    (and (consistent-thread-entry-obj-init (car tt) hp-init)
         (consistent-thread-table-obj-init (cdr tt) hp-init))))



(defun consistent-state-obj-init (s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-heap-init-map-strong (heap-init-map (aux s))))))
  (consistent-thread-table-obj-init (thread-table s) (heap-init-map (aux s))))


(in-theory (disable consistent-state-obj-init
                    consistent-thread-table-obj-init
                    consistent-thread-entry-obj-init
                    consistent-call-stack-obj-init
                    consistent-frame-obj-init
                    consistent-opstack-obj-init
                    consistent-locals-obj-init))

;----------------------------------------------------------------------


