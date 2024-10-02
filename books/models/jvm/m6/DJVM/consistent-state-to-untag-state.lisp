(in-package "DJVM")
(include-book "../DJVM/consistent-state")

(acl2::set-verify-guards-eagerness 0) 

;----------------------------------------------------------------------

;; (defun untag-value (v)
;;   (if (equal v 'topx)  ;; Mon Aug  1 23:43:27 2005 
;;       'topx
;;     (value-of v)))

;; ;;; we have this fix!! Mon Aug  1 23:43:25 2005
;; ;; no longer necessary 



(defun untag-value (v)
     (value-of v))


;; how to deal with the long and 
(defun untag-opstack (opstack)
  (if (not (consp opstack))
      opstack
    (cons (untag-value (car opstack))
          (untag-opstack (cdr opstack)))))



;; ;; how to deal with the long and 
;; (defun untag-opstack (opstack)
;;   (if (not (consp opstack))
;;       nil
;;     (cond ((canPopCategory1 opstack)
;;            (push (untag-value (top opstack)) (untag-opstack (popCategory1 opstack))))
;;           ((canPopCategory2 opstack)
;;            (push (untag-value (top opstack))
;;                  (push 0
;;                        (untag-opstack (popCategory2 opstack))))))))



;; Fri Apr  9 18:33:32 2004

(defun untag-locals (locals)
  (if (not (consp locals))
      locals
    (cons (untag-value (car locals))
          (untag-locals (cdr locals)))))




;; (defun untag-locals (locals)
;;   (if (not (consp locals))
;;       nil
;;     (cond ((Category1Loc locals)
;;            (cons (untag-value (car locals))
;;                  (untag-locals (shift1slot locals))))
;;           ((Category2Loc locals)
;;            (cons (untag-value (car locals))
;;                  (cons 0
;;                        (untag-locals (shift2slot locals)))))
;;           (t (cons '0 (untag-locals (shift1slot locals)))))))



(defun untag-frame (frame)
  (frame-set-operand-stack 
   (untag-opstack (operand-stack frame))
   (frame-set-locals (untag-locals (locals frame)) frame)))

(defun untag-call-stack (call-stack)
  (if (endp call-stack) nil
    (cons (untag-frame (top call-stack))
          (untag-call-stack (pop call-stack)))))

(defun untag-thread-entry (thread)
  (thread-set-call-stack 
   (untag-call-stack 
    (thread-call-stack thread)) thread))


(defun untag-thread-table (tt)
  (if (endp tt) nil
      (cons (untag-thread-entry (car tt))
            (untag-thread-table (cdr tt)))))

(defun untag-state (s)
  (state-set-thread-table (untag-thread-table (thread-table s))
                          s))

;----------------------------------------------------------------------

;; (i-am-here) ;; Sun Jul 31 18:28:46 2005


(defun locals-equiv (m6-locals djvm-locals)
  (if (endp djvm-locals) 
      (endp m6-locals)
    (if (endp m6-locals) nil
      (and (or (equal (tag-of (car djvm-locals)) 'topx)
               (equal (value-of (car djvm-locals)) 
                      (car m6-locals)))
           (locals-equiv (cdr m6-locals)
                         (cdr djvm-locals))))))

;;;
;;; Tue Aug  2 01:15:02 2005
;;;

;; (defun locals-equiv (m6-locals djvm-locals)
;;   (if (endp djvm-locals) 
;;       (endp m6-locals)
;;     (cond ((category1loc djvm-locals)
;;            (and (consp m6-locals)
;;                 (or (equal (tag-of (car djvm-locals)) 'topx)
;;                     (equal (car m6-locals) (value-of (car djvm-locals))))
;;                 (locals-equiv (cdr m6-locals) (cdr djvm-locals))))
;;           ((category2loc djvm-locals)
;;            (and (consp m6-locals)
;;                 (consp (cdr m6-locals))
;;                 (equal (car m6-locals)  (value-of (car djvm-locals)))
;;                 (equal (cadr m6-locals) 'topx)
;;                 (locals-equiv (cddr m6-locals) (cddr djvm-locals)))))))



(defun frame-equiv (m6-frame djvm-frame)
  (and (locals-equiv (locals m6-frame)
                     (locals djvm-frame))
       (equal (frame-set-locals (locals m6-frame)
                                (frame-set-aux (frame-aux m6-frame)
                                               (untag-frame djvm-frame)))
              m6-frame)))


(defun call-stack-equiv (m6-cs djvm-cs)
  (if (endp djvm-cs)
      (endp m6-cs)
    (if (endp m6-cs) nil
      (and (frame-equiv (car m6-cs) (car djvm-cs))
           (call-stack-equiv (cdr m6-cs) 
                             (cdr djvm-cs))))))

(defun thread-entry-equiv (m6-thread djvm-thread)
  (and (call-stack-equiv (thread-call-stack m6-thread)
                         (thread-call-stack djvm-thread))
       (equal (thread-set-call-stack 
                 (thread-call-stack m6-thread)
                 (untag-thread-entry djvm-thread))
              m6-thread)))


(defun thread-table-equiv (m6-tt  djvm-tt)
  (if (endp djvm-tt)
      (endp m6-tt)
    (if (endp m6-tt) nil
      (and (thread-entry-equiv (car m6-tt) (car djvm-tt))
           (thread-table-equiv (cdr m6-tt) 
                               (cdr djvm-tt))))))
                                


;;; NOTE THIS DEFINITION OF state-equiv IS NOT CORRECT!!! 
;;; Mon Jun 12 15:54:09 2006
;;; 
;;; 
;;; It does not taken into account the object initialization status!!!  The
;;; DJVM maintains an extract heap-init-map
;;;
;;; These went undetected before we have not deal with object initialization
;;; yet.
;;;

(defun state-equiv (m6-s djvm-s)
  (and (thread-table-equiv (thread-table m6-s) 
                           (thread-table djvm-s))
       (equal (state-set-thread-table 
                 (thread-table m6-s)
                 (untag-state djvm-s))
              m6-s)))

;; (defun state-equiv (m6-s djvm-s)
;;   (and (thread-table-equiv (thread-table m6-s) 
;;                            (thread-table djvm-s))
;;        (equal (state-set-thread-table 
;;                  (thread-table m6-s)
;;                  (untag-state djvm-s)
;;               m6-s)))

;;; We keep this definition. However keep the note that this definition is
;;; wrong
;;;
;;; it does not talk about the heap-init-map component of the DJVM!!!
;;;


;; ;;;
;; ;;; Mon Jun 12 15:58:56 2006. FIXED !! 
;; ;;;
;; (defun state-equiv (m6-s djvm-s)
;;   (and (thread-table-equiv (thread-table m6-s) 
;;                            (thread-table djvm-s))
;;        (equal (state-set-thread-table 
;;                  (thread-table m6-s)
;;                  (state-set-aux (aux m6-s)
;;                                 (untag-state djvm-s)))
;;               m6-s)))




;----------------------------------------------------------------------


(defun wff-state-alt (s)
  (declare (xargs :guard (wff-state s)))
  (equal (make-state (pc s)
                     (current-thread s)
                     (heap s)
                     (thread-table s)
                     (class-table s)
                     (env s)
                     (error-flag s)
                     (aux s))
         s))


;----------------------------------------------------------------------
