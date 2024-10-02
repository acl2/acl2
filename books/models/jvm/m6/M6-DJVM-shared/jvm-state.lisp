(in-package "JVM")
(include-book "misc/records" :dir :system)
(include-book "../M6-DJVM-shared/jvm-class-table")
(include-book "../M6-DJVM-shared/jvm-env")
(include-book "../M6-DJVM-shared/jvm-internal-primitives")


(acl2::set-verify-guards-eagerness 2)

; The following originally is from djvm-state.lisp. Guard verified. 
;----------------------------------------------------------------------
  
(defun make-state (ip cur javaheap thread-table internal-class-table env
                      error-flag aux)
  (list 'state 
        ip 
        cur 
        (cons 'heap         javaheap)
        (cons 'thread-table thread-table)
        internal-class-table 
        env error-flag
        aux))


;;;; 
;;;; really want to have the following property. 
;;;; 

;;;; so modified!! 

(defun wff-state (s) 
  (declare (xargs :verify-guards t))
  (and (equal (len s) 9)
       (equal (car s) 'state)
       (true-listp s)
       (integerp (nth 1 s)) ;; updated. Sat May  7 21:17:15 2005
       (consp (nth 3 s))
       (equal (car (nth 3 s)) 'heap)
       (consp (nth 4 s))
       (equal (car (nth 4 s)) 'thread-table)))



;; (defun wff-state (s) 
;;   (declare (xargs :verify-guards t))
;;   (and (equal (len s) 9)
;;        (true-listp s)
;;        (integerp (nth 1 s)) ;; updated. Sat May  7 21:17:15 2005
;;        (consp (nth 3 s))
;;        (consp (nth 4 s))
;;        (equal (car s) 'state)))


;; (skip-proofs 
;;  (defthm wff-state-implies-make-state-equal-state
;;    (implies (wff-state s)
;;             (equal (make-state (pc s)
;;                                (current-thread s)
;;                                (heap s)
;;                                (thread-table s)
;;                                (class-table s)
;;                                (env s)
;;                                (error-flag s)
;;                                (aux s))
;;                    s))))






(defun pc (s)
  (declare (xargs :guard (wff-state s))) 
  (nth 1 s)) ;; global register : a number  

(defun current-thread (s)
  (declare (xargs :guard (wff-state s))) 
  (nth 2 s)) ;; global register : a number 

(defun heap  (s)  
  (declare (xargs :guard (wff-state s)))
  (cdr (nth 3 s))) ;; java heap : a list of java Objects 


(defun thread-table (s)           
  (declare (xargs :guard (wff-state s)))
  (cdr (nth 4 s))) ;; a list of internal rep of threads


(defun class-table  (s)
  (declare (xargs :guard (wff-state s))) 
  (nth 5 s)) ;; a list of internal rep of classes 


(defun env (s)   
  (declare (xargs :guard (wff-state s)))
  (nth 6 s)) ;; only loader read from env



(defun error-flag  (s) 
  (declare (xargs :guard (wff-state s)))
  (nth 7 s)) ;; only loader read from env

(defun aux  (s) 
  (declare (xargs :guard (wff-state s)))
  (nth 8 s))



(defun wff-aux (aux)
  (declare (ignore aux))
  t)


(defun heap-init-map (aux)
  (declare (xargs :guard (wff-aux aux)))
  (acl2::g 'heap-init-map aux))

;;(i-am-here) ;; Sun Jun 12 23:42:44 2005

(encapsulate () 
 (local 
  (encapsulate ()  

     (defthm len-equal-0-implies-equal
       (implies (and l 
                     (equal (len l) 0))
                (not (true-listp l))))


     (defthm len-equal-1-implies-equal
       (implies (and (true-listp l)
                     (equal (len l) 1))
                (equal (list (car l))
                       l)))

     (defthm len-equal-2-implies-equal
       (implies (and (true-listp l)
                     (equal (len l) 2))
                (equal (list (car l)
                             (nth 1 l))
                       l)))


     (defthm len-equal-3-implies-equal
       (implies (and (true-listp l)
                     (equal (len l) 3))
                (equal (list (car l)
                             (nth 1 l)
                             (nth 2 l))
                       l)))


     (defthm len-equal-4-implies-equal
       (implies (and (true-listp l)
                     (equal (len l) 4))
                (equal (list (car l)
                             (nth 1 l)
                             (nth 2 l)
                             (nth 3 l))
                       l)))


     (defthm len-equal-5-implies-equal
       (implies (and (true-listp l)
                     (equal (len l) 5))
                (equal (list (car l)
                             (nth 1 l)
                             (nth 2 l)
                             (nth 3 l)
                             (nth 4 l))
                       l)))


     (defthm len-equal-6-implies-equal
       (implies (and (true-listp l)
                     (equal (len l) 6))
                (equal (list (car l)
                             (nth 1 l)
                             (nth 2 l)
                             (nth 3 l)
                             (nth 4 l)
                             (nth 5 l))
                       l)))


     (defthm len-equal-7-implies-equal
       (implies (and (true-listp l)
                     (equal (len l) 7))
                (equal (list (car l)
                             (nth 1 l)
                             (nth 2 l)
                             (nth 3 l)
                             (nth 4 l)
                             (nth 5 l)
                             (nth 6 l))
                       l)))

     (defthm len-equal-8-implies-equal
       (implies (and (true-listp l)
                     (equal (len l) 8))
                (equal (list (car l)
                             (nth 1 l)
                             (nth 2 l)
                             (nth 3 l)
                             (nth 4 l)
                             (nth 5 l)
                             (nth 6 l)
                             (nth 7 l))
                       l)))



     (defthm len-equal-8-implies-equal-general
       (implies (and (true-listp l)
                     (equal (len l) 8)
                     (equal (nth 2 l) nth2)
                     (equal (nth 3 l) nth3))
                (equal (list (car l)
                             (nth 1 l)
                             nth2 
                             nth3 
                             (nth 4 l)
                             (nth 5 l)
                             (nth 6 l)
                             (nth 7 l))
                       l)))))

 (defthm wff-state-implies-make-state-equal-state
   (implies (wff-state s)
            (equal (make-state (pc s)
                               (current-thread s)
                               (heap s)
                               (thread-table s)
                               (class-table s)
                               (env s)
                               (error-flag s)
                               (aux s))
                   s))
  :hints (("Goal" 
           :in-theory (enable wff-state 
                              make-state)
           :expand 
           ((make-state (pc s)
                        (current-thread s)
                        (heap s)
                        (thread-table s)
                        (class-table s)
                        (env s)
                        (error-flag s)
                        (aux s))
            (pc s)
            (current-thread s)
            (heap s)
            (thread-table s)
            (class-table s)
            (env s)
            (error-flag s)
            (aux s))))))
 


;;;
;;; Sun Jun 12 21:07:50 2005
;;; Should not affect much of the old proof!! 
;;;
;; generic functions to modify the state. hide the internal structures.
(defun state-set-pc  (pc s)
  (declare (xargs :guard (wff-state s)))
  (make-state pc 
              (current-thread s)
              (heap s)
              (thread-table s)
              (class-table s)
              (env s)
              (error-flag s)
              (aux s)))

(defun state-set-current-thread  (id s)
  (declare (xargs :guard (wff-state s)))
  (make-state (pc s) 
              id
              (heap s)
              (thread-table s)
              (class-table s)
              (env s)
              (error-flag s)
              (aux s)))

(defun state-set-heap  (heap s)
  (declare (xargs :guard (wff-state s)))
  (make-state (pc s) 
              (current-thread s)
              heap
              (thread-table s)
              (class-table s)
              (env s)
              (error-flag s)
              (aux s)))
  

(defun state-set-thread-table  (tt s)
  (declare (xargs :guard (wff-state s)))
  (make-state (pc s) 
              (current-thread s)
              (heap s)
              tt
              (class-table s)
              (env s)
              (error-flag s)
              (aux s)))

(defun state-set-class-table (ct s)
  (declare (xargs :guard (wff-state s)))
  (make-state (pc s) 
              (current-thread s)
              (heap s)
              (thread-table s)
              ct
              (env s)
              (error-flag s)
              (aux s)))

(defun state-set-env (env s)
  (declare (xargs :guard (wff-state s)))
  (make-state (pc s) 
              (current-thread s)
              (heap s)
              (thread-table s)
              (class-table s)
              env
              (error-flag s)
              (aux s)))


(defun state-set-error-flag (ef s)
  (declare (xargs :guard (wff-state s)))
  (make-state (pc s) 
              (current-thread s)
              (heap s)
              (thread-table s)
              (class-table s)
              (env s)
              ef
              (aux s)))

 
(defun state-set-aux (aux s)
  (declare (xargs :guard (wff-state s)))
  (make-state (pc s) 
              (current-thread s)
              (heap s)
              (thread-table s)
              (class-table s)
              (env s)
              (error-flag s)
              aux))

(defthm state-accessor 
  (mylet* ((s (make-state pc th hp tt cl env ef aux)))
  (and (equal (pc                  s)    pc)
       (equal (current-thread      s)    th)
       (equal (thread-table        s)    tt)
       (equal (heap                s)    hp)
       (equal (class-table         s)    cl)
       (equal (env                 s)    env)
       (equal (error-flag          s)    ef)
       (equal (aux                 s)   aux))))


;----------------------------------------------------------------------

(defun instance-class-table (S)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s)))))
  (cdr (nth 1 (class-table s))))

(defun array-class-table (s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s)))))
  (cdr (nth 2 (class-table s))))

;----------------------------------------------------------------------

;(acl2::set-verify-guards-eagerness 0) ;; temp  Wed Mar 31 11:43:45 2004

; The following comes from m6-state.lisp. There is no need to do guard
; verificaiton.?? 

; ADD guard verification for DJVM primitives is a big task!! Wed Mar 31
; 11:42:56 2004 and lots of work. 
;

;----------------------------------------------------------------------
;
; Eventually we still need to do guard verification... 
; Because quite a few functions are neeeded in defining the class loader...

(defun trace-aux (aux)
  (acl2::g 'trace aux))

(defun aux-set-trace (trace aux)
  (acl2::s 'trace trace aux))

(defun ptable-aux (aux)
  (acl2::g 'ptable aux))

(defun set-ptable-aux (ptable aux)
  (acl2::s 'ptable ptable aux))

(defun mtrace (s)
  (declare (xargs :guard (wff-state s)))
  (trace-aux (aux s)))


;; this is used for package!! 
(defun pname (n s)
  (declare (xargs :guard (and (wff-state s)
                              (alistp (ptable-aux (aux s))))))
  (if (consp (assoc-equal n (ptable-aux (aux s))))
      (cdr (assoc-equal n (ptable-aux (aux s))))
    nil))


(defun state-set-trace  (trace s)
  (declare (xargs :guard (wff-state s)))
  (state-set-aux (aux-set-trace trace (aux s)) s))


(defun pending-exception-aux (aux)
  (acl2::g 'pending-exception aux))

(defun set-pending-exception-aux-safe (pending aux)
  (if (not (pending-exception-aux aux))
      (acl2::s 'pending-exception pending aux)
    aux))

(defun set-pending-exception-aux (pending aux)
  (acl2::s 'pending-exception pending aux))


;; (defun state-set-pending-exception-safe (pending s)
;;   (state-set-aux (set-pending-exception-aux-safe pending (aux s)) s))


(defun pending-exception (s)
  (declare (xargs :guard (wff-state s)))
  (pending-exception-aux (aux s)))

(defun state-set-pending-exception-safe (pending s)
  (declare (xargs :guard (wff-state s)))
  (state-set-aux (set-pending-exception-aux-safe pending (aux s)) s))

(defun state-set-instance-class-table (instance-class-table s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s)))))
  (state-set-class-table 
    (make-class-table instance-class-table
                      (array-class-table s)) s))

(defun state-set-array-class-table (array-class-table s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s)))))
  (state-set-class-table 
    (make-class-table (instance-class-table s)
                      array-class-table)        s))


(defun add-instance-class-entry (class-rep class-table)
  (cons class-rep class-table))

;----------------------------------------------------------------------

(defun setClassInitialThread  (classname init-tid s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table
                                                         s))
                              (wff-class-rep (class-by-name classname
                                              (instance-class-table s))))))
  (mylet* ((old-instance-class-table (instance-class-table s))
           (old-class-rep  (class-by-name classname old-instance-class-table))
           (new-class-rep  (make-runtime-class-rep
                            (classname old-class-rep)
                            (super     old-class-rep)
                            (constantpool old-class-rep)
                            (fields       old-class-rep)
                            (methods      old-class-rep)
                            (interfaces    old-class-rep)
                            (static-fields old-class-rep)
                            (class-status  old-class-rep)
                            (class-accessflags old-class-rep)
                            init-tid
                            (class-ref    old-class-rep)))
           (new-instance-class-table 
            (replace-class-table-entry old-class-rep new-class-rep
                                       old-instance-class-table)))
          (state-set-class-table (make-class-table new-instance-class-table
                                                   (array-class-table s))
                                 s)))


(defun setClassStatus  (classname new-status s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table
                                                         s))
                              (wff-class-rep (class-by-name classname
                                              (instance-class-table s))))))
  (let* ((old-instance-class-table (instance-class-table s))
         (old-class-rep  (class-by-name classname old-instance-class-table))
         (new-class-rep  (make-runtime-class-rep
                          (classname old-class-rep)
                          (super     old-class-rep)
                          (constantpool old-class-rep)
                          (fields       old-class-rep)
                          (methods      old-class-rep)
                          (interfaces    old-class-rep)
                          (static-fields old-class-rep)
                          new-status
                          (class-accessflags old-class-rep)
                          (init-thread-id old-class-rep) 
                          (class-ref    old-class-rep)))
         (new-instance-class-table 
             (replace-class-table-entry old-class-rep new-class-rep
                                        old-instance-class-table)))
    (state-set-class-table (make-class-table new-instance-class-table
                                             (array-class-table s))
                           s)))


;;these belongs to M6/jvm-state.lisp

(defun class-initialized? (classname s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table
                                                         s))
                              (wff-class-rep (class-by-name classname
                                              (instance-class-table s))))))
  (mylet* ((class-rep (class-by-name classname (instance-class-table s)))
           (status    (class-status class-rep))
           (init-thread-id (init-thread-id class-rep)))
    (or (equal status 'class_ready)
        (equal init-thread-id (current-thread s)))))

;----------------------------------------------------------------------
(acl2::set-verify-guards-eagerness 2)

(defun external-class-table (s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-env (env s)))))
  (env-class-table (env s)))


;; (acl2::set-verify-guards-eagerness 0)
;; Tue Dec 23 17:13:46 2003 from jvm-env
;; Wed Mar 31 12:13:50 2004. add


;----------------------------------------------------------------------

;;; (acl2::set-verify-guards-eagerness 0)
;;; Wed Mar 31 12:14:46 2004

;;; Wed Mar 31 12:17:13 2004

(defun update-trace (obj-ref s)
  (declare (xargs :guard (wff-state s)))
  (state-set-trace 
   (add-obj-th-count obj-ref (current-thread s) (mtrace s))
   s))



;----------------------------------------------------------------------
; Thu Dec 25 11:41:10 2003

(acl2::set-verify-guards-eagerness 2)
(defun m6-internal-error (msg s)
  (declare (xargs :guard (wff-state s)))
  (prog2$ 
   (acl2::cw msg)
   (state-set-error-flag msg s)))


(defun fatalError (msg s)
  (declare (xargs :guard (wff-state s)))
  (m6-internal-error msg s))


(defun no-fatal-error? (s)
  (declare (xargs :guard (wff-state s)))
  (equal (error-flag s) nil))

;; should stop abruptly. could implment it set a flag in the state 
;; so the interpreter will detect. 

(defun alertUser (msg s)
  (prog2$ (acl2::cw "~p0~%" msg)
          s))

;----------------------------------------------------------------------

(defun class-ref-by-name (classname s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-instance-class-table (instance-class-table
                                                         s))
                              (wff-class-rep (class-by-name classname
                                              (instance-class-table s))))))
  (class-ref (class-by-name classname (instance-class-table s))))

;----------------------------------------------------------------------

;; (defun make-state (ip cur javaheap thread-table internal-classble env
;;                       error-flag aux)
;;   (list 'state 
;;         ip 
;;         cur 
;;         (cons 'heap         javaheap)
;;         (cons 'thread-table thread-table)
;;         internal-class-table 
;;         env error-flag
;;         aux))

;(in-theory (disable make-state current-thread heap thread-table current-thread
;                    class-table instance-class-table array-class-table env
;                    error-flag aux pc) )



(defthm state-accessor-set-pc
  (let ((s1 (state-set-pc pc s0)))
    (and (equal (pc s1) pc)
         (equal (current-thread s1) (current-thread s0))
         (equal (heap s1) (heap s0))
         (equal (thread-table s1) (thread-table s0))
         (equal (class-table s1) (class-table s0))
         (equal (instance-class-table s1) (instance-class-table s0))
         (equal (array-class-table s1) (array-class-table s0))
         (equal (env s1) (env s0))
         (equal (error-flag s1) (error-flag s0))
         (equal (aux s1) (aux s0)))))

(defthm state-accessor-set-current-thread
  (let ((s1 (state-set-current-thread tid s0)))
    (and (equal (pc s1) (pc s0))
         (equal (current-thread s1) tid)
         (equal (heap s1) (heap s0))
         (equal (thread-table s1) (thread-table s0))
         (equal (class-table s1) (class-table s0))
         (equal (instance-class-table s1) (instance-class-table s0))
         (equal (array-class-table s1) (array-class-table s0))
         (equal (env s1) (env s0))
         (equal (error-flag s1) (error-flag s0))
         (equal (aux s1) (aux s0)))))


(defthm state-accessor-set-heap
  (let ((s1 (state-set-heap hp s0)))
    (and (equal (pc s1) (pc s0))
         (equal (current-thread s1) (current-thread s0))
         (equal (heap s1) hp)
         (equal (thread-table s1) (thread-table s0))
         (equal (class-table s1) (class-table s0))
         (equal (instance-class-table s1) (instance-class-table s0))
         (equal (array-class-table s1) (array-class-table s0))
         (equal (env s1) (env s0))
         (equal (error-flag s1) (error-flag s0))
         (equal (aux s1) (aux s0)))))



(defthm state-accessor-set-thread-table
  (let ((s1 (state-set-thread-table tt s0)))
    (and (equal (pc s1) (pc s0))
         (equal (current-thread s1) (current-thread s0))
         (equal (heap s1) (heap s0))
         (equal (thread-table s1) tt)
         (equal (class-table s1) (class-table s0))
         (equal (instance-class-table s1) (instance-class-table s0))
         (equal (array-class-table s1) (array-class-table s0))
         (equal (env s1) (env s0))
         (equal (error-flag s1) (error-flag s0))
         (equal (aux s1) (aux s0)))))



(defthm state-accessor-set-class-table
  (let ((s1 (state-set-class-table cl s0)))
    (and (equal (pc s1) (pc s0))
         (equal (current-thread s1) (current-thread s0))
         (equal (heap s1) (heap s0))
         (equal (thread-table s1) (thread-table s0))
         (equal (class-table s1) cl)
;;         (equal (instance-class-table s1) (
;;         (equal (array-class-table s1) (array-class-table s0))
;; Mon Dec 29 16:14:33 2003 leave it here now
         (equal (env s1) (env s0))
         (equal (error-flag s1) (error-flag s0))
         (equal (aux s1) (aux s0)))))


(defthm state-accessor-set-env
  (let ((s1 (state-set-env env s0)))
    (and (equal (pc s1) (pc s0))
         (equal (current-thread s1) (current-thread s0))
         (equal (heap s1) (heap s0))
         (equal (thread-table s1) (thread-table s0))
         (equal (class-table s1) (class-table s0))
         (equal (instance-class-table s1) (instance-class-table s0))
         (equal (array-class-table s1) (array-class-table s0))
         (equal (env s1) env)
         (equal (error-flag s1) (error-flag s0))
         (equal (aux s1) (aux s0)))))

(defthm state-accessor-set-error-flag
  (let ((s1 (state-set-error-flag ef s0)))
    (and (equal (pc s1) (pc s0))
         (equal (current-thread s1) (current-thread s0))
         (equal (heap s1) (heap s0))
         (equal (thread-table s1) (thread-table s0))
         (equal (class-table s1) (class-table s0))
         (equal (instance-class-table s1) (instance-class-table s0))
         (equal (array-class-table s1) (array-class-table s0))
         (equal (env s1) (env s0))
         (equal (error-flag s1) ef)
         (equal (aux s1) (aux s0)))))


(defthm state-accessor-set-aux
  (let ((s1 (state-set-aux aux s0)))
    (and (equal (pc s1) (pc s0))
         (equal (current-thread s1) (current-thread s0))
         (equal (heap s1) (heap s0))
         (equal (thread-table s1) (thread-table s0))
         (equal (class-table s1) (class-table s0))
         (equal (instance-class-table s1) (instance-class-table s0))
         (equal (array-class-table s1) (array-class-table s0))
         (equal (env s1) (env s0))
         (equal (error-flag s1) (error-flag s0))
         (equal (aux s1) aux))))

;; (in-theory (disable make-state current-thread heap thread-table current-thread
;;                     class-table instance-class-table array-class-table env
;;                     error-flag aux pc) )



(in-theory (disable make-state env pc current-thread thread-table heap class-table
                    env error-flag))

