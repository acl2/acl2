(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-loader")
(include-book "../M6-DJVM-shared/jvm-state")
(include-book "../M6-DJVM-shared/jvm-type-value")


(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)


;; This is really runtime type hierachy for M6. and DJVM
;;; Tue Jan 13 16:09:38 2004 need to get this to guard verify!!
;;; Need to get class loader to guard verify
;;;;
;;;; Tue Jan 13 16:10:01 2004

(acl2::set-verify-guards-eagerness 0) 

(defthm load_class_does_not_change_env 
   (let ((s1 (load_class classname s0)))
     (equal (env s1) (env s0))))

(in-theory (disable load_class env))


(defun superClass1-measure (seen s)
  (let ((cl (env-class-table (env s))))
    (len (set-diff (all-class-names-s cl) seen))))


;; to be proved?  no executable... 
;; we will be able to prove this to be an invariant starting any aribitary
;; program.
;;
;;
;; this is true for all reachable state. --- use defun to characterize


(defun isSuperClass1-invariant (from s)
  (implies (class-loaded? from s)
           (class-exists-externally? from (env-class-table (env s)))))
;;; needed for termination!! Wed Oct 20 11:03:25 2004

;; can prove it as the property of the JVM.

;; rely on the fact that class

(in-theory (disable class-loaded? no-fatal-error? env-class-table))


(in-theory (enable class-exists-externally?))

;;; Wed Oct 20 10:28:56 2004.
;;; 
;;; There is a stronger invariant about isSuperClass1 testing.
;;; JVM will make sure that all superclasses are loaded. 
;;; before executing the following. 
;;;
;;; So we can characterize that all superclasses are loaded as the guard.
;;;
;;; So we revise accordingly.


;(i-am-here)

;; Wed Oct 20 11:09:11 2004
;;; should be an easy proof 
(skip-proofs 
 (defthm loader-inv-class-loaded-implies-isSuperClass-invariant
   (implies (and (loader-inv s)
                 (class-loaded? fromClass s))
            (isSuperClass1-invariant fromClass s))))


;; deal with the guard verification later!! 

;; ;;; modification here 
;;;;;; Fri Jun 10 19:54:07 2005
;;;;;; so it does not return nil merely because 
;;;;;; there is an fatal error... 
;;;;;; maybe not. Let me not change it. 
;;;;;; afraid of changing definition. 


(defun isSuperClass1 (fromClass toClass s seen)
  (declare (xargs :measure (superClass1-measure seen s)
                  :guard (and (loader-inv s)
                              (class-loaded? fromClass s)
                              (class-loaded? toClass s))))
  (if (not (isSuperClass1-invariant fromClass s))
      (mv nil s)
    ;; the guard will ensure this will not fail. 
    (if (not (no-fatal-error? s))
      (mv nil s)
    (if (mem fromClass seen)
        (mv nil s)
      (if (equal fromClass toClass) 
          (mv t s)
        (if (equal fromClass "java.lang.Object")
            (mv nil s)
          (if (class-loaded? fromClass s)
              (isSuperClass1 (super (class-by-name fromClass 
                                                   (instance-class-table s)))
                             toClass  s (cons fromClass seen))
            ;; only possible, when the from Class is does ntot exist in the
            ;; external class table. Dangling link
            (mv nil s))))))))

                                                  

;; (defun isSuperClass1 (fromClass toClass s seen)
;;   (declare (xargs :measure (superClass1-measure seen s)
;;                   :hints (("Subgoal 1" :use 
;;                            no-fatal-error?-after-load-implies-class-exists-externally))))
;;   ;; guard 
;;   (if (not (isSuperClass1-invariant fromClass s))
;;       (mv nil (fatalError "loaded Class desc not found in the env" s))

;;   (if (mem fromClass seen)
;;       (mv nil s)
;;     (if (equal fromClass toClass) 
;;         (mv t s)
;;       (if (equal fromClass "java.lang.Object")
;;           (mv nil s)
;;         (if (class-loaded? fromClass s)
;;             (isSuperClass1 (super (class-by-name fromClass 
;;                                                  (instance-class-table s)))
;;                            toClass  s (cons fromClass seen))
;;           (let ((new-s (load_class fromClass s)))
;;             (if (not (no-fatal-error? new-s))
;;                 (mv nil new-s)
;;               (isSuperClass1 (super (class-by-name fromClass 
;;                                                    (instance-class-table new-s)))
;;                              toClass new-s  (cons fromClass seen))))))))))
                                                  



(defun isSuperClass (fromClass toClass s)
  (isSuperClass1 fromClass toClass s nil))


(defthm s-not-changed-isSuperClass1
  (equal (mv-nth 1 (isSuperClass1 from to s seen))  s))

;; call this method with no array classes.
;; no termination proof yet.


(defun unseen-class-count (seen s)
  (let ((cl (env-class-table (env s))))
    (+ 1 (len (set-diff (all-class-names-s cl) seen)))))


(defun classImplements-measure (stage seen s)
  (cons (cons (unseen-class-count seen s) 0) stage))
        


(defun classImplementsInterface1-invariant (from s)
  (implies (class-loaded? from s)
           (class-exists-externally? from (env-class-table (env s)))))

(defun classImplementsInterface1-aux-invariant (thisClass seen s)
  (and (class-loaded? thisClass s)
       (not (mem thisClass seen))
       (class-exists-externally? thisClass (env-class-table (env s)))))


(defun interfacesImplementsInterface1-inv (s1 s2)
  (equal (env s1) (env s2)))

(defun simple-inv1 (s1 s2)
  (equal (env s1) (env s2)))


;; have to manually insert those invariants into the body of functions later we
;; will prove this invariants are actually true for all reachable state.

;; make it easier by adding a new parameter 'seen'

(defun implementInterface-x-measure (p s seen mode)
  (let ((interfaces p))
    (cond ((equal mode 0) 
           (classImplements-measure 0 seen s))
          ((equal mode 1)
           (classImplements-measure 1 seen s))
          ((equal mode 2)
           (classImplements-measure (+ 3 (len Interfaces)) seen s))
          (t 0))))
           


(in-theory (disable interfaces super))

(defun all-loaded?-x (names s)
  (if (not (consp names))
      t
    (and (class-loaded? (car names) s)
         (all-loaded?-x (cdr names) s))))

(defun implementInterface-x-guard (p s mode)
  (and (loader-inv s)
       (let ((interfaces p))
         (cond ((equal mode 0)
                (class-loaded? p s))
               ((equal mode 1)
                (class-loaded? p s))
               ((equal mode 2)
                (all-loaded?-x interfaces s))
               (t nil)))))


;(i-amhere)

(defun implementInterface-x (p thisInterface s seen mode)
  (declare (xargs :measure (implementInterface-x-measure p s seen mode)
                  :guard (implementInterface-x-guard p s mode)))
  (cond ((equal mode 0) ;; classImplementsInterface1-aux
         (if (not (no-fatal-error? s))
             (mv nil s)
           (let ((thisClass p)
                 (new-s     s))
             (if (not (classImplementsInterface1-aux-invariant thisClass seen new-s))
                 (mv nil s)
               (let* ((class-rep (class-by-name thisClass 
                                                (instance-class-table
                                                 new-s)))
                      (superclass (super class-rep))
                      (interfaces (interfaces class-rep)))
                 (if (mem thisInterface interfaces)
                     (mv t new-s)
                   (mv-let (assignable new-s2) ;; interfacesImplementInterface1
                           (implementInterface-x interfaces thisInterface
                                                 new-s (cons thisClass seen) 2)
                             
                           (if (not (simple-inv1 new-s2 new-s))
                               (mv nil s)
                             (if (not (no-fatal-error? new-s2))
                                 (mv nil new-s2)
                               (if assignable 
                                   (mv t new-s2)
                                 (mv-let (assignable new-s3)
                                         (implementInterface-x ;; classImplementInterface1
                                          superclass thisInterface new-s2 (cons thisClass seen) 1)
                                         (if (not (simple-inv1 new-s3 new-s))
                                             (mv nil new-s3)
                                           (if (not (no-fatal-error? new-s3))
                                               (mv nil new-s3)
                                             (if assignable
                                                 (mv t new-s3)
                                               (mv nil new-s3)))))))))))))))
        ((equal mode 1)
         (if (not (no-fatal-error? s))
             (mv nil s)
           (if (not (class-loaded? thisInterface s)) ;; Sun Nov  7 20:55:08 2004
               (mv nil s)  ;; Sun Nov  7 20:55:11 2004
             (let ((thisClass p))
               (if (not (classImplementsInterface1-invariant thisClass s))
                   (mv nil s)

                 (if (mem thisClass seen)
                     (mv nil s)

                   (if (equal thisClass thisInterface)
                       (mv t s)
                     (if (not (class-loaded? thisClass s))
                         (mv nil s) ;; impossible. 
                       ;; 
                       ;; Sun Nov  7 20:54:00 2004
                       ;; Shall we assert that To must be loaded?? 
                       ;; 
                       ;;
                       ;;                      (let ((new-s (load_class thisClass s)))
                       ;;                        (if (not (no-fatal-error? new-s))
                       ;;                            (mv nil new-s) ;; fatal error marker, the caller can converted
                       ;;                          ;; into an exception.
                       ;;                          (implementInterface-x thisClass thisInterface new-s seen 0)))
                       (implementInterface-x thisClass thisInterface s seen 0)))))))))
        ((equal mode 2)
         (if (not (no-fatal-error? s))
             (mv nil s)
           (let ((interfaces p))
             (if (not (consp interfaces))
                 (mv nil s)
               (mv-let (res new-s)
                       (implementInterface-x (car interfaces) thisInterface s seen 1)
                       ;; classImplementsInterface1
             
                       (if (not (no-fatal-error? new-s))
                           (mv nil new-s) ;; return on seen a fatal error
                         (if (not (interfacesImplementsInterface1-inv new-s s))
                             (mv nil new-s)
                           (if res 
                               (mv t new-s)
                             (implementInterface-x (cdr interfaces) thisInterface
                                                   new-s seen 2)))))))))
        (t (mv nil s))))


;; (defun implementInterface-x (p thisInterface s seen mode)
;;   (declare (xargs :measure (implementInterface-x-measure p s seen mode)))
;;   (cond ((equal mode 0) ;; classImplementsInterface1-aux
;;          (let ((thisClass p)
;;                (new-s     s))
;;                (if (not (classImplementsInterface1-aux-invariant thisClass seen new-s))
;;                    (mv nil 
;;                        (fatalError "classImplementsInterface1-aux violate internal inv" new-s))  
;;                  (let* ((class-rep (class-by-name thisClass 
;;                                                   (instance-class-table
;;                                                    new-s)))
;;                         (superclass (super class-rep))
;;                         (interfaces (interfaces class-rep)))
;;                    (if (mem thisInterface interfaces)
;;                        (mv t new-s)
;;                      (mv-let (assignable new-s2) ;; interfacesImplementInterface1
;;                              (implementInterface-x interfaces thisInterface
;;                                                    new-s (cons thisClass seen) 2)
                             
;;                              (if (not (simple-inv1 new-s2 new-s))
;;                                  (mv nil (fatalError "env changed: invariant-violated" new-s2))

;;                                (if (not (no-fatal-error? new-s2))
;;                                    (mv nil new-s2)
;;                                  (if assignable 
;;                                      (mv t new-s2)
;;                                    (mv-let (assignable new-s3)
;;                                            (implementInterface-x ;; classImplementInterface1
;;                                             superclass thisInterface new-s2 (cons thisClass seen) 1)
;;                                 (if (not (simple-inv1 new-s3 new-s))
;;                                     (mv nil (fatalError "env changed: invariant-violated" new-s3))

;;                                   (if (not (no-fatal-error? new-s3))
;;                                       (mv nil new-s3)
;;                                     (if assignable
;;                                         (mv t new-s3)
;;                                       (mv nil new-s3))))))))))))))
;;         ((equal mode 1)
;;          (let ((thisClass p))
;;            (if (not (classImplementsInterface1-invariant thisClass s))
;;                (mv nil (fatalError "loaded Class desc not found in the env" s))

;;              (if (mem thisClass seen)
;;                  (mv nil s)
     
;;                (if (equal thisClass thisInterface)
;;                    (mv t s)
;;                  (if (not (class-loaded? thisClass s))
;;                      (let ((new-s (load_class thisClass s)))
;;                        (if (not (no-fatal-error? new-s))
;;                            (mv nil new-s) ;; fatal error marker, the caller can converted
;;                          ;; into an exception.
;;                          (implementInterface-x thisClass thisInterface new-s seen 0)))
;;                    (implementInterface-x thisClass thisInterface s seen 0)))))))
;;         ((equal mode 2)
;;          (let ((interfaces p))
;;            (if (endp interfaces)
;;                (mv nil s)
;;              (mv-let (res new-s)
;;                      (implementInterface-x (car interfaces) thisInterface s seen 1)
;;                      ;; classImplementsInterface1
             
;;              (if (not (no-fatal-error? new-s))
;;                  (mv nil new-s)  ;; return on seen a fatal error
               
;;                (if (not (interfacesImplementsInterface1-inv new-s s))
;;                    (mv nil 
;;                        (fatalError "interfacesImplementsInterface1 violate inv" new-s)) 
;;                  (if res 
;;                      (mv t new-s)
;;                    (implementInterface-x (cdr interfaces) thisInterface
;;                                          new-s seen 2))))))))
;;         (t (mv nil s))))


(defun interfacesImplementsInterface (interfaces thisInterface s)
  (implementInterface-x interfaces thisInterface s nil 2))

(defun classImplementsInterface (thisClass thisInterface s)
  (implementInterface-x thisClass thisInterface s nil 1))




;; in our implementation of loader, if an array class is loaded, then its base
;; class must have been loaded, so we don't need to worry about testing whether
;; a class is loaded or not.

;; assuming this java.lang.Clone, java.lang.Serializeable are interfaces.
;; assuming array only implement those two interfaces. 


;; (defthm no-fatal-error?-implies-state-no-change-lemma
;;   (implies (no-fatal-error? (mv-nth 1 (implementinterface-x any1 any2 s seen mode))) 
;;            (equal (mv-nth 1 (implementinterface-x any1 any2 s seen mode))
;;                   s)))



(defthm state-no-change-lemma
  (equal (mv-nth 1 (implementinterface-x any1 any2 s seen mode)) s))
         


;; (defthm no-fatal-error?-implies-state-no-change
;;   (implies (no-fatal-error? (mv-nth 1 (classImplementsInterface any1 any2 s)))
;;            (equal (mv-nth 1 (classImplementsInterface any1 any2 s)) s)))

(defun isAssignableTo (fromClass toClass s)
  (cond ((equal fromClass toClass) (mv t s))
        ((primitive-type? fromClass) (mv nil s))
        ;;
        ;; Mon Oct 25 12:16:54 2004; 
        ;; 
        ((equal toClass  "java.lang.Object") (mv t s))
        ((array-type? toClass) 
         (cond ((array-type? fromClass)
                (cond ((primitive-array? fromClass)
                       (mv (equal (array-base-type fromClass) 
                                  (array-base-type toClass))
                           s))
                      ((primitive-array? toClass) (mv nil s))
                      (t (isAssignableTo (array-base-type fromClass)
                                         (array-base-type toClass) 
                                         s))))
               (t (mv nil s))))
        ((isInterface (class-by-name toClass (instance-class-table s)))
         (cond ((array-type? fromClass) ;; 
                (mv (mem toClass *array-implemented-interfaces*)
                    s))
               (t (classImplementsInterface fromClass toClass s))))
        ((array-type? fromClass)  (mv nil s))
        ((isInterface (class-by-name fromClass (instance-class-table s)))
                      (mv nil s))
        (t (isSuperClass fromClass toClass s))))

(defthm state-no-change-isAssignable
  (equal (mv-nth 1 (isAssignableTo any1 any2 s)) s))



;; (in-theory (enable fatalError))



;; (defthm implementinterface-x-no-fatal-Error
;;   (implies (no-fatal-error? (mv-nth 1 (implementinterface-x p interfaces s seen
;;                                                             mode)))
;;            (equal (mv-nth 1 (implementinterface-x p interfaces s seen mode))
;;                   s)))



;; (defthm  isImplementationof-changes-only-error-flag-lemma
;;   (mv-let (assignable s1)
;;           (implementInterface-x t1 t2 s0 seen mode)
;;           (declare (ignore assignable))
;;           (and    (equal (pc s1) (pc s0))
;;                   (equal (current-thread s1) (current-thread s0))
;;                   (equal (thread-table   s1) (thread-table s0))
;;                   (equal (env            s1) (env s0))
;;                   (equal (aux            s1) (aux s0))
;;                   (equal (heap           s1) (heap s0))
;;                   (equal (class-table    s1) (class-table s0))))
;;   :hints (("Goal" :in-theory (disable aux))))


;; (defthm  isImplementationof-changes-only-error-flag
;;   (mv-let (assignable s1)
;;           (implementInterface-x t1 t2 s0 seen mode)
;;           (declare (ignore assignable))
;;           (and    (equal (pc s1) (pc s0))
;;                   (equal (current-thread s1) (current-thread s0))
;;                   (equal (thread-table   s1) (thread-table s0))
;;                   (equal (env            s1) (env s0))
;;                   (equal (aux            s1) (aux s0))
;;                   (equal (heap           s1) (heap s0))
;;                   (equal (class-table    s1) (class-table s0))
;;                   (equal (instance-class-table s1) 
;;                          (instance-class-table s0))
;;                   (equal (array-class-table s1)
;;                          (array-class-table s0))))
;;   :hints (("Goal" :in-theory (enable instance-class-table array-class-table))))




;; (in-theory (disable fatalError))

;; ;; (defthm  implementInterface-x-only-change-class-table-error-flag-heap
;; ;;   (implies (or (equal mode 0)
;; ;;                (equal mode 1)
;; ;;                (equal mode 2))
;; ;;            (and  (mv-let (assignable s1)
;; ;;                          (implementInterface-x t1 t2 s0 seen mode)
;; ;;                          (declare (ignore assignable))
;; ;;                          (and    (equal (pc s1) (pc s0))
;; ;;                                  (equal (current-thread s1) (current-thread s0))
;; ;;                                  (equal (thread-table   s1) (thread-table s0))
;; ;;                                  (equal (env            s1) (env s0)))))))

;; (in-theory (disable implementInterface-x))

;; (defthm isAssignableTo-no-fatal-Error
;;   (implies (no-fatal-error? (mv-nth 1 (isAssignableTo any1 any2 s)))
;;            (equal (mv-nth 1 (isAssignableTo any1 any2 s)) s)))



;; (defthm  isAssignableTo-changes-only-error-flag-lemma
;;   (mv-let (assignable s1)
;;           (isAssignableTo any1 any2 s0)
;;           (declare (ignore assignable))
;;           (and    (equal (pc s1) (pc s0))
;;                   (equal (current-thread s1) (current-thread s0))
;;                   (equal (thread-table   s1) (thread-table s0))
;;                   (equal (env            s1) (env s0))
;;                   (equal (aux            s1) (aux s0))
;;                   (equal (heap           s1) (heap s0))
;;                   (equal (class-table    s1) (class-table s0))))
;;   :hints (("Goal" :in-theory (e/d (isAssignableTo) (aux)))))

    

;; (defthm  isAssignableTo-changes-only-error-flag
;;   (mv-let (assignable s1)
;;           (isAssignableTo any1 any2 s0)
;;           (declare (ignore assignable))
;;           (and    (equal (pc s1) (pc s0))
;;                   (equal (current-thread s1) (current-thread s0))
;;                   (equal (thread-table   s1) (thread-table s0))
;;                   (equal (env            s1) (env s0))
;;                   (equal (aux            s1) (aux s0))
;;                   (equal (heap           s1) (heap s0))
;;                   (equal (class-table    s1) (class-table s0))
;;                   (equal (instance-class-table s1) 
;;                          (instance-class-table s0))
;;                   (equal (array-class-table s1)
;;                          (array-class-table s0))))
;;   :hints (("Goal" :in-theory (enable instance-class-table array-class-table))))
