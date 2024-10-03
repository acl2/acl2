(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-loader")

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(acl2::set-verify-guards-eagerness 0)
(in-theory (enable no-fatal-error?))

(defun all-interfaces-are-loaded? (interfaces cl env-cl)
  (if (endp interfaces)
      t
    (and (correctly-loaded? (car interfaces) cl env-cl)
         (all-interfaces-are-loaded? (cdr interfaces) cl env-cl))))



(defun load-class-x-3-pre (s)
  (or (not (no-fatal-error? s))
      (loader-inv-helper (instance-class-table s)
                         (instance-class-table s)
                         (external-class-table s))))


(defun load-class-x-3-post (classname s)
  (or (not (no-fatal-error? s))
      (and (loader-inv-helper (instance-class-table s)
                              (instance-class-table s)
                              (external-class-table s))
           (correctly-loaded? classname (instance-class-table s)
                              (external-class-table s)))))

  


(defun load-class-x-2-pre (classname s)
  (and (load-class-x-3-pre s)
       (no-fatal-error? s)
       (not (class-loaded? classname s))
       (mv-let (def-found class-desc)
               (class-by-name-s classname (external-class-table s))
               (declare (ignore class-desc))
               def-found)))



(defun load-class-x-2-post (classname s)
  (or  (not (no-fatal-error? s))
       (mv-let (def-found class-desc)
               (class-by-name-s classname (external-class-table s))
               (declare (ignore def-found))
               (let ((super (super-s class-desc)))
                 (and (correctly-loaded? super (instance-class-table s)
                                         (external-class-table s))
                      (loader-inv-helper (instance-class-table s)
                                         (instance-class-table s)
                                         (external-class-table s)))))))
                   


(defun load-class-x-1-pre (classname s)
  (and (no-fatal-error? s)
       (loader-inv-helper (instance-class-table s)
                          (instance-class-table s)
                          (external-class-table s))
       (mv-let (def-found class-desc)
               (class-by-name-s classname (external-class-table s))
               (declare (ignore class-desc))
               def-found)))


(defun load-class-x-1-post (classname s)
  (or (not (no-fatal-error? s))
      (mv-let (def-found class-desc)
              (class-by-name-s classname (external-class-table s))
              (declare (ignore def-found))
              (let ((interfaces (interfaces-s class-desc)))
                 (and (all-correctly-loaded? interfaces (instance-class-table s)
                                             (external-class-table s))
                      (loader-inv-helper (instance-class-table s)
                                         (instance-class-table s)
                                         (external-class-table s)))))))


(defun load-class-x-0-pre (s)
  (or (not (no-fatal-error? s))
      (loader-inv-helper  (instance-class-table s)
                          (instance-class-table s)
                          (external-class-table s))))


(defun load-class-x-0-post(interfaces s)
  (or (not (no-fatal-error? s)) 
      (and (loader-inv-helper  (instance-class-table s)
                               (instance-class-table s)
                               (external-class-table s))
           (all-correctly-loaded? interfaces 
                                  (instance-class-table s)
                                  (env-class-table (env s))))))


(defun load-class-x-pre (classname s mode)
  (cond ((equal mode 3)
         (load-class-x-3-pre s))
        ((equal mode 2)
         (load-class-x-2-pre classname s))
        ((equal mode 1)
         (load-class-x-1-pre classname s))
        ((equal mode 0)
         (load-class-x-0-pre s))
        (t nil)))



(defun load-class-x-post (p s mode)
  (cond ((equal mode 3)
         (load-class-x-3-post p s))
        ((equal mode 2)
         (load-class-x-2-post p s))
        ((equal mode 1)
         (load-class-x-1-post p s))
        ((equal mode 0)
         (load-class-x-0-post p s))
        (t t)))




(in-theory (disable interfaces-s super-s correctly-loaded?))


(defthm env-does-not-change-load_class_x
  (let ((new-s (load_class_x any s seen mode)))
    (equal (env new-s)
           (env s)))
  :hints (("Goal" :in-theory (enable env fatalError make-state load_class2))))


(defthm instance-class-table-make-class-table-x
  (equal (instance-class-table (make-state pc th hp tt 
                                           (make-class-table icl
                                                             acl)
                                           env
                                           err
                                           aux))
         icl)
  :hints (("Goal" :in-theory (enable instance-class-table make-class-table))))



(defthm correctly-loaded?-add-instance-class-entry
  (implies (and (correctly-loaded? classname cl env-cl)
                (not (equal (classname new-class-rep) classname)))
           (correctly-loaded? classname (add-instance-class-entry new-class-rep cl)
                              env-cl))
  :hints (("Goal" :in-theory (enable correctly-loaded? class-by-name
                                     add-instance-class-entry))))


(defthm class-by-name-cons
  (implies (equal (classname new-class-rep) classname)
           (equal (class-by-name classname (cons new-class-rep cl))
                  new-class-rep)))
                        


(defthm correctly-loaded?-add-instance-class-entry-2
  (mv-let (def-found class-desc)
          (class-by-name-s classname env-cl)
          (implies (and (correctly-loaded? classname cl env-cl)
                        (class-is-loaded-from new-class-rep class-desc)
                        (equal (classname new-class-rep) classname)
                        (isClassTerm new-class-rep)
                        def-found)
                   (correctly-loaded? classname 
                                      (add-instance-class-entry new-class-rep cl)
                                      env-cl)))
  :hints (("Goal" :in-theory (enable correctly-loaded? class-by-name
                                     add-instance-class-entry))))



(in-theory (disable make-class-table add-instance-class-entry))


;; (defthm instance-class-table-make-state-
;;   (equal (instance-class-table (make-state pc th hp tt
;;                                            (class-table s)
;;                                            env 
;;                                            err 
;;                                            aux))
;;          (instance-class-table s))
;;   :hints (("Goal" :in-theory (enable instance-class-table))))
;;
;; also defined in jvm-loader2.lisp

(defthm instance-class-table-make-state-2
  (equal (instance-class-table (make-state pc th hp tt
                                           (class-table s)
                                           env 
                                           err 
                                           aux))
         (instance-class-table s))
  :hints (("Goal" :in-theory (enable instance-class-table))))


(defthm class-by-name-s-found-implies-equal-class-name
  (mv-let (def-found class-desc)
          (class-by-name-s classname env-cl)
          (implies def-found
                   (equal (classname-s class-desc)
                          classname))))


(in-theory (enable make-runtime-class-rep))

(in-theory (disable add-instance-class-entry))


(defthm correctly-loaded?-load_class2
  (let ((new-s (load_class2 any s)))
    (implies (correctly-loaded? classname (instance-class-table s)
                                (env-class-table (env s)))
             (correctly-loaded? classname (instance-class-table new-s)
                                (env-class-table (env s)))))
  :hints (("Goal" :in-theory (enable load_class2 super interfaces fatalError)
           :do-not '(generalize)
           :cases ((equal classname any)))))


(defthm correctly-loaded?-implies-always-correctly-loaded
  (let ((new-s (load_class_x any s seen mode)))
    (implies (correctly-loaded? classname (instance-class-table s)
                                (env-class-table (env s)))
             (correctly-loaded? classname (instance-class-table new-s)
                                (env-class-table (env new-s)))))
  :hints (("Goal"  :in-theory (enable fatalError)
           :do-not '(generalize))
          ("Subgoal *1/7" :use ((:instance correctly-loaded?-load_class2
                                           (s (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SEEN 2)
                                                            SEEN 1)))))))
                                   
;;; if originally loaded, still loaded!!


(defthm loader-inv-helper1-implies-correctly-loaded?-2
  (implies (and (loader-inv-helper1 class-rep cl env-cl)
                (equal (classname class-rep) classname))
           (correctly-loaded? classname  cl env-cl))
  :rule-classes nil)


(defthm loader-inv-helper-and-loaded-implies-correctly-loaded?-2
  (implies (and (loader-inv-helper classes cl env-cl)
                (class-by-name classname classes))
           (loader-inv-helper1 (class-by-name classname classes) cl env-cl)))



(in-theory (disable classname loader-inv-helper1))

(defthm class-loaded?-implies-classname-class-by-name
  (implies (isClassTerm (class-by-name classname cl))
           (equal (classname (class-by-name classname cl))
                  classname))
  :hints (("Goal" :in-theory (enable class-by-name isClassTerm classname))))
                                     
           


;; for subgoal 16.
(defthm loaded-lorder-inv-helper-implies-correctly-loaded?
  (implies (and (class-loaded? classname s)
                (loader-inv-helper (instance-class-table s)
                                   (instance-class-table s)
                                   (env-class-table (env s))))
           (correctly-loaded? classname (instance-class-table s)
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable class-loaded?)
            :use ((:instance loader-inv-helper1-implies-correctly-loaded?-2
                                   (class-rep 
                                    (class-by-name classname
                                                   (instance-class-table s)))
                                   (cl (instance-class-table s))
                                   (env-cl (env-class-table (env s))))))))
           

(defthm load_class2_no-fatal-error?-class-table
  (implies (no-fatal-error? (load_class2 classname s))
           (equal (cdr (instance-class-table (load_class2 classname s)))
                  (instance-class-table s)))
  :hints (("Goal" :in-theory (enable load_class2 fatalError
                                     add-instance-class-entry))))


(defthm load_class2_no-fatal-error?-correctly-loaded?
  (implies (no-fatal-error? (load_class2 classname s))
           (correctly-loaded? classname 
                              (instance-class-table
                               (load_class2 classname s))
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable load_class2 correctly-loaded?
                                     add-instance-class-entry
                                     classname fatalError
                                     interfaces
                                     super))))

;; this is the one that we need to verify-guard of load_class_x 

;; Thu Apr  1 22:36:42 2004

;; (verify-guards load_class_x 
;;                :hints (("Goal" :in-theory (e/d (fatalError class-loaded?)
;;                                                (load_class2
;;                                                 fields
;;                                                 class-table
;;                                                 load_class2_guard-strong
;;                                                 load-class-x-guard-strong
;;                                                 load_cp_entry
;;                                                 wff-class-rep
;;                                                 wff-env
;;                                                 wff-class-table
;;                                                 load_class2_guard))
;;                        :do-not '(generalize)
;;                        :do-not-induct t)))




(defthm correctly-loaded?-cons-class-rep
  (mv-let (def-found class-desc)
          (class-by-name-s (classname class-rep) env-cl)
          (declare (ignore def-found))
          (implies (and (correctly-loaded? classname cl env-cl)
                        (isClassTerm class-rep)
                        (class-is-loaded-from class-rep class-desc))
                   (correctly-loaded? classname (cons class-rep cl) env-cl)))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))



(defthm all-correctly-loaded?-cons-class-rep
  (mv-let (def-found class-desc)
          (class-by-name-s (classname class-rep) env-cl)
          (declare (ignore def-found))
          (implies (and (all-correctly-loaded? classnames cl env-cl)
                        (isClassTerm class-rep)
                        (class-is-loaded-from class-rep class-desc))
                   (all-correctly-loaded? classnames (cons class-rep cl)
                                          env-cl)))
  :hints (("Goal" :in-theory (disable isClassTerm class-by-name-s
                                      class-is-loaded-from))))
                        

(defthm loader-inv-helper1-loader-inv-helper1
  (mv-let (def-found class-desc)
          (class-by-name-s (classname class-rep) env-cl)
          (declare (ignore def-found))
          (implies (and (loader-inv-helper1 class cl env-cl)
                        (isClassTerm class-rep)
                        (class-is-loaded-from class-rep class-desc))
                   (loader-inv-helper1 class (cons class-rep cl) env-cl)))
    :hints (("Goal" :in-theory (cons 'loader-inv-helper1
                                     (disable isClassTerm class-by-name-s
                                              class-is-loaded-from)))))

(defthm loader-inv-helper-loader-inv-helper
  (mv-let (def-found class-desc)
          (class-by-name-s (classname class-rep) env-cl)
          (declare (ignore def-found))
          (implies (and (loader-inv-helper classes cl env-cl)
                        (isClassTerm class-rep)
                        (class-is-loaded-from class-rep class-desc))
                   (loader-inv-helper classes (cons class-rep cl) env-cl)))
    :hints (("Goal" :in-theory (disable isClassTerm class-by-name-s
                                        class-is-loaded-from))))



(defthm found-implies-classname-s-equal
  (mv-let (def-found class-desc)
          (class-by-name-s classname env-cl)
          (implies def-found
                   (equal (classname-s class-desc)
                          classname))))



(defthm loader-inv-helper1-car-load_class2-lemma-1
  (mv-let (def-found class-desc)
          (class-by-name-s (classname class-rep) env-cl)
          (implies (and def-found
                        (isClassTerm class-rep)
                        (class-is-loaded-from class-rep class-desc))
                   (correctly-loaded? (classname class-rep) 
                                      (cons class-rep cl)
                                      env-cl)))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))

; (acl2::set-match-free-error nil)

(defthm correctly-loaded?-classname-class-by-name
  (implies (correctly-loaded? classname cl env-cl)
           (equal (classname (class-by-name classname cl))
                  classname))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))


(defthm loader-inv-helper1-correct-loaded?
  (implies (and (loader-inv-helper1 (class-by-name super cl) cl env-cl)
                (correctly-loaded?  super cl env-cl))
           (all-correctly-loaded? (collect-assignableToName super env-cl)
                                  cl env-cl))
  :hints (("Goal" :in-theory (enable loader-inv-helper1))))


(defun collect-all-assignableToName (interfaces env-cl)
  (if (endp interfaces)
      nil
    (app (collect-assignableToName (car interfaces) env-cl)
         (collect-all-assignableToName (cdr interfaces) env-cl))))

(defthm all-correctly-loaded?-app
  (implies (and (all-correctly-loaded? l1 cl env-cl)
                (all-correctly-loaded? l2 cl env-cl))
           (all-correctly-loaded? (app l1 l2) cl env-cl)))


(defthm loader-inv-helper-correct-loaded?-implies-loader-inv-helper1
  (implies (and (loader-inv-helper cl cl env-cl)
                (correctly-loaded? classname cl env-cl))
           (loader-inv-helper1 (class-by-name classname cl) cl env-cl))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))


(defthm loader-inv-helper-all-correct-loaded?
  (implies (and (loader-inv-helper cl cl env-cl)
                (all-correctly-loaded? interfaces cl env-cl))
           (all-correctly-loaded? 
            (collect-all-assignableToName interfaces env-cl) cl env-cl))
  :hints (("Goal" :in-theory (disable collect-assignableToName)
           :do-not '(generalize))))






(defthm subset-collect-1
  (mv-let (def-found class-desc)
          (class-by-name-s classname env-cl)
          (declare (ignore def-found))
  (subset  (collect-superclassname1 classname env-cl seen)
           (cons classname (collect-superclassname1 (super-s class-desc) env-cl
                                                    (cons classname seen))))))

(defun collect-x (n-or-ns env-cl mode)
  (let ((n n-or-ns)
        (ns n-or-ns))
  (cond ((equal mode 1) 
         (collect-assignableToName n env-cl))
        ((equal mode 2)
         (collect-all-assignableToName ns env-cl))
        (t nil))))
        
(defthm subset-app
  (implies (and (subset a b)
                (subset c b))
           (subset (app a c) b))
  :hints (("Goal" :do-not '(generalize))))


(defthm subset-app-2
  (implies (subset a b)
           (subset a (app b d)))
  :hints (("Goal" :do-not '(generalize))))

(defthm subset-app-2-1
  (implies (subset c d)
           (subset c (app b d)))
  :hints (("Goal" :do-not '(generalize))))


(defthm subset-app-3
  (implies (and (subset a b)
                (subset c d))
           (subset (app a c) (app b d)))
  :hints (("Goal"  :in-theory (disable subset-app-2
                                       subset-app-2-1)
           :use ((:instance subset-app-2)
                 (:instance subset-app-2-1)))))

(defthm subset-app-4
  (implies (subset s1 s2)
           (subset (app x s1) (cons y (app x s2)))))

(defthm subset-cons
  (implies (subset s1 s2)
           (subset s1 (cons x s2))))



(defun collect-super-induct (n env-cl seen1 seen2)
  (declare (xargs :measure  (COLLECT-SUPERCLASSNAME1-MEASURE ENV-CL SEEN1)))
  (mv-let (def-found class-desc)
          (class-by-name-s n env-cl)
          (if def-found
              (cond ((mem n seen1)
                     (list n env-cl seen1 seen2))
                    (t (collect-super-induct (super-s class-desc) 
                                             env-cl 
                                             (cons n seen1)
                                             (cons n seen2))))
            nil)))


(defthm collect-superclassname1-seen
   (implies (subset seen2 seen1)
            (subset (collect-superclassname1 n env-cl seen1)
                    (collect-superclassname1 n env-cl seen2)))
   :hints (("Goal" :induct (collect-super-induct n env-cl seen1 seen2))))

(defun collect-superinterface-induct (n-or-ns env-cl seen1 seen2 mode)
   (DECLARE (XARGS :MEASURE  (COLLECT-INTERFACE-X-ENV-MEASUSRE
                              N-OR-NS ENV-CL SEEN1 MODE)))
   (let ((n1 n-or-ns) 
         (ns n-or-ns))
    (cond ((equal mode 1)
           (mv-let (found class-desc)
                   (class-by-name-s n1 env-cl)
                   (let ((interfaces (interfaces-s class-desc))
                         (super      (super-s class-desc)))
                     (if (not found) 
                         (list n-or-ns env-cl seen1 seen2 mode)
                       (if (mem n1 seen1)
                           nil
                         (list (collect-superinterface-induct 
                                super env-cl (cons n1 seen1) (cons n1 seen2) 1)
                               (collect-superinterface-induct 
                                interfaces env-cl (cons n1 seen1) 
                                (cons n1 seen2) 2)))))))
          ((equal mode 2)
           (if (endp ns)
               nil
             (list (collect-superinterface-induct (car ns) env-cl seen1 seen2
                                                  1)
                   (collect-superinterface-induct (cdr ns) env-cl seen1 seen2
                                                  2))))
          (t nil))))
                                                  
                               

(defthm collect-interface-x-env-seen
  (implies (subset seen2 seen1)
           (subset (collect-interface-x-env n-or-ns env-cl seen1 mode)
                   (collect-interface-x-env n-or-ns env-cl seen2  mode)))
  :hints (("Goal" :induct (collect-superinterface-induct n-or-ns env-cl seen1
                                                         seen2 mode))))
                                     











(defthm subset-collect-2
  (subset  (collect-interface-x-env n-or-ns env-cl seen mode)
           (collect-x n-or-ns env-cl mode)))


(defthm subset-collect-3
  (subset (COLLECT-INTERFACE-X-ENV super ENV-CL
                                           (CONS classname SEEN) 1)
          (collect-assignableToName super
                                    env-cl)))


(defthm subset-collect-4
  (subset (COLLECT-INTERFACE-X-ENV interfaces ENV-CL
                                   (CONS classname SEEN) 2)
          (collect-all-assignableToName interfaces env-cl)))

(defthm collect-assignableToName-implies-mem-n
  (mem n (collect-assignableToName n env-cl)))

(defthm collect-all-assignableToName-implies-subset
  (subset interfaces (collect-all-assignableToName interfaces env-cl)))


(defthm subset-collect-5 
  (subset (APP
           (CONS N1 INTERFACES)
           (APP
            (COLLECT-INTERFACE-X-ENV SUPER ENV-CL (CONS N1 SEEN)
                                     1)
            (COLLECT-INTERFACE-X-ENV
             INTERFACES ENV-CL (CONS N1 SEEN)
             2)))
          (cons n1 (app (collect-assignableToName super env-cl)
                        (collect-all-assignableToName interfaces env-cl))))
  :hints (("Goal" :in-theory (disable collect-all-assignableToName
                                      collect-assignableToName))))



                               
(defthm subset-collect-6
  (mv-let (def-found class-desc)
          (class-by-name-s classname env-cl)
          (declare (ignore def-found))
          (let ((super (super-s class-desc))
                (interfaces (interfaces-s class-desc)))
            (subset (collect-superinterface classname env-cl)
                    (cons classname 
                          (app (collect-assignableToName super env-cl)
                               (collect-all-assignableToName interfaces
                                                             env-cl))))))
  :hints (("Goal" :in-theory (disable collect-assignableToName
                                      collect-all-assignableToName)
           :expand (COLLECT-INTERFACE-X-ENV CLASSNAME ENV-CL NIL 1)
           :do-not-induct t)))



(defthm subset-collect-7
  (mv-let (def-found class-desc)
          (class-by-name-s classname env-cl)
          (declare (ignore def-found))
          (let ((super (super-s class-desc))
                (interfaces (interfaces-s class-desc)))
            (subset (collect-superclassname classname env-cl)
                    (cons classname 
                          (app (collect-assignableToName super env-cl)
                               (collect-all-assignableToName interfaces
                                                             env-cl))))))
  :hints (("Goal" :in-theory (disable  collect-all-assignableToName collect-superinterface)
           :expand   (COLLECT-SUPERCLASSNAME1 CLASSNAME ENV-CL NIL))))


(defthm subset-collect
  (mv-let (def-found class-desc)
          (class-by-name-s classname env-cl)
          (declare (ignore def-found))
          (let ((super (super-s class-desc))
                (interfaces (interfaces-s class-desc)))
            (subset (collect-assignableToName classname env-cl)
                    (cons classname 
                          (app (collect-assignableToName super env-cl)
                               (collect-all-assignableToName interfaces
                                                             env-cl))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable collect-all-assignableToName
                               collect-superclassname
                               collect-superinterface
                               collect-assignableToName)
           :expand (collect-assignableToName classname env-cl))))




(defthm all-correctly-loaded?-subset
  (implies (and (subset s1 s2)
                (all-correctly-loaded? s2 cl env-cl))
           (all-correctly-loaded? s1 cl env-cl)))

;(i-am-here)

; (defthm |Goal'8'-lemma-2|
;   (mv-let (def-found class-desc)
;           (class-by-name-s (classname class-rep) env-cl)
;           (declare (ignore def-found))
;           (implies (and (isClassTerm class-rep)
;                         (class-is-loaded-from class-rep class-desc)
;                         (CORRECTLY-LOADED? (SUPER-s class-desc)
;                                            CL ENV-CL)
;                         (ALL-CORRECTLY-LOADED? (INTERFACES-s class-desc)
;                                                CL ENV-CL)
;                         (LOADER-INV-HELPER CL CL ENV-CL))
;                    (ALL-CORRECTLY-LOADED?
;                     (cons (classname class-rep)
;                           (app (collect-assignableToName (super-s class-desc) env-cl)
;                                (collect-all-assignableToName (interfaces-s class-desc) env-cl)))
;                    (cons class-rep CL)  ENV-CL)))
;           :hints (("Goal" 
;                    :do-not '(generalize)
;                    :in-theory (cons 'correctly-loaded? 
;                                            (disable collect-assignabletoname
;                                               isClassTerm class-is-loaded-from
;                                               loader-inv-helper)))))




(defthm all-correctly-loaded?-implies-all-correctly-loaded?
    (mv-let (def-found class-desc)
          (class-by-name-s (classname class-rep) env-cl)
          (declare (ignore def-found))
          (implies (all-correctly-loaded? 
                    (cons (classname class-rep)
                          (app (collect-assignableToName (super-s class-desc) env-cl)
                               (collect-all-assignableToName 
                                (interfaces-s class-desc) env-cl)))
                      cl env-cl)
                   (all-correctly-loaded?
                    (collect-assignableToName (classname class-rep) env-cl)
                    cl env-cl)))
    :hints (("Goal" :in-theory (disable all-correctly-loaded? 
                                        collect-assignableToName
                                        collect-all-assignableToName)
             :use ((:instance all-correctly-loaded?-subset
                              (s1 (collect-assignableToName 
                                   (classname class-rep) env-cl))
                              (s2 (mv-let (def-found class-desc)
                                          (class-by-name-s (classname class-rep) env-cl)
                                          (declare (ignore def-found))
                                           (cons (classname class-rep)
                                                 (app (collect-assignableToName (super-s class-desc) env-cl)
                                                      (collect-all-assignableToName 
                                                       (interfaces-s class-desc) env-cl))))))))))



(defthm loader-inv-helper1-car-load_class2-lemma-2
  (mv-let (def-found class-desc)
          (class-by-name-s (classname class-rep) env-cl)
          (implies (and (correctly-loaded? (super-s class-desc) cl env-cl)
                        (all-correctly-loaded? (interfaces-s class-desc) cl env-cl)
                        (loader-inv-helper cl cl env-cl)
                        (no-fatal-error? s)
                        (isClassTerm class-rep)
                        (class-is-loaded-from class-rep class-desc)
                        def-found)
                   (loader-inv-helper1 class-rep (cons class-rep cl) env-cl)))
  :hints (("Goal" :in-theory (cons 'loader-inv-helper1 (disable classname-s 
                                                                isClassTerm class-is-loaded-from
                                                                collect-assignableToName))
           :do-not-induct t)))


(defthm loader-inv-helper1-cons-load_class2
  (mv-let (def-found class-desc)
          (class-by-name-s classname (env-class-table (env s)))
          (let ((class-rep (car (instance-class-table (load_class2 classname s)))))
            (and (implies def-found
                          (isClassTerm class-rep))
                 (implies def-found
                          (class-is-loaded-from class-rep class-desc)))))
  :hints (("Goal" :in-theory (enable load_class2 make-class-table
                                     add-instance-class-entry 
                                     instance-class-table
                                     classname classname-s
                                     super super-s
                                     interfaces interfaces-s
                                     class-is-loaded-from))))



(defthm no-fatal-error?-load_class2-implies-found
  (mv-let (def-found class-desc)
          (class-by-name-s classname (env-class-table (env s)))
          (declare (ignore class-desc))
          (implies (no-fatal-error? (load_class2 classname s))
                   def-found))
  :hints (("Goal" :in-theory (enable load_class2 fatalError))))
  


(defthm loader-inv-helper1-cons-load_class2-x
  (mv-let (def-found class-desc)
          (class-by-name-s classname (env-class-table (env s)))
          (declare (ignore def-found))
          (let ((class-rep (car (instance-class-table (load_class2 classname s)))))
            (and (implies (no-fatal-error? (load_class2 classname s))
                          (isClassTerm class-rep))
                 (implies (no-fatal-error? (load_class2 classname s))
                          (class-is-loaded-from class-rep class-desc))))))

(defthm no-fatal-error?-consp
  (implies (no-fatal-error? (load_class2 classname s))
           (consp (instance-class-table (load_class2 classname s))))
  :hints (("Goal" :in-theory (enable load_class2 instance-class-table
                                     make-class-table fatalError
                                     add-instance-class-entry))))

(defthm no-fatal-error?-cons-car-cdr
  (implies (no-fatal-error? (load_class2 classname s))
           (equal (cons (car (instance-class-table (load_class2 classname s)))
                        (instance-class-table s))
                  (instance-class-table (load_class2 classname s))))
  :hints (("Goal" :in-theory (enable load_class2 instance-class-table
                                     make-class-table fatalError
                                     add-instance-class-entry))))



(defthm no-fatal-error?-classname-load_class2
  (implies (no-fatal-error? (load_class2 classname s))
           (equal (CLASSNAME 
                   (CAR (INSTANCE-CLASS-TABLE (LOAD_CLASS2 CLASSNAME S))))
                  classname))
  :hints (("Goal" :in-theory (enable load_class2 classname instance-class-table
                                     fatalError
                                     make-class-table add-instance-class-entry))))


(defthm no-fatal-error?-no-fatal-error?-load_cp_entry
  (mv-let (loaded-cp new-s)
          (load_cp_entry cp s)
          (declare (ignore loaded-cp))
          (equal (error-flag new-s)
                 (error-flag s)))
          :hints (("Goal" :in-theory (enable load_cp_entry))))


(defthm no-fatal-error?-no-fatal-error?-load_cp_entries
  (mv-let (loaded-cps new-s)
          (load_cp_entries entries s)
          (declare (ignore loaded-cps))
          (equal (error-flag new-s)
                 (error-flag s)))
  :hints (("Goal" :in-theory (disable load_cp_entry))))
        

(defthm no-fatal-error?-no-fatal-error?
  (implies (no-fatal-error? (load_class2 classname s))
           (no-fatal-error? s))
  :hints (("Goal" :in-theory (enable load_class2 fatalError))))





(defthm correctly-loaded?-super-interfaces-and-loader-inv-helper-implies-2
   (mv-let (def-found class-desc)
           (class-by-name-s classname (env-class-table (env s)))
           (declare (ignore def-found))
           (let ((super (super-s class-desc))
                 (interfaces (interfaces-s class-desc)))
             (implies (and  (correctly-loaded? super 
                                               (instance-class-table s)
                                               (env-class-table (env s)))
                            (all-correctly-loaded? interfaces
                                                   (instance-class-table s)
                                                   (env-class-table (env s)))
                            (loader-inv-helper (instance-class-table s)
                                               (instance-class-table s)
                                               (env-class-table (env s)))
                            (no-fatal-error? (load_class2 classname s)))
                      (correctly-loaded? classname 
                                         (instance-class-table (load_class2
                                                                classname s))
                                         (env-class-table (env s)))))))



(defthm correctly-loaded?-super-interfaces-and-loader-inv-helper-implies
   (mv-let (def-found class-desc)
           (class-by-name-s classname (env-class-table (env s)))
           (declare (ignore def-found))
           (let ((super (super-s class-desc))
                 (interfaces (interfaces-s class-desc)))
             (implies (and  (no-fatal-error? (load_class2 classname s))
                            (correctly-loaded? super 
                                              (instance-class-table s)
                                              (env-class-table (env s)))
                            (all-correctly-loaded? interfaces
                                                   (instance-class-table s)
                                                   (env-class-table (env s)))
                            (loader-inv-helper (instance-class-table s)
                                               (instance-class-table s)
                                               (env-class-table (env s))))
                      (loader-inv-helper (instance-class-table 
                                          (load_class2 classname s))
                                         (instance-class-table 
                                          (load_class2 classname s))
                                         (env-class-table (env s))))))
   :hints (("Goal" :in-theory (disable no-fatal-error?))
           ("Subgoal 2" :use ((:instance
                               loader-inv-helper1-car-load_class2-lemma-2
                               (class-rep (car (instance-class-table
                                                (load_class2 classname s))))
                               (cl (instance-class-table s))
                               (env-cl (env-class-table (env s))))
                              (:instance no-fatal-error?-load_class2-implies-found)))
           ("Subgoal 1" :use ((:instance loader-inv-helper-loader-inv-helper
                                        (classes (instance-class-table s))
                                        (cl (instance-class-table s))
                                        (class-rep (car (instance-class-table
                                                        (load_class2 classname
                                                                     s))))
                                        (env-cl (env-class-table (env s))))))))



(defthm |Subgoal *1/6.2|
  (IMPLIES
   (mv-let (def-found class-desc)
           (class-by-name-s p (env-class-table (env s)))
           (declare (ignore def-found))
           (AND  (CORRECTLY-LOADED?
                 (SUPER-S class-desc)
                          (INSTANCE-CLASS-TABLE (LOAD_CLASS_X P S SEEN 2))
                          (ENV-CLASS-TABLE (ENV S)))
                 (ALL-CORRECTLY-LOADED?
                  (INTERFACES-S class-desc)
                  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                                      SEEN 1))
                  (ENV-CLASS-TABLE (ENV S)))
                 (LOADER-INV-HELPER
                  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                                      SEEN 1))
                  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                                      SEEN 1))
                  (ENV-CLASS-TABLE (ENV S)))
                 (NO-FATAL-ERROR? (LOAD_CLASS2 P
                                               (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                                             SEEN 1)))))
           (LOADER-INV-HELPER
            (INSTANCE-CLASS-TABLE
             (LOAD_CLASS2 P
                          (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                        SEEN 1)))
            (INSTANCE-CLASS-TABLE
             (LOAD_CLASS2 P
                          (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                        SEEN 1)))
            (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal"  :in-theory (disable no-fatal-error?)
           :use ((:instance 
                  correctly-loaded?-implies-always-correctly-loaded
                  (classname (super-s 
                              (mv-let (def-found class-desc)
                                                 (class-by-name-s p
                                                                  (env-class-table (env s)))
                                                 (declare (ignore def-found))
                                                 class-desc)))
                             (any p)
                             (s (load_class_x p s seen 2))
                             (mode 1))
                 (:instance 
                  correctly-loaded?-super-interfaces-and-loader-inv-helper-implies
                  (s (load_class_x p (load_class_x p s seen 2) seen 1))
                  (classname p))))))


(defthm |Subgoal *1/6.1|
  (IMPLIES
   (mv-let (def-found class-desc)
           (class-by-name-s p (env-class-table (env s)))
           (declare (ignore def-found))
           (AND (CORRECTLY-LOADED?
                 (SUPER-S class-desc)
                          (INSTANCE-CLASS-TABLE (LOAD_CLASS_X P S SEEN 2))
                          (ENV-CLASS-TABLE (ENV S)))
                 (ALL-CORRECTLY-LOADED?
                  (INTERFACES-S class-desc)
                  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                                      SEEN 1))
                  (ENV-CLASS-TABLE (ENV S)))
                 (LOADER-INV-HELPER
                  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                                      SEEN 1))
                  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                                      SEEN 1))
                  (ENV-CLASS-TABLE (ENV S)))
                 (NO-FATAL-ERROR? (LOAD_CLASS2 P
                                               (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                                             SEEN 1)))))
           (correctly-loaded? p
            (INSTANCE-CLASS-TABLE
             (LOAD_CLASS2 P
                          (LOAD_CLASS_X P (LOAD_CLASS_X P S SEEN 2)
                                        SEEN 1)))
            (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal"   :in-theory (disable no-fatal-error?)
           :use ((:instance 
                  correctly-loaded?-implies-always-correctly-loaded
                  (classname (super-s 
                              (mv-let (def-found class-desc)
                                                 (class-by-name-s p
                                                                  (env-class-table (env s)))
                                                 (declare (ignore def-found))
                                                 class-desc)))
                             (any p)
                             (s (load_class_x p s seen 2))
                             (mode 1))
                 (:instance 
                  correctly-loaded?-super-interfaces-and-loader-inv-helper-implies-2
                  (s (load_class_x p (load_class_x p s seen 2) seen 1))
                  (classname p))))))

(in-theory (enable fatalError))

(defthm load_class_x_establish_post_given_pre
     (implies (load-class-x-pre p s mode)
              (load-class-x-post p 
                                 (load_class_x p s seen mode)
                                 mode))
     :hints (("Goal" :do-not '(generalize)
              :induct (load_class_x p s seen mode))
             ("Subgoal *1/19"
              :use ((:instance
                     correctly-loaded?-implies-always-correctly-loaded
                     (classname (car p)) (any (cdr p)) 
                     (s (LOAD_CLASS_X (car p) S SEEN 3))
                     (mode 0))))
             ("Subgoal *1/16"
              :use ((:instance
                     correctly-loaded?-implies-always-correctly-loaded
                     (classname (car p)) (any (cdr p)) (s (LOAD_CLASS_X (car p) S SEEN 3))
                     (mode 0))))
             ("Subgoal *1/6" :in-theory (disable no-fatal-error?))))

;(i-am-here)

;; we need some property that load_class_x preserve wff-state
;;
;; 

(defthm wff-state-preserved-by-load_class_x
  (implies (wff-state s)
           (wff-state (load_class_x any s seen mode))))
;; proved in jvm-loader.lisp also.

(defthm wff-class-table-preserved-by-load_cp_entry
  (implies (wff-class-table (class-table s))
           (wff-class-table (class-table (mv-nth 1 (load_cp_entry cp s))))))


(defthm wff-class-table-preserved-by-load_cp_entries
  (implies (wff-class-table (class-table s))
           (wff-class-table (class-table (mv-nth 1 (load_cp_entries cps s))))))


(defthm wff-class-table-make-class-table
  (wff-class-table (make-class-table anycl anyacl))
  :hints (("Goal" :in-theory (enable wff-class-table make-class-table))))

(defthm wff-class-table-preserved-by-load_class2
  (implies (wff-class-table (class-table s))
           (wff-class-table (class-table (load_class2 any s))))
  :hints (("Goal" :in-theory (e/d (load_class2)
                                  (class-table wff-class-table)))))

(defthm wff-class-table-preserved-by-load_class_x
  (implies (wff-class-table (class-table s))
           (wff-class-table (class-table (load_class_x any s seen mode)))))


;; we may prove a stronger property that state how instance class-table
;; change. (It is complicated. We may just open the definition of load_class2
;; in that case)

; (defthm instance-class-table-load_class2-is
;   (implies (mv-nth 0 (class-by-name-s classname scl))
;            (equal (instance-class-table (load_class2 any s))
;                   (add-instance-class-entry (make-class-rep

;; (defthm true-listp-load_cp_entries
;;   (true-listp (car (load_cp_entries cps s))))

(defthm wff-constant-pool-entry-load_cp_entry
  (implies (wff-constant-pool-entry-s cp)
           (wff-constant-pool-entry (car (load_cp_entry cp s))))
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(defthm wff-constant-pool-load_cp_entries
  (implies (wff-constant-pool-s cps)
           (wff-constant-pool (car (load_cp_entries cps s)))))

;; Fri Aug  6 17:32:29 2004. after modifying wff-class-rep-strong
;; need to fix this theorem. 

;(i-am-here)

;; (i-am-here) ;; Mon May  1 01:13:19 2006

(defthm wff-method-decl-RUNTIME-METHOD-REP
  (implies (RUNTIME-METHOD-REP-GUARD amethod)
           (wff-method-decl (runtime-method-rep amethod name))))

(defthm wff-method-decls-RUNTIME-METHOD-REP1
  (implies (RUNTIME-METHOD-REP-GUARDS methods)
           (wff-class-method-decls (runtime-methods-rep1 methods name))))



(defthm wff-fields-s-x-wff-static-fields-x
  (implies (wff-fields-s-x fields)
           (wff-static-fields-x (runtime-static-fields-rep1
                                 fields classname dynamic-cp))))

(defthm wff-fields-s-x-wff-fields
  (implies (wff-fields-s-x fields)
           (wff-fields-x (runtime-instance-fields-rep1 fields classname))))

(defthm wff-fields-s-x-wff-fields-2
  (implies (wff-fields-s-x fields)
           (wff-class-fields (runtime-instance-fields-rep1 fields classname))))

;;; Fri Nov  5 13:15:40 2004. changed the signature of
;;; runtime-instance-fields-rep1
;;;

;(i-am-here)

(defthm wff-class-rep-strong-if-wff-static-class-rep
  (implies (and (wff-class-rep-static-strong class-static-rep)
                (integerp new-address) 
                t)
           (wff-class-rep-strong 
            (make-runtime-class-rep 
             classname 
             super
             (car (load_cp_entries (constantpool-s class-static-rep) s))
             (RUNTIME-INSTANCE-FIELDS-REP1 (fields-s class-static-rep) classname)
             (RUNTIME-METHODS-REP1 (methods-s class-static-rep) CLASSNAME)
             (interfaces-s class-static-rep)
             (RUNTIME-STATIC-FIELDS-REP1 (fields-s class-static-rep) classname
                                         (car (load_cp_entries (constantpool-s class-static-rep) s)))
             *CLASS_LOADED*
             (accessflags-s class-static-rep)
             -1 new-address)))
  :hints (("Goal" :in-theory (enable wff-class-rep-static 
                                     constantpool-s interfaces-s))))
    
(defthm wff-instance-class-table-strong-add-instance-class-rep
  (implies (and (wff-instance-class-table-strong cl)
                (wff-class-rep-strong rep))
           (wff-instance-class-table-strong (add-instance-class-entry rep cl)))
  :hints (("Goal" :in-theory (enable add-instance-class-entry))))



(defthm wff-instance-class-table-strong-preserved-by-load_class2
  (implies (and (wff-instance-class-table-strong (instance-class-table s))
                (mv-nth 0 (class-by-name-s any (external-class-table s)))
                (wff-static-class-table-strong (external-class-table s)))
           (wff-instance-class-table-strong (instance-class-table 
                                             (load_class2 any s))))
  :hints (("Goal" :in-theory (e/d (load_class2)
                                  (make-runtime-class-rep wff-class-rep-strong
                                   accessflags-s constantpool-s)))))

(defthm wff-instance-class-table-preserved-by-load_class_x
  (implies (and (wff-instance-class-table-strong (instance-class-table s))
                (wff-static-class-table-strong (external-class-table s)))
           (wff-instance-class-table-strong (instance-class-table (load_class_x any s seen mode)))))

;; is this true?  Fri Jun 25 10:55:00 2004
;; Do we need some properties about static-class-table?
;(i-am-here)

(defthm load-class-x-prop-implies
  (implies (loader-inv s)
           (loader-inv (load_class_x classname s seen 3)))
  :hints (("Goal" :use ((:instance load_class_x_establish_post_given_pre
                                   (p classname)
                                   (mode 3)))
           :in-theory (disable wff-state wff-class-table))))

;(i-am-here)

; (defthm loader-inv-make-state-equal-trivial
;   (implies (and some-error
;                 (wff-env wff_env))
;            (loader-inv (make-state any_pc
;                                    any_th
;                                    any_hp
;                                    any_tt
;                                    any_cl
;                                    wff_env
;                                    some-error
;                                    any_aux)))


; (defthm loader-inv-make-state-equal-simple
;   (implies (and (LOADER-INV S)
                
;                 some_error)
;            (LOADER-INV (MAKE-STATE (pc s)
;                                    any_th
;                                    any_hp
;                                    any_tt
;                                    some_class_table
;                                    ;(CLASS-TABLE S)
;                                    (ENV S)
;                                    some_error
;                                    any_aux))))
                                 
; (skip-proofs 
;  (defthm load-class-x-prop-implies-x
;   (implies (loader-inv s)
;            (loader-inv (load_class_x classname s seen mode)))
;   :hints (("Goal" :use ((:instance load_class_x_establish_post_given_pre
;                                    (p classname)))
;            :do-not '(generalize)
;            :in-theory (disable wff-state wff-class-table loader-inv)))))


(in-theory (disable loader-inv))

(defthm loader-inv-current-thread-doesnt-matter
  (implies (loader-inv s)
           (loader-inv (state-set-current-thread any s)))
  :hints (("Goal" :in-theory (enable loader-inv state-set-current-thread))))

(in-theory (disable state-set-current-thread))

;; Step 1.

(defthm loader-inv-is-inv-respect-to-loading-primitive
    (implies (loader-inv s)
             (loader-inv (load_class classname s)))
    :hints (("Goal" :in-theory (cons 'load_class (disable load_class_x)))))


;;
;; this invariant will implies isAssignableTo A B according to env-class-table 
;; and A is loaded, then B is correctly loaded, anywhere during JVM execution,
;; where no error occurs. 
;;

(defun isInterface-s (class-desc)
  (mem '*interface* (accessflags-s class-desc)))


(defun isSuperClass-env1 (A B env-cl seen)
  (declare (xargs :measure (collect-superclassname1-measure env-cl seen)))
  (mv-let (foundA classA) 
          (class-by-name-s A env-cl)
          (if (not foundA)
              nil
            (if (mem A seen)
                nil
             (if (equal A B) 
                 t
               (isSuperClass-env1 (super-s classA) B env-cl (cons A seen)))))))



(defun isSuperClass-env (A B env-cl)
  (isSuperClass-env1 A B env-cl nil))

(defun implement-x-env-measure (A-or-As env-cl seen mode)
  (cond ((equal mode 1) 
         (collect-superinterface1-measure env-cl seen 0))
        ((equal mode 2)
         (collect-superinterface1-measure env-cl seen (len A-or-As)))
        (t 0)))
  

(defun implement-x-env (A-or-As B env-cl seen mode)
  (declare (xargs :measure (implement-x-env-measure A-or-As env-cl seen mode)))
  (let ((A  A-or-As)
        (As A-or-As))
    (cond ((equal mode 1)
           (mv-let (foundA classA)
                   (class-by-name-s A env-cl)
                   (if (not foundA)
                       nil
                     (if (mem A seen)
                         nil
                       (if (equal A B)
                           t
                         (let ((interfaces (interfaces-s classA)))
                           (if (mem B interfaces)
                               t
                             (implement-x-env interfaces B env-cl (cons A seen)
                                              2))))))))
          ((equal mode 2)
           (if (endp As)
               nil
             (or (implement-x-env (car As) B env-cl seen 1)
                 (implement-x-env (cdr As) B env-cl seen 2))))
          (t nil))))


(defun classImplementsInterface-env1 (A B env-cl seen)
  (implement-x-env A B env-cl seen 1))

(defun classImplementsInterface-env2 (A B env-cl seen)
  (implement-x-env A B env-cl seen 2))


(defun classImplementsInterface-env (A B env-cl)
  (classImplementsInterface-env1 A B env-cl nil))


(defun isAssignableTo-env (A B env-cl)
  (mv-let (foundB classB)
          (class-by-name-s B env-cl)
          (mv-let (foundA classA)
                  (class-by-name-s A env-cl)
                  (cond ((not foundB) nil)
                        ((not foundA) nil)
                        ((equal A B) t)
                        ((isInterface-s classB)
                         (classImplementsInterface-env A B env-cl))
                        ((isInterface-s classA) nil)
                        (t (isSuperClass-env A B env-cl))))))
   

;; Step 2 



(defthm mem-A-collect-superclassname1-A
  (mv-let (foundA classA)
          (class-by-name-s A env-cl)
          (declare (ignore classA))
          (implies foundA
                   (mem A (collect-superclassname1 A env-cl nil))))
          :hints (("Goal" :expand (collect-superclassname1 A env-cl nil))))


(defthm mem-app-1
  (implies (mem A l1)
           (mem A (app l1 l2))))

(defthm mem-app-2
  (implies (mem A l2)
           (mem A (app l1 l2))))



(defthm implement-x-env-mem-collect-interface
  (implies (implement-x-env A-or-As B env-cl seen mode)
           (mem B (collect-interface-x-env A-or-As env-cl seen mode))))

(defthm classImplementsInterface-env-collect
  (implies (classImplementsInterface-env A B env-cl)
           (mem B (collect-superinterface A env-cl))))


(defthm isSuperClass-env1-collect
  (implies (isSuperClass-env1 A B env-cl seen)
           (mem B (collect-superclassname1 A env-cl seen))))


(defthm isAssignableTo-env-collect-assignableToName
  (implies (isAssignableTo-env A B env-cl)
           (mem B (collect-assignableToName A env-cl))))



(in-theory (disable isAssignableTo-env collect-assignableToName))
 

(defthm mem-all-correctly-loaded?-implies
  (implies (and (mem B A-supers)
                (all-correctly-loaded? A-supers cl env-cl))
           (correctly-loaded? B cl env-cl)))
           
           
(in-theory (disable correctly-loaded?))           
(in-theory (enable loader-inv-helper1))

;; not so good rewrite rules, with many free variables.
(defthm loader-inv-helper1-implies-mem
  (implies (and (loader-inv-helper1 classA cl env-cl)
                (isAssignableTo-env (classname classA) B env-cl))
           (correctly-loaded? B cl env-cl))
  :hints (("Goal" :use ((:instance mem-all-correctly-loaded?-implies
                                   (A-supers (collect-assignableToName 
                                              (classname classA) env-cl)))))))


(defthm correctly-loaded?-implies-mem-class-table
  (implies (correctly-loaded? A cl env-cl)
           (mem (class-by-name A cl) cl))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))



(defthm correctly-loaded?-implies-classname-class-by-name
  (implies (correctly-loaded? A cl env-cl)
           (equal (classname (class-by-name A cl)) A))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))

(in-theory (disable classname))

  
(defthm loader-inv-helper-mem-implies
  (implies (and (loader-inv-helper l1 cl env-cl)
                (mem classA l1))
           (loader-inv-helper1 classA cl env-cl)))


(in-theory (enable loader-inv))
;; a major step: our invariant is stronge enough. 

(defthm inv-and-isAssignableTo-env
  (implies (and (loader-inv s)
                (no-fatal-error? s)
                (isAssignableTo-env A B (env-class-table (env s))))
           (implies (correctly-loaded? A 
                                       (instance-class-table s)
                                       (env-class-table (env s)))
                    (correctly-loaded? B 
                                       (instance-class-table s)
                                       (env-class-table (env s)))))
  :hints (("Goal" :use ((:instance loader-inv-helper-mem-implies
                                   (l1 (instance-class-table s))
                                   (cl (instance-class-table s))
                                   (env-cl (env-class-table (env s)))
                                   (classA (class-by-name A
                                                          (instance-class-table s))))
                        (:instance loader-inv-helper1-implies-mem
                                   (classA (class-by-name A
                                                          (instance-class-table s)))
                                   (env-cl (env-class-table (env s)))
                                   (cl (instance-class-table s)))))))



;; #| haven't define M6 run
;; ;; final goal 
;; (defthm isAssignableTo-env-loaded-A-implies-loaded-B
;;   (implies (and (isAssignableTo-env A B (env-class-table (env s)))
;;                 (no-fatal-error? (m6run sched s))
;;                 (not (class-loaded? A s)))
;;            (implies (class-loaded? A (m6run sched s))
;;                     (class-loaded? B (m6run sched s)))))
;; |#



;; (defthm load_class2_no-fatal-error?-wff-class-rep
;;   (implies (and (no-fatal-error? (load_class2 classname s))
;;                 (wff-static-class-table (env-class-table (env s))))
;;            (wff-class-rep (car (instance-class-table
;;                                 (load_class2 classname s)))))
;;   :hints (("Goal" :in-theory (e/d (load_class2 add-instance-class-entry)
;;                                   (wff-class-rep make-runtime-class-rep)))))

;; (verify-guards load_class_x 
;;                :hints (("Goal" :in-theory (e/d (fatalError class-loaded?)
;;                                                (load_class2
;;                                                 fields
;;                                                 class-table
;;                                                 load_class2_guard-strong
;;                                                 load-class-x-guard-strong
;;                                                 load_cp_entry
;;                                                 wff-class-rep
;;                                                 wff-env
;;                                                 wff-class-table
;;                                                 load_class2_guard))
;;                        :do-not '(generalize)
;;                        :do-not-induct t)
;;                        ("Subgoal 2" :expand (LOAD_CLASS_X P1 S SEEN 3))
;;                        ("Subgoal 1" :expand (LOAD_CLASS_X P1 S SEEN 3))))
