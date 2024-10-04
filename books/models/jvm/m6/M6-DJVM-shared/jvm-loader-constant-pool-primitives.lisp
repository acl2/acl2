(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-loader-primitives")

;------------------------------------------------------------  
;  We need to describe how to create the dynamic class table 
;------------------------------------------------------------  

;;; Wed Mar 31 14:00:46 2004 GUARD VERIFICATION!! 
(acl2::set-verify-guards-eagerness 2)
(defun load_CP_entry_guard (cpentry S)
  (and (wff-constant-pool-entry-s cpentry)
       (or (not (equal (cpentry-type-s cpentry) 'STRING))
           (create-string-guard (string-value-cp-entry-s cpentry) S))))

(defun load_CP_entry (cpentry-s S)
  (declare (xargs :guard (load_CP_entry_guard cpentry-s S)))
  (if (equal (cpentry-type-s  cpentry-s) 'STRING)
      (let ((str  (string-value-cp-entry-s cpentry-s)))
        (mv-let (the-String-obj new-S)
                (ACL2-str-to-JavaString str S)
                (let* ((heap   (heap new-S))
                       (new-addr (alloc heap))
                       (new-heap (bind new-addr the-String-obj heap)))
                  (mv (make-string-cp-entry new-addr)
                      (update-trace new-addr (state-set-heap new-heap new-s))))))
    (mv cpentry-s s)))  ;; because static and dynamic representation are same.

;;;
;;; only String has the special treatment!! 
;;;


(defun load_CP_entries_guard (cpentries s)
  (if (not (consp cpentries)) t
    (and (load_CP_entry_guard (car cpentries) s)
         (load_CP_entries_guard (cdr cpentries) s))))


(acl2::set-match-free-default :all)

(defthm build-immediate-instance-data-guard-equal-class-table
  (implies (and (equal (class-table s2) (class-table s1)) 
                (wff-state s2) (wff-state s1))
           (equal (build-immediate-instance-data-guard any S2)
                  (build-immediate-instance-data-guard any S1)))
  :rule-classes nil)

;;; this rule will loop on itself!!!


(defthm build-a-java-visible-instance-data-guard-equal-class-table
  (implies (and (equal (class-table s2) (class-table s1)) 
                (wff-state s2) 
                (wff-state s1))
           (equal (build-a-java-visible-instance-data-guard anylist S2)
                  (build-a-java-visible-instance-data-guard anylist S1)))
  :hints (("Goal" :use ((:instance
                         build-immediate-instance-data-guard-equal-class-table
                         (any (car anyList))))))
  :rule-classes nil)

;(i-am-here) Wed Jun 23 21:36:08 2004.  after we assert that to build a
;; java-visible instance, we need all super are loaded!!

(defthm build-a-java-visible-instance-guard-equal-class-table
  (implies (and (equal (class-table s2) (class-table s1))
                (wff-env (env s2)) 
                (wff-env (env s1))
                (equal (external-class-table s2) (external-class-table s1))
                (wff-state s2) 
                (wff-state s1))
           (equal (build-a-java-visible-instance-guard any s2)
                  (build-a-java-visible-instance-guard any s1)))
  :hints (("Goal" 
           :in-theory (disable external-class-table class-table)
           :use ((:instance
                  build-a-java-visible-instance-data-guard-equal-class-table
                  (anylist (COLLECT-SUPERCLASS-LIST ANY (CDR (NTH 1
                                                                  (CLASS-TABLE
                                                                   S1)))))))))
  :rule-classes nil)

(defthm load_CP_entry-change-no-class-table
  (equal (class-table (mv-nth 1 (load_CP_entry cp s)))
         (class-table s)))

(defthm load_CP_entry-change-no-pc
  (equal (pc (mv-nth 1 (load_CP_entry cp s)))
         (pc s)))


(defthm load_CP_entry-preserve-wff-state
  (implies (wff-state s)
           (wff-state (mv-nth 1 (load_CP_entry cp s)))))

(defthm load_CP_entry-preserve-wff-heap
  (implies (wff-heap (heap s))
           (wff-heap (heap (mv-nth 1 (load_CP_entry cp s))))))


(defthm build-a-java-visible-instance-guard-implies-wff-state
  (implies (build-a-java-visible-instance-guard any s)
           (wff-state s))
  :rule-classes :forward-chaining)


;; Wed Jun 23 21:45:19 2004
;; need to say that load_cp does not change env

(defthm load_cp_entry-does-not-change-env
  (equal (env (mv-nth 1 (load_cp_entry cp s)))
         (env s)))

(defthm build-a-java-visible-instance-guard-implies-wff-env
  (implies (build-a-java-visible-instance-guard any s)
           (wff-env (env s)))
  :rule-classes :forward-chaining)


(defthm build-a-java-visible-instance-guard-after-load_cp
  (implies (build-a-java-visible-instance-guard any s)
           (build-a-java-visible-instance-guard any (mv-nth 1 (load_CP_entry cp
                                                                             s))))
  :hints (("Goal" :in-theory (disable load_CP_entry wff-env
                                      build-a-java-visible-instance-guard)
           :use ((:instance
                  build-a-java-visible-instance-guard-equal-class-table
                  (s2 (mv-nth 1 (load_CP_entry cp s)))
                  (s1 s))))))

  
(defthm create-string-guard_after_load_cp_entry
  (implies (create-string-guard str s)
           (create-string-guard str (mv-nth 1 (load_CP_entry any s))))
  :hints (("Goal" :in-theory (disable build-a-java-visible-instance-guard load_CP_entry))))


(defthm load_CP_entry_guard-load_CP_entry_guard
  (implies (load_CP_entry_guard x s)
           (load_CP_entry_guard x (mv-nth 1 (load_CP_entry any s))))
  :hints (("Goal" :in-theory (disable create-string-guard load_CP_entry))))



(defthm load_CP_entries_guard-load_CP_entry_guard
  (implies (load_CP_entries_guard cps s)
           (load_CP_entries_guard cps (mv-nth 1 (load_CP_entry any s))))
  :hints (("Goal" :in-theory (disable load_CP_entry_guard load_CP_entry))))



(acl2::set-verify-guards-eagerness 0)

;; Wed Jun 23 21:53:01 2004 
;; guard verified later!! 

(defun load_CP_entries (cps s)
  (declare (xargs :guard (load_CP_entries_guard cps s)))
  (if (not (consp cps))
      (mv nil s)
    (mv-let (new-ent new-state)
            (load_CP_entry   (car cps) s)
            (mv-let (new-ents final-state)
                    (load_CP_entries (cdr cps) new-state)
                    (mv (cons new-ent new-ents) final-state)))))

(acl2::set-verify-guards-eagerness 2)
    
(verify-guards load_CP_entries
               :hints (("Goal" :in-theory (disable load_CP_entry
                                                   load_CP_entry_guard)
                        :induct (load_CP_entries cps s))))



(defun load_CP (static-cp S)
  (declare (xargs :guard (load_CP_entries_guard static-cp s)))
  (load_CP_entries static-cp s))

(defthm load_CP_entries_guard-wff-state
  (implies (wff-state s)
           (wff-state (mv-nth 1 (load_CP_entries  cps s))))
  :hints (("Goal" :in-theory (disable load_CP_entry))))

(defthm load_CP_entries_guard-wff-heap
  (implies (wff-heap (heap s))
           (wff-heap (heap (mv-nth 1 (load_CP_entries  cps s)))))
  :hints (("Goal" :in-theory (disable load_CP_entry wff-heap))))


(defthm load_CP_entries_guard-do-not-change-class-table
  (equal (class-table (mv-nth 1 (load_CP_entries  cps s)))
         (class-table s))
  :hints (("Goal" :in-theory (disable load_CP_entry))))

(defthm load_CP_entries_guard-do-not-change-pc
  (equal (pc (mv-nth 1 (load_CP_entries  cps s)))
         (pc s))
  :hints (("Goal" :in-theory (disable load_CP_entry))))

(defthm build-a-java-visible-instance-guard-after-load_cp_entries
  (implies (build-a-java-visible-instance-guard any s)
           (build-a-java-visible-instance-guard any 
                       (mv-nth 1 (load_CP_entries  cps s))))
  :hints (("Goal" :in-theory (disable load_CP_entry 
                                      build-a-java-visible-instance-guard))))



;-----------------------------------
; how to construct the dynamic rep.

;; (defun runtime-instance-field-rep (sfield classname)
;;   (declare (xargs :guard (and (wff-field-s sfield)
;;                               (wff-type-rep (field-fieldtype-s sfield)))))
;;   (make-field classname 
;;               (field-fieldname-s sfield) 
;;               (normalize-type-rep (field-fieldtype-s sfield))
;;               (field-fieldaccessflags-s sfield)))  ;; throw away the cpindex
;;                                                    ;; fields in the sfield


;; (defun runtime-static-field-rep (sfield classname)
;;   (declare (xargs :guard (and (wff-field-s sfield)
;;                               (wff-type-rep (field-fieldtype-s sfield)))))
;;   (make-static-field classname 
;;               (field-fieldname-s sfield) 
;;               (normalize-type-rep (field-fieldtype-s sfield))
;;               (field-fieldaccessflags-s sfield)
;;               (field-cpindex-s sfield)))
      

;; (defun runtime-instance-fields-rep1 (static-fields classname)
;;   (declare (xargs :guard (wff-fields-s static-fields)))
;;   (if (not (consp static-fields))
;;       nil
;;     (if (static-field?-s (car static-fields))
;;           (runtime-instance-fields-rep1 (cdr static-fields) classname)
;;     (cons (runtime-instance-field-rep (car static-fields) classname)
;;           (runtime-instance-fields-rep1 (cdr static-fields) classname)))))

;; (defun runtime-instance-fields-rep (static-field-table classname)
;;   (declare (xargs :guard (wff-fields-s static-field-table)))
;;   (runtime-instance-fields-rep1 static-field-table classname))


;; (defun runtime-static-fields-rep1 (static-fields classname)
;;   (declare (xargs :guard (wff-fields-s static-fields)))
;;   (if (not (consp static-fields))
;;       nil
;;     (if (not (static-field?-s (car static-fields)))
;;           (runtime-static-fields-rep1 (cdr static-fields) classname)
;;     (cons (runtime-static-field-rep (car static-fields) classname)
;;           (runtime-static-fields-rep1 (cdr static-fields) classname)))))


;; (defun runtime-static-fields-rep (static-field-table classname)
;;   (declare (xargs :guard (wff-fields-s static-field-table)))
;;   (runtime-static-fields-rep1 static-field-table classname))



;; (defun runtime-code-rep0 (scode)
;;   (declare (xargs :guard (wff-code-s scode)))
;;   (make-code 
;;    (code-max-stack-s scode)
;;    (code-max-local-s scode)
;;    (code-code-length-s scode)
;;    (code-instrs-s    scode)
;;    (code-handlers-s  scode)
;;    (code-stackmaps-s scode)))

;; (defun runtime-code-rep (scode accessflag)
;;   (declare (xargs :guard (wff-code-s scode)))
;;   (cond ((mem '*native* accessflag)   (make-code 0 0 0 0 nil nil))
;;         ((mem '*abstract* accessflag) (make-code 0 0 0 0 nil nil))
;;         (t (runtime-code-rep0 scode))))

;; (defun runtime-method-rep-guard (amethod)
;;   (and (wff-method-decl-s amethod)
;;        (wff-type-reps (method-args-s amethod))
;;        (wff-type-rep (method-returntype-s amethod))
;;        (wff-code-s (method-code-s amethod))))

;; (defun runtime-method-rep (amethod classname)
;;   (declare (xargs :guard (runtime-method-rep-guard  amethod)))
;;   (make-method classname 
;;               (method-methodname-s  amethod) 
;;               (normalize-type-reps (method-args-s        amethod))
;;               (normalize-type-rep  (method-returntype-s  amethod))
;;               (method-accessflags-s amethod)
;;               (runtime-code-rep 
;;                (method-code-s        amethod) (method-accessflags-s amethod))))

;; (defun runtime-method-rep-guards (methods)
;;   (if (not (consp methods)) t
;;       (and (runtime-method-rep-guard (car methods))
;;            (runtime-method-rep-guards (cdr methods)))))

;; (defun runtime-methods-rep1 (methods classname)
;;   (declare (xargs :guard (runtime-method-rep-guards methods)))
;;   (if (not (consp methods))
;;       nil
;;     (cons (runtime-method-rep (car methods) classname)
;;           (runtime-methods-rep1 (cdr methods) classname))))


;; (defun runtime-methods-rep (static-method-table classname)
;;   (declare (xargs :guard (runtime-method-rep-guards static-method-table)))
;;   (runtime-methods-rep1 static-method-table classname))




