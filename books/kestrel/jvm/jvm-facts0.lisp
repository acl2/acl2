; Rules about the JVM model
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Note: Portions of this file may be taken from books/models/jvm/m5.  See the
; LICENSE file and authorship information there as well.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "jvm")

; Here we develop the general theory for proving things about the
; JVM bytecode.

;(local (include-book "kestrel/library-wrappers/arithmetic-top-with-meta" :dir :system)) ;made this local. -EWS
;(local (include-book "ihs/quotient-remainder-lemmas" :dir :system)) ;made this local. -EWS
;(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system)) ;to get the disables of bad rules brought in just above

(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

(local (in-theory (disable default-cdr
                           default-car
                           intersection-equal
                           )))

;(local (in-theory (disable acl2::NTH-OF-CDR))) ;looped!

;(local (in-theory (cons 'zp (disable mod))))

;(local (in-theory (disable ACL2::LOGAPP-0))) ;does forcing

; Mappings

(defthm assoc-equal-bind
  (equal (assoc-equal key1 (bind key2 val alist))
         (if (equal key1 key2)
             (cons key1 val)
           (assoc-equal key1 alist)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm bind-bind
  (equal (bind x v (bind x w a))
         (bind x v a)))

; Semi-Ground Terms

(in-theory (disable nth))

(defthm run-of-nil
  (equal (run nil s)
         s)
  :hints (("Goal" :in-theory (e/d (run)( step)))))

(defthm run-of-cons
  (equal (run (cons th sched) s)
         (if (bound-in-alistp th (thread-table s))
             (run sched (step th s))
           (run sched s)))
  :hints (("Goal" :in-theory (e/d (run)( step)))))

(defthm run-append
  (equal (run (append sched1 sched2) s)
         (run sched2 (run sched1 s)))
  :hints (("Goal" :in-theory (enable run))))

;do we still need this?
(defun acl2::quotep-for-tracing (x)
  (quotep x))

;(in-theory (disable true-listp))

;gross proof?
(defthm make-state-equal-rewrite-2
  (equal (equal s (make-state thread-table heap class-table hrt monitor-table sfm ic intern-table))
         (and (true-listp s) ;these two are a sort of weak-jvm-statep
              (equal 8 (len s))
              (equal (thread-table s) thread-table)
              (equal (heap s) heap)
              (equal (heapref-table s) hrt)
              (equal (monitor-table s) monitor-table)
              (equal (class-table s) class-table)
              (equal (static-field-map s) sfm)
              (equal (initialized-classes s) ic)
              (equal (intern-table s) intern-table)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (make-state class-table thread-table heap jvm-statep heapref-table monitor-table static-field-map initialized-classes intern-table
                                       ;acl2::consp-cdr
                                       ACL2::CAR-BECOMES-NTH-OF-0
                                       acl2::nth-of-cdr
                                       ;;acl2::CDR-OF-CDR-BECOMES-NTHCDR
                                       acl2::3-cdrs
                                       acl2::CDR-OF-NTHCDR
                                       )
                           (len nth TRUE-LISTP ;LIST::LEN-EQUAL-1-REWRITE
                                )))))

;test
(in-theory (disable thread-top-frame bind binding))

(defthm reduce-make-state-equality-when-all-but-heaps-match
  (equal (equal (make-state thread-table heap class-table hrt monitor-table sfm ic intern-table)
		(make-state thread-table heap2 class-table hrt monitor-table sfm ic intern-table))
	 (equal heap heap2))
  :hints (("Goal" :in-theory (enable make-state))))

(defthm reduce-make-state-equality-when-all-but-thread-tables-match
  (equal (equal (make-state thread-table heap class-table hrt monitor-table sfm ic intern-table)
		(make-state thread-table2 heap class-table hrt monitor-table sfm ic intern-table))
	 (equal thread-table thread-table2))
  :hints (("Goal" :in-theory (enable make-state))))

;; (defthm move-bound?-inside-bind
;;   (implies (not (equal x y))
;; 	   (equal (BOUND?
;; 		   x
;; 		   (BIND
;; 		    y
;; 		    val
;; 		    alist))
;; 		  (bound? x alist)))
;;   :hints (("Goal" :in-theory (enable bound?))))

;; (defthm bound?-bind
;;   (BOUND? x (BIND x val alist))
;;    :hints (("Goal" :in-theory (enable bound?))))


(defthm move-binding-inside-bind
  (implies (not (equal x y))
	   (equal (binding x (bind y val alist))
                  (binding x alist)))
  :hints (("Goal" :in-theory (enable bind binding))))

(defthm bind-bind-diff
  (implies (and (assoc-equal y alist) ;case-split?
		(case-split (not (equal x y)))
		)
	   (equal (bind x xval (bind y yval alist))
		  (bind y yval (bind x xval alist))))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable bind ;bound?
                                     assoc-equal))))

(defthm bind-bind-diff-2
  (implies (and (assoc-equal x alist) ;case-split?
		(case-split (not (equal x y)))
		)
	   (equal (bind x xval (bind y yval alist))
		  (bind y yval (bind x xval alist))))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable bind assoc-equal))))

(defthm bind-with-constant-key-move-past-first-binding-with-diff-constant-key
  (implies (and (stringp (caar alist)) ;generalize this but still restrict to constants
		(stringp key1) ;generalize this but still restrict to constants
		(not (equal key1 (caar alist)))
		(case-split (consp alist))
		)
	   (equal (bind key1 val1 alist)
		  (cons (car alist) (bind key1 val1 (cdr alist)))))
  :hints (("Goal" :in-theory (enable bind))))

(defthm bind-with-constant-key-move-past-first-binding-with-same-constant-key
  (implies (and (stringp (caar alist)) ;generalize this but still restrict to constants
		(stringp key1) ;generalize this but still restrict to constants
		(equal key1 (caar alist))
		(case-split (consp alist))
		)
	   (equal (bind key1 val1 alist)
		  (cons (cons key1 val1) (cdr alist))))
  :hints (("Goal" :in-theory (enable bind))))

; test for the rules above
;; (thm (equal zz (BIND "previous" (LIST 'REF (LEN (HEAP S)))
;;                      '(("element" REF -1)
;;                        ("next" REF -1)
;;                        ("previous" REF -1)))))

(defthm alistp-bind
  (implies (case-split (alistp alist))
           (alistp (bind key val alist)))
  :hints (("Goal" :in-theory (enable alistp bind))))

(defthm alistp-bind-force
  (implies (force (alistp alist))
           (alistp (bind key val alist)))
  :hints (("Goal" :in-theory (enable alistp bind))))

;; ;Note: this does not check that the field actually exists!!
;; ;Does the JVM model check that we are setting a valid field?  It really should, and return an error state if we are not setting a valid field.
;; (defun set-field-in-instance (field class value instance)
;;   (let* ((fields-for-this-class (binding class instance))
;; 	 (new-fields-for-this-class (bind field value fields-for-this-class))
;; 	 (new-instance (bind class new-fields-for-this-class instance)))
;;     new-instance))







;; ;this allowed effect-of-invoking-addbefore to be proved
;; (def axiom bind-bind-diff-3
;;   (implies (and ;(bound? y alist) ;case-split?
;; 		(case-split (not (equal x y)))
;; 		)
;; 	   (equal (bind x xval (bind y yval alist))
;; 		  (bind y yval (bind x xval alist)))))




;rename
(defthm binding-with-const-1
  (implies (not (equal key1 key2))
	   (equal (BINDING
		   key1
		   (cons
		    (CONS key2
			  val)
		    rest))
		  (binding key1 rest)))
  :hints (("Goal" :in-theory (enable binding))))

(defthm binding-with-const-2
  (equal (BINDING
	  key1
	  (cons
	   (CONS key1
		 val)
	   rest))
	 val)
  :hints (("Goal" :in-theory (enable binding))))

(defthm binding-with-const-both
  (equal (binding key1 (cons (cons key2 val) rest))
	 (if (equal key1 key2)
	     val
	   (binding key1 rest)))
  :hints (("goal" :in-theory (enable binding))))

(defthm binding-bind
  (equal (binding x (bind x val alist))
   val)
  :hints (("goal" :in-theory (enable bind binding))))

;causes a case-split but I think we usually want this rule
(defthm move-binding-inside-bind-both
  (equal (binding x (bind y val alist))
	 (if (equal x y)
	     val
	   (binding x alist)))
  :hints (("goal" :in-theory (enable bind binding))))


;; ;can classes be different? no?
;; ;rename
;; (defthm field-value-of-set-instance-field
;;   (equal (get-field-of-instance class field1 (set-field-of-instance class field2 val instance))
;;    (if (equal field1 field2)
;;        val
;;      (get-field-of-instance class field1 instance)))
;;   :hints (("goal" :in-theory (enable get-field-of-instance set-field-of-instance)))
;; )


;; ;expand a call to set-field-of-instance when everything but perhaps the value is constant
;; (defthm set-field-of-instance-in-const
;;   (implies (syntaxp (and (quotep instance)
;; 			 (quotep class-name)
;; 			 (quotep field-id)))
;; 	   (equal
;; 	    (set-field-of-instance CLASS-NAME FIELD-ID VALUE INSTANCE)
;; 	    (s CLASS-NAME
;; 		  (s FIELD-ID
;; 			VALUE (g CLASS-NAME INSTANCE))
;; 		  INSTANCE)))
;;   :hints (("Goal" :in-theory (enable set-field-of-instance)))
;;   )


;search for stringp and fix that to use syntaxp!



;; ;having to enable bind here seems to indicate that a bind theorem is missing
;; (defthm set-field-of-instance-into-cons
;;   (equal
;;    (set-field-of-instance class1 field val
;; 		       (cons (cons class2 class2-binding)
;; 			     rest))
;;    (if (equal class1 class2)
;;        (cons (cons class2 (bind field val class2-binding))
;;              rest)
;;      (cons (cons class2 class2-binding)
;; 	   (bind class1
;; 		 (bind field val (binding class1 rest))
;; 		 rest))))
;;   :hints (("goal" :in-theory (enable set-field-of-instance bind)))
;;   )


;; (defthm get-field-of-instance-into-cons
;;   (equal
;;    (get-field-of-instance
;;     class
;;     field
;;     (cons (cons class2 class2-binding) rest))
;;    (if (equal class class2)
;;        (binding field class2-binding)
;;      (binding field (binding class rest))))
;;   :hints (("goal" :in-theory (enable get-field-of-instance))))




;; (defthm deref-bind
;;   (equal
;;    (DEREF
;;     ref
;;     (BIND adr
;; 	  val
;; 	  alist))
;;    (if (equal (get-adr ref) adr)
;;        val
;;      (deref ref alist)))
;;   :hints (("Goal" :in-theory (enable deref))))

(defthm bind-equal-rewrite
 (equal (equal (bind key val1 alist)
	       (bind key val2 alist))
	(equal val1 val2))
 :hints (("Goal" :in-theory (enable bind)))
)

;; (defthm set-field-of-instance-diff
;;   (implies (not (equal field1 field2))
;; 	   (equal (set-field-of-instance
;; 		   class field1 val1
;; 		   (set-field-of-instance
;; 		    class field2 val2
;; 		    instance))
;; 		  (set-field-of-instance
;; 		   class field2 val2
;; 		   (set-field-of-instance
;; 		    class field1 val1
;; 		    instance))))
;;   :rule-classes ((:rewrite :loop-stopper ((field1 field2))))
;;  :hints (("Goal" :in-theory (enable set-field-of-instance)))
;; )


;; (defthm set-field-of-instance-same
;;   (equal (set-field-of-instance
;; 		   class field val1
;; 		   (set-field-of-instance
;; 		    class field val2
;; 		    instance))
;; 		  (set-field-of-instance
;; 		    class field val1
;; 		    instance))

;;  :hints (("Goal" :in-theory (enable set-field-of-instance))))

(in-theory (disable bind-bind-diff bind-bind-diff-2))

;BOZO yuck! this caused problems later on.
(defthm bind-bind-diff-force
  (implies (and (force (or (assoc-equal y alist) (assoc-equal x alist))) ;case-split?
		(case-split (not (equal x y)))
		)
	   (equal (bind x xval (bind y yval alist))
		  (bind y yval (bind x xval alist))))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable bind assoc-equal assoc-equal))))

(defthm bind-to-binding
  (implies (and (force (alistp alist))
		(force (assoc-equal field alist))
		)
	   (equal (bind field (binding field alist) alist)
		  alist))
  :hints (("goal" :in-theory (enable bind assoc-equal binding assoc-equal))))

(defthm bind-to-binding-better
  (implies (and (case-split (alistp alist))
                (case-split (assoc-equal field alist)))
           (equal (bind field (binding field alist) alist)
                  alist))
  :hints (("goal" :in-theory (enable bind binding assoc-equal))))

(in-theory (disable bind-to-binding))


;; ;can any of the classes be diff?
;; (defthm set-field-of-instance-to-get-field-of-instance-with-an-intervening-set
;;   (implies (and
;; 	    (not (equal field1 field2))
;; 	    (force (BOUND? FIELD1 (BINDING CLASS1 REF)))
;; 	    (force (ALISTP (BINDING CLASS1 REF)))
;; 	    (force (BOUND? FIELD2 (BINDING CLASS1 REF)))
;; 	    )
;; 	   (equal
;; 	    (set-field-of-instance
;; 	     class1 field2
;; 	     (GET-FIELD-OF-INSTANCE class1
;; 			  field2 ref)
;; 	     (set-field-of-instance class1 field1
;; 				 val2
;; 				 ref))
;; 	    (set-field-of-instance class1 field1
;; 				val2
;; 				ref)))
;;    :hints (("Goal" :in-theory (enable set-field-of-instance get-field-of-instance))))

;; (defthm set-field-of-instance-to-get-field-of-instance
;;   (implies (and
;; 	    (force (ALISTP (BINDING CLASS1 instance)))
;; 	    (force (BOUND? FIELD2 (BINDING CLASS1 instance)))
;; 	    (BOUND? CLASS1 INSTANCE)
;; 	    (force (alistp instance))
;; 	    )
;; 	   (equal
;; 	    (set-field-of-instance
;; 	     class1 field2
;; 	     (GET-FIELD-OF-INSTANCE class1
;; 			  field2 instance)
;; 	     instance)
;; 	    instance))
;;    :hints (("Goal" :do-not-induct t
;; 	    :in-theory (enable set-field-of-instance get-field-of-instance))))

;; ;remove?
;; ;expensive?
;; (defthm set-field-of-instance-to-get-field-of-instance-2
;;   (implies (and
;; 	    (equal val2 (GET-FIELD-OF-INSTANCE class1 field2 instance))
;; 	    (force (ALISTP (BINDING CLASS1 instance)))
;; 	    (force (BOUND? FIELD2 (BINDING CLASS1 instance)))
;; 	    (force (BOUND? CLASS1 INSTANCE))
;; 	    (force (alistp instance))

;; 	    )
;; 	   (equal
;; 	    (set-field-of-instance
;; 	     class1 field2
;; 	     val2
;; 	     instance)
;; 	    instance))
;;    :hints (("Goal" :do-not-induct t
;; 	    :in-theory (enable set-field-of-instance get-field-of-instance))))






;; (defthm hack2
;;   (equal (SET-FIELD-OF-REF
;; 	  adr ; adrs match
;; 	  class-name
;; 	  field-id
;; 	  value
;; 	  (S adr
;; 	     instance
;; 	     heap))
;; 	 (s adr
;; 	    (SET-FIELD-OF-instance
;; 	     class-name
;; 	     field-id
;; 	     value
;; 	     instance)
;; 	    heap))
;; :hints (("Goal" :in-theory (enable set-field-of-ref set-instance get-instance))))

;(local (in-theory (disable ACL2::MOD-X-Y-=-X+Y))) ;made local since the include-book is local -EWS

;BOZO LEN-CDR-BOTH and defun len loop
;BOZO LEN-CDR and defun len loop

;; ;fixme restrict to non-constants? see EQUAL-CONS-CASES2-ALT-BETTER
;; (defthmd cons-equal-rewrite
;;   (equal (equal (cons x y) z)
;;          (and (consp z)
;;               (equal x (car z))
;;               (equal y (cdr z)))))

;use iff?
(defthm len-hack
  (implies (and (true-listp x)
                x ;is not nil
                )
           (not (equal 0 (len x)))))

;pull out a more general lemma?
(defthm jvm-statep-reassemble
  (implies (case-split (jvm-statep s))
           (EQUAL (MAKE-STATE (THREAD-TABLE S)
                              (HEAP S)
                              (CLASS-TABLE S)
                              (heapref-table s)
                              (monitor-table s)
                              (static-field-map s)
                              (initialized-classes s)
                              (intern-table s))
                  S))
  :hints (("Goal" :in-theory (enable JVM-STATEP))))


(defthm thread-table-equal-bind-thread-table-rewrite
  (implies (case-split (alistp thread-table))
           (equal (equal thread-table (bind th thread thread-table))
                  (if (assoc-equal th thread-table)
                      (equal thread (binding th thread-table))
                    nil))))


;; (thm
;;  (implies (and (not (memberp elem lst2))
;;                (string-listp lst2)
;;                (stringp elem)
;;                (string-listp lst1)
;;                )
;;           (stringp (first-non-member (acl2::append lst1 (list elem)) lst2)))
;;  :hints (("Goal" :in-theory (enable first-non-member))))

(DEFTHM ACL2::USE-monitor-tablep
  (IMPLIES (AND (monitor-tablep MONITOR-TABLE)
                (set::in X (acl2::rkeys monitor-table)))
           (AND (CONSP (G X MONITOR-TABLE))
                (THREAD-DESIGNATORP (CAR (G X MONITOR-TABLE)))
                (MCOUNTP (CDR (G X MONITOR-TABLE)))))
  :hints (("Goal" :in-theory (enable MONITOR-TABLEP))))

;; (defun RESOLVE-FIELD-AUX-induction (field-id class-or-interface-name class-table ctr)
;;    (declare (xargs :measure (+ 1 (nfix ctr)) ;:guard (natp ctr)
;;                    ))
;;    (if (zp ctr)
;;        (list field-id class-or-interface-name class-table ctr)
;;      (list (RESOLVE-FIELD-AUX-induction field-id (car class-or-interface-name) class-table (+ -1 (nfix ctr)))
;;            (RESOLVE-FIELD-AUX-induction field-id (cdr class-or-interface-name) class-table (+ -1 (nfix ctr)))
;;            (let* ((class-decl (get-class-info class-or-interface-name class-table))
;;                   (interface-names (class-decl-interfaces class-decl)))
;;            (RESOLVE-FIELD-AUX-induction field-id interface-names class-table (+ -1 (nfix ctr))))
;;            (let* ((class-decl (get-class-info class-or-interface-name class-table))
;;                   (superclass (class-decl-superclass class-decl)))
;;              (RESOLVE-FIELD-AUX-induction field-id superclass class-table (+ -1 (nfix ctr)))))))

;; (thm
;;  (and
;;   (implies (and (class-tablep class-table)
;;                 (STRING-listP CLASS-OR-INTERFACE-NAME)
;;                 (resolve-field-aux-lst field-id class-or-interface-name class-table ctr) ;result is not nil
;;                 (natp ctr)
;;                 )
;;            ;;so it might be a string:
;;            (stringp (resolve-field-aux-lst field-id class-or-interface-name class-table ctr)))
;;   (implies (and (class-tablep class-table)
;;                 (STRINGP CLASS-OR-INTERFACE-NAME)
;;                 (resolve-field-aux field-id class-or-interface-name class-table ctr) ;result is not nil
;;                 (natp ctr)
;;                 )
;;            ;;so it might be a string:
;;            (stringp (resolve-field-aux field-id class-or-interface-name class-table ctr))))
;;  :hints (("Goal" :induct (resolve-field-aux-induction field-id class-or-interface-name class-table ctr)
;;           :expand ((RESOLVE-FIELD-AUX-LST FIELD-ID CLASS-OR-INTERFACE-NAME
;;                                           CLASS-TABLE CTR)
;;                    (RESOLVE-FIELD-AUX FIELD-ID CLASS-OR-INTERFACE-NAME
;;                                       CLASS-TABLE CTR))
;;           :in-theory (enable resolve-field-aux))))

(in-theory (disable ACL2::HEAP-OBJECT-KEYP)) ;fixme move up

;; (thm
;;  (implies (and (not (equal nil (LOCKED-OBJECT (TOP-FRAME-of-thread TH S))))
;;                (NOT (EMPTY-CALL-STACKP (BINDING TH (THREAD-TABLE S))))
;;                (JVM-STATEP S))
;;           (ADDRESSP (LOCKED-OBJECT (TOP-FRAME-of-thread TH S)))))

;; ;fixme putback
;; (defthm framep-of-top-frame
;;   (implies (and (thread-designatorp th)
;;                 (jvm-statep s)
;;                 (bound-in-alistp th (thread-table s))
;;                 (call-stack-non-emptyp th s))
;;            (framep (thread-top-frame th s)))
;;   :hints (("Goal" :in-theory (enable top-frame))))

(defthm pcp-of-myif
  (equal (pcp (myif test tp ep))
         (myif test (pcp tp) (pcp ep)))
  :hints (("Goal" :in-theory (enable myif))))

;; (thm
;;  (IMPLIES (AND (JVM-STATEP S))
;;           (CALL-STACKP (POP-FRAME (BINDING 0 (THREAD-TABLE S)))))
;;  :hints (("Goal" :in-theory (enable JVM-STATEP))))

;(in-theory (disable BAG::MEMBERP-CAR-WHEN-DISJOINT)) ;bad rule

(defthm class-namep-of-first-non-member
  (implies (and (all-class-namesp items)
                (not (ACL2::SUBSETP-EQ items items-to-exclude))) ;ensures it finds an item
           (class-namep (acl2::first-non-member items items-to-exclude)))
  :hints (("Goal" :in-theory (enable ;all-class-namesp
                              ))))

(defthm all-class-namesp-of-reverse-list
  (equal (all-class-namesp (acl2::reverse-list x))
         (all-class-namesp x)))

(defthm all-bound-in-class-tablep-of-reverse-list
  (equal (all-bound-in-class-tablep (acl2::reverse-list x) class-table)
         (all-bound-in-class-tablep x class-table))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm bound-in-class-tablep-of-first-non-member
  (implies (and (all-bound-in-class-tablep class-names class-table)
                (acl2::first-non-member class-names class-names-to-exclude))
           (bound-in-class-tablep (acl2::first-non-member class-names class-names-to-exclude) class-table))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm first-non-member-iff
  (implies (all-class-namesp items)
           (iff (acl2::first-non-member items items-to-exclude)
                (not (acl2::subsetp-equal items items-to-exclude))))
  :hints (("Goal" :in-theory (enable acl2::subsetp-equal))))

(defthm subsetp-equal-of-reverse-list
  (equal (acl2::subsetp-equal (acl2::reverse-list x) y)
         (acl2::subsetp-equal x y))
  :hints (("Goal" :in-theory (enable acl2::subsetp-equal))))

(defthm jvm-statep-of-invoke-static-initializer-for-class
  (implies (and (class-namep class-to-initialize)
                (jvm-statep s)
;                (bound-in-class-tablep class-name (class-table s))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
;              (not (memberp class-name (initialized-classes s)))
                )
           (jvm-statep (invoke-static-initializer-for-class initialized-classes th s class-to-initialize)))
  :hints (("Goal" :in-theory (enable invoke-static-initializer-for-class))))

(defthm jvm-statep-of-invoke-static-initializer-for-next-class-helper
  (implies (and (class-namep class-name)
                (all-class-namesp superclass-names)
                (jvm-statep s)
                (bound-in-class-tablep class-name (class-table s))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
                (not (memberp class-name (initialized-classes s))))
           (jvm-statep (invoke-static-initializer-for-next-class-helper class-name superclass-names th s)))
  :hints (("Goal" :in-theory (enable invoke-static-initializer-for-next-class-helper))))

(defthm jvm-statep-of-invoke-static-initializer-for-next-class
  (implies (and (class-namep class-name)
                (jvm-statep s)
                (bound-in-class-tablep class-name (class-table s))
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
                (not (memberp class-name (initialized-classes s))))
           (jvm-statep (invoke-static-initializer-for-next-class class-name th s)))
  :hints (("Goal" :in-theory (enable invoke-static-initializer-for-next-class))))


;; ;in case bound-in-class-tablep is opened up
;; (defthm class-namep-when-in-of-rkeys
;;   (implies (and (SET::IN class-name (ACL2::RKEYS CLASS-TABLE))
;;                 (class-tablep class-table))
;;            (class-namep class-name))
;;   :hints (("Goal" :in-theory (enable class-tablep))))

(defthm jvm-statep-of-execute-java.lang.object.getclass
  (implies (and (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
;                (not (empty-call-stackp (binding th (thread-table s)))) ;new
                )
           (jvm-statep (execute-java.lang.object.getclass th s)))
  :hints (("Goal" :in-theory (e/d (execute-java.lang.object.getclass) (acons)))))

(defthm jvm-statep-of-execute-java.lang.class.getPrimitiveClass
  (implies (and (jvm-statep s)
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th)
;                (not (empty-call-stackp (binding th (thread-table s)))) ;new
                )
           (jvm-statep (execute-java.lang.class.getPrimitiveClass th s)))
  :hints (("Goal" :in-theory (e/d (execute-java.lang.class.getPrimitiveClass
                                   class-namep ;fixme breaks the abstraction
                                   ) (acons)))))

(defthm not-memberp-of-strip-cdrs-of-intern-table
  (implies (and (jvm-statep s)
                (not (set::in ad (acl2::rkeys (heap s)))))
           (not (memberp ad (strip-cdrs (intern-table s)))))
  :hints (("Goal" :in-theory (enable jvm-statep intern-table heap))))

(defthm-flag-build-multi-dim-array
 (defthm intern-table-okp-of-mv-nth-1-of-build-multi-dim-array
   (equal (intern-table-okp intern-table (mv-nth 1 (build-multi-dim-array counts array-type heap)))
          (intern-table-okp intern-table heap))
   :flag build-multi-dim-array)
 (defthm intern-table-okp-of-mv-nth-1-of-build-multi-dim-arrays
   (equal (intern-table-okp intern-table (mv-nth 1 (build-multi-dim-arrays counts array-type heap count)))
          (intern-table-okp intern-table heap))
   :flag build-multi-dim-arrays)
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :expand (build-multi-dim-array counts array-type heap))))

(defthm-flag-lookup-field
 (defthm not-equal-special-data-of-lookup-field
   (implies (and ;(lookup-field field-id c class-table ctr)
                 (class-tablep class-table)
                 (class-namep c)
             )
            (not (equal :special-data (lookup-field field-id c class-table ctr))))
   :flag lookup-field)
 (defthm not-equal-special-data-of-lookup-field-lst
   (implies (and ;(lookup-field-lst field-id class-or-interface-names class-table ctr)
                 (class-tablep class-table)
                 (all-class-namesp class-or-interface-names)
                 )
            (not (equal :special-data (lookup-field-lst field-id class-or-interface-names class-table ctr))))
   :flag lookup-field-lst)
 :hints (("Goal" :in-theory (enable lookup-field lookup-field-lst)
          :do-not '(generalize eliminate-destructors))))

;todo: prove this for throw-exception and then disable that
;fffixme: is this theorem really helpful for anything?  it's kind of nonsense without hyps saying that the stack looks right according to the instruction about to be executed...
(defthm jvm-statep-of-do-inst
  (implies (and (jvm-statep s)
;                (call-stack-non-emptyp th s)
                ;; (jvm-instruction-okayp inst (pc (thread-top-frame th s)) (strip-cars (program (thread-top-frame th s)))) ;fixme putback
;;                (not (empty-call-stackp (binding th (thread-table s)))) ;new
                (bound-in-alistp th (thread-table s))
                (thread-designatorp th))
           (jvm-statep (do-inst (op-code inst) inst th s)))
  :otf-flg t
  :hints (("goal" :do-not '(generalize eliminate-destructors)
;           :induct nil
           :in-theory (e/d (JVM-INSTRUCTION-OKAYP
                            resolve-class
                            resolve-non-array-class
                            failed-to-enter-monitor-wrapper
                            obtain-and-throw-exception
                            ;;thread-top-frame ;why?  don't we have rules about this (maybe later in the development)?
                            SKIP-INVOKESTATIC-INSTRUCTION
                            JVM-INSTRUCTIONP
;                            acl2::mv-nth-becomes-nth
                            ;JVM-STATEP
                            ;make-state
                            ;class-table
                            ;MONITOR-TABLE
                            ;;INITIALIZED-CLASSES
                            do-inst
                            execute-invokespecial
                            execute-invokespecial-helper
                            execute-invokestatic
                            execute-invokestatic-helper
                            execute-new
                            execute-invokevirtual
                            execute-invokevirtual-helper
                            resolve-field ; so we can see what exceptions/errors it throws
                            execute-java.lang.float.floattorawintbits
                            execute-java.lang.float.intbitstofloat
                            )
                           (acons
                            mv-nth
                            TRUE-LISTP
;                            MEMBERP-OF-CONS
                            ACL2::FIRST-NON-MEMBER-OF-APPEND
                            ; INTERFACEP ;seems needed
                            ;;INITIALIZED-CLASSES
                            bind-bind-diff-force
;                            resolve-field
                            ;INTERN-STRING ;fixme
;for speed:
;                                   OBJECTLOCKABLE?

;                                  LOCK-OBJECT
                            initialize-locals)))))

;ffffixme prove this after strenghthening framep to require that the pc is in the program and having jvm-instruction-okayp ensure that relative jumps are okay...
;; (thm
;;  (implies (and (jvm-statep s)
;;                (call-stack-non-emptyp th s)
;;                )
;;           (JVM-INSTRUCTION-OKAYP (ACL2::LOOKUP-EQUAL (PC (TOP-FRAME-of-thread TH S)) (PROGRAM (TOP-FRAME-of-thread TH S))) (PC (TOP-FRAME-of-thread TH S))))
;;  :hints (("Goal" :in-theory (enable jvm-statep call-stack-non-emptyp))))

(defthm jvm-statep-step
  (implies (and (jvm-statep s)
;                (call-stack-non-emptyp th s)
                (bound-in-alistp th (thread-table s)) ;now step ignores thread IDs that are not bound
                (thread-designatorp th) ;or step could ignore bad thread ids
                )
           (jvm-statep (step th s)))
  :hints (("goal" :in-theory (e/d (step) ( ;do-inst
                                          )))))

(acl2::defforall-simple thread-designatorp)

(defthm jvm-statep-run
  (implies (and (jvm-statep s)
                (acl2::all-thread-designatorp sched))
           (jvm-statep (run sched s)))
  :hints (("goal" :in-theory (e/d (run) ()))))

;move
(defthm addressp-of-myif (equal (jvm::addressp (myif test tp ep)) (myif test (addressp tp) (addressp ep))) :hints (("Goal" :in-theory (enable myif))))

(acl2::defopeners jvm::execute-invokestatic-helper :hyps ((syntaxp (quotep jvm::actual-class-name))))

(acl2::defopeners jvm::execute-invokespecial-helper
                  :hyps ((syntaxp (quotep jvm::closest-method-info))
                         (syntaxp (quotep jvm::actual-class-name))
                         (stringp jvm::actual-class-name))) ;exclude nil (which may occur if we can't resolve?)

(acl2::defopeners invoke-static-initializer-for-class :hyps ((syntaxp (quotep jvm::class-to-initialize))))

;; Only open if the class name and its super classes have been figured out:
(acl2::defopeners invoke-static-initializer-for-next-class-helper :hyps ((syntaxp (quotep jvm::class-name))
                                                                         (syntaxp (quotep jvm::superclass-names))))

;; Only open if the class name is a constant and is bound in the class-table (TODO: rephrase to not call 'g'?):
(acl2::defopeners invoke-static-initializer-for-next-class :hyps ((syntaxp (quotep jvm::class-name))
                                                                  (bound-in-class-tablep jvm::class-name (class-table jvm::s))))

;; Only open when method selection worked:
(acl2::defopeners jvm::execute-invokevirtual-helper :hyps ((syntaxp (quotep jvm::method-info))
                                                           (syntaxp (quotep jvm::class-name))))

(acl2::defopeners primitive-typep :hyps ((syntaxp (quotep type))))

(acl2::defopeners array-typep :hyps ((syntaxp (quotep type))))

;; Using this instead of jvm::execute-new prevents NEW from opening up if we
;; can't resolve the class, which can make things a lot cleaner.  TODO: We
;; could speed this up a bit by getting rid of the bound-in-class-tablep in the
;; RHS, since it is assumed as a hyp in this rule.  Creates
;; JVM::EXECUTE-NEW-BASE-OPENER-SAFE.  TODO: Remove the "BASE" from this name:
(acl2::defopeners jvm::execute-new
  :hyps ((jvm::bound-in-class-tablep (farg1 jvm::inst) (jvm::class-table jvm::s)))
  :suffix -opener-safe)

;todo: more like this
(defthm sbvlt32-of-0-and-fcmpg
  (implies (and (not (equal :float-nan value1))
                (not (equal :float-nan value2))
                (java-floatp value1)
                (java-floatp value2))
           (equal (acl2::sbvlt 32 0 (fcmpg value1 value2))
                  (float> value1 value2)))
  :hints (("Goal" :use (:instance float-trichotomy (x value1) (y value2)))))
