; flag.lisp -- Introduce induction scheme for mutually recursive functions.
; Sol Swords and Jared Davis {sswords,jared}@cs.utexas.edu

; Examples
#|
(include-book  ;; this newline is so that this is ignored in dependency scanning
 "tools/flag" :dir :system)

(FLAG::make-flag flag-pseudo-termp 
                 pseudo-termp
                 :flag-var flag
                 :flag-mapping ((pseudo-termp . term)
                                (pseudo-term-listp . list))
                 ;; :hints {for the measure theorem}
                 :defthm-macro-name defthm-pseudo-termp
                 ;; make everything local but the defthm macro
                 :local t 
                 )

; This introduces (flag-pseudo-termp flag x lst)
; Theorems equating it with pseudo-termp and pseudo-term-listp
; And the macro shown below.

(in-theory (disable (:type-prescription pseudo-termp)
                    (:type-prescription pseudo-term-listp)))

(defthm-pseudo-termp type-of-pseudo-termp
  (term (booleanp (pseudo-termp x))
        :rule-classes :rewrite 
        :doc nil)
  (list (booleanp (pseudo-term-listp lst))
        )
  :hints(("Goal" 
          :induct (flag-pseudo-termp flag x lst))))



(defstobj term-bucket
  (terms))

(mutual-recursion

 (defun terms-into-bucket (x term-bucket) 
   ;; Returns (mv number of terms added, term-bucket)
   (declare (xargs :stobjs (term-bucket)
                   :verify-guards nil))
   (cond ((or (atom x)
              (quotep x))
          (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
            (mv 1 term-bucket)))
         (t
          (mv-let (numterms term-bucket)
                  (terms-into-bucket-list (cdr x) term-bucket)
                  (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
                    (mv (+ numterms 1) term-bucket))))))

 (defun terms-into-bucket-list (x term-bucket)
   (declare (xargs :stobjs (term-bucket)))
   (if (atom x) 
       (mv 0 term-bucket)
     (mv-let (num-car term-bucket)
             (terms-into-bucket (car x) term-bucket)
             (mv-let (num-cdr term-bucket)
                     (terms-into-bucket-list (cdr x) term-bucket)
                     (mv (+ num-car num-cdr) term-bucket))))))

(terms-into-bucket '(f x y z) term-bucket)

(FLAG::make-flag flag-terms-into-bucket
                 terms-into-bucket)
|#                 



(in-package "FLAG")

(program)

(acl2::defmacro
 maybe-print-event-name (form name)
 `(with-output
   :off :all
   :stack :push
   (progn (with-output
           :stack :pop
           ,form)
          (value-triple
           (prog2$ (and (cadr (assoc t (table-alist 'print-event-names-table (w state))))
                        (cw "~x0~%" ',name))
                   ',name)))))

(acl2::defmacro
 defmacro (name &rest defmacro-args)
 `(maybe-print-event-name
   (acl2::defmacro ,name . ,defmacro-args)
   (acl2::defmacro ,name)))



(defmacro defthm (name &rest defthm-args)
  `(maybe-print-event-name
    (acl2::defthm ,name . ,defthm-args)
    (acl2::defthm ,name)))

(defmacro defun (name &rest defun-args)
  `(maybe-print-event-name
    (acl2::defun ,name . ,defun-args)
    (acl2::defun ,name)))

(defmacro verify-guards (name &rest verify-guards-args)
  `(maybe-print-event-name
    (acl2::verify-guards ,name . ,verify-guards-args)
    (acl2::verify-guards ,name)))

(defmacro defconst (name &rest defconst-args)
  `(maybe-print-event-name
    (acl2::defconst ,name . ,defconst-args)
    (acl2::defconst ,name)))

(defun replace-with-acl2-defuns (lst)
  (if (atom lst)
      nil
    (cons (cons 'acl2::defun (cdar lst))
          (replace-with-acl2-defuns (cdr lst)))))

(defun defun-names (lst)
  (if (atom lst)
      nil
    (cons (cadar lst)
          (defun-names (cdr lst)))))

(defmacro mutual-recursion (&rest defuns)
  `(maybe-print-event-name
    (acl2::mutual-recursion . ,(replace-with-acl2-defuns defuns))
    (acl2::mutual-recursion . ,(defun-names defuns))))

(table print-event-table nil nil
       :guard (and (eq acl2::key t)
                   (boolean-listp acl2::val)))


(defmacro print-event-names-push-on ()
  `(with-output
    :off :all
    (table print-event-names-table t
           (cons t (cdr (assoc t (table-alist 'print-event-names-table world)))))))

(defmacro print-event-names-push-off ()
  `(with-output
    :off :all
    (table print-event-names-table t
           (cons nil (cdr (assoc t (table-alist 'print-event-names-table world)))))))

(defmacro print-event-names-pop ()
  `(with-output
    :off :all
    (table print-event-names-table t
           (cddr (assoc t (table-alist 'print-event-names-table world))))))

(defmacro with-event-printing (onoff event)
  `(with-output
    :off :all :stack :push
    (progn ,(case onoff
              ((nil :off) '(print-event-names-push-off))
              (otherwise '(print-event-names-push-on)))
           (with-output :stack :pop ,event)
           (print-event-names-pop))))
  


(defmacro id (form) form)

(defun get-clique-members (fn world)
  (or (getprop fn 'recursivep nil 'current-acl2-world world)
      (er hard 'get-clique-members "Expected ~s0 to be in a mutually-recursive nest.~%"
          fn)))
  
(defun get-formals (fn world)
  (getprop fn 'formals nil 'current-acl2-world world))

(defun get-body (fn world)
  ;; This gets the original, normalized or non-normalized body based on what
  ;; the user typed for the :normalize xarg.  The use of "last" skips past 
  ;; any other :definition rules that have been added since then.
  (access def-body 
          (car (last (getprop fn 'def-bodies nil 'current-acl2-world world)))
          :concl))

(defun get-measure (fn world)
  (access justification
          (getprop fn 'justification nil 'current-acl2-world world)
          :measure))

(defun get-wfr (fn world)
  (access justification
          (getprop fn 'justification nil 'current-acl2-world world)
          :rel))

(defun make-flag-measure-aux (alist world)
  (cond ((and (consp alist)
              (consp (cdr alist)))
         (cons `(,(cdar alist) ,(get-measure (caar alist) world))
               (make-flag-measure-aux (cdr alist) world)))
        ((consp alist)
         (list `(otherwise ,(get-measure (caar alist) world))))
        (t 
         (er hard 'make-flag-measure-aux "Never get here."))))

(defun make-flag-measure (flag-var alist world)
  (declare (xargs :guard (symbolp flag-var)
                  :mode :program))
  `(case ,flag-var
     . ,(make-flag-measure-aux alist world)))

(defun merge-formals (alist world)
  (if (consp alist)
      (union-eq (get-formals (caar alist) world)
                (merge-formals (cdr alist) world))
    nil))

(defun merge-actuals (alist formals)
  ;; The alist has in it (orig-formal . actual) pairs.  Walk through formals 
  ;; and replace any orig-formal with its actual; replace any unbound new
  ;; formals with nil.
  (if (consp formals)
      (cons (cdr (assoc-eq (car formals) alist))
            (merge-actuals alist (cdr formals)))
    nil))

(mutual-recursion 

 (defun mangle-body (body fn-name alist formals world)
   (cond ((atom body)
          body)
         ((eq (car body) 'quote)
          body)
         ((symbolp (car body))
          (let ((lookup   (assoc-eq (car body) alist))
                (new-args (mangle-body-list (cdr body) fn-name alist formals world)))
            (if lookup
                (let* ((orig-formals (get-formals (car lookup) world))
                       (new-actuals (merge-actuals (pairlis$ orig-formals new-args) formals)))
                  `(,fn-name ',(cdr lookup) . ,new-actuals))
              (cons (car body) new-args))))
         (t
          (let ((lformals (cadar body))
                (lbody    (caddar body))
                (largs    (cdr body)))
            (cons (list 'lambda 
                        lformals
                        (mangle-body lbody  fn-name alist formals world))
                  (mangle-body-list largs fn-name alist formals world))))))

 (defun mangle-body-list (list fn-name alist formals world)
   (if (consp list)
       (cons (mangle-body (car list) fn-name alist formals world)
             (mangle-body-list (cdr list) fn-name alist formals world))
     nil)))


(defun make-flag-body-aux (fn-name formals alist full-alist world)
  (if (consp alist)
      (let* ((orig-body (get-body (caar alist) world))
             (new-body (mangle-body orig-body fn-name full-alist formals world)))
        (cond ((consp (cdr alist))
               (cons `(,(cdar alist) ,new-body)
                     (make-flag-body-aux fn-name formals (cdr alist) full-alist world)))
              (t
               (list `(otherwise ,new-body)))))
    (er hard 'make-flag-body-aux "Never get here.")))

(defun make-flag-body (fn-name flag-var alist hints world)
  (let ((formals (merge-formals alist world)))
  `(defun ,fn-name (,flag-var . ,formals)
     (declare (xargs :verify-guards nil
                     :normalize nil
                     :measure ,(make-flag-measure flag-var alist world)
                     :non-executable t
                     :hints ,hints
                     :well-founded-relation ,(get-wfr (caar alist)
                                                      world)
                     :mode :logic)
              (ignorable . ,formals))
     (case ,flag-var
       . 
       ,(make-flag-body-aux fn-name formals alist alist world)))))
     
(defun extract-keyword-from-args (kwd args)
  (if (consp args)
      (if (eq (car args) kwd)
          (if (consp (cdr args))
              (cadr args)
            (er hard "Expected something to follow ~s0.~%" kwd))
        (extract-keyword-from-args kwd (cdr args)))
    nil))

(defun throw-away-keyword-parts (args)
  (if (consp args)
      (if (keywordp (car args))
          nil
        (cons (car args)
              (throw-away-keyword-parts (cdr args))))
    nil))

(defun pair-up-cases-with-thmparts (alist thmparts)
  ;; Each thmpart is an thing like (flag <thm-body> :name ... :rule-classes ... :doc ...)
  (if (consp alist)
      (let* ((flag   (cdar alist))
             (lookup (assoc-eq flag thmparts)))
        (if (not lookup)
            (er hard 'pair-up-cases-with-thmparts 
                "Expected there to be a case for the flag ~s0.~%" flag)
          (if (consp (cdr alist))
              (cons `(,flag ,(cadr lookup))
                    (pair-up-cases-with-thmparts (cdr alist) thmparts))
            (list `(otherwise ,(cadr lookup))))))
    (er hard 'pair-up-cases-with-thmparts
        "Never get here.")))

(defun make-defthm-macro-fn-aux (name flag-var alist thmparts)
  ;; We have just proven the lemma and it's time to instantiate it to 
  ;; give us each thm.
  (if (consp alist)
      (let* ((flag (cdar alist))
             (lookup (assoc-eq flag thmparts)))
        ;; Not checking for lookup, already did it when we did cases.
        (let ((this-name (or (extract-keyword-from-args :name (cddr lookup))
                             (intern-in-package-of-symbol 
                              (concatenate 'string 
                                           (symbol-name name)
                                           "-"
                                           (symbol-name flag))
                              name)))
              (rule-classes (let ((mem (member :rule-classes (cddr lookup))))
                              (if mem (cadr mem) :rewrite)))
              (doc          (extract-keyword-from-args :doc (cddr lookup)))
              (skip (extract-keyword-from-args :skip (cddr lookup))))
          (if skip
              (make-defthm-macro-fn-aux name flag-var (cdr alist) thmparts)
            (cons `(defthm ,this-name
                     ,(cadr lookup)
                     :rule-classes ,rule-classes
                     :doc ,doc
                     :hints(("Goal" 
                             :in-theory (theory 'minimal-theory)
                             :use ((:instance ,name (,flag-var ',flag))))))
                  (make-defthm-macro-fn-aux name flag-var (cdr alist) thmparts)))))
    nil))

(defun make-defthm-macro-fn (name args alist flag-var)
  (let ((thmparts (throw-away-keyword-parts args)))
    `(progn
       (encapsulate
        ()
        (local (defthm ,name
                 (case ,flag-var . ,(pair-up-cases-with-thmparts alist thmparts))
                 :rule-classes nil
                 ;; user must give induction scheme.  lolol.
                 :hints ,(extract-keyword-from-args :hints args)
                 :instructions ,(extract-keyword-from-args :instructions args)
                 :otf-flg ,(extract-keyword-from-args :otf-flg args)))
      
        . ,(make-defthm-macro-fn-aux name flag-var alist thmparts))
       (value-triple ',name))))

(defun make-defthm-macro (real-macro-name alist flag-var)
  `(defmacro ,real-macro-name (name &rest args)
     (declare (xargs :guard (symbolp name)))
     (make-defthm-macro-fn name args ',alist ',flag-var)))

(defun make-cases-for-equiv (alist world)
  (if (consp alist)
      (let* ((fn   (caar alist))
             (flag (cdar alist))
             (fn-formals (get-formals fn world)))
        (if (consp (cdr alist))
            (cons `(,flag (,fn . ,fn-formals))
                  (make-cases-for-equiv (cdr alist) world))
          (list `(otherwise (,fn . ,fn-formals)))))
    nil))


;; Collects up any calls of functions listed in FNS that are present in x.
(mutual-recursion
 (defun find-calls-of-fns-term (x fns acc)
   (cond ((or (atom x) (eq (car x) 'quote)) acc)
         ((member-eq (car x) fns)
          (find-calls-of-fns-list (cdr x) fns (cons x acc)))
         (t
          (find-calls-of-fns-list (cdr x) fns acc))))
 (defun find-calls-of-fns-list (x fns acc)
   (if (atom x)
       acc
     (find-calls-of-fns-term
      (car x) fns
      (find-calls-of-fns-list (cdr x) fns acc)))))

;; Gives an expand hint for any function in FNS present in the
;; conclusion of the clause.
(defun expand-calls-computed-hint (clause fns)
 (let ((expand-list (find-calls-of-fns-term (car (last clause)) fns nil)))
   `(:expand ,expand-list)))


(defun flag-table-events (alist entry)
  (if (atom alist)
      nil
    (cons `(table flag-fns ',(caar alist) ',entry)
          (flag-table-events (cdr alist) entry))))

(defun make-flag-fn (flag-fn-name clique-member-name flag-var flag-mapping hints 
                                  defthm-macro-name local world)
  (let* ((flag-var (or flag-var 
                       (intern-in-package-of-symbol "FLAG" flag-fn-name)))
         (alist (or flag-mapping
                    (pairlis$ (get-clique-members clique-member-name world)
                              (get-clique-members clique-member-name world))))
         (defthm-macro-name (or defthm-macro-name
                                (intern-in-package-of-symbol 
                                 (concatenate 'string "DEFTHM-" (symbol-name flag-fn-name))
                                 flag-fn-name)))
         (equiv-thm-name (intern-in-package-of-symbol 
                          (concatenate 'string (symbol-name flag-fn-name) "-EQUIVALENCES")
                          flag-fn-name))
         (formals        (merge-formals alist world)))
    `(,@(if local '(progn) '(encapsulate nil))
      ;; use encapsulate instead of progn so set-ignore-ok is local to this
      (logic)
      ,@(and (not local) '((set-ignore-ok t))) ;; can't wrap this in local --- fubar!

      (,(if local 'local 'id)
       ,(make-flag-body flag-fn-name flag-var alist hints world))
      ,(make-defthm-macro defthm-macro-name alist flag-var)

      (,(if local 'local 'id)
       (with-output
        :off prove ;; hides induction scheme, too
        (encapsulate nil
          (logic)
          (defthm ,equiv-thm-name
            (equal (,flag-fn-name ,flag-var . ,formals)
                   (case ,flag-var
                     ,@(make-cases-for-equiv alist world)))
            :hints (("Goal"
                     :induct 
                     (,flag-fn-name ,flag-var . ,formals)
                     :in-theory 
                     (set-difference-theories 
                      (union-theories (theory 'minimal-theory)
                                      '((:induction ,flag-fn-name)))
                      ;; Jared found a case where "linear" forced some goals
                      ;; from an equality, which were unprovable.  So, turn off
                      ;; forcing.
                      '((:executable-counterpart force))))
                    (and stable-under-simplificationp
                         (expand-calls-computed-hint ACL2::clause
                                                     ',(cons flag-fn-name
                                                             (strip-cars alist)))))))))
      
      (progn . ,(flag-table-events alist `(,flag-fn-name
                                           ,alist 
                                           ,defthm-macro-name
                                           ,equiv-thm-name)))
      (,(if local 'local 'id)
       (in-theory (disable (:definition ,flag-fn-name)))))))
        
(defmacro make-flag (flag-fn-name clique-member-name 
                     &key
                     flag-var
                     flag-mapping 
                     hints
                     defthm-macro-name
                     local)
  `(make-event (make-flag-fn ',flag-fn-name 
                             ',clique-member-name 
                             ',flag-var
                             ',flag-mapping 
                             ',hints
                             ',defthm-macro-name
                             ',local
                             (w state))))


;; Accessors for the records stored in the flag-fns table
(defun flag-present (fn world)
  (consp (assoc-eq fn (table-alist 'flag::flag-fns world))))

(defun flag-fn-name (fn world)
  (nth 0 (cdr (assoc-eq fn (table-alist 'flag::flag-fns world)))))

(defun flag-alist (fn world)
  (nth 1 (cdr (assoc-eq fn (table-alist 'flag::flag-fns world)))))

(defun flag-defthm-macro (fn world)
  (nth 2 (cdr (assoc-eq fn (table-alist 'flag::flag-fns world)))))

(defun flag-equivs-name (fn world)
  (nth 3 (cdr (assoc-eq fn (table-alist 'flag::flag-fns world)))))





(logic) ;; so local events aren't skipped

(local 

; A couple tests to make sure things are working.

 (encapsulate
  ()
  
  (FLAG::make-flag flag-pseudo-termp 
                   pseudo-termp
                   :flag-var flag
                   :flag-mapping ((pseudo-termp . term)
                                  (pseudo-term-listp . list))
                   ;; :hints {for the measure theorem}
                   :defthm-macro-name defthm-pseudo-termp
                   )
  
; This introduces (flag-pseudo-termp flag x lst)
; Theorems equating it with pseudo-termp and pseudo-term-listp
; And the macro shown below.

  (in-theory (disable (:type-prescription pseudo-termp)
                      (:type-prescription pseudo-term-listp)))
  
  (defthm-pseudo-termp type-of-pseudo-termp
    (term (booleanp (pseudo-termp x))
          :rule-classes :rewrite 
          :doc nil)
    (list (booleanp (pseudo-term-listp lst))
          )
    :hints(("Goal" 
            :induct (flag-pseudo-termp flag x lst))))



  (defstobj term-bucket
    (terms))

  (mutual-recursion

   (defun terms-into-bucket (x term-bucket) 
     ;; Returns (mv number of terms added, term-bucket)
     (declare (xargs :stobjs (term-bucket)
                     :verify-guards nil))
     (cond ((or (atom x)
                (quotep x))
            (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
              (mv 1 term-bucket)))
           (t
            (mv-let (numterms term-bucket)
                    (terms-into-bucket-list (cdr x) term-bucket)
                    (let ((term-bucket (update-terms (cons x (terms term-bucket)) term-bucket)))
                      (mv (+ numterms 1) term-bucket))))))

   (defun terms-into-bucket-list (x term-bucket)
     (declare (xargs :stobjs (term-bucket)))
     (if (atom x) 
         (mv 0 term-bucket)
       (mv-let (num-car term-bucket)
               (terms-into-bucket (car x) term-bucket)
               (mv-let (num-cdr term-bucket)
                       (terms-into-bucket-list (cdr x) term-bucket)
                       (mv (+ num-car num-cdr) term-bucket))))))

  (FLAG::make-flag flag-terms-into-bucket
                   terms-into-bucket)


  ;; previously this didn't work, now we set-ignore-ok to fix it.
  (encapsulate
   ()
   (set-ignore-ok t)
   (mutual-recursion
    (defun ignore-test-f (x)
      (if (consp x)
          (let ((y (+ x 1)))
            (ignore-test-g (cdr x)))
        nil))
    (defun ignore-test-g (x)
      (if (consp x)
          (ignore-test-f (cdr x))
        nil))))

  (FLAG::make-flag flag-ignore-test
                   ignore-test-f)

  ))
