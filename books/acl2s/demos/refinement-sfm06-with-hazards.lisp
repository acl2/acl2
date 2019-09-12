(in-package "ACL2")
(include-book "acl2/utilities" :dir :system)
#|
This is the weak defun-sk macro.  I only thought about existential
quantification.  Do a macro-expansion to see what it produces, but
essentially it produces a function with only one constraint: this
allows you to prove the function is non-nil if you can exhibit a
witness.  Many times that is all one needs.

|#

(defmacro defun-weak-sk (name args body &key doc quant-ok
  skolem-name thm-name rewrite)
  (let* ((exists-p (and (true-listp body)
                        (symbolp (car body))
                        (equal (symbol-name (car body)) "EXISTS")))
         (bound-vars (let ((var-lst (cadr body)))
                       (and (true-listp body)
                            (or (symbolp var-lst)
                                (true-listp var-lst))
                            (cond ((atom var-lst)
                                   (list var-lst))
                                  (t var-lst)))))
         (body-guts (and (true-listp body) (caddr body)))
         (skolem-name
          (or skolem-name
              (acl2s::fix-intern-in-pkg-of-sym
               (concatenate 'string (symbol-name name) "-WITNESS")
               name)))
         (skolem-constraint-name
          (acl2s::fix-intern-in-pkg-of-sym
           (concatenate 'string (symbol-name skolem-name) "-CONSTRAINT")
           skolem-name))
         (thm-name
          (or thm-name
              (acl2s::fix-intern-in-pkg-of-sym
               (concatenate 'string (symbol-name name)
                            (if exists-p "-SUFF" "-NECC"))
               name)))
         (msg (non-acceptable-defun-sk-p name args body
  quant-ok rewrite exists-p nil nil)))
    (if msg
        `(er soft '(defun-sk . ,name)
             "~@0"
             ',msg)
      `(encapsulate
        ((,name ,args ,(if (= (length bound-vars) 1)
                           (car bound-vars)
                         (cons 'mv bound-vars))))
        (local 
         (encapsulate                
          ((,skolem-name ,args
                         ,(if (= (length bound-vars) 1)
                              (car bound-vars)
                            (cons 'mv bound-vars))))
          (local (in-theory '(implies)))
          (local
           (defchoose ,skolem-name ,bound-vars ,args
             ,(if exists-p
                  body-guts
                `(not ,body-guts))))

               ; A :type-prescription lemma is needed in the case of more than one bound
           ; variable, in case we want to do guard proofs.
          
        ; PETE: I am leaving this because it comes from defun-sk, but
        ; notice that it is not very useful because this theorem will
        ; not exists outside the main encapsulate.  I should either
        ; prove it's analogue in the surrounding encapsulate or I
        ; should delete it.  This seems kind of kludgy, e.g., why not
        ; prove that what you get is a true-list of the right size?
        ; Perhaps I should just blow up (exists (a ... n) body) into
        ; (exists (a) ... (exists (n) body) ... )?

          ,@(cond 
             ((null (cdr bound-vars)) nil)
             (t
              `((local (defthm ,(acl2s::fix-intern-in-pkg-of-sym
                                 (concatenate 'string (symbol-name skolem-name) "-TYPE-PRESCRIPTION")
                                 skolem-name)
                         (true-listp ,(cons skolem-name args))
                         :rule-classes :type-prescription
                         :hints (("Goal" :by ,skolem-name)))))))
          (defthm ,skolem-constraint-name
            (implies ,body-guts
                     ,(if (= (length bound-vars) 1)
                          `(let ((,(car bound-vars) (,skolem-name ,@args)))
                             ,body-guts)
                        `(mv-let (,@bound-vars)
                                 (,skolem-name ,@args)
                                 ,body-guts)))
            :hints (("Goal"
                     :use ,skolem-name))
            :rule-classes nil)))
        (local 
         (defun ,name ,args (declare (xargs :normalize nil))
           ,(if (= (length bound-vars) 1)
                `(let ((,(car bound-vars) (,skolem-name ,@args)))
                   ,body-guts)
              `(mv-let (,@bound-vars)
                       (,skolem-name ,@args)
                       ,body-guts))))
        (defthm ,thm-name
          ,(if exists-p
               `(implies ,body-guts
                         (,name ,@args))
             `(implies (not ,body-guts)
                       (not (,name ,@args))))
          :hints (("Goal" 
                   :in-theory nil
                   :use ((:instance ,skolem-constraint-name)
                         (:instance ,name)))))

        ; PETE: The above was added to make sure that nothing
        ; interferes with the proof (e.g., function definitions and
        ; rewrites).  I wanted to add the above rule as a
        ; forward-chaining rule, but due to the free variable problem,
        ; but since I don't want to explore body-guts (to figure out
        ; what the trigger-terms should be), I can't.

        ,@(if doc
              `((defdoc ,name ,doc))
            nil)))))


#|

This is a set of macros for relating an abstract system and a concrete
system with a WEB.  The systems are deterministic.

Compare with macro.old.lisp, which was a first attempt and which
motivated the defun-weak-sk macro.

I should use a macro to customize the names of theorems.


(defun bor-macro (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (if (consp (cdr lst))
          (list 'if
                (car lst)
                t
                (bor-macro (cdr lst)))
        (car lst))
    nil))

(defmacro bor (&rest args)
  (bor-macro args))

; The reason for the bor macro is that (or a b) gets expanded to (if a
; a b).  This results in extra rewriting in many situations.  bor is
; equivalent to or if all the arguments are booleans.

; Generate-Full-System is given abs-step, the function that steps the
; abstract system for one step, abs-p, the predicate that recognizes
; abstract states, con-step, the function that steps the concrete
; system for one step, con-p, the predicate that recognizes concrete
; states, and con-rank, the rank of a concrete state.  Note that I am
; assuming that the step of abstract and concrete states depends only
; on the state.  There may be situations in which this is not the
; case.  If so, these macros will have to be altered somewhat.  Also,
; I am assuming that the rank of abstract states is 0.  This may also
; not be the case in general.  R, B, rank, and take-appropriate-step
; should be undefined. 
|#

(defmacro generate-full-system (abs-step abs-p con-step con-p 
                                con-to-abs good-con con-rank)
  `(progn 

     (defun WF-rel (x y) 
       (declare (xargs :normalize nil))
       (and (,abs-p x)
            (,con-p y)
            (,good-con y)
            (equal x (,con-to-abs y))))

     (defun B (x y) 
       (declare (xargs :normalize nil))
       (or (WF-rel x y)
           (WF-rel y x)
           (equal x y)
           (and (,con-p x)
                (,con-p y)
                (,good-con x)
                (,good-con y)
                (equal (,con-to-abs x)
                       (,con-to-abs y)))))

     (defun rank (x) 
       (declare (xargs :normalize nil))
       (if (,con-p x)
           (,con-rank x)
         0))

     (defun R (x y)
       (declare (xargs :normalize nil))
       (cond ((,abs-p x)
              (equal y (,abs-step x)))
             (t (equal y (,con-step x)))))

     (encapsulate 
      ()
      (local (in-theory nil))

      (defthm WF-rel-fc
        (equal (Wf-rel x y)
               (and (,abs-p x)
                    (,con-p y)
                    (,good-con y)
                    (equal x (,con-to-abs y))))
        :hints (("goal" :by Wf-rel))
        :rule-classes ((:forward-chaining :trigger-terms ((Wf-rel x y)))))

      (defthm B-fc
        (equal (B x y) 
               (or (WF-rel x y)
                   (WF-rel y x)
                   (equal x y)
                   (and (,con-p x)
                        (,con-p y)
                        (,good-con x)
                        (,good-con y)
                        (equal (,con-to-abs x)
                               (,con-to-abs y)))))
        :hints (("goal" :by B))
        :rule-classes ((:forward-chaining :trigger-terms ((B x y)))))
        
      (defthm rank-fc
        (equal (rank x) 
               (if (,con-p x)
                   (,con-rank x)
                 0))
        :hints (("goal" :by rank))
        :rule-classes ((:forward-chaining :trigger-terms ((rank x)))))

      (defthm R-fc 
        (equal (R x y)
               (cond ((,abs-p x)
                      (equal y (,abs-step x)))
                     (t (equal y (,con-step x)))))
        :hints (("goal" :by R))
        :rule-classes ((:forward-chaining :trigger-terms ((R x y)))))


;note that if I fix the free variable problem, the forward
;chaining rules for defun-sk's won't be necessary.  Also, for the
;fix to constraints I discusses with J will make the
;forward-chaining definition rules unnecessary, so everything in
;the encapsulate is irrelevant
      )
     )
  )

(defmacro prove-web (abs-step abs-p con-step con-p con-to-abs con-rank)
  `(progn
     (defthm B-is-a-WF-bisim-core
       (let ((u (,abs-step s))
             (v (,con-step w)))
         (implies (and (WF-rel s w)
                       (not (WF-rel u v)))
                  (and (WF-rel s v)
                       (o< (,con-rank v) 
                           (,con-rank w))))))

     (in-theory (disable b-is-a-wf-bisim-core))

     (defthm con-to-abs-type
       (,abs-p (,con-to-abs x)))

     (defthm abs-step-type
       (,abs-p (,abs-step x)))

     (defthm con-step-type
       (,con-p (,con-step x)))

     (defthm con-not-abs 
       (implies (,con-p x)
                (not (,abs-p x))))

     (defthm abs-not-con
       (implies (,abs-p x)
                (not (,con-p x))))))

(defmacro wrap-it-up (abs-step abs-p con-step con-p good-con con-to-abs con-rank)
  `(encapsulate
    ()

    (encapsulate 
     ()
     (local (in-theory nil))

     (local (in-theory (enable abs-step-type con-step-type con-not-abs abs-not-con 
                               con-to-abs-type
                               Wf-rel-fc B-fc
                               b-is-a-wf-bisim-core)))
    
     (defequiv b
       :hints (("goal" 
                :by (:functional-instance
                     encap-B-is-an-equivalence
  
                     (encap-abs-step ,abs-step)
                     (encap-abs-p ,abs-p)
                     (encap-con-step ,con-step)
                     (encap-con-p ,con-p)
                     (encap-con-to-abs ,con-to-abs)
                     (encap-good-con ,good-con)
                     (encap-con-rank ,con-rank)
                    
                     (encap-wf-rel wf-rel)
                     (encap-B B))))))
     
    (defthm rank-well-founded 
      (o-p (rank x)))

    (defun-weak-sk exists-w-succ-for-u-weak (w u)
      (exists (v)
        (and (R w v)
             (B u v))))

    (defun-weak-sk exists-w-succ-for-s-weak (w s)
      (exists (v)
        (and (R w v)
             (B s v)
             (o< (rank v) (rank w)))))

    (encapsulate 
     ()
     (local (in-theory nil))

     (defthm exists-w-succ-for-u-weak-fc
       (implies (and (R w v)
                     (B u v))
                (exists-w-succ-for-u-weak w u))
       :hints (("goal" :by exists-w-succ-for-u-weak-suff))
       :rule-classes ((:forward-chaining 
                       :trigger-terms ((r w v) (b u v)
                                       (exists-w-succ-for-u-weak w u)))))

     (defthm exists-w-succ-for-s-weak-fc
       (implies (and (R w v)
                     (B s v)
                     (o< (rank v) (rank w)))
                (exists-w-succ-for-s-weak w s))
       :hints (("goal" :by exists-w-succ-for-s-weak-suff))
       :rule-classes ((:forward-chaining 
                       :trigger-terms ((r w v) (b s v)
                                       (exists-w-succ-for-s-weak w s))))))

    (local (in-theory nil))

    (local (in-theory (enable abs-step-type con-step-type con-not-abs abs-not-con 
                              con-to-abs-type
                              exists-w-succ-for-s-weak-fc exists-w-succ-for-u-weak-fc
                              R-fc Wf-rel-fc B-fc rank-fc 
                              b-is-a-wf-bisim-core)))
    
    (defthm b-is-a-wf-bisim-weak
      (implies (and (b s w)
                    (r s u))
               (or (exists-w-succ-for-u-weak w u)
                   (and (b u w)
                        (o< (rank u) (rank s)))
                   (exists-w-succ-for-s-weak w s)))
      :hints (("goal" 
               :by (:functional-instance
                    B-is-a-WF-bisim-sk
                    
                    (encap-abs-step ,abs-step)
                    (encap-abs-p ,abs-p)
                    (encap-con-step ,con-step)
                    (encap-con-p ,con-p)
                    (encap-con-to-abs ,con-to-abs)
                    (encap-good-con ,good-con)
                    (encap-con-rank ,con-rank)
                    
                    (encap-R R)
                    (encap-wf-rel wf-rel)
                    (encap-B B)
                    (encap-rank rank)
                    
                    (encap-exists-w-succ-for-u exists-w-succ-for-u-weak)
                    (encap-exists-w-succ-for-s exists-w-succ-for-s-weak))))
      :rule-classes nil)

    (defun-sk exists-w-succ-for-u (w u)
      (exists (v)
        (and (R w v)
             (B u v))))

    (defun-sk exists-w-succ-for-s (w s)
      (exists (v)
        (and (R w v)
             (B s v)
             (o< (rank v) (rank w)))))

    (local (in-theory nil))
    (local (in-theory (enable exists-w-succ-for-s-suff exists-w-succ-for-u-suff)))

    (defthm b-is-a-wf-bisim
      (implies (and (b s w)
                    (r s u))
               (or (exists-w-succ-for-u w u)
                   (and (b u w)
                        (o< (rank u) (rank s)))
                   (exists-w-succ-for-s w s)))
      :hints (("goal" 
               :by (:functional-instance
                    B-is-a-WF-bisim-weak
                    
                    (exists-w-succ-for-u-weak exists-w-succ-for-u)
                    (exists-w-succ-for-s-weak exists-w-succ-for-s))))
      :rule-classes nil)
    )
  )


#|
(defun bor-macro (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (if (consp (cdr lst))
          (list 'if
                (car lst)
                t
                (bor-macro (cdr lst)))
        (car lst))
    nil))

(defmacro bor (&rest args)
  (bor-macro args))
|#

(encapsulate
 ((encap-abs-step (abs) t)
  (encap-abs-p (abs) t)
  (encap-con-step (con) t)
  (encap-con-p (con) t)
  (encap-con-to-abs (con) t)
  (encap-good-con (con) t)
  (encap-con-rank (con) t))
 
 (local (defun encap-abs-step (abs)
          (declare (ignore abs))
          t))
 
 (local (defun encap-abs-p (abs)
          (equal abs t)))
 
 (local (defun encap-con-step (con)
          (declare (ignore con))
          nil))
 
 (local (defun encap-con-p (con)
          (equal con nil)))
 
 (local (defun encap-con-to-abs (con)
          (declare (ignore con))
          t))
 
 (local (defun encap-good-con (con)
          (declare (ignore con))
          t))
 
 (local (defun encap-con-rank (con)
          (declare (ignore con))
          0))
 
 (defun encap-WF-rel (x y) 
   (and (encap-abs-p x) ;not needed, but helps with case analysis
        (encap-con-p y)
        (encap-good-con y)
        (equal x (encap-con-to-abs y))))

 (defthm encap-B-is-a-WF-bisim-core
   (let ((u (encap-abs-step s))
         (v (encap-con-step w)))
     (implies (and (encap-wf-rel s w)
                   (not (encap-wf-rel u v)))
              (and (encap-wf-rel s v)
                   (o< (encap-con-rank v) 
                       (encap-con-rank w)))))
   :rule-classes nil)
 
 (defthm encap-abs-step-type
   (encap-abs-p (encap-abs-step x)))
 
 (defthm encap-con-step-type
   (encap-con-p (encap-con-step x)))

 (defthm encap-con-not-abs
   (implies (encap-con-p x)
            (not (encap-abs-p x))))
 
 (defthm encap-abs-not-con
   (implies (encap-abs-p x)
            (not (encap-con-p x))))

 (defthm encap-con-to-abs-type 
   (encap-abs-p (encap-con-to-abs x)))
 )

(defun encap-R (x y)
  (cond ((encap-abs-p x)
         (equal y (encap-abs-step x)))
        (t (equal y (encap-con-step x)))))

(defun encap-B (x y)
  (or (encap-WF-rel x y)
      (encap-WF-rel y x)
      (equal x y)
      (and (encap-con-p x)
           (encap-con-p y)
           (encap-good-con x)
           (encap-good-con y)
           (equal (encap-con-to-abs x)
                  (encap-con-to-abs y)))))
 
(defequiv encap-B)

(defun encap-rank (x) 
  (if (encap-con-p x)
      (encap-con-rank x)
    0))
 
(defun encap-take-appropriate-step (w)
  (cond ((encap-abs-p w)
         (encap-abs-step w))
        (t (encap-con-step w))))

(defthm encap-B-is-a-WF-bisim-0
  (implies (and (encap-WF-rel s w)
                (encap-R s u))
           (or (encap-B u (encap-take-appropriate-step w))
               (and (encap-B u w)
                    (o< (encap-rank u) (encap-rank s)))
               (and (encap-B s (encap-take-appropriate-step w))
                    (o< (encap-rank (encap-take-appropriate-step w)) 
                        (encap-rank w)))))
  :hints (("goal" 
           :use (:instance encap-B-is-a-WF-bisim-core)))
  :rule-classes nil)

(defthm encap-B-is-a-WF-bisim-1
  (implies (and (encap-WF-rel w s)
                (encap-R s u))
           (or (encap-B u (encap-take-appropriate-step w))
               (and (encap-B u w)
                    (o< (encap-rank u) (encap-rank s)))
               (and (encap-B s (encap-take-appropriate-step w))
                    (o< (encap-rank (encap-take-appropriate-step w)) 
                        (encap-rank w)))))
  :hints (("goal" 
           :use (:instance encap-B-is-a-WF-bisim-core (s w) (w s))))
  :rule-classes nil)

(defthm encap-B-is-a-WF-bisim-2
  (implies (and (equal s w)
                (encap-R s u))
           (or (encap-B u (encap-take-appropriate-step w))
               (and (encap-B u w)
                    (o< (encap-rank u) (encap-rank s)))
               (and (encap-B s (encap-take-appropriate-step w))
                    (o< (encap-rank (encap-take-appropriate-step w)) 
                        (encap-rank w)))))
  :rule-classes nil)

(defthm encap-B-is-a-WF-bisim-3
  (implies (and (encap-con-p s)
                (encap-con-p w)
                (encap-good-con s)
                (encap-good-con w)
                (equal (encap-con-to-abs s)
                       (encap-con-to-abs w))
                (encap-R s u))
           (or (encap-B u (encap-take-appropriate-step w))
               (and (encap-B u w)
                    (o< (encap-rank u) (encap-rank s)))
               (and (encap-B s (encap-take-appropriate-step w))
                    (o< (encap-rank (encap-take-appropriate-step w)) 
                        (encap-rank w)))))
  :hints (("goal" 
           :use ((:instance encap-B-is-a-WF-bisim-core (w (encap-con-to-abs s)))
                 (:instance encap-B-is-a-WF-bisim-core (s (encap-con-to-abs w)))
                 (:instance encap-B-is-a-WF-bisim-core (w s) (s (encap-con-to-abs w)))
                 (:instance encap-B-is-a-WF-bisim-core (w (encap-con-to-abs w)) (s w)))))
  :rule-classes nil)

(defthm encap-B-is-a-WF-bisim
  (implies (and (encap-B s w)
                (encap-R s u))
           (or (encap-B u (encap-take-appropriate-step w))
               (and (encap-B u w)
                    (o< (encap-rank u) (encap-rank s)))
               (and (encap-B s (encap-take-appropriate-step w))
                    (o< (encap-rank (encap-take-appropriate-step w)) 
                        (encap-rank w)))))
  :hints (("goal" 
           :use ((:instance encap-b (x s) (y w))
                 (:instance encap-B-is-a-WF-bisim-0)
                 (:instance encap-B-is-a-WF-bisim-1)
                 (:instance encap-B-is-a-WF-bisim-2)
                 (:instance encap-B-is-a-WF-bisim-3))
           :in-theory (disable encap-wf-rel encap-r 
                               encap-take-appropriate-step encap-rank o< encap-b)))
  :rule-classes nil)

(defun-weak-sk encap-exists-w-succ-for-u (w u)
  (exists (v)
    (and (encap-R w v)
         (encap-B u v))))

(defun-weak-sk encap-exists-w-succ-for-s (w s)
  (exists (v)
    (and (encap-R w v)
         (encap-B s v)
         (o< (encap-rank v) (encap-rank w)))))

(defthm R-take-step
  (encap-R w (encap-take-appropriate-step w)))

(in-theory (disable encap-B encap-R encap-rank encap-take-appropriate-step))

(defthm B-is-a-WF-bisim-sk
  (implies (and (encap-B s w)
                (encap-R s u))
           (or (encap-exists-w-succ-for-u w u)
               (and (encap-B u w)
                    (o< (encap-rank u) (encap-rank s)))
               (encap-exists-w-succ-for-s w s)))
  :hints (("goal" 
           :use ((:instance encap-B-is-a-WF-bisim)
                 (:instance encap-exists-w-succ-for-u-suff 
                            (v (encap-take-appropriate-step w)))
                 (:instance encap-exists-w-succ-for-s-suff 
                            (v (encap-take-appropriate-step w))))))
  :rule-classes nil)

(include-book "arithmetic/top-with-meta" :dir :system)

(defun seq-macro (st pairs)
  (if (endp pairs)
      st
    (list 's 
          (car pairs) 
          (cadr pairs) 
          (if (endp (cddr pairs))
              st
            (seq-macro st (cddr pairs))))))

(defun up-macro (pairs ans)
  (if (endp pairs)
      ans
    (up-macro (cddr pairs) `(s ,(car pairs)
                               ,(cadr pairs)
                               ,ans))))
        
(defmacro seq (st &rest pairs)
  (seq-macro st pairs))

(defmacro up (st &rest pairs)
  "do the update in the sequence of pairs"
  (up-macro pairs st))


(include-book "defexec/other-apps/records/records" :dir :system)
(defmacro g (a r) `(acl2::mget ,a ,r))
(defmacro s (a v r) `(acl2::mset ,a ,v ,r))

;pred
(defun ISA-p (x)
  (equal (g :type x) 'ISA))


  ;constructor helper
(defmacro seq-isa (ISA &rest pairs)
  (seq-macro ISA (append (list :type ''ISA) pairs)))


(defun latch1p (x)
  (declare (xargs :guard t))
  (if (good-map x)
    (equal (g :type x) 'LATCH1)
    nil))

(defmacro seq-l1 (l1 &rest pairs);modifier
  (seq-macro l1 (append (list :type ''latch1) pairs)))

(defmacro seq-l2 (l2 &rest pairs);modifier
  (seq-macro l2 (append (list :type ''latch2) pairs)))

(defmacro seq-ma (MA &rest pairs);modifier
  (seq-macro MA (append (list :type ''MA) pairs)))

(defun latch1 (validp op rc ra rb pch) ;constructor
  (seq-l1 nil
          :validp  validp 
          :op      op 
          :rc      rc
          :ra      ra
          :rb      rb
          :pch     pch))

(defun latch2 (validp op rc ra-val rb-val pch) ;constructor
  (seq-l2 nil
          :validp  validp 
          :op      op 
          :rc      rc
          :ra-val  ra-val
          :rb-val  rb-val
          :pch     pch))

(defun MA-state (pc regs imem dmem latch1 latch2) ;constructor
  (seq-ma nil
          :pc      pc
          :regs    regs 
          :imem    imem
          :dmem    dmem
          :latch1  latch1
          :latch2  latch2))



  

(defun latch2p (x)
  (declare (xargs :guard t))
  (if (good-map x)
    (equal (g :type x) 'LATCH2)
    nil))




;pred
(defun MA-p (x)
  (equal (g :type x) 'MA))



;----------------ISA MODEL--------------------------------------------
(defun add-rc (ra rb rc regs)
  (seq regs rc (+ (g ra regs)
                  (g rb regs))))

(defun ISA-add (rc ra rb ISA)
  (seq-isa nil
           :pc   (1+ (g :pc ISA))
           :regs (add-rc ra rb rc (g :regs ISA))
           :imem (g :imem ISA)
           :dmem (g :dmem ISA)))
        
(defun sub-rc (ra rb rc regs)
  (seq regs rc (- (g ra regs)
                  (g rb regs))))

(defun ISA-sub (rc ra rb ISA)
  (seq-isa nil 
           :pc   (1+ (g :pc ISA))
           :regs (sub-rc ra rb rc (g :regs ISA))
           :imem (g :imem ISA)
           :dmem (g :dmem ISA)))

(defun mul-rc (ra rb rc regs)
  (seq regs rc (* (g ra regs)
                  (g rb regs))))

(defun ISA-mul (rc ra rb ISA)
  (seq-isa nil
           :pc   (1+ (g :pc ISA))
           :regs (mul-rc ra rb rc (g :regs ISA))
           :imem (g :imem ISA)
           :dmem (g :dmem ISA)))

(defun load-rc (ad rc regs dmem)
  (seq regs rc (g ad dmem)))

(defun ISA-loadi (rc ra ISA)
  (let ((regs (g :regs ISA)))
    (seq-isa nil 
             :pc   (1+ (g :pc ISA))
             :regs (load-rc (g ra regs) rc regs (g :dmem ISA))
             :imem (g :imem ISA)
             :dmem (g :dmem ISA))))

(defun ISA-load (rc ad ISA)
  (seq-isa nil 
           :pc   (1+ (g :pc ISA))
           :regs (load-rc  ad rc (g :regs ISA) (g :dmem ISA))
           :imem (g :imem ISA)
           :dmem (g :dmem ISA)))

(defun store (ra rb regs dmem)
  (seq dmem (g ra regs) (g rb regs)))

(defun ISA-store (ra rb ISA)
  (seq-isa nil
           :pc   (1+ (g :pc ISA))
           :regs (g :regs ISA)
           :imem (g :imem ISA)
           :dmem (store ra rb (g :regs ISA) (g :dmem ISA))))

(defun bez (ra rb regs pc)
  (if (equal 0 (g ra regs))
      (ifix (+ pc (g rb regs)))
    (1+ pc)))

(defun ISA-bez (ra rb ISA)
  (seq-isa nil
           :pc (bez ra rb (g :regs ISA) (g :pc ISA))
           :regs (g :regs ISA)
           :imem (g :imem ISA)
           :dmem (g :dmem ISA)))

(defun ISA-jump (ra ISA)
  (seq-isa nil
           :pc (ifix (g ra (g :regs ISA)))
           :regs (g :regs ISA)
           :imem (g :imem ISA)
           :dmem (g :dmem ISA)))

(defun ISA-default (ISA)
  (seq-isa nil 
           :pc (1+ (g :pc ISA))
           :regs (g :regs ISA)
           :imem (g :imem ISA)
           :dmem (g :dmem ISA)))

(defun ISA-step (ISA)
  (let ((inst (g (g :pc ISA) (g :imem ISA))))
    (let ((op (g :opcode inst))
          (rc (g :rc     inst))
          (ra (g :ra     inst))
          (rb (g :rb     inst)))
      (case op
        (add       (ISA-add rc ra rb ISA))  ; REGS[rc] := REGS[ra] + REGS[rb]
        (sub       (ISA-sub rc ra rb ISA))  ; REGS[rc] := REGS[ra] - REGS[rb]
        (mul       (ISA-mul rc ra rb ISA))  ; REGS[rc] := REGS[ra] * REGS[rb]
        (load      (ISA-load rc ra ISA))    ; REGS[rc] := MEM[ra]
        (loadi     (ISA-loadi rc ra ISA))   ; REGS[rc] := MEM[REGS[ra]]
        (store     (ISA-store ra rb ISA))   ; MEM[REGS[ra]] := REGS[rb]
        (bez       (ISA-bez ra rb ISA))     ; REGS[ra]=0 -> pc:=pc+REGS[rb]
        (jump      (ISA-jump ra ISA))       ; pc:=REGS[ra]
        (otherwise (ISA-default ISA))))))

(defun ISA-run (ISA n)
  (if (zp n)
      ISA
    (ISA-run (ISA-step ISA) (1- n))))

;---------------------------MA model---------------------------------------
(defun ALU-output (op val1 val2)
  (cond ((equal op 'add) 
         (+ val1 val2))
        ((equal op 'sub) 
         (- val1 val2))
        (t (* val1 val2))))

(defun in (x y)
  (if (endp y)
      nil
    (or (equal x (car y))
        (in x (cdr y)))))

(defun alu-opp (op)
  (in op '(add sub mul)))

(defun load-opp (op)
  (in op '(load loadi)))

(defun step-regs (MA)
  (let* ((regs     (g :regs MA))
         (dmem     (g :dmem MA))
         (latch2   (g :latch2 MA))
         (validp   (g :validp latch2))
         (op       (g :op latch2))
         (rc       (g :rc latch2))
         (ra-val   (g :ra-val latch2))
         (rb-val   (g :rb-val latch2)))
    (if validp
        (cond ((alu-opp op)
               (seq regs rc (ALU-output op ra-val rb-val)))
              ((load-opp op)
               (seq regs rc (g ra-val dmem)))
              (t regs))
      regs)))

(defun rc-activep (op)
  (or (alu-opp op)
      (load-opp op)))

(defun uses-rbp (op)
  (or (alu-opp op)
      (in op '(store bez))))

;inject error 1 (Data Hazard)
(defun stall-l1p (MA)
  (let* ((latch1   (g :latch1 MA))
         (l1validp (g :validp latch1))
         (latch2   (g :latch2 MA))
         (l1op     (g :op latch1))
         (l2op     (g :op latch2))
         (l2validp (g :validp latch2))
         (l2rc     (g :rc latch2))
         ;(l1ra     (g :ra latch1))
         (l1rb     (g :rb latch1)))
    (and l2validp l1validp
         (rc-activep l2op)
         ;;The following commented out portion refers to the first
         ;;type of injected error mentioned in the paper. (Data hazard).
         (or ;(equal l1ra l2rc)
             (and (uses-rbp l1op)
                  (equal l1rb l2rc))))))

(defun invalidate-l1p (MA)
  (let* ((latch1   (g :latch1 MA))
         (l1op     (g :op latch1))
         (l1validp (g :validp latch1))
         (latch2   (g :latch2 MA))
         (l2op     (g :op latch2))
         (l2validp (g :validp latch2)))
    (or (and l1validp
             (in l1op '(bez jump)))
        (and l2validp
             (equal l2op 'bez)))))

(defun step-latch1 (MA)
  (let ((latch1 (g :latch1 MA))
        (inst   (g (g :pc MA) (g :imem MA))))
    (cond ((stall-l1p MA)
           latch1)
          ((invalidate-l1p MA)
           (seq-l1 nil :validp nil))
          (t (seq-l1 nil
                     :validp t
                     :op     (g :opcode inst)
                     :rc     (g :rc inst)
                     :ra     (g :ra inst)
                     :rb     (g :rb inst)
                     :pch    (g :pc MA))))))

(defun step-latch2 (MA)
  (let* ((latch1 (g :latch1 MA))
         (l1op   (g :op latch1)))
  ;;Commenting out the condition (not (g :validp latch1)) is the
  ;;second error mentioned in the paper (control hazard). Try and see.
    (if (or (not (g :validp latch1)) ;inject error 2 (control hazard) 
            (stall-l1p MA))
        (seq-l2 nil :validp nil)
      (seq-l2 nil
              :validp t
              :op     l1op
              :rc     (g :rc latch1)
              :ra-val (if (equal l1op 'load)
                          (g :ra latch1) 
                        (g (g :ra latch1) (g :regs MA)))
              :rb-val (g (g :rb latch1) (g :regs MA))
              :pch    (g :pch latch1)))))

(defun step-pc (MA)
  (let* ((pc       (g :pc MA))
         (inst     (g (g :pc MA) (g :imem MA)))
         (op       (g :opcode inst))
         (regs     (g :regs MA))
         (latch1   (g :latch1 MA))
         (l1op     (g :op latch1))
         (latch2   (g :latch2 MA))
         (l2op     (g :op latch2))
         (l2validp (g :validp latch2))
         (l2ra-val (g :ra-val latch2))
         (l2rb-val (g :rb-val latch2)))
    (cond ((stall-l1p MA)
           pc)
          ((invalidate-l1p MA)
           (cond ((and l2validp
                       (equal l2op 'bez))
                  (if (equal 0 l2ra-val)
                      (ifix (ALU-output 'add pc l2rb-val))
                    (1+ pc)))
                 ((equal l1op 'jump)
                  (ifix (g (g :ra latch1) regs)))
                 (t pc)))
          ((in op '(jump bez))
           pc)
          (t (1+ pc)))))

(defun step-dmem (MA)
  (let* ((dmem     (g :dmem MA))
         (latch2   (g :latch2 MA))
         (l2validp (g :validp latch2))
         (l2op     (g :op latch2))
         (l2ra-val (g :ra-val latch2))
         (l2rb-val (g :rb-val latch2)))
    (if (and l2validp (equal l2op 'store))
        (seq dmem l2ra-val l2rb-val)
      dmem)))

(defun MA-step (MA)
  (seq-ma nil
          :pc     (step-pc MA)
          :regs   (step-regs MA)
          :dmem   (step-dmem MA)
          :imem   (g :imem MA)
          :latch1 (step-latch1 MA)
          :latch2 (step-latch2 MA)))

(defun MA-run (MA n)
  (if (zp n)
      MA
    (MA-run (MA-step MA) (1- n))))
(set-case-split-limitations 'nil)

(defun committed-pc (l1 l2 pc)
  (cond ((g :validp l2)
         (g :pch l2))
        ((g :validp l1)
         (g :pch l1))
        (t pc)))

(defun committed-MA (MA)
  (let* ((pc       (g :pc MA))
         (latch1   (g :latch1 MA))
         (latch2   (g :latch2 MA)))
    (seq-ma nil :pc     (committed-pc latch1 latch2 pc)
                :regs   (g :regs MA)
                :dmem   (g :dmem MA)
                :imem   (g :imem MA)
                :latch1 (seq-l1 nil)
                :latch2 (seq-l2 nil))))

(defun equiv-l1 (la lb)
  (let ((laop (g :op la))
        (lbop (g :op lb)))
  (and (equal laop lbop)
       (equal (g :pch la) (g :pch lb))
       (implies (in laop '(add sub mul load loadi store bez jump))
                (equal (g :ra la) (g :ra lb)))
       (implies (in laop '(add sub mul store bez))
                (equal (g :rb la) (g :rb lb)))
       (implies (in laop '(add sub mul load loadi))
                (equal (g :rc la) (g :rc lb))))))

(defun equiv-l2 (la lb)
  (let ((laop (g :op la))
        (lbop (g :op lb)))
  (and (equal laop lbop)
       (equal (g :pch la) (g :pch lb))
       (implies (in laop '(add sub mul load loadi store bez jump))
                (equal (g :ra-val la) (g :ra-val lb)))
       (implies (in laop '(add sub mul store bez))
                (equal (g :rb-val la) (g :rb-val lb)))
       (implies (in laop '(add sub mul load loadi))
                (equal (g :rc la) (g :rc lb))))))

(defun equiv-Ma (ma1 ma2)
  (and (equal (g :pc ma1) (g :pc ma2))
       (equal (g :regs ma1) (g :regs ma2))
       (equal (g :dmem ma1) (g :dmem ma2))
       (equal (g :imem ma1) (g :imem ma2))
       (equal (g :validp (g :latch1 MA1)) 
              (g :validp (g :latch1 MA2)))
       (equal (g :validp (g :latch2 MA1)) 
              (g :validp (g :latch2 MA2)))
       (implies (g :validp (g :latch1 MA1))
                (equiv-l1 (g :latch1 ma1) (g :latch1 ma2)))
       (implies (g :validp (g :latch2 MA1))
                (equiv-l2 (g :latch2 ma1) (g :latch2 ma2)))))

(defun good-MA (ma)
  (and (integerp (g :pc MA))
       (let* ((latch1 (g :latch1 MA))
              (latch2 (g :latch2 MA))
              (nma (committed-ma ma)))
         (cond ((g :validp latch2)
                (equiv-ma (ma-step (ma-step nma)) ma))
               ((g :validp latch1)
                (equiv-ma (ma-step nma) ma))
               (t t)))))

(defun MA-to-ISA (MA)
  (let ((MA (committed-MA MA)))
    (seq-isa nil :pc   (g :pc MA)
                 :regs (g :regs MA)
                 :dmem (g :dmem MA)
                 :imem (g :imem MA))))

(defun MA-rank (MA)
  (let ((latch1 (g :latch1 MA))
        (latch2 (g :latch2 MA)))
    (cond ((g :validp latch2)
           0)
          ((g :validp latch1)
           1)
          (t 2))))

;--------other misc theorems----------------

(defthm g-same-s-
  (implies (equal r1 (s a v r))
           (equal (g a r1)
                  v)))
(defthm plus-s-g-
  (implies (and (integerp i)
                (not (equal i 0)))
           (not (equal (s a (+ i (g a w)) r) w)))
     :hints (("goal" :use ((:instance g-same-s- (r1 w) (v (+ i (g a w)))))
              :in-theory (disable g-same-s- ))))

;;;; NOTE: I often use the following instead of the above rules
;;;; to force ACL2 to do a case-split. In some cases, I will
;;;; disable this rule ACL2 is sluggish or if the number of cases
;;;; is unreasonable


;paste
; Put in records.lisp since it helped the other proofs.
(defthm s-not-equal
  (implies (not (equal x y))
           (not (equal (s v x r1)
                       (s v y r2))))
  :hints (("goal" :use ((:instance mget-same-mset (r r1) (a v) (v x))
                        (:instance mget-same-mset (r r2) (a v) (v y)))
           :in-theory (disable mget-same-mset ))))

(in-theory (disable (:executable-counterpart mset)))
