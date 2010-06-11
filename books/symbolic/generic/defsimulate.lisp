(in-package "ACL2")

#| help for the dependency scanner:

(include-book "assertions")
(include-book "measures")
(include-book "partial-correctness")
(include-book "total-correctness")

|#



#||

  defsimulate.lisp
  ~~~~~~~~~~~~~~~~

Here we define a macro that takes a step function, a predicate specifying
cutpoints, and a default-state, and automatically generates the correctness
results. It does this by functionally instantiating the generic theorems in the
other books, namely partial-correctness.lisp and total-correctness.lisp. On the
way, it applies the work in assertions.lisp to obtain efficient symbolic
simulation rules.

Restrictions:

1. The functions precondition, postcondition, cutpoint, etc., must be functions
of the same arity. In addition the machine state must be the last formal of
these functions.

2. The function run, if provided (see :define-run keyword in the macro for
details of what I am talking about) must be a function of two arguments and the
first argument must be the machine state. I should have changed it to last for
lack of ambiguity, but since I have (run s n) ingrained in my brain I dont
think I can do the change reliably.

||#


;; OK, some generic stuff. 

;; The function create-variables here takes a number n (think of the i to be 0)
;; and creates a list (s0 s1 ... sn). I use that list as formals inside the
;; macro.

(defun create-variables (n i)
  (declare (xargs :mode :program))
  (if (zp n) nil
    (cons (packn (list 's i))
          (create-variables (1- n) (1+ i)))))

;; snoc is inverse (literally) of cons...:->

(defun snoc (x e)
  (if (endp x) (list e) (cons (first x) (snoc (rest x) e))))

;; lastval and dellast, the names say it all. I am using these functions so
;; many times now, that I am now sincerely thinking that we should probably
;; have a generic book of "utilities" which has these functions in it.

(defun lastval (x) 
  (cond ((endp x) nil)
        ((endp (rest x)) (first x))
        (t (lastval (rest x)))))

(defun dellast (x) 
  (cond ((endp x) nil)
        ((endp (rest x)) nil)
        (t (cons (first x) (dellast (rest x))))))

;; I need these books to get the correctness theorems. I would actually have
;; liked to be able to include them from inside the macro, but it seems ACL2
;; has forbidden (probably recently) inclusion of books other than local ones
;; from inside encapsulation.

(include-book "ordinals/ordinals-without-arithmetic" :dir :system)
(include-book "misc/defpun" :dir :system)
      
    

(defun defsimulate-partial (nextt run arity cutname exitname defaultname exitsteps 
                               prename postname assertname define-run? hints thms)

  (declare (xargs :mode :program))
  (let* (;; I do a little trick with run. If define-run? is T then run is the
         ;; name of the function run, otherwise run is simply runn irrespective
         ;; of what the user has written. Maybe this is a trivial deal.
         (run (if define-run? 
                  (prog2$ (cw "You have decided to call this macro with ~
                               :define-run? parameter set to T. We will define ~
                               a function called runn and prove the ~
                               correctness theorem in terms of that function. ~
                               If you later decide to define your own run ~
                               function then in order to use the results of ~
                               this macro you need to prove that your run is ~
                               equal to runn. That should be pretty easy to ~
                               prove by induction based on your run. Good ~
                               luck!~|") 
                          'runn)
                (prog2$ (cw "You have decided to use your own run function. ~
                             Please note that we will assume that your ~
                             function is of the form <run s n> where s is the ~
                             machine-state paramter. If this is not how you ~
                             defined it, for example if your function is <run ~
                             n s>, please either abort the macro and redefine ~
                             it this way or call our macro with :define-run? ~
                             t. Good luck!~|")
                        run)))

         ;; Ok now create the formals for this macro. I will always refer to
         ;; the variables in this macro as (s0 s1 s2 ....) so that I have a
         ;; good handle of what it is that I am doing.
         (params (create-variables arity 0))
           
           ;; A few shortcuts I will probably use often. For some of these
           ;; functions I create terms like (pre s0 s1)
           (preterm (cons prename params))
           (assertterm (cons assertname params))
           (cutterm (cons cutname params))
           (exitterm (cons exitname params))
           (postterm (cons postname params)))

    (append 
     
     ;; First the run function definition to be installed in ACL2. This is only
     ;; in case of :define-run?

     (if define-run?
         (prog2$
          (cw "We define the function ~s0~ here. This definition will be ~
               exported from this macro, and if we successfully prove the ~
               desired correctness theorem, then the theorem will be in terms ~
               of this function. The function is recursive. Note however, that ~
               the induction scheme specified for this function may not be ~
               exported. Thus if you plan to use the function for induction ~
               you should either define it outside first and call this macro ~
               with :define-run? nil or after execution of the macro define ~
               another recursive version of ~s0~ and inductively prove that to ~
               be equal to the one we generate.~|" 
              run)
          
          (list

           `(defun-nx ,run (,(lastval params) n)  
              ;; I add the :non-executable argument in the declare because nextt
              ;; might otherwise have stobjs or something like that and I dont
              ;; want to deal with them.
              (if (zp n) ,(lastval params) 
                (,run (,nextt ,(lastval params)) (1- n))))))
       nil) 
     
     (list
      ;; Let us get the easy theorems through first. These theorems should go
      ;; through rather easily. However, I at least need some tricks with
      ;; theories. This is because I cannot indiscriminately open nextt when I
      ;; am proving the rules by symbolic simulation. For machines such as M5
      ;; and M6 it is vital that nextt is disabled and opened via openers;
      ;; otherwise I dont know how long a proof might take. I achieve this by
      ;; storing the theory at the beginning of the events as a deftheory form.
      
      `(local (deftheory oldth (current-theory :here)))
      ;; These theorems are the proof obligations for partial correctness. The
      ;; easy stuff is all those except for the one which says that assertions
      ;; persist over cutpoints. I will handle that using symbolic simulation
      ;; later. Now let us get on with the easy theorems.

      `(local
        (defthm default-not-cutpoint
          (not ,(cons cutname (snoc (dellast params)
                                    (list defaultname))))))

      `(local 
        (defthm pre-implies-cutpoint
          (implies ,preterm ,cutterm)))
      
      `(local
        (defthm exitpoint-is-cutpoint
          (implies ,exitterm  ,cutterm)))
      
      `(local
        (defthm pre-implies-assertion
          (implies ,preterm ,assertterm)))
      
      `(local
        (defthm assertion-implies-post
          (implies (and ,assertterm ,exitterm) ,postterm)))
      
      ;; To get the difficult one, I would first define the tail-recursive
      ;; steps-to-cutpoint function. 

      ;; There seems to be some problem with defpun when the function next is
      ;; enabled. So disable it.

      `(local (in-theory (disable ,nextt)))

      `(local 
        (defpun concrete-steps-to-cutpoint-tail ,(snoc params 'i)
          (if ,cutterm
              i
            ,(cons 'concrete-steps-to-cutpoint-tail 
                   (snoc (snoc (dellast params)
                               (list nextt (lastval params)))
                               '(1+ i))))))


      ;; We define the function steps-to-exitpoint here.

      `(defpun ,(packn (list exitsteps '-tail)) ,(snoc params 'i)
         (if ,exitterm
             i
           ,(cons (packn (list exitsteps '-tail)) 
                   (snoc (snoc (dellast params)
                               (list nextt (lastval params)))
                         '(1+ i)))))
      

      
      `(local
        (defun-nx concrete-steps-to-cutpoint ,params
          (declare (xargs :normalize nil :non-executable t))
          (let ((steps ,(cons 'concrete-steps-to-cutpoint-tail (snoc params 0)))
                (s ,(lastval params)))
            (if ,(cons cutname (snoc (dellast params) (list run 's 'steps)))
                steps 
              (omega)))))
      
      ;; Now we define the nextt-cutpoint function. All this is automatic, since
      ;; no user input should be required.
      
      `(local 
        (defun-nx concrete-nextt-cutpoint ,params
          (declare (xargs :normalize nil :non-executable t))
          (let* ((s ,(lastval params))
                 (steps ,(cons 'concrete-steps-to-cutpoint 
                              (snoc (dellast params) 's))))
            (if (natp steps)
                (,run s steps)
              (,defaultname)))))
      
      ;; Ok, now I need to prove some stuff. The first thing I will prove is
      ;; the symbolic simulation rules for nextt-cutpoint. This would be useful
      ;; to then prove that assertion is invariant over cutpoints. But I have
      ;; already proved this theorem generically!! All that I need to do now is
      ;; include the book and functionally instantiate the theorem. No property
      ;; of concrete step or default should be required, and hence I am fine
      ;; with just disabling stuff.
      
      `(local (in-theory (disable ,nextt ,defaultname (,defaultname))))
      
      `(local
        (encapsulate
         ()
         
         ;; How do we prove the symbolic simulation theorems? Well, just a
         ;; simple functional instantiation of the previous theorems we have
         ;; proved.
         
         ;; Note: Why do I do this within another encapsulate? Well there are
         ;; name clashes between partial/total correctness book and the
         ;; assertion book (for example the name of the function run. Rather
         ;; than write something else for run in one of those I simply include
         ;; the assertions book locally.
         
         (local (include-book "symbolic/generic/assertions" :dir :system))
         
         ;; I should only need the theorems about cutpoint and assertion that I
         ;; have already proved. So I disable them. In fact I disable
         ;; everything since I am in the middle of a macro and I am afraid that
         ;; things can cause trouble by interfering with my plan of proof.

         (local (in-theory (theory 'minimal-theory)))
         
         ;; These are theorems that should be trivial to prove. But I dont want
         ;; to needlessly risk symbolic simulation on the concrete
         ;; machine. Rather I know that I have already proved the generic
         ;; theorems so I will functionally instantiate them.

         (defthm nextt-cutpoint-for-cutpoint
           (implies ,cutterm
                    (equal ,(cons 'concrete-nextt-cutpoint params)
                           ,(lastval params)))
           :hints (("Goal"
                    :in-theory 
                    (disable |nextt cutpoint for cutpoint|)
                   :use 
                    ((:instance 
                      (:functional-instance 
                       |nextt cutpoint for cutpoint|
                       (run (lambda (s n) (,run s n)))
                       (nextt (lambda (s) (,nextt s)))
                       (default-state (lambda () (,defaultname)))
                       (cutpoint 
                        (lambda (s) 
                          ,(cons cutname (snoc (dellast params) 's))))
                       (nextt-cutpoint 
                        (lambda (s) 
                          ,(cons 'concrete-nextt-cutpoint 
                                 (snoc (dellast params) 's))))
                       (steps-to-cutpoint 
                        (lambda (s) ,(cons 'concrete-steps-to-cutpoint 
                                           (snoc (dellast params) 's))))
                       (steps-to-cutpoint-tail
                         (lambda (s i) 
                           ,(cons 'concrete-steps-to-cutpoint-tail
                                  (snoc (snoc (dellast params) 's) 'i)))))
                      (s ,(lastval params)))))
                   ("Subgoal 1"
                    :in-theory (enable ,run))
                   ("Subgoal 2"
                    :use ((:instance default-not-cutpoint)))
                   ("Subgoal 3"
                    :use ((:instance concrete-steps-to-cutpoint-tail-def
                                     (,(lastval params) s))))
                   ("Subgoal 4"
                    :use ((:instance (:definition concrete-steps-to-cutpoint)
                                     (,(lastval params) s))))
                   ("Subgoal 5"
                     :use ((:instance (:definition concrete-nextt-cutpoint)
                                (,(lastval params) s))))))

         ;; The constraints have already been established for the encapsulate
         ;; in course of proving the previous theorem. So all that I would need
         ;; is a statement that says this is a propositional tautology. So I am
         ;; fine here without the nasty subgoal hints.

         (defthm nextt-cutpoint-for-not-cutpoint
           (implies (not ,cutterm)
                    (equal ,(cons 'concrete-nextt-cutpoint params)
                           ,(cons 'concrete-nextt-cutpoint 
                                  (snoc (dellast params) 
                                        (list nextt (lastval params))))))
           :hints (("Goal"
                    :in-theory 
                    (disable |nextt cutpoint for not cutpoint|)
                   :use 
                    ((:instance 
                      (:functional-instance 
                       |nextt cutpoint for not cutpoint|
                       (run (lambda (s n) (,run s n)))
                       (nextt (lambda (s) (,nextt s)))
                       (default-state (lambda () (,defaultname)))
                       (cutpoint 
                        (lambda (s) 
                          ,(cons cutname (snoc (dellast params) 's))))
                       (nextt-cutpoint 
                        (lambda (s) 
                          ,(cons 'concrete-nextt-cutpoint 
                                 (snoc (dellast params) 's))))
                       (steps-to-cutpoint 
                        (lambda (s) ,(cons 'concrete-steps-to-cutpoint 
                                           (snoc (dellast params) 's))))
                       (steps-to-cutpoint-tail
                         (lambda (s i) ,(cons 'concrete-steps-to-cutpoint-tail
                                            (snoc (snoc (dellast params) 's) 'i)))))
                      (s ,(lastval params)))))))))

      
      ;; Now apply symbolic simulation based on the rules above to prove the
      ;; theorem below. This needs me to open nextt, but disable
      ;; concrete-nextt-cutpoint.

      `(local (in-theory (union-theories (theory 'oldth)
                                         '(nextt-cutpoint-for-cutpoint
                                           nextt-cutpoint-for-not-cutpoint))))
;       `(local (in-theory (disable concrete-nextt-cutpoint)))
;       `(local (in-theory (enable ,assertname ,cutname)))
                                 ;; ,nextt)))

      ;; This is the one theorem for which the user better know
      ;; something. (S)he is trying to prove that the assertion is invariant
      ;; over cutpoints. I might have to consider hints for this one.

      ;; Further note: In case nextt imposes a huge case split, possibly on
      ;; different values of the program counter, the proof of this theorem can
      ;; blow up. This is because ACL2 has inside-out rewriting and hence all
      ;; the nextt would be opened up first before the assertions are
      ;; checked. This can happen (I think) if the code involves a large body
      ;; of sequential code as complicated as apprentice.  But right now I dont
      ;; consider efficiency issues. Also I am right now relying on the fact if
      ;; we have the theorems for the two cases (cutpoint s) and (not (cutpoint
      ;; s)) then this theorem should just go through. Since ACL2 does very
      ;; light-wieght simplification while relieving hypothesis of a rewrite
      ;; rule, it is possible that if we hit a state s where to figure out
      ;; whether s is a cutpoint requires (say) some induction. Then it will
      ;; not be possible for these two rules to be sufficient. However, if
      ;; indeed that is necessary then it is also true that such inductive
      ;; theorems should have been proved earlier as rewrite rules in ACL2.
      
      )

     thms
      
     (list
      
      `(local
        (defthm assertion-invariant-over-cutpoints
          (implies (and ,cutterm ,assertterm (not ,exitterm))
                   (let ((s ,(lastval params)))
                     ,(cons assertname 
                            (snoc (dellast params)
                                  (cons 'concrete-nextt-cutpoint 
                                        (snoc (dellast params)
                                              (list nextt 's)))))))
          :hints ,hints))
                   
      
      ;; OK, so this completes all the proof obligations that the user has. The
      ;; last thing then is to define steps-to-exitpoint and prove the partial
      ;; correctness theorem by functional instantiation.
      

      `(defun-nx ,exitsteps ,params
         (declare (xargs :normalize nil :non-executable t))
         (let ((steps ,(cons (packn (list exitsteps '-tail)) (snoc params 0)))
               (s ,(lastval params)))
           (if ,(cons exitname (snoc (dellast params) (list run 's 'steps)))
               steps 
             (omega))))
      
      ;; Now just include the book we desire and throw in partial correctness.
      
      `(local 
        (include-book "symbolic/generic/partial-correctness" :dir :system))

      ;; The job of assertion, cutpoint and nextt is done. So I disable them.
      `(local (in-theory (theory 'minimal-theory)))
      
      ;; The final theorem. please dont be overawed by the number of :use
      ;; hints. These would not have been required if I were doing theorem
      ;; proving. But here now I am specifying a macro and it better be that
      ;; when I do it I leave nothing to chance (read ACL2's heuristics...:->)
      ;; so I am working with the minimal theory and using whichever theorems
      ;; are to be required manually.

      `(defthm ,(packn (list nextt '-partial-correctness))
         (implies (and ,preterm 
                       ,(cons exitname 
                              (snoc (dellast params) 
                                    (list run (lastval params) 'n))))
                    (let ((steps ,(cons exitsteps params)))
                      ,(cons postname 
                             (snoc (dellast params) 
                                   (list run (lastval params) 'steps)))))
         :hints (("Goal"
                  :use 
                  ((:instance 
                    (:functional-instance 
                     |partial correctness|
                     (pre (lambda (s) 
                            ,(cons prename (snoc (dellast params) 's))))
                     
                     (cutpoint 
                      (lambda (s) 
                        ,(cons cutname (snoc (dellast params) 's))))
                     
                     (assertion 
                      (lambda (s) 
                        ,(cons assertname 
                               (snoc (dellast params) 's))))
                     (exitpoint 
                      (lambda (s) 
                        ,(cons exitname 
                               (snoc (dellast params) 's))))
                     (steps-to-exitpoint 
                      (lambda (s) 
                        ,(cons exitsteps
                               (snoc (dellast params) 's))))
                     (steps-to-cutpoint 
                      (lambda (s)
                        ,(cons 'concrete-steps-to-cutpoint 
                               (snoc (dellast params) 's))))
                     
                     (steps-to-cutpoint-tail 
                      (lambda (s i) 
                        ,(cons 'concrete-steps-to-cutpoint-tail 
                               (snoc (snoc (dellast params) 's) 'i))))
                     
                     
                     (steps-to-exitpoint-tail
                      (lambda (s i) 
                        ,(cons (packn (list exitsteps '-tail))
                               (snoc (snoc (dellast params) 's) 'i))))
                     
                     (nextt-cutpoint
                      (lambda (s) 
                        ,(cons 'concrete-nextt-cutpoint 
                               (snoc (dellast params) 's))))
                     (post 
                      (lambda (s) 
                        ,(cons postname 
                               (snoc (dellast params) 's))))
                     (default-state (lambda () (,defaultname)))
                     (nextt (lambda (s) (,nextt s)))
                     (run (lambda (s n) (,run s n))))
                    (s ,(lastval params)))))
                  ("Subgoal 1"
                  :use ((:instance (:definition concrete-steps-to-cutpoint)
                                   (,(lastval params) s))))
                  ("Subgoal 2"
                  :use ((:instance (:definition concrete-nextt-cutpoint)
                                   (,(lastval params) s))))
                 ("Subgoal 3"
                  :use ((:instance exitpoint-is-cutpoint
                                   (,(lastval params) s))))
                 ("Subgoal 4"
                  :use ((:instance pre-implies-assertion
                                   (,(lastval params) s))))
                 ("Subgoal 5"
                  :use ((:instance pre-implies-cutpoint
                                   (,(lastval params) s))))
                 ("Subgoal 6"
                  :use ((:instance assertion-implies-post
                                   (,(lastval params) s))))
                 ("Subgoal 7"
                  :use ((:instance concrete-steps-to-cutpoint-tail-def
                                   (,(lastval params) s))))
                        
                 ("Subgoal 8"
                  :use ((:instance assertion-invariant-over-cutpoints
                                   (,(lastval params) s))))
                 ("Subgoal 9"
                  :in-theory (enable ,run))
                 ("Subgoal 10"
                  :use ((:instance 
                         (:definition ,(packn (list exitsteps '-tail-def)))
                         (,(lastval params) s))))
                 ("Subgoal 11"
                  :use ((:instance (:definition ,exitsteps)
                                   (,(lastval params) s))))))))))


;; Here is a similar function for total correctness. This is to a big extent a
;; copy-paste of the function for partial correctness above. The only changes
;; are in the inclusion of the measures book, the proofs of invariance of
;; assertion, etc. I document them when I reach them.

(defun defsimulate-total (nextt run arity measure cutname exitname 
                                 defaultname exitsteps 
                                 prename postname assertname define-run? hints
                                 thms)

  (declare (xargs :mode :program))
  (let* (;; I do a little trick with run. If define-run? is T then run is the
         ;; name of the function run, otherwise run is simply runn irrespective
         ;; of what the user has written. Maybe this is a trivial deal.
         (run (if define-run? 
                  (prog2$ (cw "You have decided to call this macro with ~
                               :define-run? parameter set to T. We will define ~
                               a function called runn and prove the ~
                               correctness theorem in terms of that function. ~
                               If you later decide to define your own run ~
                               function then in order to use the results of ~
                               this macro you need to prove that your run is ~
                               equal to runn. That should be pretty easy to ~
                               prove by induction based on your run. Good ~
                               luck!~|") 
                          'runn)
                (prog2$ (cw "You have decided to use your own run function. ~
                             Please note that we will assume that your ~
                             function is of the form <run s n> where s is the ~
                             machine-state paramter. If this is not how you ~
                             defined it, for example if your function is <run ~
                             n s>, please either abort the macro and redefine ~
                             it this way or call our macro with :define-run? ~
                             t. Good luck!~|") 
                        run)))

         ;; Ok now create the formals for this macro. I will always refer to
         ;; the variables in this macro as (s0 s1 s2 ....) so that I have a
         ;; good handle of what it is that I am doing.
         (params (create-variables arity 0))
           
           ;; A few shortcuts I will probably use often. For some of these
           ;; functions I create terms like (pre s0 s1)
           (preterm (cons prename params))
           (assertterm (cons assertname params))
           (cutterm (cons cutname params))
           (exitterm (cons exitname params))
           (postterm (cons postname params)))

    (append 
     
     ;; First the run function definition to be installed in ACL2. This is only
     ;; in case of :define-run?

     (if define-run?
         (prog2$
          (cw "We define the function ~s0~ here. This definition will be ~
               exported from this macro, and if we successfully prove the ~
               desired correctness theorem, then the theorem will be in terms ~
               of this function. The function is recursive. Note however, that ~
               the induction scheme specified for this function may not be ~
               exported. Thus if you plan to use the function for induction ~
               you should either define it outside first and call this macro ~
               with :define-run? nil or after execution of the macro define ~
               another recursive version of ~s0~ and inductively prove that to ~
               be equal to the one we generate.~|"
              run)
          
          (list

           `(defun-nx ,run (,(lastval params) n) 
              ;; I add the :non-executable argument in the declare because nextt
              ;; might otherwise have stobjs or something like that and I dont
              ;; want to deal with them.
              (if (zp n) ,(lastval params) 
                (,run (,nextt ,(lastval params)) (1- n))))))
       nil) 
     
     (list
      ;; Let us get the easy theorems through first. These theorems should go
      ;; through rather easily. I have to think about hint settings later, but I
      ;; think they might not be necessary. 

       
      `(local (deftheory oldth (current-theory :here)))

      ;; These theorems are the proof obligations for partial correctness. The
      ;; easy stuff is all those except for the one which says that assertions
      ;; persist over cutpoints. I will handle that using symbolic simulation
      ;; later. Now let us get on with the easy theorems.

      `(local
        (defthm default-not-cutpoint
          (not ,(cons cutname (snoc (dellast params)
                                    (list defaultname))))))

      `(local 
        (defthm pre-implies-cutpoint
          (implies ,preterm ,cutterm)))
      
      `(local
        (defthm exitpoint-is-cutpoint
          (implies ,exitterm  ,cutterm)))
      
      `(local
        (defthm pre-implies-assertion
          (implies ,preterm ,assertterm)))
      
      `(local
        (defthm assertion-implies-post
          (implies (and ,assertterm ,exitterm) ,postterm)))

      ;; For total correctness I add the new thing about measure.

      `(local 
        (defthm measure-is-ordinal
          (o-p ,(cons measure params))))
      
      ;; To get the difficult one, I would first define the tail-recursive
      ;; steps-to-cutpoint function. 

      ;; There seems to be some problem with defpun when the function next is
      ;; enabled. So disable it.

      `(local (in-theory (disable ,nextt)))

      `(local 
        (defpun concrete-steps-to-cutpoint-tail ,(snoc params 'i)
          (if ,cutterm
              i
            ,(cons 'concrete-steps-to-cutpoint-tail 
                   (snoc (snoc (dellast params)
                               (list nextt (lastval params)))
                               '(1+ i))))))

      ;; We define the function steps-to-exitpoint here.


      `(defpun ,(packn (list exitsteps '-tail)) ,(snoc params 'i)
         (if ,exitterm
             i
           ,(cons (packn (list exitsteps '-tail)) 
                   (snoc (snoc (dellast params)
                               (list nextt (lastval params)))
                         '(1+ i)))))
      
      
      `(local
        (defun-nx concrete-steps-to-cutpoint ,params
          (declare (xargs :normalize nil :non-executable t))
          (let ((steps ,(cons 'concrete-steps-to-cutpoint-tail (snoc params 0)))
                (s ,(lastval params)))
            (if ,(cons cutname (snoc (dellast params) (list run 's 'steps)))
                steps 
              (omega)))))
      
      ;; Now we define the nextt-cutpoint function. All this is automatic, since
      ;; no user input should be required.
      
      `(local 
        (defun-nx concrete-nextt-cutpoint ,params
          (declare (xargs :normalize nil :non-executable t))
          (let* ((s ,(lastval params))
                 (steps ,(cons 'concrete-steps-to-cutpoint 
                              (snoc (dellast params) 's))))
            (if (natp steps)
                (,run s steps)
              (,defaultname)))))
      
      ;; Ok, now I need to prove some stuff. The first thing I will prove is
      ;; the symbolic simulation rules for nextt-cutpoint. This would be useful
      ;; to then prove that assertion is invariant over cutpoints. But I have
      ;; already proved this theorem generically!! All that I need to do now is
      ;; include the book and functionally instantiate the theorem. No property
      ;; of concrete step or default should be required, and hence I am fine
      ;; with just disabling stuff.
      
      `(local (in-theory (disable ,nextt ,defaultname (,defaultname))))
      
      `(local
        (encapsulate
         ()
         
         ;; How do we prove the symbolic simulation theorems? Well, just a
         ;; simple functional instantiation of the previous theorems we have
         ;; proved.
         
         ;; Note: Why do I do this within another encapsulate? Well there are
         ;; name clashes between partial/total correctness book and the
         ;; assertion book (for example the name of the function run. Rather
         ;; than write something else for run in one of those I simply include
         ;; the assertions book locally.
         
         (local (include-book "symbolic/generic/assertions" :dir :system))
         
         ;; I should only need the theorems about cutpoint and assertion that I
         ;; have already proved. So disable them. In fact I disable everything
         ;; since I am in the middle of a macro and I am afraid that things can
         ;; cause trouble by interfering with my plan of proof.

         (local (in-theory (theory 'minimal-theory)))
         
         ;; These are theorems that should be trivial to prove. But I dont want
         ;; to needlessly risk symbolic simulation on the concrete
         ;; machine. Rather I know that I have already proved the generic
         ;; theorems so I will functionally instantiate them.

         (defthm nextt-cutpoint-for-cutpoint
           (implies ,cutterm
                    (equal ,(cons 'concrete-nextt-cutpoint params)
                           ,(lastval params)))
           :hints (("Goal"
                    :in-theory 
                    (disable |nextt cutpoint for cutpoint|)
                   :use 
                    ((:instance 
                      (:functional-instance 
                       |nextt cutpoint for cutpoint|
                       (run (lambda (s n) (,run s n)))
                       (nextt (lambda (s) (,nextt s)))
                       (default-state (lambda () (,defaultname)))
                       (cutpoint 
                        (lambda (s) 
                          ,(cons cutname (snoc (dellast params) 's))))
                       (nextt-cutpoint 
                        (lambda (s) 
                          ,(cons 'concrete-nextt-cutpoint 
                                 (snoc (dellast params) 's))))
                       (steps-to-cutpoint 
                        (lambda (s) ,(cons 'concrete-steps-to-cutpoint 
                                           (snoc (dellast params) 's))))
                       (steps-to-cutpoint-tail
                         (lambda (s i) 
                           ,(cons 'concrete-steps-to-cutpoint-tail
                                  (snoc (snoc (dellast params) 's) 'i)))))
                      (s ,(lastval params)))))
                   ("Subgoal 1"
                    :in-theory (enable ,run))
                   ("Subgoal 2"
                    :use ((:instance default-not-cutpoint)))
                   ("Subgoal 3"
                    :use ((:instance concrete-steps-to-cutpoint-tail-def
                                     (,(lastval params) s))))
                   ("Subgoal 4"
                    :use ((:instance (:definition concrete-steps-to-cutpoint)
                                     (,(lastval params) s))))
                   ("Subgoal 5"
                     :use ((:instance (:definition concrete-nextt-cutpoint)
                                (,(lastval params) s))))))

         ;; The constraints have already been established for the encapsulate
         ;; in course of proving the previous theorem. So all that I would need
         ;; is a statement that says this is a propositional tautology. So I am
         ;; fine here without the nasty subgoal hints.

         (defthm nextt-cutpoint-for-not-cutpoint
           (implies (not ,cutterm)
                    (equal ,(cons 'concrete-nextt-cutpoint params)
                           ,(cons 'concrete-nextt-cutpoint 
                                  (snoc (dellast params) 
                                        (list nextt (lastval params))))))
           :hints (("Goal"
                    :in-theory 
                    (disable |nextt cutpoint for not cutpoint|)
                   :use 
                    ((:instance 
                      (:functional-instance 
                       |nextt cutpoint for not cutpoint|
                       (run (lambda (s n) (,run s n)))
                       (nextt (lambda (s) (,nextt s)))
                       (default-state (lambda () (,defaultname)))
                       (cutpoint 
                        (lambda (s) 
                          ,(cons cutname (snoc (dellast params) 's))))
                       (nextt-cutpoint 
                        (lambda (s) 
                          ,(cons 'concrete-nextt-cutpoint 
                                 (snoc (dellast params) 's))))
                       (steps-to-cutpoint 
                        (lambda (s) ,(cons 'concrete-steps-to-cutpoint 
                                           (snoc (dellast params) 's))))
                       (steps-to-cutpoint-tail
                         (lambda (s i) ,(cons 'concrete-steps-to-cutpoint-tail
                                            (snoc (snoc (dellast params) 's) 
                                                  'i)))))
                      (s ,(lastval params)))))))))

      
      ;; Now apply symbolic simulation based on the rules above to prove the
      ;; theorem below. This needs me to open nextt, but disable
      ;; concrete-nextt-cutpoint.
      
       `(local (in-theory (union-theories (theory 'oldth)
                                         '(nextt-cutpoint-for-cutpoint
                                           nextt-cutpoint-for-not-cutpoint))))
;       `(local (in-theory (disable concrete-nextt-cutpoint)))
;       `(local (in-theory (enable ,assertname ,cutname ,nextt)))

      ;; This is the one theorem for which the user better know
      ;; something. She is trying to prove that the assertion is invariant
      ;; over cutpoints. I might have to consider hints for this one.

      ;; Note for total correctness: I modify the theorem below to the actual
      ;; total correctness theorem that I want.

      ;; Further note: In case nextt imposes a huge case split, possibly on
      ;; different values of the program counter, the proof of this theorem can
      ;; blow up. This is because ACL2 has inside-out rewriting and hence all
      ;; the nextt would be opened up first before the assertions are
      ;; checked. This can happen (I think) if the code involves a large body
      ;; of sequential code as complicated as apprentice.  But right now I dont
      ;; consider efficiency issues. Also I am right now relying on the fact if
      ;; we have the theorems for the two cases (cutpoint s) and (not (cutpoint
      ;; s)) then this theorem should just go through. Since ACL2 does very
      ;; light-wieght simplification while relieving hypothesis of a rewrite
      ;; rule, it is possible that if we hit a state s where to figure out
      ;; whether s is a cutpoint requires (say) some induction. Then it will
      ;; not be possible for these two rules to be sufficient. However, if
      ;; indeed that is necessary then it is also true that such inductive
      ;; theorems should have been proved earlier as rewrite rules in ACL2.


       )
     
     thms
      
     (list
     `(local
       (defthm total-correctness-proof-obligation
         (implies (and ,cutterm 
                       ,assertterm 
                       (not ,exitterm)
                       (let ((s ,(lastval params)))
                         (equal ns 
                                ,(cons 
                                  'concrete-nextt-cutpoint 
                                  (snoc (dellast params) 
                                      (list nextt 's))))))
                  (and ,(cons assertname
                              (snoc (dellast params) 'ns))
                       ,(cons cutname (snoc (dellast params) 'ns))
                       (o< ,(cons measure (snoc (dellast params) 'ns))
                           ,(cons measure params))))
         :hints ,hints))


     ;; OK once this theorem is proved by symbolic simulation there is really
     ;; precious little to do. No more symbolic simulation left, so I should be
     ;; able to do the rest of the work with minimal theory. I should have
     ;; actually used minimal-theory globally, but I need to use defpun and it
     ;; seems that defpun cannot do its job in minimal-theory so I locally make
     ;; things minimal-theory.

     ;; Since I am going to use :use hints with minimal theory, I prefer to
     ;; have more specific theorems.
     `(local
       (defthm assertion-invariant-over-cutpoints
         (implies (and ,cutterm ,assertterm (not ,exitterm))
                  (let ((s ,(lastval params)))
                    ,(cons assertname 
                           (snoc (dellast params)
                                 (cons 'concrete-nextt-cutpoint 
                                       (snoc (dellast params)
                                             (list nextt 's)))))))
         :hints (("Goal"
                  :in-theory (theory 'minimal-theory)
                  :use ((:instance total-correctness-proof-obligation
                                   (ns ,(cons 'concrete-nextt-cutpoint 
                                              (snoc (dellast params)
                                                   (list nextt (lastval
                                                               params)))))))))))

     `(local
       (defthm nextt-cutpoint-is-cutpoint
         (implies (and ,cutterm ,assertterm (not ,exitterm))
                  (let ((s ,(lastval params)))
                    ,(cons cutname 
                           (snoc (dellast params)
                                 (cons 'concrete-nextt-cutpoint 
                                       (snoc (dellast params)
                                             (list nextt 's)))))))
         :hints (("Goal"
                  :in-theory (theory 'minimal-theory)
                  :use ((:instance total-correctness-proof-obligation
                                   (ns ,(cons 'concrete-nextt-cutpoint 
                                              (snoc (dellast params)
                                                   (list nextt (lastval params)))))))))))

     `(local
       (defthm cutpoint-measure-decreases
         (implies (and ,cutterm ,assertterm (not ,exitterm))
                  (let ((s ,(lastval params)))
                    (o< ,(cons measure 
                               (snoc (dellast params) 
                                     (cons 'concrete-nextt-cutpoint 
                                           (snoc (dellast params)
                                                 (list nextt 's)))))
                        ,(cons measure (snoc (dellast params) 's)))))
         :hints (("Goal"
                  :in-theory (theory 'minimal-theory)
                  :use ((:instance total-correctness-proof-obligation
                                   (ns ,(cons 'concrete-nextt-cutpoint 
                                              (snoc (dellast params)
                                                    (list nextt (lastval params)))))))))))
     
     ;; OK two down, one to go. For this last one, which is just to say that
     ;; the nextt-cutpoint is natp, I am really doing the simple matter of
     ;; instantiating the corresponding generic theorem. 

     `(local
       (encapsulate 
        ()

        (local (include-book "symbolic/generic/measures" :dir :system))

        (local (in-theory (theory 'minimal-theory)))

        (defthm some-cutpoint-is-reachable
          (implies (and ,cutterm ,assertterm (not ,exitterm))
                   (let ((s ,(lastval params)))
                     (natp ,(cons 'concrete-steps-to-cutpoint 
                                  (snoc (dellast params) 
                                        (list nextt 's))))))
          :hints (("Goal"
                   :use 
                   ((:instance 
                     (:functional-instance 
                      |some cutpoint is reachable|
                       (run (lambda (s n) (,run s n))) 
                       (nextt (lambda (s) (,nextt s)))
                       (default-state (lambda () (,defaultname)))
                       (assertion 
                        (lambda (s)
                          ,(cons assertname (snoc (dellast params) 's))))
                       (exitpoint 
                        (lambda (s) 
                          ,(cons exitname (snoc (dellast params) 's))))
                       (cutpoint 
                        (lambda (s) 
                          ,(cons cutname (snoc (dellast params) 's))))
                       (nextt-cutpoint 
                        (lambda (s) 
                          ,(cons 'concrete-nextt-cutpoint 
                                 (snoc (dellast params) 's))))
                       (steps-to-cutpoint 
                        (lambda (s) ,(cons 'concrete-steps-to-cutpoint 
                                           (snoc (dellast params) 's))))
                       (steps-to-cutpoint-tail
                         (lambda (s i) 
                           ,(cons 'concrete-steps-to-cutpoint-tail
                                  (snoc (snoc (dellast params) 's) 'i)))))
                      (s ,(lastval params)))))
                  ("Subgoal 1"
                   :use ((:instance (:definition concrete-steps-to-cutpoint)
                                    (,(lastval params) s))))
                  ("Subgoal 2"
                   :use ((:instance (:definition concrete-nextt-cutpoint)
                                    (,(lastval params) s))))
                  ("Subgoal 3"
                   :use ((:instance concrete-steps-to-cutpoint-tail-def
                                    (,(lastval params) s))))
                  ("Subgoal 4"
                   :use ((:instance default-not-cutpoint)))
                  ("Subgoal 5"
                   :use ((:instance nextt-cutpoint-is-cutpoint
                                    (,(lastval params) s))))
                  ("Subgoal 6"
                   :in-theory (enable ,run))))))

        

      ;; OK, so this completes all the proof obligations that the user has. The
      ;; last thing then is to define steps-to-exitpoint and prove the partial
      ;; correctness theorem by functional instantiation.
      

      `(defun-nx ,exitsteps ,params
         (declare (xargs :normalize nil :non-executable t))
         (let ((steps ,(cons (packn (list exitsteps '-tail)) (snoc params 0)))
               (s ,(lastval params)))
           (if ,(cons exitname (snoc (dellast params) (list run 's 'steps)))
               steps 
             (omega))))
      
      ;; Now just include the book we desire and throw in total
      ;; correctness. Finally I can make things minimal-theory as well.
      
      `(local (in-theory (theory 'minimal-theory)))

      `(local 
        (include-book "symbolic/generic/total-correctness" :dir :system))
      
      ;; The final theorem. please dont be overawed by the number of :use
      ;; hints. These would not have been required if I were doing theorem
      ;; proving. But here now I am specifying a macro and it better be that
      ;; when I do it I leave nothing to chance (read ACL2's heuristics...:->)
      ;; so I am working with the minimal theory and using whichever theorems
      ;; are to be required manually.

      `(defthm ,(packn (list nextt '-total-correctness))
         (implies ,preterm 
                    (let ((steps ,(cons exitsteps params)))
                      ,(cons postname 
                             (snoc (dellast params) 
                                   (list run (lastval params) 'steps)))))
         :hints (("Goal"
                  :use 
                  ((:instance 
                    (:functional-instance 
                     |total correctness|
                     (pre (lambda (s) 
                            ,(cons prename (snoc (dellast params) 's))))
                     
                     (cutpoint 
                      (lambda (s) 
                        ,(cons cutname (snoc (dellast params) 's))))
                     (cutpoint-measure
                      (lambda (s)
                        ,(cons measure (snoc (dellast params) 's))))
                     (assertion 
                      (lambda (s) 
                        ,(cons assertname 
                               (snoc (dellast params) 's))))
                     (exitpoint 
                      (lambda (s) 
                        ,(cons exitname 
                               (snoc (dellast params) 's))))
                     (steps-to-exitpoint 
                      (lambda (s) 
                        ,(cons exitsteps
                               (snoc (dellast params) 's))))
                     (steps-to-cutpoint 
                      (lambda (s)
                        ,(cons 'concrete-steps-to-cutpoint 
                               (snoc (dellast params) 's))))
                     
                     (steps-to-cutpoint-tail 
                      (lambda (s i) 
                        ,(cons 'concrete-steps-to-cutpoint-tail 
                               (snoc (snoc (dellast params) 's) 'i))))
                     
                     
                     (steps-to-exitpoint-tail
                      (lambda (s i) 
                        ,(cons (packn (list exitsteps '-tail))
                               (snoc (snoc (dellast params) 's) 'i))))
                     
                     (nextt-cutpoint
                      (lambda (s) 
                        ,(cons 'concrete-nextt-cutpoint 
                               (snoc (dellast params) 's))))
                     (post 
                      (lambda (s) 
                        ,(cons postname 
                               (snoc (dellast params) 's))))
                     (default-state (lambda () (,defaultname)))
                     (nextt (lambda (s) (,nextt s)))
                     (run (lambda (s n) (,run s n))))
                    (s ,(lastval params)))))
                 ("Subgoal 1"
                  :use ((:instance (:definition concrete-steps-to-cutpoint)
                                   (,(lastval params) s))))
                 ("Subgoal 2"
                  :use ((:instance (:definition concrete-nextt-cutpoint)
                                   (,(lastval params) s))))
                 ("Subgoal 3"
                  :use ((:instance exitpoint-is-cutpoint
                                   (,(lastval params) s))))
                 ("Subgoal 4"
                  :use ((:instance pre-implies-assertion
                                   (,(lastval params) s))))
                 ("Subgoal 5"
                  :use ((:instance pre-implies-cutpoint
                                   (,(lastval params) s))))
                 ("Subgoal 6"
                  :use ((:instance assertion-implies-post
                                   (,(lastval params) s))))
                 ("Subgoal 7"
                  :use ((:instance concrete-steps-to-cutpoint-tail-def
                                   (,(lastval params) s))))
                        
                 ("Subgoal 8"
                  :use ((:instance assertion-invariant-over-cutpoints
                                   (,(lastval params) s))))
                 ("Subgoal 9"
                  :use ((:instance measure-is-ordinal
                                   (,(lastval params) s))))
                 ("Subgoal 10"
                  :use ((:instance cutpoint-measure-decreases
                                   (,(lastval params) s))))
                 ("Subgoal 11"
                  :use ((:instance some-cutpoint-is-reachable
                                   (,(lastval params) s))))
                 ("Subgoal 12"
                  :in-theory (enable ,run))
                 ("Subgoal 9"
                  :use ((:instance (:definition concrete-steps-to-cutpoint)
                                   (,(lastval params) s))))
                 ("Subgoal 13"
                  :use ((:instance 
                         (:definition ,(packn (list exitsteps '-tail-def)))
                         (,(lastval params) s))))
                 ("Subgoal 14"
                  :use ((:instance (:definition ,exitsteps)
                                   (,(lastval params) s))))))))))



(defun defsimulate-fn (nextt arity mode measure run cutpoint exitpoint default
                            exitsteps pre post assertion define-run? hints thms)
  (declare (xargs :mode :program
                  :guard 
                  (and (symbolp exitsteps)
                       (symbolp nextt)
                       (or (eq mode :partial)
                           (eq mode :total)))))

  (if (eq mode :partial)
      `(encapsulate 
        ()
        ,@(defsimulate-partial 
            nextt run arity 
            cutpoint exitpoint default exitsteps pre post
            assertion define-run? hints thms))

    ;; Total correctness 
    `(encapsulate 
        ()
        ,@(defsimulate-total 
            nextt run arity measure
            cutpoint exitpoint default exitsteps pre post
            assertion define-run? hints thms))))
      
(defmacro defsimulate 
  (nextt
   &key
   ;; Partial opr total correctness?
   (mode ':partial)
   
   ;; arity is the arity of the functions precondition, postcondition,
   ;; assertion, cutpoint, exitpoint, etc. These functions must each have the
   ;; same arity and the arity must be specified here. By default (if all of
   ;; the above are unary) the arity can be left unspecified and is taken to be
   ;; 1.
   (arity '1)
   
   ;; I am not sure if this parameter is necessary. I often while using this
   ;; macro was forgetting to define the function run, and hence getting error
   ;; and so I put this keyword in so that I was testing with it on. If this is
   ;; set then the macro defines a function runn, and it proves all theorems
   ;; using this function. There is no real problem with this definition but if
   ;; the user has already defined run then the user should just use that
   ;; function. That saves him/her the headache of getting everything in terms
   ;; of a function for which (possibly) no induction scheme is exported.
   (define-run? 'nil)

   ;; the measure is required to be specified only for total correctness
   ;; simulation. Can be ignored for partial correctness.
   (measure 'measure)

   ;; Ok now the function names. Notice that you better give me function names
   ;; that are correct, because I have no way of checking. I can check if
   ;; the function exists or not but then I need to call a function that takes
   ;; state and I will not be able to put a defsimulate form then in a
   ;; certified book.

   ;; Note the function run if provided must be of the form (run s n) where the
   ;; first argument is the machine state, and the second is the number of
   ;; steps to run.
   (run 'runn)

   ;; This is the steps-to-exitpoint function that I define. If nothing is
   ;; provided then I will just take the default name 'exitsteps. 
   (exitsteps 'exitsteps)

   ;; Now the other functions.
   (default 'defaultstate)
   (pre 'precondition)
   (post 'postcondition)
   (cutpoint 'cutpointp)
   (exitpoint 'exitpointp)
   (assertion 'assertions)
   ;; I decided to add hints and forms here since I was finding it really
   ;; inconvenient that I cannot write my own openers and cannot give hints to
   ;; control the theorems especially during the debugging stages.
   (hints 'nil)
   (thms 'nil))
  
  (defsimulate-fn nextt arity mode measure run cutpoint exitpoint default
    exitsteps pre post assertion define-run? hints thms))

         

;; Testing: We now consider defining a "concrete version" of the functions step,
;; assertion, cutpoint, etc. and see how the macro is working. 

;; Note: I used to comment out all my testing. But I have since realized that
;; if I submit the book to Matt then I need to have my testing such that books
;; are certified with the testing. This is so that when ACL2 is upgraded my
;; theorems done suddenly start breaking. So I have the tendency of putting
;; bogus encapsulates for testing purposes. Maybe I will remove these to a
;; "testing book" but since this book takes very little time to certify even
;; with the encapsulates below I dont bother.

;; Case 1: Partial correctness. Here is the first example:

;; We define the following functions. For this  first test I am lazy and will
;; simply use the system default names.

;; 

(encapsulate 
 ()
 
 ;; First define the functions that you need.

 (local
  (defun stepp (a) (declare (xargs :normalize nil)) a) )
 (local
  (defun defaultstate () nil))
 
 (local
  (defun precondition (a) (not (equal a nil))))

 (local
  (defun postcondition (a) (declare (ignore a)) t))

 (local 
  (defun cutpointp (a) (not (equal a nil))))
 (local
  (defun assertions (a) (declare (ignore a)) t))

 (local
  (defun exitpointp (a) (declare (ignore a)) nil))

;; Then get the partial correctness theorem by this approach.
 (local
  (defsimulate stepp :define-run? t)))


;; Another example. This uses all the keywords and further allows more than one
;; argument.

(encapsulate 
  nil

  (local (defun stepp2 (a) (declare (xargs :normalize nil)) a))
  (local (defun defaultstate2 () nil))
  (local (defun precondition2 (i a) (declare (ignore i)) (not (equal a nil))))
  (local (defun postcondition2 (i a) (declare (ignore i a)) t))
  (local (defun cutpointp2 (i a) (declare (ignore i))(not (equal a nil))))
  (local (defun assertions2 (i a) (declare (ignore i a)) t))
  (local (defun exitpointp2 (i a) (declare (ignore i a)) nil))

  (local (defun runf (b k) (if (zp k) b (runf (stepp2 b) (1- k)))))

  (local
   (defsimulate stepp2 
     :default defaultstate2
     :cutpoint cutpointp2 
     :assertion assertions2 
     :pre precondition2
     :exitpoint exitpointp2
     :exitsteps exitsteps2
     :post postcondition2
     :arity 2
     :run runf)))


;; Case 2: Total correctness. Here is the first example:

;; We define the following functions. For this  first test I am lazy and will
;; simply use the system default names.


(encapsulate 
 ()
 
 ;; First define the functions that you need.

 (local (defun stepp (a) (declare (xargs :normalize nil)) a) )
 (local (defun defaultstate () nil))
 (local (defun precondition (a) (not (equal a nil))))
 (local (defun postcondition (a) (declare (ignore a)) t))
 (local (defun measure (a) (declare (ignore a)) 0))
 (local (defun cutpointp (a) (not (equal a nil))))
 (local (defun assertions (a) (declare (ignore a)) t))
 (local (defun exitpointp (a) (not (equal a nil))))

;; Then get the partial correctness theorem by this approach.
 (local (defsimulate stepp :mode :total :define-run? t)))


;; Another example. This uses all the keywords and further allows more than one
;; argument.

(encapsulate 
  nil

  (local (defun stepp2 (a) (declare (xargs :normalize nil)) a))
  (local (defun defaultstate2 () nil))
  (local (defun precondition2 (i a) (declare (ignore i)) (not (equal a nil))))
  (local (defun postcondition2 (i a) (declare (ignore i a)) t))
  (local (defun measure2 (i a) (declare (ignore i a)) 0))
  (local (defun cutpointp2 (i a) (declare (ignore i))(not (equal a nil))))
  (local (defun assertions2 (i a) (declare (ignore i a)) t))
  (local (defun exitpointp2 (i a) (declare (ignore i)) (not (equal a nil))))

  (local (defun runf (b k) (if (zp k) b (runf (stepp2 b) (1- k)))))

  (local
   (defsimulate stepp2 
     :default defaultstate2
     :mode :total
     :cutpoint cutpointp2 
     :assertion assertions2 
     :pre precondition2
     :exitpoint exitpointp2
     :measure measure2
     :exitsteps exitsteps2
     :post postcondition2
     :arity 2
     :run runf)))


