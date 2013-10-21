; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the TRACE* book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
; only load for interactive sessions: 
#+acl2s-startup (include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (assign evalable-printing-abstractions nil)

;arithmetic book
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading arithmetic-5/top book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "arithmetic-5/top" :dir :system)

;basic thms/lemmas about lists
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading coi/lists book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "coi/lists/basic" :dir :system)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2's lexicographic-ordering-without-arithmetic book.~%This indicates that either your ACL2 installation is missing the standard books are they are not properly certified.") (value :invisible))
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading DataDef+RandomTesting book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2-datadef/acl2-check" :uncertified-okp nil :dir :acl2s-modes :load-compiled-file :comp)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :load-compiled-file :comp)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)

; Non-events:
(set-guard-checking :none)

;Settings for avoiding control stack errors for testing non-tail-recursive fns
(defdata-testing pos :test-enumerator nth-pos-testing)
(defdata-testing integer :test-enumerator nth-integer-testing)
(defdata-testing nat :test-enumerator nth-nat-testing)
(defdata-testing neg :test-enumerator nth-neg-testing)


; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;$ACL2s-LMode$;Demo

(in-package "ACL2")


(defdata reg nat)
(defdata pc nat)
(defdata register (map reg nat))
(defdata dmemory (map nat integer))
                      

(defdata operation-code (enum '(add sub mul load loadi store bez jump)))

       
(defdata inst (record (opcode . operation-code)
                      (rc . reg)
                      (ra . reg)
                      (rb . reg)))

(defdata imemory (map pc inst))

(defdata ISA (record 
              (pc . pc)
              (regs . register)
              (imem . imemory)
              (dmem . dmemory)))

 
(defdata latch1 (record (validp . boolean)
                        (op . operation-code)
                        (rc . reg)
                        (ra . reg)
                        (rb . reg)
                        (pch . pc)))


(defdata latch2 (record (validp . boolean)
                        (op . operation-code)
                        (rc . reg)
                        (ra-val . nat)
                        (rb-val . nat)
                        (pch . pc)))

  
(defdata MAA (record  (pc . pc)
                      (regs . register)
                      (imem . imemory)
                      (dmem . dmemory)
                      (ltch1 . latch1)
                      (ltch2 . latch2)))

(acl2s-defaults :set num-trials 1)

;:set-ignore-ok t
;Here is one of the 3000 subgoals which failed:

;(set-acl2s-random-testing-debug 1)

;(trace$ process-dependencies do-let*-ordering conditional-eval)

(test?
 (implies (and (maap w)
               (equal (mget :pc w)
                      (+ 1 (mget :pch (mget :ltch2 w))))
               (equal t 
                      (mget :validp (mget :ltch2 w)))
               (equal (mget (mget :rb (mget (mget :pch (mget :ltch2 w))
                                            (mget :imem w)))
                            (mget :regs w))
                      (mget :rb-val (mget :ltch2 w)))
               (equal (mget :opcode (mget (mget :pch (mget :ltch2 w))
                                          (mget :imem w)))
                      'bez)
               (equal 0
                      (mget (mget :ra (mget (mget :pch (mget :ltch2 w))
                                            (mget :imem w)))
                            (mget :regs w)))
               
               (equal 0 (mget :ra-val (mget :ltch2 w)))
               
               )
          (not (equal (mget :op (mget :ltch2 w)) 'bez))))

(acl2s-defaults :set num-trials 100)

(test? 
       (IMPLIES (AND (MAap W)
               (INTEGERP (MGET :PC W))
               (EQUAL (+ 1 (MGET :PCH (MGET :LTCH2 W)))
                      (MGET :PC W))
               (EQUAL T (MGET :VALIDP (MGET :LTCH2 W)))
               (EQUAL (MGET (MGET :RB (MGET (MGET :PCH (MGET :LTCH2 W))
                                            (MGET :IMEM W)))
                            (MGET :REGS W))
                      (MGET :RB-VAL (MGET :LTCH2 W)))
               (EQUAL (MGET :OPCODE (MGET (MGET :PCH (MGET :LTCH2 W))
                                          (MGET :IMEM W)))
                      'BEZ)
               (EQUAL 0
                      (MGET (MGET :RA (MGET (MGET :PCH (MGET :LTCH2 W))
                                            (MGET :IMEM W)))
                            (MGET :REGS W)))
               (INTEGERP (+ (MGET :PCH (MGET :LTCH2 W))
                            (MGET :RB-VAL (MGET :LTCH2 W))))
               (NOT (MGET :VALIDP (MGET :LTCH1 W)))
               (EQUAL (MGET :OP (MGET :LTCH2 W)) 'BEZ)
               (EQUAL 0 (MGET :RA-VAL (MGET :LTCH2 W))))
          
          (NOT (INTEGERP (+ 1 (MGET :PCH (MGET :LTCH2 W))
                            (MGET (MGET :RB (MGET (MGET :PCH (MGET :LTCH2 W))
                                                  (MGET :IMEM W)))
                                  (MGET :REGS W)))))))

(test?
 (IMPLIES
 (AND
  (MAaP W)
  (EQUAL (MGET :OPCODE (MGET (MGET :PCH (MGET :ltch2 W))
                             (MGET :IMEM W)))
         'BEZ)
  (ACL2-NUMBERP (MGET :PCH (MGET :ltch2 W)))
  (EQUAL NIL (MGET :VALIDP (MGET :ltch1 W)))
  (EQUAL (MGET :OP (MGET :ltch2 W)) 'BEZ)
  (NOT (EQUAL 0 (MGET :RA-VAL (MGET :ltch2 W))))
  
  (INTEGERP (MGET :PC W))
  (EQUAL (+ 1 (MGET :PCH (MGET :ltch2 W)))
         (MGET :PC W))
  (EQUAL T (MGET :VALIDP (MGET :ltch2 W)))
  (EQUAL (MGET (MGET :RA (MGET (MGET :PCH (MGET :ltch2 W))
                               (MGET :IMEM W)))
               (MGET :REGS W))
         (MGET :RA-VAL (MGET :ltch2 W))))
 (NOT (EQUAL (MGET (MGET :RB (MGET (MGET :PCH (MGET :ltch2 W))
                                   (MGET :IMEM W)))
                   (MGET :REGS W))
             (MGET :RB-VAL (MGET :ltch2 W))))))




(test?
 (IMPLIES
 (AND
  (MAaP W)
  (EQUAL (MGET :OPCODE (MGET (MGET :PCH (MGET :ltch2 W))
                             (MGET :IMEM W)))
         'BEZ)
  (ACL2-NUMBERP (MGET :PCH (MGET :ltch2 W)))
  (EQUAL NIL (MGET :VALIDP (MGET :ltch1 W)))
  (EQUAL (MGET :OP (MGET :ltch2 W)) 'BEZ)
  (NOT (EQUAL 0 (MGET :RA-VAL (MGET :ltch2 W))))
  #|
  (MAaP
      (MSET :PC (+ 1 (MGET :PC W))
            (MSET :DMEM (MGET :DMEM W)
                  (MSET :IMEM (MGET :IMEM W)
                        (MSET :REGS (MGET :REGS W)
                              ;(MSET :TYPE 'MA
                                    (MSET :ltch1
                                          ;(MSET :TYPE 'LATCH1
                                                (MSET :VALIDP NIL NIL)
                                          (MSET :ltch2
                                                ;(MSET :TYPE 'LATCH2
                                                      (MSET :VALIDP NIL NIL)
                                                NIL)))))))
  |#
  (INTEGERP (MGET :PC W))
  (EQUAL (+ 1 (MGET :PCH (MGET :ltch2 W)))
         (MGET :PC W))
  (EQUAL T (MGET :VALIDP (MGET :ltch2 W)))
  (EQUAL (MGET (MGET :RA (MGET (MGET :PCH (MGET :ltch2 W))
                               (MGET :IMEM W)))
               (MGET :REGS W))
         (MGET :RA-VAL (MGET :ltch2 W))))
 (NOT (EQUAL (MGET (MGET :RB (MGET (MGET :PCH (MGET :ltch2 W))
                                   (MGET :IMEM W)))
                   (MGET :REGS W))
             (MGET :RB-VAL (MGET :ltch2 W))))))
 
;Mitesh's bug (removed from stall1p the predicate (eqyal l1ra l2rc))
(test?
(IMPLIES
 (AND
  (EQUAL (MGET :PC W)
         (+ 1 (MGET :PCH (MGET :Ltch1 W))))
  (MAAP W)
  (EQUAL (MGET :OPCODE (MGET (MGET :PCH (MGET :Ltch2 W))
                             (MGET :IMEM W)))
         'LOADI)
  (ACL2-NUMBERP (MGET :PCH (MGET :Ltch2 W)))
  (EQUAL (MGET :OP (MGET :Ltch2 W))
         'LOADI)
  (NOT (EQUAL (MGET :OPCODE (MGET (MGET :PC W) (MGET :IMEM W)))
              'JUMP))
  (NOT (EQUAL (MGET :OPCODE (MGET (MGET :PC W) (MGET :IMEM W)))
              'BEZ))
  #|
  (MAAP
   (MSET
    :PC (+ 1 (MGET :PC W))
    (MSET
     :DMEM (MGET :DMEM W)
     (MSET
      :IMEM (MGET :IMEM W)
      (MSET
       :REGS
       (MSET (MGET :RC (MGET :Ltch2 W))
             (MGET (MGET :RA-VAL (MGET :Ltch2 W))
                   (MGET :DMEM W))
             (MGET :REGS W))
       ;(MSET
        ;:TYPE 'MA
        (MSET
         :Ltch1
         (MSET
              :OP
              (MGET :OPCODE (MGET (MGET :PC W) (MGET :IMEM W)))
              (MSET :RA
                    (MGET :RA (MGET (MGET :PC W) (MGET :IMEM W)))
                    (MSET :RB
                          (MGET :RB (MGET (MGET :PC W) (MGET :IMEM W)))
                          (MSET :RC
                                (MGET :RC (MGET (MGET :PC W) (MGET :IMEM W)))
                                (MSET :PCH (MGET :PC W)
                                      (MSET :TYPE 'Ltch1
                                            (MSET :VALIDP T NIL)))))))
         (MSET
          :Ltch2
          (MSET
              :OP 'LOADI
              (MSET :RC (MGET :RC (MGET :Ltch1 W))
                    (MSET :PCH (MGET :PCH (MGET :Ltch1 W))
                          (MSET :TYPE 'Ltch2
                                (MSET :RA-VAL
                                      (MGET (MGET :RA (MGET :Ltch1 W))
                                            (MGET :REGS W))
                                      (MSET :RB-VAL
                                            (MGET (MGET :RB (MGET :Ltch1 W))
                                                  (MGET :REGS W))
                                            (MSET :VALIDP T NIL)))))))
          NIL)))))))
  |#
  (INTEGERP (MGET :PC W))
  (EQUAL (+ 2 (MGET :PCH (MGET :Ltch2 W)))
         (MGET :PC W))
  (EQUAL T (MGET :VALIDP (MGET :Ltch1 W)))
  (EQUAL T (MGET :VALIDP (MGET :Ltch2 W)))
  (EQUAL (MGET :OPCODE (MGET (MGET :PCH (MGET :Ltch1 W))
                             (MGET :IMEM W)))
         'LOADI)
  (EQUAL (+ 1 (MGET :PCH (MGET :Ltch2 W)))
         (MGET :PCH (MGET :Ltch1 W)))
  (EQUAL (MGET :RA (MGET (MGET :PCH (MGET :Ltch1 W))
                         (MGET :IMEM W)))
         (MGET :RA (MGET :Ltch1 W)))
  (EQUAL (MGET :RC (MGET (MGET :PCH (MGET :Ltch1 W))
                         (MGET :IMEM W)))
         (MGET :RC (MGET :Ltch1 W)))
  (EQUAL (MGET (MGET :RA (MGET (MGET :PCH (MGET :Ltch2 W))
                               (MGET :IMEM W)))
               (MGET :REGS W))
         (MGET :RA-VAL (MGET :Ltch2 W)))
  (EQUAL (MGET :RC (MGET (MGET :PCH (MGET :Ltch2 W))
                         (MGET :IMEM W)))
         (MGET :RC (MGET :Ltch2 W)))
  (EQUAL (MGET :OP (MGET :Ltch1 W))
         'LOADI))
 ;conclusion
 (EQUAL (MGET (MGET :RA (MGET :Ltch1 W))
              (MSET (MGET :RC (MGET :Ltch2 W))
                    (MGET (MGET :RA-VAL (MGET :Ltch2 W))
                          (MGET :DMEM W))
                    (MGET :REGS W)))
        (MGET (MGET :RA (MGET :Ltch1 W))
              (MGET :REGS W)))))

(mutual-recursion
 ;cons up calls
 (defun build-enumcall-rec-lst1 (te-lst typ defs sizes wrld state ans)
    (declare (xargs :stobjs (state) :mode :program))
   (if (endp te-lst)
     (value ans)
     (er-let* ((call 
                (build-enumcall-rec1 (car te-lst) typ
                                    defs sizes wrld state)))
       (build-enumcall-rec-lst1 (cdr te-lst) typ
                               defs sizes wrld state (append ans (list call)))))) 
      
 (defun build-enumcall-rec1 (te typ defs size wrld state)
   (declare (xargs :stobjs (state) :mode :program))
   (cond 
;constant values are returned unchanged
    ((defdata::possible-constant-valuep te)
     (value te));constant (singleton type)
;primitive/custom/registered-custom types dont have definition bodies
    ((or (defdata::is-a-registered-custom-type te wrld)
         (defdata::is-a-custom-type te wrld))
     (er-let* ((enum-info 
                (get-enum-info te 'build-enumcall-rec wrld state)))
       (build-enumcall-from-enum-info te enum-info 
                                      'build-enumcall-rec state)))
;defdata type has definition stored in types-info-table
      ;; defdata mutually-recursive sibling type
      ((and (symbolp te)
            (not (eq te typ))
            (assoc-eq te defs))
       (build-enumcall-rec1 (car (defdata::get-val te defs))
                            te defs (1- size) wrld state))
      ;; defdata type other than typ (and also not a sibling mut-rec type)         
      ((and (symbolp te)
            (not (eq te typ))
            (defdata::is-a-defdata-type te wrld))
       (mv-let (size state);take new size just in case its recursive
               (random-small-length state)
               (let* ((tbl (table-alist 'defdata::types-info-table wrld))
                      (defs (fifth (defdata::get-val te tbl)))
                      (def (car (defdata::get-val te defs))))
                 (er-let* ((call (build-enumcall-rec1 
                                  def te defs size wrld state)))
                   (value (list te :size size call)))))) 
      ;; defdata type same as typ
      ((eq te typ)
       (build-enumcall-rec1 (car (defdata::get-val typ defs))
                            typ defs (1- size) wrld state))
      ((atom te) 
       (er soft 'build-enum-rec "~x0 is an ill-formed type exp~%" te))
;consp 
;union type expression
      ((defdata::mem1 (car te) '(oneof anyof))
       (let ((bi-s (get-base-member-i-s (cdr te) 0 typ))
             (ri-s (get-recursive-member-i-s (cdr te) 0 typ)))
         (if (or (= size 0) (null ri-s))
;Either non-recursive union expression or recursion size limit reached
           (er-let* ((bi (random-elem bi-s state))
;randomly pick a base member
                     (call (build-enumcall-rec1 (nth bi (cdr te)) typ defs
                                                size wrld state)))
             (value (list :bindex bi (len bi-s) call)))
;otherwise pick a recursive member and recurse
           (er-let* ((ri (random-elem ri-s state))
                     (call (build-enumcall-rec1 (nth ri (cdr te)) typ defs
                                                size wrld state)))
             (value (list :rindex ri (len ri-s) call))))))
;macro-call/product-expression
       (t (build-enumcall-rec-lst1 (cdr te)
                                   typ defs
                                   size wrld state (list (car te))))))

)


(defun coerce-well-formedness (alist)
  (if (good-map alist)
    alist
    (if (endp alist)
      nil
      (if (wf-keyp (caar alist))
        (s (caar alist) (cdar alist)
           (coerce-well-formedness (cdr alist)))
        (coerce-well-formedness (cdr alist))))))

(defthm coerce-well-formedness-gives-good-map
  (good-map (coerce-well-formedness r)))

(defun val (x alist)
  (cdr (assoc-equal x alist)))

(defmacro defdata-map (tname texp1 texp2)
  (let ((orig-pred (defdata::modify-symbol "IFR" tname "P"))
        (ifr-name (defdata::modify-symbol "IFR" tname nil)) 
        (pred (defdata::modify-symbol nil tname "P"))
        (enum (defdata::modify-symbol "NTH-" tname nil)))
    `(progn
      (defdata ,ifr-name
        (listof (cons ,texp1 ,texp2)))
      (defun ,pred (v)
        (declare (xargs :guard t))
        (and (good-map v)
             (,orig-pred v)))
      (defun ,enum (n)
        (coerce-well-formedness
         (,(defdata::modify-symbol "NTH-IFR" tname nil) n)))
      (table
            defdata::types-info-table
             ',tname 
             '(t ,enum ,pred nil ((,tname ,ifr-name))
                      t);defdata == derived data-type
             :put))))


;CCG example
(defun nnf (f)
   (cond ((posp f) f)
        ((and (eq (first f) 'not) (posp (second f))) f)
        ((and (eq (first f) 'not) (eq 'not (first (second f)))) (nnf f))
        ((eq (first f) 'and) (list 'and (nnf (second f)) (nnf (third f))))
        ((eq (first f) 'or) (list 'or (nnf (second f)) (nnf (third f))))
        ((eq (first f) 'implies) (list 'implies (nnf (second f)) (nnf (third f))))
        ((and (eq (first f) 'not)
              (eq 'and (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'or (nnf (list 'not lhs)) (nnf (list 'not rhs)))))
        ((and (eq (first f) 'not)
              (eq 'or (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'and (nnf (list 'not lhs)) (nnf (list 'not rhs)))))     
         ((and (eq (first f) 'not)
              (eq 'implies (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'and (nnf lhs) (nnf (list 'not rhs)))))
        (t f)))

;GOOD EXAMPLE
(defthm rel-count-stupid
  (implies (rel (remove-el y A) (remove-el y B))
           (equal (count-el x A)
                  (count-el x B))))
#|
ACL2 Warning [Free] in ( DEFTHM REL-COUNT-STUPID ...):  A :REWRITE
rule generated from REL-COUNT-STUPID contains the free variables B
and Y.  These variables will be chosen by searching for an instance
of (REL (REMOVE-EL Y A) (REMOVE-EL Y B)) in the context of the term
being rewritten.  This is generally a severe restriction on the applicability
of a :REWRITE rule.  See :DOC free-variables.


<< Starting proof tree logging >>


[Note: We now enable non-linear arithmetic.]


[Note:  A hint was supplied for our processing of the goal above. 
Thanks!]

Random testing above formula with type-alist 
((Y ALL) (A ALL) (B ALL) (X ALL))


We falsified the conjecture. Here is the counterexample:
 -- (B (0 . T)), (A NIL), (Y 0) and (X 0)

Cases in which the conjecture is true include:
 -- (B 3), (A #\a), (Y #\b) and (X (0 T T))
 -- (B 0), (A 0), (Y #\a) and (X NIL)
 -- (B T), (A 0), (Y T) and (X (0 . 0))

We tried 100 random trials, 55 of which satisfied the hypotheses. Of
these, one was a counterexample and 54 were witnesses.
See :doc random-testing for more information.

Summary
Form:  ( DEFTHM REL-COUNT-STUPID ...)
Rules: NIL
Warnings:  Free
Time:  15.44 seconds (prove: 15.44, print: 0.00, proof tree: 0.00, other: 0.00)

ACL2 Error in ( DEFTHM REL-COUNT-STUPID ...):  See :DOC failure.

******** FAILED ********
|#

(defun sum-n (n)
  (if (zp n)
    0
    (+ (nfix n) (sum-n (- n 1)))))
(defthm sum-less-than
  (implies (and (natp x)
                (natp y)
                (< (sum-n x) (sum-n y)))
           (< x y))
  :rule-classes (:rewrite))
#|
(defthm whatman
  (implies (and (natp y)
                (natp p)
                (< (sum-n y) (sum-n (+ 1 p)))
                (<= p y))
           (equal (equal y p) t)))
|#

(defun rev (x)
  (if (consp x)
      (append (rev (cdr x)) (cons (car x) nil))
    x))

;(thm (true-listp (rev (rev x))))


#|
(include-book "acl2-check")

(set-acl2s-random-testing-num-of-witnesses-to-generate 10)
(set-acl2s-random-testing-num-of-counterexamples-to-generate 10)
(set-acl2s-random-testing-verbose t)
(set-acl2s-random-testing-enabled t)
(set-acl2s-random-testing-max-num-of-random-trials 100)
(set-acl2s-random-testing-debug nil)
|#
;(set-acl2s-random-testing-enabled nil)


;(thm (equal (rev (rev x)) x))

(program)
(DEFUN ROTATE-RIGHT (L)
                    (DECLARE (XARGS :GUARD (TRUE-LISTP L)))
                    (IF (ENDP L)
                        NIL
                        (CONS (CAR (LAST L)) (BUTLAST L 1))))
(set-acl2s-random-testing-use-instantiation-method 'simple)
(trace$ thm-fn translate)
(test? (implies (true-listp l) (equal (len (rotate-right l)) (len l))))

(logic)

(defconst *colors* '(blue red yellow green fuchsia purple))

(set-acl2s-random-testing-enabled t)

;(assign make-event-debug t)

(defdata color (enum *colors*))

(assign make-event-debug t)

(defdata row (listof color))
(set-acl2s-defdata-verbose t)
(set-acl2s-random-testing-enabled t)
;(set-ccg-inhibit-output-lst *ccg-valid-output-names*)
(set-ccg-print-proofs t)

(defun canComposeRes (res-lst target-res acc-res)
  (if (endp res-lst)
    (if (equal target-res acc-res)
      t
      nil)
    (or (canComposeRes (rest res-lst) target-res (compose-in-parallel acc-res (first res-lst)))
        (canComposeRes (rest res-lst) target-res (compose-in-serial acc-res (first res-lst))))))
    

(defdata lon (listof nat))

(test? (implies (true-listp n) (< (len n) 5)))

(set-acl2s-random-testing-num-of-witnesses-to-generate 3)
(set-acl2s-random-testing-num-of-counterexamples-to-generate 0)
;(trace$ print-stats)
(set-acl2s-random-testing-verbose nil)

;(include-book "arithmetic/top" :dir :system)
;(include-book "coi/lists/list-top" :dir :system)


(set-acl2s-random-testing-max-num-of-random-trials 300)

(thm (IMPLIES (AND (RATIONALP X)
                    (RATIONALP Y)
                    (NOT (EQUAL Y 0))
                    (<= 0 Y)
                    (<= 0 X)
                    (<= Y X)
                    (INTEGERP (+ 1 (- X)))
                    (< 1 X)
                    (NOT (INTEGERP (+ 1 (- X) (* 2 Y))))
                    (<= X (+ 1 (* 2 Y))))
               (< X
                  (+ 1 (DENOMINATOR (+ 1 (- X) (* 2 Y)))
                     (NUMERATOR (+ 1 (- X) (* 2 Y)))))))

(thm? (implies (true-listp x)
              (equal (reverse (reverse x)) x)))



(test? (implies (and (posp (car x))
                     (equal y y)
                     (equal z y)
                     (posp (cdr x)))
                (<= (cdr x) (len x)))
       )
(test? (implies (and (posp (car x))
              (posp (cdr x)))
         (<= (cdr x) (len x)))
              )

(thm? (equal x (cons z y)))


(thm? (equal x y))


(thm (implies (true-listp x)
              (equal (reverse (reverse x)) x)))

(include-book "arithmetic-5/top" :dir :system)
(defthm ok (IMPLIES (AND (RATIONALP X)
                    (RATIONALP Y)
                    (NOT (EQUAL Y 0))
                    (<= 0 Y)
                    (<= 0 X)
                    (<= Y X)
                    (INTEGERP (+ 1 (- X)))
                    (< 1 X)
                    (NOT (INTEGERP (+ 1 (- X) (* 2 Y))))
                    (<= X (+ 1 (* 2 Y))))
               (< X
                  (+ 1 (DENOMINATOR (+ 1 (- X) (* 2 Y)))
                     (NUMERATOR (+ 1 (- X) (* 2 Y)))))))

(defun pascal (r c)
  (if (or (zp r) (zp c) (>= c r))
    1
    (+ (pascal (- r 1) c)
       (pascal (- r 1) (- c 1)))))

(defun app (x y)
  (if (endp x)
    y
    (cons (car x) (app (cdr x) y))))

(test? (implies (and (true-listp x)
                     (true-listp y))
                (true-listp (app x y))))

;(pascal 200 30)

(defun fact (n)
  (if (zp n)
      1
    (* n (fact (- n 1)))))

(defun choose (n k)
  (/ (fact n)
     (* (fact k) (fact (- n k)))))


(thm
 (implies (and (natp x) (natp y) (>= x y)
               (or (zp x) (zp y) (>= y x)))
          (= (pascal x y) (choose x y))))


(thm
 (implies (and (natp x) (natp y) (>= x y)
               (not (or (zp x) (zp y) (>= y x)))
               (= (pascal (- x 1) y)
                  (choose (- x 1) y))
               (= (pascal (- x 1) (- y 1))
                  (choose (- x 1) (- y 1))))
          (= (pascal x y) (choose x y))))


(test? (implies (rationalp x)
                (not (equal x (/ 12312312 213712312445)))))



(test? (implies (and (posp (car x))
              (posp (cdr x)))
         (<= (cdr x) (len x)))
              )




;(include-book "acl2-check")

(defun app (x y)
  (if (endp x)
    y
    (cons (car x) (app (cdr x) y))))

(thm-fn '(implies (and (true-listp x)
                                     (true-listp y))
                                (true-listp (app x y)))
         state 
         '(("Goal"
            ;:do-not-induct t 
            :do-not '(generalize fertilize)))
         nil nil)

(test? (implies (and (true-listp x) (true-listp y))
                (true-listp (app x y))))


(defun split-list (x)
  (cond ((atom x) (mv nil nil))
        ((atom (cdr x)) (mv x nil))
        (t (mv-let (a b)
                   (split-list (cddr x))
                   (mv (cons (car x) a) (cons (cadr x) b))))))




(set-acl2s-random-testing-enabled nil)
(defun wffp-flag (flag sexp)
  (if (equal flag 'term)
    (cond ((endp sexp) t)
          ((or (equal (car sexp) 'or)
               (equal (car sexp) 'and)) (and (> (length sexp) 2)
                                             (wffp-flag 'list (cdr sexp))))
          ((equal (car sexp) 'not) (and (= (length sexp) 2)
                                        (wffp-flag 'term (cadr sexp))))
          ((or (equal (car sexp) 'iff)
               (equal (car sexp) 'xor)) (and (= (length sexp) 3)
                                             (wffp-flag 'list (cdr sexp))))
          ((equal (car sexp) 'ite) (and (= (length sexp) 4)
                                        (wffp-flag 'list (cdr sexp))))
          (t nil))
    (cond ((endp sexp) t)
          (t (and (wffp-flag 'term (car sexp))
                  (wffp-flag 'list (cdr sexp)))))))
(set-acl2s-random-testing-enabled t)
(set-acl2s-random-testing-max-num-of-random-trials 20)
(set-acl2s-random-testing-verbose nil)

(defun maj (p q c)
  (or (and p q)
      (or (and p c)
          (and q c))))

(defun full-adder (p q c)
  (mv (xor p (xor q c))
      (maj p q c)))
(set-guard-checking t)

(defun serial-adder (a b c)
  (cond ((and (endp a) (endp b))
         (list c))
        (t (mv-let (sum cout)
                   (full-adder (first a) (first b) c)
                   (cons sum (serial-adder (rest a) (rest b) cout))))))

(set-acl2s-random-testing-verbose t)
(set-acl2s-random-testing-enabled t)
(set-acl2s-random-testing-max-num-of-random-trials 50)

; utility function for making symbols
(defun bvname (basename width count)
  (cond ((zp width) nil)
        (t (cons (intern (coerce
                          (append (coerce basename 'list)
                                  (list #\[)
                                  (explode-nonnegative-integer count 10 nil)
                                  (list #\]))
                          'string)
                         "ACL2")
                 (bvname basename (1- width) (1+ count))))))

;(defdata-testing pos :test-enumerator nth-pos-testing)
;(defdata-testing integer :test-enumerator nth-integer-testing)
;(defdata-testing nat :test-enumerator nth-nat-testing)
;(defdata-testing neg :test-enumerator nth-neg-testing)
;(set-acl2s-random-testing-use-test-enumerator t)

(thm 
     (implies (and (stringp bvaname)
                   (posp n)
                   (natp b))
              (symbol-listp (bvname bvaname n b))))


(set-acl2s-random-testing-enabled t)

;this checks that top goal counterexamples are printed

(test? (implies (and (posp (car x))
              (posp (cdr x)))
         (<= (cdr x) (len x)))
              )




(set-acl2s-random-testing-verbose t)

(thm? (implies (and (or (true-listp x)
                             (stringp x))
                         (not (equal x nil))
                         (not (equal x "")))
                    (> (len x) 0)))

;TODO: NIL causing problem above in bindings

(thm (iff (implies p q) (or (not p) p)))

(test? (implies (and (posp (car x))
                     (equal y y)
                     (equal z y)
                     (posp (cdr x)))
                (<= (cdr x) (len x)))
       )

(include-book "arithmetic/top" :dir :system)
;(include-book "coi/lists/list-top" :dir :system)


(set-acl2s-random-testing-max-num-of-random-trials 300)

(thm? (IMPLIES (AND (RATIONALP X)
                    (RATIONALP Y)
                    (NOT (EQUAL Y 0))
                    (<= 0 Y)
                    (<= 0 X)
                    (<= Y X)
                    (INTEGERP (+ 1 (- X)))
                    (< 1 X)
                    (NOT (INTEGERP (+ 1 (- X) (* 2 Y))))
                    (<= X (+ 1 (* 2 Y))))
               (< X
                  (+ 1 (DENOMINATOR (+ 1 (- X) (* 2 Y)))
                     (NUMERATOR (+ 1 (- X) (* 2 Y)))))))
(set-acl2s-random-testing-num-of-counterexamples-to-generate 10)
(test? (implies (and (posp (car x))
                     (equal y y)
                     (equal z y)
                     (posp (cdr x)))
                (<= (cdr x) (len x)))
       )

(thm? (IMPLIES (AND (RATIONALP X)
              (RATIONALP Y)
              (NOT (EQUAL Y 0))
              (<= 0 Y)
              (<= 0 X)
              (<= Y X))
         (O< (ACL2-COUNT (+ 1 0 (- (+ (+ X (- Y)) Y))))
             (ACL2-COUNT (+ 1 Y (- (+ X (- Y))))))))



;----------------------------------------------------------------------------
(defun s (alist key val)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) (cons (cons key val) nil))
        ((equal (caar alist) key) (cons (cons key val) (cdr alist)))
        (t (cons (car alist) (s (cdr alist) key val)))))

(defun s-many (alist keys vals)
  (declare (xargs :guard (and (alistp alist)
                              (true-listp keys)
                              (true-listp vals)
                              (equal (length keys)
                                     (length vals)))))
  (if (or (endp keys) (endp vals))
    alist
    (s-many (s alist (car keys) (car vals)) (cdr keys) (cdr vals))))

(defthm getseteq
           (equal (assoc-equal key (s alist key val)) (cons key val)))

(defthm set-persists
  (assoc-equal key (s (s alist key val) key2 val2)))

(defthm set-ow-vac
  (implies (not (assoc-equal key (s alist key1 val1)))
           (not (assoc-equal key alist))))

(defthm set-many-no-delete
  (implies (assoc-equal key alist)
           (assoc-equal key (s-many alist keys vals))))

(set-acl2s-random-testing-enabled nil)



(defthm set-many-persists
  (assoc-equal key (s-many (s alist key val) keys vals))
   :hints (("Goal" :do-not '(generalize))))




(defthm alist-no-overwrite
  (implies (not (equal key1 key2))
           (equal (assoc-equal key1 (s alist key2 val2)) (assoc-equal key1
alist))))

(defthm set-is-alist
  (implies (alistp alist)
           (alistp (s alist key val))))

(defun distinctlistp (lst)
  (equal lst (remove-duplicates-equal lst)))

(defun list-in-alistp (lst alist)
  (if (endp lst)
      t
    (and (assoc-equal (car lst) alist)
         (list-in-alistp (cdr lst) alist))))

(defthm s-no-overwrite
  (assoc-equal a (s-many (s alist a v) keys vals)))


;----------------------------------------------------------------------------


;returns controller pocket
(defun is-recursive-fn (nm wrld)
  (declare (xargs :mode :program))
  (if (and (not (symbolp nm))
           (not (function-symbolp nm wrld)))
    nil
    (let ((rl (find-runed-lemma `(:definition ,nm)
                                (getprop nm 'lemmas nil
                                         'current-acl2-world wrld))))
      (if rl
        (let ((ctrl-pocket  (cdr (assoc-eq nm (cdr (access rewrite-rule
                                                           rl
                                                           :heuristic-info))))))
          (if (defdata::mem1 'T ctrl-pocket)
            ctrl-pocket
            nil))
        nil))))

(trace$ extract-var-typ-alist-from-term)
(defun how-many (e x)
  (cond
   ((endp x)
    0)
   ((equal e (car x))
    (1+ (how-many e (cdr x))))
   (t
    (how-many e (cdr x)))))

; We aim to prove that (perm x y) is the same as checking that for all e,
; (how-many e x) is (how-many e y).  We can do that by defining the function
; (perm-counter-example x y) -- the counterexample generator -- that finds an e that occurs a
; different number of times in x than in y.

; Thus, the following definition is modeled after the definition of perm.
(defun rm (e x)
  (if (consp x)
      (if (equal e (car x))
          (cdr x)
          (cons (car x) (rm e (cdr x))))
      nil))
(defun tlfix (x)
  (if (endp x)
      nil
    (cons (car x) (tlfix (cdr x)))))

(defun memb (e x)
  (if (consp x)
      (or (equal e (car x))
          (memb e (cdr x)))
      nil))


(defun perm-counter-example (x y)
  (cond ((atom x)
         (car y))
        ((not (memb (car x) y))
         (car x))
        (t (perm-counter-example (cdr x) (rm (car x) y)))))
(thm? (equal (perm-counter-example (tlfix x) y)
         (perm-counter-example x y)))
(set-guard-checking t)
(thm? (implies (not (consp x))
               (equal (perm-counter-example x (tlfix y))
                      (perm-counter-example x y))))


(test?
 (IMPLIES (NOT (CONSP X))
          (EQUAL (< X (nFIX Y))
                 (< X Y))))

(thm 
     (implies (and (stringp bvaname)
                   (posp n)
                   (natp b))
              (symbol-listp (bvname bvaname n b))))


(let ((name 'bvname))
  (find-runed-lemma `(:definition ,name)
                                       (getprop name 'lemmas nil
                                                'current-acl2-world (w state))))



(let ((name 'len))
  (cdr (assoc-eq
        name
        (cdr (access rewrite-rule
                     (find-runed-lemma `(:definition ,name)
                                       (getprop name 'lemmas nil
                                                'current-acl2-world (w state)))
                     :heuristic-info)))))

  




(in-theory (disable bvname))
 (in-theory (enable bvname))   
  
  
(mutual-recursion

 (defun collect-fns-from-term (term wrld acc)
   (declare (xargs :mode :program
                   :guard (and (symbol-listp acc)
                               (plist-plist-worldp wrld)
                               (termp term wrld))))

   ;; Fns is a list of function symbols and term is an ACL2 term.
   ;; We determine whether any fn in fns is used anywhere in term.

   (cond ((or (variablep term)
              (fquotep term)
              (not (function-symbolp (ffn-symb term) wrld))) 
              
          acc)
         ((flambda-applicationp term) 
          (let ((fns (collect-fns-from-term (third (car term)) wrld nil)))
            (collect-fns-from-term-lst (fargs term) wrld (append fns acc))))
         ((defdata::mem1 (ffn-symb term) '(if equal not implies iff car cons cdr BINARY-+ UNARY--
                                            mv mv-let and or))
          (collect-fns-from-term-lst (cdr term) wrld acc));ignore these
         ((not (find-runed-lemma `(:definition ,(ffn-symb term))
                                (getprop (ffn-symb term) 'lemmas nil
                                         'current-acl2-world wrld)))
          (collect-fns-from-term-lst (fargs term) wrld acc));ignore boot-strap fns
         (t
          (collect-fns-from-term-lst (fargs term) wrld (cons (ffn-symb term) acc)))))

 (defun collect-fns-from-term-lst (terms wrld acc)
   (declare (xargs :guard (and (plist-plist-worldp wrld)
                               (symbol-listp acc)
                               (term-listp terms wrld))))
   (if (endp terms)
       acc
     (let ((fns (collect-fns-from-term (car terms) wrld nil)));start
       (collect-fns-from-term-lst (cdr terms) wrld (append fns acc)))))

 )
(defun collect-functions-from-term (term wrld)
   (declare (xargs :mode :program
                   :guard (and (plist-plist-worldp wrld)
                               (termp term wrld))))
   (remove-duplicates-eql (collect-fns-from-term term wrld nil)))
  (defun get-matching-args (args bools)
    (declare (xargs :guard (and (true-listp args)
                                (boolean-listp bools)
                                (equal (len args) (len bools)))))
    (if (endp args)
      nil
      (if (car bools)
        (cons (car args) (get-matching-args (cdr args) (cdr bools)))
        (get-matching-args (cdr args) (cdr bools)))))
              
                    
 (defun get-controller-arguments-for-fun-call (fn-call wrld)
  (declare (xargs :mode :program
                  :guard (and (pseudo-termp fn-call)
                              (function-symbolp (ffn-symb fn-call) wrld)
                              (plist-plist-worldp wrld))))
  (let ((ctlr-pocket (is-recursive-fn (ffn-symb fn-call) wrld)))
    (if ctrlr-pocket 
      (get-matching-args (fargs fn-call) ctrlr-pocket)
      
  
(set-acl2s-random-testing-enabled nil)
(thm 
     (implies (and (stringp bvaname)
                   (posp n)
                   (natp b))
              (symbol-listp (bvname bvaname n b))))

(trace* prettyify-clause)
(thm (iff (implies p q) (or (not p) p)))

(test? (implies (and (posp (car x))
                     (equal y y)
                     (equal z y)
                     (posp (cdr x)))
                (<= (cdr x) (len x)))
       )


(defun rv3 (x)
  (if (endp x)
    nil
    (if (endp (cdr x))
      (list (car x))
      (cons (car (rv3 (cdr x)))
            (rv3 (cons (car x)
                       (rv3 (cdr (rv3 (cdr x))))))))))
(defun ack (x y)
  (cond ((zp x) (1+ y))
        ((zp y) (ack (1- x) 1))
        (t (ack (1- x) (ack x (1- y))))))




(include-book "switchnat")
(include-book "splitnat")
(defun nth-foo (x)
  (declare (xargs :measure (nfix x)
                  :guard (natp x)))
    (let* ((sw-v (defdata::switch-nat 2 (defdata::nfixg x)))
           (sw (first sw-v))
           (v (second sw-v)))
      (if (= sw 0)
        v
        (cons 'x (nth-foo v)))))
(defun nth-nat (n)
  (declare (xargs :guard (natp n)))
  n)

(defun nth-integer (n)
  (declare (xargs :guard (natp n)))
  (let* (;(n (mod n 1000))
         (mag (floor n 2))
        (sign (rem n 2)))
    (if (= sign 0)
      mag
      (- -1 mag))))


(DEFUN NTH-NOO (X)
  (DECLARE (XARGS :MEASURE (NFIX X)))
                 
  (LET* ((N-X (defdata::SWITCH-NAT 2 (defdata::nfixg x)))
         (N (first n-x))
         (x (second n-x)))
          (IF (= N 0)
            (NTH-NAT X)
            (LET ((INFXLST (defdata::SPLIT-NAT 2 x)))
              (CONS (LET ((X (NTH 0 INFXLST)))
                      (NTH-INTEGER X))
                    (LET ((X (NTH 1 INFXLST)))
                      (NTH-NOO X)))))))




(include-book "acl2-check")

(defdata
  (bexpr (oneof boolean
               (cons boolean bexpr-list)))
  (bexpr-list (oneof nil
                    (cons bexpr bexpr-list))))

:trans1 (defdata
     (koo (oneof (cons koo integer )
                 integer
                 ) 
          :hints (("Goal" :do-not-induct t)))
     )
(defun nth-koo (x)
  (declare (xargs :measure (nfix x)))
  (let* ((n-and-x (defdata::switch-nat 2 (defdata::nfixg x)))
         (n (first n-and-x))
         (x (second n-and-x)))
    (if (= n 0)
      (nth-integer x)
      (let ((infxlst (defdata::split-nat 2 x)))
        (cons (let ((x (nth 0 infxlst))) (nth-koo x))
              (let ((x (nth 1 infxlst)))
                (nth-integer x))))
      )))
(thm
(AND
 (O-P (NFIX X))
 (IMPLIES
  (= (CAR (DEFDATA::SWITCH-NAT 2 (DEFDATA::NFIXG X)))
          1)
  (O<
   (NFIX
    (NTH
     0
     (DEFDATA::SPLIT-NAT 2
                         (CADR (DEFDATA::SWITCH-NAT 2 (DEFDATA::NFIXG X))))))
   (NFIX X)))))

(thm
(AND
 (O-P (NFIX X))
 (IMPLIES
  (= (CAR (DEFDATA::SWITCH-NAT 2 (DEFDATA::NFIXG X)))
     0)
  (O<
   (NFIX
    (NTH
     0
     (DEFDATA::SPLIT-NAT 2
                         (CADR (DEFDATA::SWITCH-NAT 2 (DEFDATA::NFIXG X))))))
   (NFIX X)))))

(defun nth-koo1 (x)
  (declare (xargs :measure (nfix x)))
  (let* ((n-and-x (defdata::switch-nat 2 (defdata::nfixg x)))
         (n (first n-and-x))
         (x (second n-and-x)))
    (if (= n 0)
      (let ((infxlst (defdata::split-nat 2 x)))
        (cons (let ((x (nth 0 infxlst))) (nth-koo1 x))
              (let ((x (nth 1 infxlst)))
                (nth-integer x))))
      (nth-integer x))))


;(union-vt-and '((x pos nat) (y all)) '((x rational) (y symbol boolean)) (w state))
(defdata::sync-globals-for-dtg)
(aref1 'newnm (compress1 'newnm '((:HEADER :DIMENSIONS (10)
                                   :MAXIMUM-LENGTH 11
                                   :DEFAULT NIL
                                   :NAME asdsadas
                                   )
                                  (0 . 52)
                                  (1 . 51)
                                  (2 . 50)
                                  (3 . 49)
                                  (4 . 48)
                                  (5 . 47)
                                  (6 . 46)
                                  (7 . 45)
                                  (8 . 44)
                                  (9 . 43)
                                  ))
       2)
(defdata::sync-globals-for-dtg)

(DEFDATA::MY-EQUAL
  '((:HEADER :DIMENSIONS (10)
     :MAXIMUM-LENGTH 11
     :DEFAULT NIL
     :NAME DEFDATA::EXPLICIT-IMPLIED-INDEX-MAP)
    (0 . 52)
    (1 . 51)
    (2 . 50)
    (3 . 49)
    (4 . 48)
    (5 . 47)
    (6 . 46)
    (7 . 45)
    (8 . 44)
    (9 . 43)
    )
  '((:HEADER :DIMENSIONS (10)
     :MAXIMUM-LENGTH 11
     :DEFAULT NIL
     :NAME DEFDATA::EXPLICIT-IMPLIED-INDEX-MAP)
    (0 . 52)
    (1 . 51)
    (2 . 50)
    (3 . 49)
    (4 . 48)
    (5 . 47)
    (6 . 46)
    (7 . 45)
    (8 . 44)
    (9 . 43)
    
    ))


(DEFDATA::MY-EQUAL
          
  '(
    (:HEADER :DIMENSIONS (9)
     :MAXIMUM-LENGTH 10
     :DEFAULT NIL
     :NAME DEFDATA::EXPLICIT-IMPLIED-INDEX-MAP)
    (0 . 0)
    (1 . 1)
    (2 . 2)
    (3 . 3)
    (4 . 4)
    (5 . 5)
    (6 . 6)
    (7 . 7)
    (8 . 8)
    )
          
  '((:HEADER :DIMENSIONS (9)
     :MAXIMUM-LENGTH 10
     :DEFAULT NIL
     :NAME DEFDATA::EXPLICIT-IMPLIED-INDEX-MAP)
    (8 . 8)
    (7 . 7)
    (6 . 6)
    (5 . 5)
    (4 . 4)
    (3 . 3)
    (2 . 2)
    (1 . 1)
    (0 . 0)
    ))











;(assign make-event-debug t)

(defdata lon (listof nat))



(set-acl2s-random-testing-max-num-of-random-trials 50)


(set-acl2s-random-testing-enabled t)


(thm? (implies (and (or (true-listp x)
                             (stringp x))
                         (not (equal x nil))
                         (not (equal x "")))
                    (> (len x) 0)))

(set-acl2s-random-testing-max-num-of-random-trials 100)

(

(test? (implies (and (posp (car x))
                     (equal y y)
                     (equal z y)
                     (posp (cdr x)))
                (<= (cdr x) (len x)))
       )


(include-book "arithmetic-3/top" :dir :system)
;(include-book "coi/lists/list-top" :dir :system)

(thm (IMPLIES (AND (RATIONALP X)
                    (RATIONALP Y)
                    (NOT (EQUAL Y 0))
                    (<= 0 Y)
                    (<= 0 X)
                    (<= Y X)
                    (INTEGERP (+ 1 (- X)))
                    (< 1 X)
                    (NOT (INTEGERP (+ 1 (- X) (* 2 Y))))
                    (<= X (+ 1 (* 2 Y))))
               (< X
                  (+ 1 (DENOMINATOR (+ 1 (- X) (* 2 Y)))
                     (NUMERATOR (+ 1 (- X) (* 2 Y)))))))


(thm? (IMPLIES (AND (RATIONALP X)
              (RATIONALP Y)
              (NOT (EQUAL Y 0))
              (<= 0 Y)
              (<= 0 X)
              (<= Y X))
         (O< (ACL2-COUNT (+ 1 0 (- (+ (+ X (- Y)) Y))))
             (ACL2-COUNT (+ 1 Y (- (+ X (- Y))))))))


(test? (IMPLIES (AND (RATIONALP X)
              (RATIONALP Y)
              (NOT (EQUAL Y 0))
              (<= 0 Y)
              (<= 0 X)
              (<= Y X))
         (O< (ACL2-COUNT (+ 1 0 (- (+ (+ X (- Y)) Y))))
             (ACL2-COUNT (+ 1 Y (- (+ X (- Y))))))))




(thm (IMPLIES (AND (RATIONALP X)
              (RATIONALP Y)
              (NOT (EQUAL Y 0))
              (<= 0 Y)
              (<= 0 X)
              (<= Y X))
         (O< (ACL2-COUNT (+ 1 0 (- (+ (+ X (- Y)) Y))))
             (ACL2-COUNT (+ 1 Y (- (+ X (- Y))))))))



(thm? (IMPLIES (AND (RATIONALP X)
                    (RATIONALP Y)
                    (NOT (EQUAL Y 0))
                    (<= 0 Y)
                    (<= 0 X)
                    (<= Y X)
                    (INTEGERP (+ 1 (- X)))
                    (< 1 X)
                    (NOT (INTEGERP (+ 1 (- X) (* 2 Y))))
                    (<= X (+ 1 (* 2 Y))))
               (< X
                  (+ 1 (DENOMINATOR (+ 1 (- X) (* 2 Y)))
                     (NUMERATOR (+ 1 (- X) (* 2 Y)))))))










(defrec person '(name addr age) 't)

;example of proving tail-recursive and simple implementation equivalent
(defun rev-s (x)
  (if (endp x)
    nil
    (append (rev-s (cdr x)) (list (car x)))))

(defun rev-t (x a)
  (if (endp x)
    a
    (rev-t (cdr x) (cons (car x) a))))

(defun rev (x)
  (rev-t x nil))

(defthm rev-t-rev-s
  (equal (rev-t x a)
         (append (rev-s x) a)))

(defthm rev-rev-s
  (equal (rev x)
         (rev-s x)))

(in-theory (disable rev rev-t))

(thm (true-listp (rev x)))

(defun xp (v)
  (and (consp v)
       (and (consp (car v))
            (or (equal nil (caar v))
                (xp (caar v)))
            (and (consp (cadr v))
                 (xp (cadar v))
                 (xp (caddr v))))
       (or (equal (cdr v) nil)
           (and (consp (cdr v))
                (posp (cdar v))
                (xp (cddr v))))))
(defun yp (v)
  (and (consp v)
       (yp (car v))
       (yp (cdr v))))

(defun possibleBooleanRange (expr wrld)
  (cond ((booleanp expr)  t)
        ((possible-predicate-fn expr wrld) t)
        ((function-expressionp expr) 
         (if (equal (first expr) 'if)
           (and (possibleBooleanRange (third expr))
                (possibleBooleanRange (fourth expr)))
           (logicalp (car expr))))
        (t 'nil)))
        



  (defun tree-count (x)
  (case-match x
   ('nil 0)
   (('node v l . r)
    (+ 1 (tree-count (val x))
       (tree-count (left x))
       (tree-count (right x))))
   (& 0))) 
  
  (defun fixpt-iter-pull-nested-ifs (if-form)
  (let ((new-form (pull-out-nested-ifs if-form)))
    (if (equal new-form if-form)
      new-form
      (fixpt-iter-pull-nested-ifs new-form))))

(trace$ fixpt-iter-pull-nested-ifs)

(defun dumm (vars allvars n)
  (if (zp n)
    nil
    (prog2$
     (cw "~x0 the element of vars is ~x1 and first is ~x2 ~%" n (car vars) (car allvars))
     (dumm (cdr vars) allvars (1- n)))))




#|
(DEFUNS (FOO0P (V) (EQUAL V '"halted")))

(defuns (FOO1P (V)
                 (AND (CONSP V)
                      (BOOLEANP (CAR V))
                      (AND (CONSP (CDR V))
                           (INTEGERP (CAR (CDR V)))
                           (EQ (CDR (CDR V)) 'NIL)))))

(defuns (FOO2P (V) (OR (FOO0P V) (FOO1P V))))

(defun pull-out-nested-if (nested-if if-then if-else)
  `(if ,(second nested-if)
     (if ,(third nested-if)
       ,if-then
       ,if-else)
     (if ,(fourth nested-if)
       ,if-then
       ,if-else)))
(defun ifp (form)
  (if (not (consp form))
    nil
    (eq 'if (car form))))
;;assume already translated if-form
(defun pull-out-nested-ifs (if-form)
  (if (not (ifp if-form))
    if-form
    (if (ifp (second if-form))
      (pull-out-nested-if (second if-form) (third if-form) (fourth if-form))
      (list 'if (second if-form) 
            (pull-out-nested-ifs (third if-form))
            (pull-out-nested-ifs (fourth if-form))))))
(program)                     
(defun fixpt-iter-pull-nested-ifs (if-form)
  (let ((new-form (pull-out-nested-ifs if-form)))
    (if (equal new-form if-form)
      new-form
      (fixpt-iter-pull-nested-ifs new-form))))
(checkproperty test-pull-nested-ifs
  ((A boolean) (B boolean) (C boolean) (X boolean) (Y boolean))
  (equal (IF (IF (IF A A B) C NIL)
            t
            (IF X Y NIL))
         (fixpt-iter-pull-nested-ifs  '(IF (IF (IF A A B) C NIL)
                                          t
                                          (IF X Y NIL)))))

:set-ignore-ok t 
(checkproperty test-pull-nested-ifs
  ((A boolean) (B boolean) (C boolean) (X boolean) (Y boolean))
  (equal (IF (IF (IF A A B) C NIL)
            't
            (IF X Y NIL)) 
         (IF A
           (IF A
             (IF C 't (IF X Y NIL))
             (IF NIL 't (IF X Y NIL)))
           (IF B
             (IF C 't (IF X Y NIL))
             (IF NIL t (IF X Y NIL))))))

(logic)

(defun blah (x)
(IF (CONSP X)
    (IF (BLAH (CDR X)) T NIL)
    (IF NIL T NIL)))
(defun blah (x)
    (if (if (consp x)
        (blah (cdr x))
        nil)
    t
    nil))
  
(defun blah (x)
  (if (consp x)
      (if  (blah (cdr x))
        t
        nil)
      (if nil
        t
        nil))
  )

(DEFUN FOOP (V)
                (if (EQ V 'NIL)
                  t
                  (if (CONSP V)
                    (and (INTEGERP (CAR V))
                         (FOOP (CDR V)))
                    (if (CONSP V)
                      (and (FOOP (CAR V))
                           (NATP (CDR V)))
                      nil))))

(defun foop (x) (allp x))

(defdata (koo int))

(defdata (foo '(1 2 3)))

;;works now -- list apparently is not such a nice data structure to prove things. use list*!(Pete)
(DEFUN FOOP (V)
                (if (EQ V 'NIL)
                  t
                  (if (CONSP V)
                    (and (INTEGERP (CAR V))
                         (FOOP (CDR V)))
                    (if (CONSP V)
                      (and (FOOP (CAR V))
                           (NATP (CDR V)))
                      nil))))

(DEFUN FOOP (V)
  (declare (xargs :measure (acl2-count v)))
  (if (CONSP V)
       (and (INTEGERP (CAR V))
            (FOOP (CDR V)))
      (INTEGERP V)))
|#
         




(defun insert-after-pos (i new-entry alist)
  (if (endp alist)
    (list new-entry)
    (if (zp i)
      (cons (car alist) (cons new-entry (cdr alist)))
      (cons (car alist)
            (insert-after-pos (- i 1) new-entry (cdr alist))))))

;Prove correctness TODO
(defun find-pos-last-match (keys list len max)
  (if (endp keys)
    max
    (let* ((pos-rev (position-equal (car keys) (reverse list)))
          (pos (if pos-rev (- (1- len) pos-rev) pos-rev)))
      (if pos
        (if (> pos (nfix max))
          (find-pos-last-match (cdr keys) list len pos)
          (find-pos-last-match (cdr keys) list len (nfix max)))
        (find-pos-last-match (cdr keys) list len max)))))




;possibility of bug here CHECK TODO
;since when records are dest-elim, the intra-dependencies might be circular
(defun stich-up-dependencies (vte-alist vte-alist1 vte-alist2)
  ;(declare 
  (if (endp vte-alist)
    (append vte-alist1 vte-alist2)
    (let* ((restvars (strip-cars vte-alist2))
          (restvarlen (len restvars))
          (curr-elem (car vte-alist))
          (currvar (car curr-elem))
          (currval (cdr curr-elem)))
      (cond ((and (symbolp currval) (not (defdata::mem1 currval restvars)));type or something else
              (stich-up-dependencies (cdr vte-alist) vte-alist1 vte-alist2));ignore
             (t 
              (let* ((dvars  (defdata::get-free-vars1 currval nil));only non-buggy for terms
                     (pos (find-pos-last-match dvars restvars restvarlen nil)))
                (if pos ;found
                  (stich-up-dependencies (cdr vte-alist)
                                         (defdata::remove-entry currvar vte-alist1)
                                         (insert-after-pos pos curr-elem vte-alist2))
                  (stich-up-dependencies (cdr vte-alist) vte-alist1 vte-alist2))))))));ignore



(defun pascal (i j)
  (cond ((= j 0) 1)
        ((= j i) 1)
        (t (+ (pascal (1- i) (1- j)) (pascal (1- i) j)))))


(defun depth7 (bt d)
  (if (endp bt)
    d
    (let ((ldep (depth7 (car bt) (1+ d)))
          (rdep (depth7 (cdr bt) (1+ d))))
      (if (> ldep rdep)
        ldep
        rdep))))


(defun rebuildtree (bt)
  (if (atom bt)
    bt
    (cons (rebuildtree (car bt)) (rebuildtree (cdr bt)))))

(defun flatten1 (bt)
  (if (atom bt)
    bt
    (append (flatten1 (car bt)) (flatten1 (cdr bt)))))

(defun flatten2 (bt)
  (if (atom bt)
    (list bt)
    (append (flatten2 (car bt)) (flatten2 (cdr bt)))))

(defun flatten3 (bt lst)
  (if (atom bt)
    (cons bt lst)
    (flatten3 (car bt) (flatten3 (cdr bt) lst))))

(defun mem (atm lst)
  (if (endp lst)
    nil
    (if (equal atm (car lst))
      t
      (mem atm (cdr lst)))))

(defun un (l1 l2)
  (cond ((endp l1) l2)
        ((endp l2) l1)
        (t (if (mem (car l2) l1)
            (un l1 (cdr l2))
            (un (cons (car l2) l1) (cdr l2))))))
(defun subset (A B)
  (if (endp B)
    t
    (and (mem (car B) A)
         (subset A (cdr B)))))

(defun int (l1 l2)
  (if (endp l1)
    nil
    (if (mem (car l1) l2)
      (cons (car l1) (int (cdr l1) l2))
      (int (cdr l1) l2))))

(defun diff (l1 l2)
  (if (endp l1)
    nil
    (if (mem (car l1) l2)
      (diff (cdr l1) l2)
      (cons (car l1) (diff (cdr l1) l2)))))

(defun rv5 (l1)
  (if (endp l1)
    nil
    (append (rv5 (cdr l1)) (list (car l1)))))

(defun app (l1 l2 )
  (if (endp l1)
    l2
    (cons (car l1) (app (cdr l1) l2))))

(defun rv1 (l1)
  (if (endp l1)
    nil
    (app (rv1 (cdr l1)) (list (car l1)))))

(defun swaptree (bt)
  (if (atom bt)
    bt
    (cons (swaptree (cdr bt)) (swaptree (car bt)))))

(defun insert (sortedlst x)
  (if (endp sortedlst)
    (list x)
    (if (< x (car sortedlst))
      (cons x sortedlst)
      (cons (car sortedlst) (insert (cdr sortedlst) x)))))
(defun isort (L)
  (if (endp L)
    nil
    (insert (isort (cdr L)) (car L))))


(defun subtree (p bt)
  (if (endp p)
    bt
    (cond ((equal (car p) 'A) (subtree (cdr p) (car bt)))
          (t (subtree (cdr p) (cdr bt))))))

(defun replsubtr (p new bt)
  (if (endp p)
    new
    (if (eq (car p) 'A)
      (cons (replsubtr (cdr p) new (car bt)) (cdr bt))
      (cons (car bt) (replsubtr (cdr p) new (cdr bt))))))

(defun deeptip (bt)
  (if (atom bt)
    bt
    (if (> (depth7 (car bt) 1) (depth7 (cdr bt) 1))
      (deeptip (car bt))
      (deeptip (cdr bt)))))

(defun dep (bt)
  (if (atom bt);leaf
    0
    (let ((ld (dep (car bt)))
          (rd (dep (cdr bt))))
      (1+ (if (> ld rd) ld rd)))))

(defun deeptip1 (bt h)
  (if (atom bt)
    (cons bt h)
    (let ((lbth (deeptip1 (car bt) (1+ h)))
          (rbth (deeptip1 (cdr bt) (1+ h))))
      (if (> (cdr lbth)(cdr rbth))
        lbth
        rbth))))

:logic



(defun pascal23 (i j)
  (cond ((zp j) 1)
        ((zp i) 1)
        ((= j i) 1)
        ((> j i) -99)
        (t (+ (pascal23 (1- i) (1- j)) (pascal23 (1- i) j)))))

:logic

(defun pascal1 (i j)
  (cond ((zp j) 1)
        ((zp i) 1)
        ((= j i) 1)
        ((> j i) -99)
        (t (+ (pascal1 (1- i) (1- j)) (pascal1 (1- i) j)))))

(defun pascal2 (i j)
  (cond ((zp j) 1)
        ((zp i) 1)
        ((= j i) 1)
        (t (+ (pascal2 (1- i) (1- j)) (pascal2 (1- i) j)))))

(defun pascal3 (i j)
  ;(declare (xargs :measure i))
  (cond 
   ((> j i) 0)
   ((zp j) 1)
        ((zp i) 1)
        ((= j i) 1)
        (t (+ (pascal3 (1- i) (1- j)) (pascal3 (1- i) j)))))



(defun dumm (vars allvars n)
  (if (zp n)
    nil
    (prog2$
     (cw "~x0 the element of vars is ~x1 and first is ~x2 ~%" n (car vars) (car allvars))
     (dumm (cdr vars) allvars (1- n)))))




(defun pull-out-nested-if (nested-if if-then if-else)
  `(if ,(second nested-if)
     (if ,(third nested-if)
       ,if-then
       ,if-else)
     (if ,(fourth nested-if)
       ,if-then
       ,if-else)))

(defun ifp (form)
  (eq 'if (car form)))

(defun pull-out-nested-ifs (if-form)
  (if (not (ifp if-form))
    if-form
    (if (ifp (second if-form))
      (pull-out-nested-if (second if-form) (third if-form) (fourth if-form))
      (list 'if (second if-form) 
            (pull-out-nested-ifs (third if-form))
            (pull-out-nested-ifs (fourth if-form))))))




(defun type-term (var term state)
  (declare (xargs :mode :program :stobjs state))
  (let ((ens (ens state))
    (wrld (w state)))
    (cond ((or (variablep term)
           (fquotep term)
               (not (symbolp (ffn-symb term)))
               (not (function-symbolp (ffn-symb term) wrld)))
           (er hard 'type-term
               "Cannot take type-term of ~x0"
               term))
          (t (mv-let (ts ttree)
                     (type-set-implied-by-term
                      var nil
                      (guard (ffn-symb term) nil (w state))
                      ens wrld nil)
                     (mv-let (result ttree)
                             (convert-type-set-to-term var ts ens wrld ttree)
                             (declare (ignore ttree))
                             result))))))

(defconst *PII* (* 44/35  1/2  5))
(defconst *atomic-value-types*
  '(atom       
     number     
      complex    
       rational   
        integer
         pos
          natural      

     character 

     symbol    
      acl2-symbol
       boolean
      
     string))
(defconst *value-types* (append '(cons true-list acons alist) *atomic-value-types*))
(defun modify-symbol (prefix sym postfix)
  (declare (xargs :guard (and (symbolp sym)
                              (or (null prefix)
                                  (stringp prefix))
                              (or (null postfix)
                                  (stringp postfix)))))
  (let* ((name (symbol-name sym))
         (name (if prefix
                 (string-append prefix name)
                 name))
         (name (if postfix
                 (string-append name postfix)
                 name)))
    (if (member-eq sym *common-lisp-symbols-from-main-lisp-package*)
      (intern-in-package-of-symbol name 'acl2::acl2-pkg-witness)
      (intern-in-package-of-symbol name sym))))
(defun get-predicate-symbol (sym)
  (declare (xargs :guard (symbolp sym)))
  (modify-symbol nil sym "P"))

#|
(legal-variable-or-constant-namep 'x)
VARIABLE
ACL2 !>VALUE (legal-variable-or-constant-namep *standard-chars*)
NIL
ACL2 !>VALUE (legal-variable-or-constant-namep '*character-values*)
CONSTANT

(conjoin '(p1 p2 p3))
(IF P1 (IF P2 P3 'NIL) 'NIL)
ACL2 !>VALUE (disjoin '(p1 p2 p3))
(IF P1 'T (IF P2 'T P3))
 (GETPROP 'fobp 'FORMALS T 'CURRENT-ACL2-WORLD (w state))
 (termp (IF X Y '123) (w state))
 
 (convert-type-set-to-term 'x 201 (ens state) (w state) nil)
((IF (IF (INTEGERP X) (NOT (< '0 X)) 'NIL)
     'T
     (IF (EQUAL X 'T) 'T (EQUAL X 'NIL)))
 NIL)
ACL2 !>VALUE (type-set '(< x y) nil nil nil nil (ens state) (w state) nil nil nil)
(192 NIL)
ACL2 !>VALUE (type-set '(binary-+ x y) nil nil nil nil (ens state) (w state) nil nil nil)
(63 ((LEMMA :FAKE-RUNE-FOR-TYPE-SET NIL)))


(guard 'max nil (w state))
(IF (RATIONALP X) (RATIONALP Y) 'NIL)

(type-set-and-returned-formals '(binary-+ x y) nil (ens state) (w state) nil)
(63 0 NIL
    ((LEMMA :FAKE-RUNE-FOR-TYPE-SET NIL)))


(getprop 'fodp 'type-prescriptions nil
                  'current-acl2-world (w state))
((192 (2542 FODP V)
      NIL (NIL :TYPE-PRESCRIPTION FODP)
      IF (EQUAL (FODP V) 'T)
      'T
      (EQUAL (FODP V) 'NIL)))
ACL2 !>VALUE 
(getprop 'fod1p 'type-prescriptions nil
                  'current-acl2-world (w state))
NIL

(formals 'max (w state))
(X Y)

(most-recent-enabled-recog-tuple 'natp (global-val 'recognizer-alist (w state))
                                             (ens state))
(NATP (493 . 3)
      (-4 . T)
      :COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
ACL2 !>VALUE 
(most-recent-enabled-recog-tuple 'rationalp (global-val 'recognizer-alist (w state))
                                             (ens state))
(RATIONALP (NIL . 31)
           (-32 . T)
           :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL)


|#

(defun getListPredicateSymbol (sym)
  (declare (xargs :guard (symbolp sym)))
  (modify-symbol nil sym "LISTP"))

(mutual-recursion
;; code taken from structures.lisp in data-structures book.
 (defun freeVars1 (term ans)
   "A free variable is a symbol that is not a constant, i.e., it excludes T,
    NIL, and *CONST* etc."
   (cond
    ((atom term) (if (and (symbolp term)
              (not (eq (legal-variable-or-constant-namep term)
                   'CONSTANT)))
             (add-to-set-eq term ans)
           ans))
    ((eq (car term) 'QUOTE) ans)
    (t (freeVars1Lst (cdr term) ans))))

 (defun freeVars1Lst (terms ans)
   (cond
    ((atom terms) ans)
    (t (freeVars1Lst (cdr terms) (freeVars1 (car terms) ans))))))

(defun freeVars (term)
  (freeVars1 term '()))

;;get-recognizer : term * Listofvars * Ens * World
;;Checks if the term is a fn application of form (type-recognizerp x)
;;if yes then we return a pair (x . type-recognizerp) 
;;we will do 2 kinds of checks
;; 1. syntactic fargs len is 1
;;    the sole farg is present in list of vars
;; 2. Does it have a compound-recognizer or type-pres rule?
;; TODO: Right now I am concentrating on getting this to work with
;; only random-state book, later integrate Peter's defdata framework.
(defun get-recognizer (guard-term vars ens wrld)
  (declare (xargs :mode :program
                  :guard (and (termp guard-term)
                              (true-listp vars))))
  (if (and (eq 1 (len (fargs guard-term)))
           (mem (fargn guard-term 1) vars))
      (let* ((fn (ffn-symb guard-term))
             (var (fargn guard-term 1))
             (recog-tuple (most-recent-enabled-recog-tuple
                           fn
                           (global-val 'recognizer-alist wrld)
                           ens)))
        (if recog-tuple
            ;we have a primitive type perhaps!?
            (cons var fn)
            (if (getprop fn
                         'type-prescriptions
                         nil
                         'current-acl2-world
                         wrld)
                ;;peter's generated type predicate!?
                (cons var fn)
                nil)))
      nil))
   
;;SImple type extraction from guards.
;;TODO: Assumption: Guards are either 'T, IF E1 E2 E3 or (type-recognizerp 'X)
;;if there are more complicated guards then we need to cover those cases as well. TODO
(defun infer-type-from-guard (guard-term vt-alist-acc ens wrld)
  (if (or (fquotep guard-term)
          (variablep guard-term)
          (not (symbolp (ffn-symb guard-term)))
          (not (function-symbolp (ffn-symb guard-term) wrld)))
      vt-alist-acc
      (if (ffn-symb guard-term 'if) ;add if cond true and then terms
          (let ((vt-alist1 (infer-type-from-guard (fargn guard-term 1) vt-alist-acc ens wrld)))
            (infer-type-from-guard (fargn guard-term 2) vt-alist1 ens wrld))
          ;guard term is of type (f a1 ...)
          (let* ((vars (strip-cars vt-alist-acc))
                 (typ-recog (get-recognizer guard-term vars ens wrld))
                 (typ-p (check-rand-generator-exists typ-recog))) ;;hack to be removed
            (if typ-p ;if we get a typ recog we add it to our var typ alist
                (union-add-alst-pair vt-alist-acc typ-recog)
                vt-alist-acc))))) ;otherwise do nothing!?
            

;;TODO: Ques: How to find the smallest type in a conjoin/intersection

;;infer-type-from-term : Term * var-typ-alist * TrueTerm * Ens * World * State -> var-types-alist 
;;Term should be a translated term i.e (f a1 a2 ...) to
;;be of relevance in inferring type of a  var. Return vt-alist-acc which stands for
;;var-types-alist-accumlated. Initial it just has free vars as keys and empty type values.
;;In the end if the returned vt-alist has some empty typ values then we fill them with
;;the default ANY type value.
;;TrueTerm can be used to obtain stronger information if the term we are trying to
;;lies in a particular then-else branch in the body of the def. Right now I ignore it
;;and only concentrate on guards. 
;;Notes:
;1. IF : Union of then and else types (if condition also gives guard information??)
;2. (f a1 a2..): recurse on f's type rules!  
;Look at type-set-and-returned-formals in defuns.lisp for a similar function!
;Note: Lets look at the context where we will be calling this function.
; We might need it in 2 situations:
; 1. Prove edge does not exist
; 2. Prove measure decreases across calls
; Generic case seems to be unclear to me at the moment, lets get this thing
; working for these special cases.
; We will restrict our type inference to a weaker notion of collecting guards and
; getting recognizers from that information only. If we are lucky we get types
; for all our free variables in the term we are checking, if not we default the
; type to ANY, that means we need a random-value generator which generates
; a random cons , list or atom.
(mutual-recursion
 (defun infer-type-from-term (term vt-alist-acc true-term ens wrld state)
   (declare (xargs :mode :program 
                   :stobjs state
                   :guard (and (symbolp var)
                               (alistp vt-alist-acc)
                               (termp term))))
   (cond
  ;if term is a variable, a constant or if term is
  ;a call of f which is not defined in the curr wrld we return with
  ;whatever var-type-alist we accumulated adding no extra info.
    ((or (variablep term)
         (fquotep term)
         (not (symbolp (ffn-symb term)))
         (not (function-symbolp (ffn-symb term) wrld)))
     vt-alist-acc)
    ;;term == (if st-cond st-then st-else) st is abbrev for subterm
    ((eq (ffn-symb term) 'if)
     (let* ((st-cond (fargn term 1))
            (st-then (fargn term 2))
            (st-else (fargn term 3))
            (vt-alst1 (infer-type-from-term st-cond vt-alist-acc true-term ens wrld state))
            (vt-alst2 (infer-type-from-term st-then vt-alst1 true-term ens wrld state))
            (vt-alst3 (infer-type-from-term st-else vt-alst1 true-term ens wrld state)))
       (union-add-alst-lst vt-alst2 vt-alst3))) ;;union of types we gathered!?
    ;;term == (f a1 a2 ...)
    (t
     (let* ((guard-term (guard (ffn-symb term) nil wrld))
            (formals-term (formals (ffn-symb term) wrld))
            (guard-term-subs (subcor-var formals-term (fargs term) guard-term))
            (extracted-typ-alst (infer-type-from-guard guard-term-subs vt-alist-acc ens wrld))
            (vt-alist1 (union-add-alst-lst vt-alist-acc extracted-typ-alst)))
       (infer-type-from-termlist (fargs term) vt-alist1 true-term ens wrld state))))) 
 
 (defun infer-type-from-termlist (termlst vt-alist-acc true-term ens wrld state)
   (declare (xargs :mode :program
                   :stobjs state
                   :guard (true-listp termlst)))
   (if (endp termlst)
       ;then return accumulated var typ alist
       vt-alist-acc
       ;else recurse over list of terms
       (let ((vt-alst1 (union-add-alst-lst  ;ASK: should be an intersection! 
                        vt-alist-acc
                      (infer-type-from-term (car termlst) vt-alist-acc true-term ens wrld state))))
         (infer-type-from-termlist (cdr termlst) vt-alst1 ens wrld state)))))


(defun append-last (list1 lst acc)
  (if (endp (cdr list1))
    (reverse (cons (append (car list1) (list lst))  acc))
    (append-last (cdr list1) lst (cons (car list1) acc)))) 

;this fun is difficult to do without in-place mutation
;also tailrecursive sol is not trivial. keep this example for future
(defun append-let (let-form subform)
  (let ((body (caddr let-form)))
    (if (or (endp body)
            (not (equal (car body) 'let)))
      (list (car let-form) 
            (cadr let-form)
            subform)
      (list (car let-form)
            (cadr let-form)
            (append-let (caddr let-form) subform)))))
;;get the outermost implies sub-form
(defun implies-subform (form)
  (declare (xargs :mode :program))
  (if (endp form)
    'NIL
    (cond 
     ((equal (car form) 'implies)
      (cadr form))
     ((equal (car form) 'let)
      (implies-subform (caddr form)))))) 
(defun let-adjusted-implies-subform (let-form)
  (declare (xargs :mode :program))
  (let ((impl (implies-subform let-form)))
  (if (endp impl)
    'NIL
    (append-let let-form impl)))) 

  (trace$ append-let)                               

(implies-subform '(LET ((X (NTH-INTEGER 8)))
     (LET ((Y (NTH-INTEGER 42659)))
       (let ((z (nth-integer 34)))
          (IMPLIES (<= X Y) (EQUAL (MAX X Y) Y))))))
(let-adjusted-implies-subform '(LET ((X (NTH-INTEGER 8)))
     (LET ((Y (NTH-INTEGER 42659)))
       (let ((z (nth-integer 34)))
          (IMPLIES (<= X Y) (EQUAL (MAX X Y) Y))))))

(set-ignore-ok t)



;DEPRECARED TYPES CODE from type.lisp 
;;------------------------------------------------------------------
;;---infer type hyps from hyps in thm forms-------------------------
;;;TODO - Rewrite this code, its not satisfactory
;;------------------------------------------------------------------

(defun empty-vt-alist1 (freevars vt-alist)
  (declare (xargs :guard (true-listp freevars)))
  (if (endp freevars)
    vt-alist
    (empty-vt-alist1 (cdr freevars)
                    (cons (cons (car freevars) (list 'ACL2::ALL)) 
                          vt-alist))))

;;initialise a var type alist with no type information to start with.
;;i.e each variable starts with having the type 'ALL'
(defun empty-vt-alist (freevars)
  (declare (xargs :guard (true-listp freevars)))
  (empty-vt-alist1 freevars '()))

   
;reset with type 'all'
(defun reset-vt-alist-with-all (vt-al ans)
  (declare (xargs :guard (symbol-alistp vt-al)))
  (if (endp vt-al)
    ans
    (reset-vt-alist-with-all (cdr vt-al) (cons (cons (caar vt-al) (list 'all)) ans))))


;TODO.Note: an elegant solution would be to collect type expressions from hyps and then use those
;directly as type information.(but we will let ACL2 do this for us through case-splitting
;and destructor-elimination)

;;pull type information from type hypotheses
(mutual-recursion       
 ;returns a list of var-typ pairs
 (defun pull-types-from-hyp (hyp wrld)
   ;(declare (xargs :verify-guards nil))
   (let ((typ (is-simple-type-hyp hyp wrld)))
     (cond ((atom hyp)  nil) ;return unchanged 
           ((eq (car hyp) 'not)
            nil)
            
           (typ 
            (list (cons (cadr hyp) (list typ)))) ;add the var-typ pair to list
           ((eq (car hyp) 'equal) 
            (let ((fst-arg (second hyp))
                  (snd-arg (third hyp)))
              (cond ((and (defdata::is-a-variablep fst-arg)
                          (defdata::possible-constant-valuep snd-arg))
                     (list (cons fst-arg (list snd-arg))))
                    ((and (defdata::is-a-variablep snd-arg)
                          (defdata::possible-constant-valuep fst-arg))
                     (list (cons snd-arg (list fst-arg))))
                    (t nil))))
           ((eq (car hyp) 'and)
            (pull-types-from-hyplst (cdr hyp) wrld))
           ((eq (car hyp) 'or);this can be taken care of using oneof now TODO?
            nil);return unchanged ...we dont know!
           (t nil)))) ;TODO: what if it is a 'if' statement or suppose a custom and or like boolean-and?
                      ;what about equal? ANS: equal is taken care of by process-dependencies!!
     
 (defun pull-types-from-hyplst (hyps wrld)
   ;(declare (xargs :verify-guards nil))
   (if (endp hyps)
     nil
     (let ((vt-al (pull-types-from-hyp (car hyps) wrld)))
       (if (null vt-al)
         (pull-types-from-hyplst (cdr hyps) wrld)
         (append vt-al 
               (pull-types-from-hyplst (cdr hyps) wrld))))))
 )


;in our case we only add the allp predicate, which always returns a 't
;Make sure missing-hyps is a list
(defun extend-hyp (hyp missing-hyps)
 ; (declare (xargs :guard (true-listp missing-hyps)))
  (if (eq 't hyp);no hyp
    (if (endp missing-hyps)
      't
      (if (= 1 (len missing-hyps))
        (car missing-hyps) ;expand it
      `(and . ,missing-hyps)))  ;add an and 
    ;hyp is present
    (if (endp missing-hyps) ;shud be a list of hyps to add
      hyp
      (if (and (consp hyp) (eq (car hyp) 'and)) ;top-level and
        (cons 'and (append (cdr hyp) missing-hyps))
        `(and ,hyp . ,missing-hyps)))))

(defun extend-hyp-with-simple-negated-concl (hyp concl)
  (if (and (consp concl)
           (eq 'not (car concl)));(not some-formula)
    (extend-hyp hyp (cdr concl));cdr makes sure that its a list i.e '(some-formula)
    hyp));only extend if there is a not in the conclusion, since otherwise
         ;;;its no use in inferring types from hyps



;The following functions helps merge 2 var-type alists by finding
;the smallest type-lists(OR of types) for each variable
;THis is useful when you have a type-alist that acl2-check infers and
;then we try to merge it with the type-alist that ACL2 computes from
;the theorem proving context which can at times be more accurate.

; NOTE in our vt-al, we can have either typenames or 
; we can have singleton types ie constant expressions

;we take the intersection of typ1 and typ2 and return the smaller of the
;types. but if we dont know the subtype relation, we just choose arbitrarily
;among the the two types. But if we know the two types are disjoint, then
;we give back NIL, we goes nicely with the calling code.

(set-verify-guards-eagerness 0);nope, no way i can prove guards for these fellows

;NOTE: In the following 2 functions,the type 'empty' has special status and treated seperately
(defun intersection-of-types (typ1 typ2 wrld)
  (cond  
   ((possible-constant-value-expressionp typ1) typ1) ;if lucky to have a singleton type, just return it
   ((possible-constant-value-expressionp typ2) typ2) ;if lucky to have a singleton type, just return it
   ((or (eq 'acl2::empty typ1) (eq 'acl2::empty typ2)) 'acl2::empty)
   (t 
    (if (and (is-a-typeName typ1 wrld)
             (is-a-typeName typ2 wrld))
      (cond ((is-subtype typ1 typ2 wrld)
             typ1)
            ((is-subtype typ2 typ1 wrld)
             typ2)
            ((is-disjoint typ2 typ1 wrld)
             'empty) ;Should we instead define the NULL type??? Modified: so Ans is YES instead of Ans: NO, the way its used now, this is right!
            ;give preference to custom type
            ((defdata::is-a-custom-type typ1 wrld)
             typ1)
            ((defdata::is-a-custom-type typ2 wrld)
             typ2)
            ;;choose the one that was defined later(earlier in reverse chronological order)
            (t (let* 
                   ((types-in-wrld 
                     (strip-cars (table-alist 
                                  'defdata::types-info-table wrld)))
                      (pos1 (position typ1 types-in-wrld))
                      (pos2 (position typ2 types-in-wrld)))
                 (if (< (nfix pos1) (nfix pos2)) typ1 typ2))));type table is already in reverse chrono order
      nil))));This should never happen right!!?

;gives back a list which represents the union of typ1 and typ2
(defun union-of-types (typ1 typ2 wrld)
  (cond  
   ((equal typ1 typ2) (list typ1))
   ((or (defdata::possible-constant-value-expressionp typ1)
        (defdata::possible-constant-value-expressionp typ2))
    (list typ1 typ2))
   (t 
    (if (and (defdata::is-a-typeName typ1 wrld)
             (defdata::is-a-typeName typ2 wrld))
      (cond ((eq 'empty typ1) (list typ2))
            ((eq 'empty typ2) (list typ1))
            ((is-subtype typ1 typ2 wrld)
             (list typ2))
            ((is-subtype typ2 typ1 wrld)
             (list typ1))
            (t ;(is-disjoint typ2 typ1 wrld)
             (list typ1 typ2)))
      nil))))
      ;(er hard 'union-of-types "~x0 and ~x1 should be 'types' that have been defined~%" typ1 typ2)))))

;takes a min-typ-or-lst and OR-merges it with a typ to give back a OR-type list which cannot be minimized furthur
(defun merge-type-with-type-list-using-OR (typ min-typ-lst wrld)
  (if (endp min-typ-lst)
    (list typ)
    (let ((un-lst (union-of-types typ (car min-typ-lst) wrld)))
      (if (= 1 (len un-lst)) ;got merged
          (merge-type-with-type-list-using-OR (car un-lst) (cdr min-typ-lst) wrld);merge with rest
          (cons (car min-typ-lst)
                (merge-type-with-type-list-using-OR typ (cdr min-typ-lst) wrld))))))

;walk through the type list and accumulate the minimal 'or' representation e.g nat \/ pos = pos
(defun collapse-or-type-list-aux (typ-lst wrld ans)
  (if (endp typ-lst)
    ans
    (collapse-or-type-list-aux (cdr typ-lst) wrld
                               (merge-type-with-type-list-using-OR (car typ-lst) ans wrld))))

(defun collapse-or-type-list (typ-lst wrld)
  (collapse-or-type-list-aux typ-lst wrld nil))

; this function takes a type and a type-list and one by one returns a list
;which is obtained by taking intersection of typ with each element of typ-lst
(defun union-vt-and4 (typ typ-lst wrld)
  (if (endp typ-lst)
    nil
    (let ((intersection-t (intersection-of-types typ (car typ-lst) wrld)))
      (if intersection-t 
        (cons intersection-t (union-vt-and4 typ (cdr typ-lst) wrld))
        (union-vt-and4 typ (cdr typ-lst) wrld)))))
                         
;This function does something similar to:
;(t1 \/ t2) /\ (t3 \/ t4) ==> (t1 /\ t3) \/ (t1 /\ t4) \/ (t2 /\ t3) \/ (t2 /\ t4) 
;note that we wont get an empty list as a first call argument
;Note that a type-list is nothing but an OR of the types
(defun union-vt-and3 (typ-lst1 typ-lst2 wrld)
  (declare (xargs :guard (and (true-listp typ-lst1)
                              (plist-worldp wrld)
                              (true-listp typ-lst2))))
  (if (endp typ-lst1)
    nil
    (append (union-vt-and4 (car typ-lst1) typ-lst2 wrld)
            (union-vt-and3 (cdr typ-lst1) typ-lst2 wrld))))
    
 ;ok now 'nil' what does it stand for? for me I have taken 'nil' as a list containing type ALL, so
 ;we just return the other list. This function also compresses the type-lists with union-of-types
;operation, so we save time done by opening up the OR operation with AND operations later:
(defun union-vt-and2 (typ-lst1 typ-lst2 wrld)
  (declare (xargs :guard (and (true-listp typ-lst1)
                              (plist-worldp wrld)
                              (true-listp typ-lst2))))
  (cond ((endp typ-lst1) (collapse-or-type-list typ-lst2 wrld))
        ((endp typ-lst2) (collapse-or-type-list typ-lst1 wrld))
        (t (union-vt-and3 (collapse-or-type-list typ-lst1 wrld)
                          (collapse-or-type-list typ-lst2 wrld)
                          wrld))))

;not tail-rec; assumption: vt-al2 has not repetetions
;For each pair in vt-al2 check if it matches the variable and
;then for the type-lists obtained from both, we try to and-merge them.
;So we give back a modified vt-al which takes into account and-merging of
;type-lists for the particular variable in vt-pair
(defun union-vt-and1 (vt-pair vt-al2 wrld)
  (if (endp vt-al2)
    (list vt-pair) ;var not found in vt-al2, so just add it into the list returned
    (let ((vt-pr2 (car vt-al2)))
      (if (eq (car vt-pr2) (car vt-pair));if variables match, then do the foll
        (cond ((equal (cdr vt-pair) '(all)) vt-al2);return unchanged (shortcircuit the recursion)
              ((equal (cdr vt-pr2) (cdr vt-pair)) vt-al2)  ;shortcircuit, return unchanged 
              ((equal (cdr vt-pr2) '(all)) (cons vt-pair (cdr vt-al2)));pick vt-pair and short-circuit
              (t (cons (cons (car vt-pair) (union-vt-and2 (cdr vt-pr2) (cdr vt-pair) wrld)) (cdr vt-al2))));diff types than all
        (cons vt-pr2 (union-vt-and1 vt-pair (cdr vt-al2) wrld))))));otherwise carry on to see if match found furthur down



;tail-rec; assumption: vt-al2 has no repetetions
(defun union-vt-and-aux (vt-al1 vt-al2 wrld)
  (if (endp vt-al1)
    vt-al2 ;return it if vt-al1 is empty 
    (union-vt-and-aux (cdr vt-al1) 
                      (union-vt-and1 (car vt-al1) vt-al2 wrld) wrld)))

; The following function walks vt-al collapsing the dup var entries with
; AND type-lists operation
;;the answer is accumulated in vt-al2 arg of union-vt-and-aux
(defun union-vt-al-collapse-and (vt-al wrld )
  (union-vt-and-aux vt-al nil wrld))


(defun union-vt-collapse-or-type-lists (vt-al wrld)
  (if (endp vt-al)
    nil
    (cons (cons (caar vt-al) (collapse-or-type-list (cdar vt-al) wrld))
          (union-vt-collapse-or-type-lists (cdr vt-al) wrld))))


;TODO: calculate the time complexity of this function
(defun union-vt-and (vt-al1 vt-al2 freevars wrld)

  (let* (
;filter relevant v-t pairs
         (vt-al2-filtered (filter-alist-keys vt-al2 freevars))
; collapse ors, i.e union types
         (vt-al2-filtered1 (union-vt-collapse-or-type-lists vt-al2-filtered wrld))
         (no-dup-vt-al2 (union-vt-al-collapse-and vt-al2-filtered1 wrld));first pass which ensures a no-dup backbone list
         (vt-al1-filtered  (defdata::filter-alist-keys vt-al1 freevars))
         (vt-al1-filtered1 (union-vt-collapse-or-type-lists vt-al1-filtered wrld));collapse ors
         (vt-al (union-vt-and-aux vt-al1-filtered1 no-dup-vt-al2 wrld)));second pass  through our maze of calls above
    (union-vt-collapse-or-type-lists vt-al wrld)));final pass, collapsing or-type-lists for each var across vt-al1 and vt-al2


;; (union-vt-and '((a integer) (b pos) (b nat) (c all) (c character) (c 1))
;;               '( (a rational) (a all) (c list) (c all) (b all)) (w state))
;;  ===> ((A INTEGER) (C 1) (B POS))

;; (union-vt-and 
;; '((a integer) (b rational) (b string positive-rational) (c pos) (c 2))
;; '( (a rational) (a all neg) (c 2 pos nat) ) (w state))


; freevars argument is necessary because the term might not
; be an acl2 term(not satisfy termp), its the responsibility
; of the calling function to provide the free variables of term
(defun extract-var-typ-alist-from-term (term freevars wrld)
 (let* ((v-all-lst (empty-vt-alist freevars))
           (hyp (get-hyp term)) 
           (concl (get-concl term))
; as pete said, we try to extract info from simple negated conclusions like
           ;;;(implies (xp a)
           ;;;         (not (yp b)))
           (hyp-neg-concl (extend-hyp-with-simple-negated-concl hyp concl))
           (var-ty-al (pull-types-from-hyp hyp-neg-concl wrld))
           (var-ty-alst (union-vt-and var-ty-al v-all-lst freevars wrld)))
      var-ty-alst))

