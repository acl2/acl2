; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(acl2::include-book "misc/eval" :dir :system)
(in-package "ACL2S")

        
;; [2017-09-19 Tue]
(acl2s-defaults :set search-strategy :simple)
(acl2s-defaults :set sampling-method :uniform-random)
(acl2s-defaults :set num-witnesses 0)

(defdata loi10 (listof integer) :min-rec-depth 10)
(defdata intlist (listof integer))
(defdata intlst50 (listof integer)
  :min-rec-depth 50
  :max-rec-depth 100)

(test? (implies (intlst50p x) (< (len x) 100)))

;; (defdata loi_<50 (listof (elem . integer)) :satisfies (<= elem 50))
;; (must-fail
;;  (defdata loi_x (listof (x . integer)) :satisfies (<= x 50)))

(defdata loi_x (listof integer)
  :satisfies (and (< (len x) 100) (> (len x) 10))
  :min-rec-depth 10)

(defconst *SRL-DATA-MINIMUM* (- (expt 2 30)))
(defconst *SRL-DATA-MAXIMUM* (expt 2 30))

(defdata srl-int
  (range integer (*SRL-DATA-MINIMUM* <= _ <= *SRL-DATA-MAXIMUM*)))

#|
(defun test-enum-dist (n state)
  (declare (xargs :stobjs (state) :verify-guards nil))
  (if (zp n)
      (value (cw "~%"))
  (b* (((mv x seed.) (NTH-SRL-INT/ACC 50 (defdata::getseed state)))
       (state (defdata::putseed seed. state)))
    (prog2$ (cw "~x0  " x)
            (test-enum-dist (1- n) state)))))

(defloop filter-1000 (xs)
  (for ((x in xs)) (append (and (> x 1000)
                                (< x 10000)
                                (list x)))))
|#

;;BUG
(defdata foo4 (oneof nil (cons (x2 . pos) foo4) (acons pos pos foo4)) :satisfies (> x2 5))


; 11 Feb 2016
; Test monomorphic sig
(defun append-natlists (l1 l2)
  (if (endp l1)
    l2
    (cons (car l1) (append-natlists (cdr l1) l2))))

;TODO change name of main signature theorem
(sig append-natlists (nat-list nat-list) => nat-list)


;5 Feb 2016 TODO -- make sure you have the right error message. records should not be nested!
(must-fail
(defdata
  (pair (record (n . nat)
                (l . lop)))
  (lop (listof pair))))

(defdata
  (lpair (pair (n . nat)
                (l . lop)))
  (lop (listof lpair)))


;(defdata sym->sym (map all all))

#| Failing ACL2s Issue
(defdata sys-trajectory true-list) 

(defdata probability (range rational (0 < _ < 1))) 

(defdata 
  (prob-node (prob-node
              (prob . probability) 
              (children . prob-node-list) ; List of child nodes 
              (trajectory . sys-trajectory))) ; Payload 
  (prob-node-list (listof prob-node)))
|#

;acl2s-issue partially fixed
#|(acl2s::sig pairlis$ ((listof :a) (listof :b)) => (alistof :a :b)
     :satisfies (= (len acl2s::x1) (len acl2s::x2))) |#


;7 Jan 2016 Check whether defdata works in program mode
(program)
(defdata rationallist (listof rational))
(defdata-attach rationallist :enumerator nth-rational-list-builtin)
(logic)

;acl2s-issue non-canonical forms 
;acl2s-issue 
(defdata integer-cons (cons integer integer))
(defdata integer-cons-lst (listof integer-cons))

(thm (implies (and (integer-cons-lstp x)
                   (integer-cons-lstp y))
              (integer-cons-lstp (append x y))))

(defdata integer-cons-lst2 (alistof integer integer))

(thm (implies (and (integer-cons-lst2p x)
                   (integer-cons-lst2p y))
              (integer-cons-lst2p (append x y))))



;TODO: Improve the error message
(acl2::must-fail
(defdata (a (oneof nil b))
         (b (enum a)))
)




(set-bogus-mutual-recursion-ok nil)
;TODO: enum shouldnt be allowed in mutually-recursive defs
(must-fail
(defdata (a (oneof nil b))
         (b (enum '(1 2))))            
)

;Jan 5 '15
(defdata is3 (enum (list 3)))

;Pete: this was failing; fixed 1/28/2020
(defdata isx (enum (list 'x)))

(defdata is4 (range integer (3 < _ < 5)))
;(acl2::defmacro must-fail (acl2::&rest rest) `(acl2::must-fail ,@rest))
(must-fail (defdata bad-range1 (range integer (3 < _ < 4))))
(must-fail (defdata bad-range2 (range rational (4 < _ < 4))))
(must-fail (defdata bad-range3 (range rational (4/3 < _ < 1/2))))
(must-fail (defdata bad-range4 (range rational (nil < _ < nil))))
(must-fail (defdata bad-range5 (range rational ("a" <= _ < "b"))))
(must-fail (defdata bad-range6 (range rational (_ <= "b"))))
(must-fail (defdata bad-range6 (range rational (_ <=))))

; Jan 5 '15
(defdata one-to-ten (range integer (1 <= _ <= 10)))
(defdata one-to-tens (listof one-to-ten))

; Jan 3 '15
(defdata trues (listof 't))


; Dec 18 '14 for defdata-boolean-algebra
(defdata consE (oneof (cons atom atom)
                      (cons atom consE)
                      (cons consE atom)
                      (cons consE consE)))

(thm
 (iff (consEp x)
      (consp x)))

(defdata ctree (oneof nil (cons ctree ctree)))
(defdata nil-list (oneof nil (cons nil nil-list)))
(thm (implies (nil-listp x) (ctreep x)))

(defdata ctree2 (oneof nil 
                       (cons nil nil) 
                       (cons nil (cons ctree2 ctree2))
                       (cons (cons ctree2 ctree2) nil)
                       (cons (cons ctree2 ctree2) (cons ctree2 ctree2))))
(thm (implies  (ctreep x) (ctree2p x))
     :hints (("Goal" :induct (ctree2p x))))

;(defdata nat acl2s::nat)
               
(defdata chk (oneof string (cons nat chk) (cons (cons chk nil) nat)))

(defdata cdr2 (oneof (cons 1 2) (cons cdr2 2)))
(defdata cdr2-unroll1 (oneof (cons 1 2) (cons (cons 1 2) 2)  (cons (cons cdr2 2) 2)))
(thm (iff (cdr2-unroll1p x)
          (cdr2p x)))



(defdata car1 (oneof (cons 1 2) (cons 1 car1)))

(acl2::must-fail (test? (implies (car1p x) (cdr2p x) )))



;Test ranges
(defdata ir1 (range integer (0 < _ < 53)))
(defdata ir2 (range integer (-42 <= _ < 53)))
(defdata r3 (range rational (-42/77 <= _ < 53/1)))
(defdata r4 (range rational (1/12 < _)))
(defdata r5 (range rational (-1/12 <= _)))


(defdata r6 (range rational ( _ <= -1/12)))
(defdata r7 (range rational (_ <= 1/12)))

(defdata ir8 (range integer (_ <= 45)))
(defdata ir9 (range integer (41 < _)))
(defdata ir10 (range integer (_ < -41)))



(must-fail (test? (implies (ir1p x) (acl2::evenp x))) ) 
(must-fail (test? (implies (ir2p x) (acl2::evenp x))) )


(must-fail (test? (implies (r3p x) (acl2::evenp x))))

(must-fail (test? (implies (r4p x) (acl2::evenp x)))  )
(must-fail (test? (implies (r5p x) (acl2::evenp x)))  )
(must-fail (test? (implies (r6p x) (acl2::evenp x)))  )
(must-fail (test? (implies (r7p x) (acl2::evenp x)))  )
(must-fail (test? (implies (ir8p x) (acl2::evenp x))) )
(must-fail (test? (implies (ir9p x) (acl2::evenp x))) )
(must-fail (test? (implies (ir10p x) (acl2::evenp x))))

(acl2::must-fail
(defdata ir11 (range integer (0 < _ < -1))) ;not allowed
)
(acl2::must-fail
(defdata ir10 (range integer)) ;not allowed 
)




;ACL2 2014 Workshop script START
(defdata inode acl2s::nat)

(defdata file (cons inode string))
(defdata er-file (oneof file nil))

(defdata UPNest 
  (oneof (oneof (cons (oneof 11 7) acl2s::pos-list) 'ok acl2s::symbol-alist) 
         (cons symbol (acl2::complex integer -1))
         (oneof (oneof 42 (cons acl2s::pos file) er-file) t 7/6)
         "nice"))

(defdata loi (oneof nil (cons integer loi)))

(defdata symb-alist (oneof nil (cons (cons symbol acl2s::all) symb-alist)))


(defdata 
  (dir (oneof nil (cons (cons string dir-entry) dir)))
  (dir-entry (oneof file dir)))


(defdata cache-miss-ratio (range rational (0 < _ < 1))) 
(defdata big-unsigned-num (range integer ((acl2::expt 2 32) < _)))

(defdata 3d-point (list rational rational rational))

(defdata files (listof file))

;(trace$ defdata::funcall-w)
;(defdata symbol-alist2 (alistof symbol all))

(defdata op-code (enum '(lw sw addi subi beqz jr)))

(defun generate-instruction-opcodes (x)
  (if (equal x 'mips-risc-model)
    '(lw sw addi subi beqz jr)
    '()))

(defdata op-code1 (enum (generate-instruction-opcodes 'mips-risc-model)))

(defdata reg-num (range integer (0 <= _ < 32)))
(defdata immediate-range (range integer (0 <= _ < (acl2::expt 2 16))))

(defthm op-codep-is-non-nil
       (implies (op-codep x) x)
       :rule-classes :forward-chaining)
     
(defdata inst (record (op  . op-code)
                      (rd  . reg-num)
                      (rs1 . reg-num)
                      (imm . immediate-range)))


 
(defdata p-addr (range integer (0 <= _ < (acl2::expt 2 32))))
;(trace$ template-subst-fn)
(defdata imem (map p-addr inst))
  
(b* (;; pick a random imemory
       (I (nth-imem 834545))
       ;; fix a program counter value
       (pc 1)
       ;; get the instruction pointed to by pc
       (instr (mget pc I)) 
       ;; get immediate value field of instr
       (im (inst-imm instr))
       ;; set immediate value field and the pc entry 
       (I1 (mset pc (set-inst-imm (1+ im) instr) I))
       ;; alternative way of getting immediate value field
       (im2 (mget :imm (mget pc I)))
       ((inst op rd rs1 imm) instr)
       )
  (list I1 instr im2 (list :op op :rd rd :rs1 rs1 :imm imm)))

(defun make-descending-addresses (n)
  (if (zp n)
    nil
    (cons (1- n) (make-descending-addresses (- n 1)))))

(defun nth-imem-custom-builtin (n)
  (declare (xargs :mode :program))
  (let* ((m (nth-imem n))
         (vals (strip-cdrs m))
         (keys (make-descending-addresses (len m))))
    (pairlis$ keys vals)))

(defun imem-customp (x)
  (or (null x)
      (and (consp x)
           (consp (car x))
           (imem-customp (cdr x))
           (instp (cdar x))
           (p-addrp (caar x))
           (or (and (null (cdr x))
                    (equal 0 (caar x)))
               (> (caar x) (caadr x))))))

(acl2s::register-type imem-custom
               :predicate imem-customp
               :enumerator nth-imem-custom-builtin)

(defdata-attach imem :test-enumerator nth-imem-custom)
;(acl2s-defaults :set testing-enabled nil)

(defdata tree (oneof 'Leaf 
                     (node (val   . string)
                           (left  . tree)
                           (right . tree))))

; ACL2 2014 Workshop script END



;order of base case and recursive cases
(defdata
  (noo (oneof (cons integer noo)
              acl2s::nat 
              )))

;Test sig with dependent hyps (make this idempotent)
#|
(acl2s::sig nth (acl2s::nat (listof :a)) => :a 
             :satisfies (< acl2s::x1 (len acl2s::x2)) :verbose t)
|#

(defdata BinOp (oneof '+ '& '== '=>))

(defdata UnaryOp '~)


;TODO
(defdata PropEx (oneof boolean 
                       symbol
                       (unary ;(uop . UnaryOp)
                              (arg . PropEx))
                       (binary ;(bop . BinOp)
                               (arg1 . PropEx) (arg2 . PropEx))))

; NO termination help is provided for this record!! 
; (Works here, but not in beginner mode?)

(acl2s::defunc get-vars (px acc)
  :input-contract (and (PropExp px) (symbol-listp acc))
  :output-contract (symbol-listp (get-vars px acc))
    (cond ((booleanp px) acc)  
          ((symbolp px) (cons px acc))  
          ((unaryp px)  
           (get-vars (unary-arg px) acc))
          ((binaryp px)
           (get-vars (binary-arg1 px)
                    (get-vars (binary-arg2 px) acc)))) 
    :timeout 80)
 

;mutually recursive types (doesnt work in COMPATIBLE MODE)

(defdata
  (sexpr (oneof symbol
               (cons symbol sexpr-list)))
  (sexpr-list (oneof nil
                    (cons sexpr sexpr-list))))

(defdata
  (bexpr (oneof boolean
               (cons boolean bexpr-list)))
  (bexpr-list (oneof nil
                    (cons bexpr bexpr-list))))


(acl2::must-fail
 (defdata 
  (ok2 ok1)
  (ok3 ok1)))




(acl2::must-fail 
(defdata noo-set (set noo))
)

(defdata
  (koo (oneof acl2s::nat 
              (cons koo integer)
              )))

(defdata symbol-int-al (alistof acl2s::proper-symbol integer))
         
;acl2s-issue defdata-taking-forever

(defdata Lett1 (oneof 'a 'b 'c 'd))
(defdata Num1 (oneof 0 1 2 3))

;took more than 4-5 mins, aborted.
(defdata rec00
  (record (f1 . Lett1)
          (f2 . Num1)
          (f3 . integer)
          (f4 . Lett1)
          (f5 . rational))
  )

;defdata-taking-forever2
(defdata lrec (listof rec00))


 

;-------BEGIN type-info-lost-via-dest-elim----------------
;(in-theory (theory 'acl2s))
(defdata Lett (enum '(a b c d)))

(defdata Num (oneof 0 1 2 3))

(defdata rec
  (record (f1 . Lett)
          (f2 . Num)
          (f3 . integer)
          (f4 . Lett)
          (f5 . rational)))
 
(table defdata-defaults-table :verbosep t)




(acl2s-defaults :set verbosity-level 2)
;(trace$ defdata::simplify-term)
;(defdata::enable-record-dest-elim)
  
(acl2::must-fail
 (test? (implies (and (recp a1)
                     (recp a2)
                     (equal (mget :f3 a2)
                            (mget :f3 a1))
                     (equal (mget :f5 a2)
                            (+ 4 (mget :f5 a1))))
                (not (equal 'c (mget :f4 a1)))))
)


;(accumulated-persistence t)

;nested-records-dest-elim-problem
(defdata Lett2 (oneof 'a 'b 'c 'd))
(defdata Num2 (enum '(0 1 2 3)))

(defdata rec2
  (record (f1 . Lett2)
          (f2 . Num2)
          (f3 . integer)
          (f4 . Lett2)
          (f5 . rational)) :verbose t)

(acl2s-defaults :set verbosity-level 2)

(acl2::must-fail
(test?
 (implies (and (rec2p r)
              (equal 'c
                     (mget :f1 r))
              (equal '2
                     (mget :f2 r))
              (equal 123 (mget :f3 r)))
         (not (equal 'd
                     (mget :f4 r)))))  
)

(defdata rec1
  (record (f1 . rec2)
          (f5 . rational))
  :verbose t)

(acl2::must-fail
(test?
 (implies (and (rec1p r)
              (equal 'c
                     (mget :f1 (mget :f1 r)))
              (equal '2
                     (mget :f2 (mget :f1 r)))
              (equal 123 (mget :f3 (mget :f1 r))))
         (not (equal 'd
                     (mget :f4 (mget :f1 r))))))

)


;acl2s-issue 27 June 13 defdata-record-nested-record-bug
(defdata r1
  (record (f2 . boolean)))



; took 3.26 seconds prev
(defdata r2  (record (f2 . r1)))
; now 0.79 sec


(program) 

(defun q1 (x)
  x)

(defun r3 (x)
  x)

(acl2::test? (equal (r3 x) (q1 x)))

(logic)

;tau complains.
(defdata element acl2s::all)
(defdata chksomething (record (fx1 . integer) (fx2 . element)))

(defdata dumb (record (x . integer)
                      (y . integer)))
 
(acl2s::defunc dum1p (v)
  :input-contract t
  :output-contract (booleanp (dum1p v))
  (and (dumbp v)
       (let ((x (mget :x v))
             (y (mget :y v)))
         (equal x y))))


(defdata (ok1 integer))
; test poly sig forms

;(sig nthcdr (nat (listof :a)) => (listof :a))

;(sig binary-append ((listof :a) (listof :a)) => (listof :a))


(defdata lon (listof acl2s::nat))

(defdata lor (listof rational))

(defdata loc (listof acl2::character))

(defdata j-base-vals (oneof lor loc))

#|
(defthm jbase-<=atom-list
  (implies (j-base-valsp x)
           (atom-listp x))
  :rule-classes :tau-system)
|#
;(defdata::set-acl2s-defdata-verbose t)

(defdata pre-value (record (dim . lon)
                           (val . j-base-vals)))



;Lesson: FORCEing hyps not good. modifier lemmas in records
;not going through if you force hyps in selector lemmas.

;TODO- Need a shape disjointedness theory.


(acl2s::defunc app (x y)
  :input-contract (and (true-listp x) (true-listp y))
  :output-contract (true-listp (app x y))
  (if (endp x)
    y
    (cons (car x) (app (cdr x) y))))

;(acl2s-defaults :set defunc-verbosity-level 4)

(acl2s::defunc square-list (l)
  :input-contract (nat-listp l)
  :output-contract (nat-listp (square-list l))
  (if (endp l)
      nil
    (app  (list (* (car l) (car l)))
          (square-list (cdr l)))))


(defdata reg nat)

(defdata pc nat)

;(defdata register (map reg integer) :type-lemmas t)
(defdata register (alistof reg integer))
;(defdata register (map reg integer))

(defdata dmemory (map nat integer))

(defdata operation-code (enum '(add sub mul load loadi store bez jump)))

(defdata instruction1 (record (opcode . operation-code)
                             (rc . reg)
                             (ra . reg)
                             (rb . reg)))

(defdata imemory (map pc instruction1))

(defdata ISA (record
              (_pc . pc)
              (_regs . register)
              (_imem . imemory)
              (_dmem . dmemory)))


;FAIL
(acl2::must-fail (defdata interrupt-level (enum 'V_IL_NONE 'V_IL_RESET 'V_IL_ILLEGAL))) 

;PASS
(defdata interrupts (oneof 'V_IL_NONE 'V_IL_RESET 'V_IL_ILLEGAL))
(defdata interrupt-level (enum '(V_IL_NONE V_IL_RESET V_IL_ILLEGAL)))

;DONE why do 2 syntaxes for enum exist? 
;It should be the same as sets::in or member-equal



; 2 April 2014 - acl2-help grant question defdata
;BUG: TESTING errors inside local events
;BUG: This form is not idempotent (redundancy does not work)

(defdata tree1 (oneof ;nil
               'leaf
               (node (id . string);symbol does not work! 
                     (left . tree1) 
                     (right . tree1))))
 

;-----------acl2s-issue defdata-mutual-recursion-error ----------------

(defdata lo-nat (listof nat))

(defdata op (oneof '+ '* 'and 'or 'not))
 
;(defdata var acl2s::proper-symbol)  ;already defined in var-book
;(verify-guards varp)
(defdata lo-var (listof var))

(defdata isort (oneof 'Nat 'Shape))

(defdata lo-isort (listof isort))

; use map (key is symbol, which can be nil, therefore not disjoint)
(defdata lo-var-isort (listof (cons var isort)))
;(set-termination-method :ccg)

(defdata 
  (expr (oneof var
               (list 'A lo-nat lo-el-expr)
               (list 'tlam lo-var expr)
               (list 'ilam lo-var-isort expr)
               (cons expr lo-expr)
               (cons 'tapp (cons expr lo-jtype))
               (cons 'iapp (cons expr lo-idx))
               (list 'sum lo-idx expr jtype)
               (list 'proj expr)))
  (el-expr (oneof integer 
                  boolean
                  (list 'lam lo-var-jtype expr)
                  op
                  expr))
  (lo-el-expr (listof el-expr))
  (jtype (oneof 'num
                'boolean
                var
                (list 'array idx jtype)
                (cons 'cross lo-jtype)
                (list (cons jtype lo-jtype) '-> jtype)
                (list 'forall lo-var jtype)
                (list 'pi lo-var-isort jtype)
                (list 'sigma lo-var-isort jtype)))
  (lo-expr (listof expr))
  (lo-var-jtype (listof (cons var jtype)))
  (lo-jtype (listof jtype))
  (idx (oneof nat
              var
              (cons 'shape lo-idx)
              (cons 'frame idx-idx)
              (list 'witness var expr)))
  (lo-idx (listof idx))
  (idx-idx (listof (cons idx idx))))



(defdata atomic-formula symbol)

(defdata 
  (ctl* (oneof t 
                nil
                atomic-formula
                (list '~ ctl*)
                (list ctl* '& ctl*)
                (list ctl* '! ctl*)
                (list ctl* '=> ctl*)
                (list ctl* '<=> ctl*)
                (list 'E ctl*path)
                (list 'A ctl*path)))
  (ctl*path (oneof nil
                   ctl* 
                (list '~ ctl*path)
                (list ctl*path '& ctl*path)
                (list ctl*path '! ctl*path)
                (list ctl*path '=> ctl*path)
                (list ctl*path '<=> ctl*path)
                (list 'X ctl*path)
                (list 'F ctl*path)
                (list 'G ctl*path)
                (list ctl*path 'U ctl*path))))

  

(defdata label integer)
;(defdata var symbol)
(defdata prim (enum '(+ - * if)))
(defdata varlst (listof var))

(defdata
  (arg (oneof var
              integer
              lam))
  (arglst (listof arg))
  (var-lam-lst (listof (cons var lam)))
  (lam (list 'lambda label varlst call))
  (call (oneof (list fun label arglst)
               (list 'letrec var-lam-lst call)))
  (fun (oneof var lam prim)))


(defdata non-neg-rational (oneof 0 acl2s::pos-rational))
(defdata-subtype non-neg-rational rational 
  :rule-classes ((:compound-recognizer) (:forward-chaining)))


;---------------------------------------------------------------------------------------------------
; pete email 28th june 13 messing cgen record elim
(defdata Lett0 (oneof 'a 'b 'c))
(defdata Num0 (oneof 1 2 3))

(defdata rec0
  (record (f1 . Lett0)
          (f2 . Lett0)
          (f3 . acl2s::all)
          (f4 . Lett0)))


(defdata rec01
  (record (f1 . rec0)
          (f5 . rational)))

(acl2s::defunc bar (x)
  :input-contract (rec01p x)
  :output-contract (booleanp (bar x))
  (implies (equal (mget :f5 x) 12)
           (equal (mget :f2 (mget :f1 x)) 'a)))

(acl2s-defaults :set verbosity-level 2)
(acl2s-defaults :set testing-enabled t)
(acl2::must-fail
 (test? (implies (rec01p x)
              (bar x)))
)



;-----------------------------------------------------------------------------------------------------









(acl2s-defaults :set testing-enabled t)


(acl2::must-fail

(thm ;test pos-rat is subtype of rat
 (implies (and (rationalp x)
               (> x 0)
               (< x 1))
          (< x y)))
)

; our replacement for exists y ...
(defun f-y (x)
 x)

; the "karl" claim
(defun karl (c x)
 (let ((y (f-y x)))
   (<= c (+ (* x y) (* (- 1 x) (- 1 (* y y)))))))

; this proof goes through, ie, the claim with c=1/2 is provably true
(thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 1))
             (karl 1/2 x)))

; this proof goes through, ie, the claim with c=.55 is provably true
(thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 1))
             (karl 55/100 x)))

; this proof goes through, ie, the claim with c=.59 is provably true
(thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 1))
             (karl 59/100 x)))

; this proof goes through, ie, the claim with c=.60 is provably true
(thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 1))
             (karl 60/100 x))
    :hints (("goal" :cases ((<= x 3/4)))))

; this proof goes through, ie, the claim with c=.61 is provably true
(thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 1))
             (karl 61/100 x))
    :hints (("goal" :cases ((<= x 60/100)))))

; this proof goes through, ie, the claim with c=.615 is provably true
(thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 1))
             (karl 615/1000 x))
    :hints (("goal" :cases ((<= x 58/100)))))

; here we get counterexamples, so the claim with c=.62 is false if y=x
(acl2::must-fail
 (thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 1))
             (karl 62/100 x)))
)

(thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 42/100))
             (karl 65/100 x)))

(thm (implies (and (rationalp x)
                  (<= 72/100 x)
                  (<= x 1))
             (karl 65/100 x)))
(acl2::must-fail
(thm (implies (and (rationalp x)
                  (<= 0 x)
                  (<= x 1))
             (karl 6152/1000 x))
    :hints (("goal" :cases ((<= x 58/100)))))
)

;;custom data type
(defun goop (x)
  (and (integerp x)
       (> x 3)))

(defun nth-goo-builtin (n)
  ;(declare (xargs :guard (natp n)))
  (+ n 4))

(acl2s::register-type goo :predicate goop :enumerator nth-goo-builtin)
;(trace$ defdata::process-and-apply-dependencies)
(acl2s-defaults :set verbosity-level 2)

(acl2::must-fail
 (test? (implies (goop x)
               (not (equal 0 (acl2::mod x 13)))))
)
;Notes: thm will not capture top-level type information. Use thm? or test? instead.

;(assign make-event-debug t)
;;union type
(acl2::verify-guards goop)

(defdata  fob (oneof goo boolean))

(defdata 
  BorC (oneof boolean acl2::character))

;alias
(defdata int integer) ;;like typedef in C and type in ML

;;test defdata syntax
(defdata foo1 (oneof 1 2 3 4))
(defdata foo2 (oneof 1 '(2 3) 4))
(defdata foo3 '(1 2 3 4))


(defdata foo4 (list 1 2 3 4))
(defdata foo6 (cons 1 2))


;test arbitrary combinations of union and product type expressions
(defdata (yoo (oneof (cons 1 2) (cons 'a 'b))))
(defdata (zz (oneof (oneof 1 2) 3)))

(defdata (zzz (oneof (oneof 1 2) (oneof 4 5))))


(defdata (zzzz (cons (oneof zz zzz) (oneof yoo int))))
(defdata (zzzzz (cons (oneof (cons zz int) zzz) (oneof yoo (cons boolean int)))))

(defdata woo (cons (cons (oneof boolean 'ok) (cons 2 'as))
                     (oneof (cons int string) (oneof nat int) 42)))

;simple recursive type
(defdata hoo (oneof 1 
                 (cons integer hoo)
                 ))



;enumeration types
(defdata rgb (enum '(red blue green)))

;FAIL
(acl2::must-fail
 (defdata rgb2 (enum 'red 'blue 'green))
)
(defdata natt nat)

(defun nat-restrict (x)
  (declare (ignore x))
  99)

(defdata-attach natt :test-enumerator nat-restrict)
(in-theory (disable nattp))
(acl2s-defaults :set verbosity-level 2)
 (test? ;BUG::Why is top-level type information getting thrown away
        ;Seems to be working fine now. But print output is misleading-- says 2 unique sat
 (implies (nattp x) (= x 99))) 


(defdata tst12 (enum '(ok1 ok2)))
(defdata less6 (enum (list 1 2 3 4 5)))
;(defdata rgb3 (enum red blue green))
(defdata chr1 (enum (acl2::append acl2s::*character-values* acl2s::*boolean-values* (list "assa"))))
(defdata char (enum acl2s::*character-values*))
;(defdata rgb1 (enum (red blue green))) ASK: Should not be allowed?


;a complex list type TODO FAILS
;(defdata lop (listof (oneof boolean integer)))



;;inductive definition List of integers and nat
;;another wat of writing the list type, infact list type is just syntactic sugar
(defdata         
  (loii (oneof nil
              (cons integer loii))))

(defun ha (a b)
  (mv (xor a b)
      (and a b)))

(defun fa (a b carry)
  (mv-let (s1 c1)
          (ha a b)
          (mv-let (s2 c2)
                  (ha s1 carry)
                  (mv s2 (or c1 c2)))))

;NOTE: CCG analysis gets ccounterexamples here in defun termination
; TODO fix DEFDATA::GET-TOP-LEVEL-ASSIGNMENT
(defun serial-adder (x y carry)
  (if (and (endp x)
           (endp y))
    (list carry)
    (mv-let (sum c)
            (fa (car x) (car y) carry)
            (cons sum (serial-adder (cdr x) (cdr y) c)))))

 

; Check Sequence. ALSO check hints syntax
(defdata
     fooo2 (oneof (cons integer fooo2)
                integer
                )
                 
          :hints (("Goal" :do-not-induct t))
     )
     

(defdata (fooo1 (oneof nil
                     (cons integer fooo1)
                     (cons fooo1 nat))))

(acl2::must-fail
 (defdata (f1 (cons integer brr1))
                (brr1 (cons nat f1)))
 )

;record types

(defdata triple (record (first . acl2s::all)
                        (second . acl2s::all)
                        (third . acl2s::all)))

(defdata mem (map nat string))


;simple recursive product data type TODO fix
(defdata tree2 (oneof 'Leaf (node1 (val . integer)
                                   (left . tree2)
                                   (right . tree2))))

(defun tree-count (tree)
  (if (endp tree)
    0
    (+ 1
       (tree-count (node1-left tree))
       (tree-count (node1-right tree)))))

