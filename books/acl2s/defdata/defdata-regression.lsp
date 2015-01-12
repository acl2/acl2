;Test sig with dependent hyps
(sig nth (nat (listof :a)) => :a 
             :satisfies (< x1 (len x2)))

(acl2s-defaults :set testing-enabled t)

(defdata BinOp (oneof '+ '& '== '=>))

(defdata UnaryOp '~)

(defdata PropEx (oneof boolean symbol
                       (unary (op . PropEx))
                       (binary (op1 . PropEx) (op2 . PropEx))))

#|
; NO termination help is provided for this record!! (Works here, but not in beginner mode?)
(defunc get-vars (px acc)
  :input-contract (and (PropExp px) (symbol-listp acc))
  :output-contract (symbol-listp (get-vars px acc))
    (cond ((booleanp px) acc)  
          ((symbolp px) (cons px acc))  
          ((unaryp px)  
           (get-vars (unary-op px) acc))
          ((binaryp px)
           (get-vars (binary-op1 px)
                    (get-vars (binary-op1 px) acc)))))  
 
|#



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

(include-book "misc/eval" :dir :system)

(must-fail
 (defdata 
  (ok2 ok1)
  (ok3 ok1)))

(defdata
  (noo (oneof nat 
              (cons integer noo)
              )))

(defdata noo-list (listof noo))

;TODO (better error message needed)
(must-fail (defdata noo-set (set noo)))


(defdata symbol-int-al (alistof proper-symbol integer))
         
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
 
(table defdata-defaults-table :verbose t)




(acl2s-defaults :set verbosity-level 2)
;(trace$ defdata::simplify-term)
;(defdata::enable-record-dest-elim)
  
(must-fail
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

(must-fail
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

(must-fail
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


:program 

(defun q1 (x)
  x)

(defun r3 (x)
  x)

(acl2::test? (equal (r3 x) (q1 x)))

:logic

;tau complains.
(defdata element all)
(defdata chksomething (record (fx1 . nat) (fx2 . element)))

(defdata dumb (record (x . nat)
                      (y . nat)))
 
(defunc foop (v)
  :input-contract t
  :output-contract (booleanp (foop v))
  (and (dumbp v)
       (let ((x (mget :x v))
             (y (mget :y v)))
         (equal x y))))


(defdata (ok1 nat))
; test poly sig forms

(sig nthcdr (nat (listof :a)) => (listof :a))

(sig binary-append ((listof :a) (listof :a)) => (listof :a))


(defdata lon (listof nat))

(defdata lor (listof rational))

(defdata loc (listof acl2::character))

(defdata j-base-vals (oneof lor loc))


(defdata pre-value (record (dim . lon)
                           (val . j-base-vals)))



;Lesson: FORCEing hyps not good. modifier lemmas in records
;not going through if you force hyps in selector lemmas.

;TODO- Need a shape disjointedness theory.


(defunc app (x y)
  :input-contract (and (true-listp x) (true-listp y))
  :output-contract (true-listp (app x y))
  (if (endp x)
    y
    (cons (car x) (app (cdr x) y))))

;(acl2s-defaults :set defunc-verbosity-level 4)

(defunc square-list (l)
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


(defdata inst (record (opcode . operation-code)
                      (rc . reg)
                      (ra . reg)
                      (rb . reg)))

(defdata imemory (map pc inst))

(defdata ISA (record
              (pc1 . pc)
              (regs . register)
              (imem . imemory)
              (dmem . dmemory)))


;FAIL
(must-fail (defdata interrupt-level (enum 'V_IL_NONE 'V_IL_RESET 'V_IL_ILLEGAL))) 

;PASS
(defdata interrupts (oneof 'V_IL_NONE 'V_IL_RESET 'V_IL_ILLEGAL))
(defdata interrupt-level (enum '(V_IL_NONE V_IL_RESET V_IL_ILLEGAL)))



; 2 April 2014 - acl2-help grant question defdata
;BUG: This form is not idempotent (redundancy does not work)

(defdata tree (oneof ;nil
               'leaf
               (node (id . string);symbol does not work! 
                     (left . tree) 
                     (right . tree))))
 


(defdata lo-nat (listof nat))

(defdata op (oneof '+ '* 'and 'or 'not))

(defdata var symbol)

(defdata lo-var (listof var))

(defdata isort (oneof 'Nat 'Shape))

(defdata lo-isort (listof isort))

; use map (key is symbol, which can be nil, therefore not disjoint)
(defdata lo-var-isort (listof (cons var isort)))

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

;TODO
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


(defdata non-neg-rational (oneof 0 positive-rational))
(defdata-subtype non-neg-rational rational 
  :rule-classes ((:compound-recognizer) (:forward-chaining)))


;---------------------------------------------------------------------------------------------------
; pete email 28th june 13 messing cgen record elim
(defdata Lett0 (oneof 'a 'b 'c))
(defdata Num0 (oneof 1 2 3))

(defdata rec0
  (record (f1 . Lett0)
          (f2 . Lett0)
          (f3 . all)
          (f4 . Lett0)))


(defdata rec01
  (record (f1 . rec0)
          (f5 . rational)))

(defunc bar (x)
  :input-contract (rec01p x)
  :output-contract (booleanp (bar x))
  (implies (equal (mget :f5 x) 12)
           (equal (mget :f2 (mget :f1 x)) 'a)))

(acl2s-defaults :set verbosity-level 2)
(acl2s-defaults :set testing-enabled t)
(must-fail
 (test? (implies (rec01p x)
              (bar x)))
)



;-----------------------------------------------------------------------------------------------------










;;custom data type
(defun goop (x)
  (and (integerp x)
       (> x 3)))

(defun nth-goo (n)
  ;(declare (xargs :guard (natp n)))
  (+ n 4))

(register-type goo :predicate goop :enumerator nth-goo)
;(trace$ defdata::process-and-apply-dependencies)
(acl2s-defaults :set verbosity-level 2)

(must-fail
 (test? (implies (goop x)
               (not (equal 0 (acl2::mod x 13)))))
)

(acl2::verify-guards goop)

(defdata fob (oneof goo boolean))

(defdata BorC (oneof boolean acl2::character))

;alias
(defdata int integer) ;;like typedef in C and type in ML

;;test defdata syntax
(defdata foo1 (oneof 1 2 3 4))
(defdata foo2 (oneof 1 '(2 3) 4))
(defdata foo3 '(1 2 3 4))


(defdata foo4 (list 1 2 3 4))
(defdata foo6 (cons 1 2))


;TODO: any expression evaluating to a constant/singletonType should be allowed. LATER


;test arbitrary combinations of union and product type expressions
(defdata (yoo (oneof (cons 1 2) (cons 'a 'b))))
(defdata (zz (oneof (oneof 1 2) 3)))(defdata (zzz (oneof (oneof 1 2) (oneof 4 5))))


(defdata (zzzz (cons (oneof zz zzz) (oneof yoo int))))
(defdata (zzzzz (cons (oneof (cons zz int) zzz) (oneof yoo (cons boolean int)))))

(defdata woo (cons (cons (oneof boolean 'ok) (cons 2 'as))
                     (oneof (cons int string) (oneof nat pos) 42)))




;enumeration types
(defdata rgb (enum '(red blue green)))

;FAIL
(must-fail
 (defdata rgb2 (enum 'red 'blue 'green))
)
(defdata natt nat)

(defun nat-restrict (x)
  (declare (ignore x))
  99)

(defdata-attach natt :test-enumerator nat-restrict)
(in-theory (disable nattp))

(must-fail
 (test? ;BUG::Why is top-level type information getting thrown away
 (implies (nattp x) (= x 99))) 
)
#|
(defdata-testing natt :test-enumerator '99) ;broke Sep 5 2013 TODO

(test? ;TODO FIX BUG
 (implies (nattp x) (= x 99))) 
|#

(defdata tst12 (enum '(ok1 ok2)))
(defdata less6 (enum (list 1 2 3 4 5)))
;(defdata rgb3 (enum red blue green))
(defdata chr1 (enum (acl2::append acl2::*character-values* acl2::*boolean-values* (list "assa"))))
(defdata char (enum acl2::*character-values*))
;(defdata rgb1 (enum (red blue green))) ASK: Should not be allowed?

;list type
(defdata loi (listof integer))


;a complex list type TODO FAILS
;(defdata lop (listof (oneof boolean integer)))

#|
(register-data-constructor (posp succ)
                           (pred))

(defdata ;TODO syntax check if succ is not defined and its not in dest-decl form!
  (nat1 (oneof (succ nat1)
              0)))
|#



 

; termination problem TODO (SEQUENCE important) ALSO check hints syntax
(defdata
     fooo2 (oneof (cons integer fooo2)
                integer
                )
                 
          :hints (("Goal" :do-not-induct t))
     )
     

;does not go thru in ACL2 compatible(now goes thru)
(defdata (fooo1 (oneof nil
                     (cons integer fooo1)
                     (cons fooo1 nat))))

(must-fail
 (defdata (f1 (cons integer brr1))
                (brr1 (cons nat f1)))
 )

;record types

(defdata triple (record (first . all)
                        (second . all)
                        (third . all)))

(defdata mem (map nat string))


;simple recursive product data
(defdata tree1 (oneof 'Leaf (node1 (val . integer)
                                   (left . tree1)
                                   (right . tree1))))


  

;TODO: Improve the error message
(must-fail
(defdata (a (oneof nil b))
         (b (enum a)))
)
;enum not allowed in mutually-recursive defs
(must-fail
(defdata (a (oneof nil b))
         (b (enum '(1 2))))            
)

