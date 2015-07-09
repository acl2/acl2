; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility

(error "Is anyone using this?  If so please remove this error.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; defpun-definitions.lisp
;; John D. Powell
(in-package "DEFPUN")

;;
;; This file isolates defpun definitions and types. The file currently 
;; contains the following ACL2 constructs as they occur in the defpun book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(defun natural-listp (list)
  (declare (type t list))
  (if (consp list)
      (and (natp (car list))
           (natural-listp (cdr list)))
    (null list)))

(defthm true-listp-from-natural-listp
  (implies (natural-listp x)
           (true-listp x))
  :rule-classes (:forward-chaining))

(defun ack_induction (x y r s)
  (declare (xargs :measure (ack_measure x y r)))
  (if (ack_terminates x y r)
      (if (and (not (consp r)) (zp x)) (+ y 1)
        (if (zp x) (ack_induction (car r) (+ y 1) (cdr r) (cdr s))
          (if (zp y) (ack_induction (1- x) 1 r s)
            (ack_induction x (1- y) (cons (1- x) r) (cons (1- x) s)))))
    (cons s (+ y 1))))

;;
;;
;;

(defun head-equal (s r)
  (if (consp s)
      (and (consp r)
           (equal (car s) (car r))
           (head-equal (cdr s) (cdr r)))
    t))

;; jcd - Removing list-equal -- use list::equiv instead, it is provably 
;; equal and already has lots of nice rules.

(defun list-equal (x y)
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (list-equal (cdr x) (cdr y)))
    (not (consp y))))

(DEFTHM OPEN-list-equal
  (IMPLIES (AND (CONSP X) (CONSP Y))
           (EQUAL (LIST-EQUAL X Y)
                  (AND (EQUAL (CAR X) (CAR Y))
                       (LIST-EQUAL (CDR X) (CDR Y)))))
  :HINTS (("Goal" :IN-THEORY (ENABLE LIST-EQUAL))))

(in-theory (disable list-equal))

;;

(DEFTHM CDR-APPEND-CONSP
  (IMPLIES (CONSP X)
           (EQUAL (CDR (APPEND X Y))
                  (APPEND (CDR X) Y)))
  :HINTS (("goal" :IN-THEORY (ENABLE APPEND))))

(DEFTHM CAR-APPEND-CONSP
  (IMPLIES (CONSP X)
           (EQUAL (CAR (APPEND X Y)) (CAR X)))
  :HINTS (("goal" :IN-THEORY (ENABLE APPEND))))

(DEFTHM LEN-APPEND
  (EQUAL (LEN (APPEND X Y))
         (+ (LEN X) (LEN Y)))
  :HINTS (("Goal" :IN-THEORY (ENABLE APPEND))))

(DEFTHM LEN-CONS
  (EQUAL (LEN (CONS A X)) (+ 1 (LEN X)))
  :HINTS (("Goal" :IN-THEORY (ENABLE LEN))))

(DEFTHM APPEND-CONSP-TYPE-TWO
  (IMPLIES (CONSP Y) (CONSP (APPEND X Y)))
  :RULE-CLASSES ((:TYPE-PRESCRIPTION)))

(DEFTHM APPEND-OF-CONS
  (EQUAL (APPEND (CONS A X) Y)
         (CONS A (APPEND X Y))))
  
(DEFTHM APPEND-OF-NON-CONSP-ONE
  (IMPLIES (NOT (CONSP X))
           (EQUAL (APPEND X Y) Y))
  :HINTS (("Goal" :IN-THEORY (ENABLE APPEND))))

;;

(defthm list-equal-implication
  (implies (list-equal r s)
           (and (head-equal r s)
                (<= (len r) (len s))))
   :rule-classes (:forward-chaining))

(defthm not-consp-implication
  (implies (not (consp r))
           (and (head-equal r s)
                (<= (len r) (len s)))))

(defthm head-equal-append
  (head-equal x (append x y)))

(in-theory (disable append))

;; we get this from lists
;; (defthm len-append
;;   (<= (len x) (len (append x y))))

(defthm ack_terminates_from_ack_terminates
  (implies (and (ack_terminates x y s)
                (head-equal r s)
                (<= (len r) (len s)))
           (ack_terminates x y r))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :induct (ack_induction x y s r))))

(defthm ack_terminates_nil
  (implies (and (ack_terminates x y s)
                (syntaxp (not (quotep s))))
           (ack_terminates x y nil))
  :rule-classes (:forward-chaining))

;; jcd - removing this, it seems redundant with the congruence rule
;; above.
;; (defthm ack_reduction_free
;;   (implies (and (ack_terminates x y r)
;;                 (syntaxp (not (acl2::term-order r s)))
;;                 (list-equal s r))
;;            (equal (ack x y s)
;;                   (ack x y r))))

(defthmd open_ack_terminates-1
  (implies
   (syntaxp (and (or (symbolp x) (quotep x))
                 (or (symbolp y) (quotep y))))
   (and
    (implies
     (not (acktest_body x y xargs))
     (iff
      (ack_terminates x y xargs)
      (let
       ((x (car (ackstep_body_1 (list x y xargs))))
        (y (car (cdr (ackstep_body_1 (list x y xargs)))))
        (xargs
         (car (cdr (cdr (ackstep_body_1 (list x y xargs)))))))
       (ack_terminates x y xargs))))
    (implies (acktest_body x y xargs)
             (ack_terminates x y xargs)))))
  
(defthm ack_termiantes_on_ack
  (implies
   (and
    (consp r)
    (ack_terminates x y (append s r)))
   (ack_terminates (car r) (ack x y s) (cdr r)))
  :hints (("goal" :in-theory (enable open_ack_terminates-1)
           :induct (ack x y s))))


(defthm ack_measure_on_ack
  (implies
   (and
    (consp r)
    (ack_terminates x y (append s r)))
   (equal (ack_measure x y (append s r))
          (+ (ack_measure x y s)
             (ack_measure (car r) (ack x y s) (cdr r)))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable open_ack_terminates-1)
           :induct (ack x y s))))


(defthm ack_measure_reduction
  (implies
   (ack_terminates x y (cons a r))
   (equal (ack_measure x y (cons a r))
          (+ (ack_measure x y nil)
             (ack_measure a (ack x y nil) r))))
  :hints (("goal" :in-theory (disable OPEN_ACK_MEASURE)
           :use (:instance ack_measure_on_ack
                           (s nil)
                           (r (cons a r))))))

(defthm ack_on_ack
  (implies
   (and
    (consp r)
    (ack_terminates x y (append s r)))
   (equal (ack x y (append s r))
          (ack (car r) (ack x y s) (cdr r))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable open_ack_terminates-1)
           :induct (ack x y s))))


(defthm ack_reduction
  (implies
   (ack_terminates x y (cons a r))
   (equal (ack x y (cons a r))
          (ack a (ack x y nil) r)))
  :hints (("goal" :use (:instance ack_on_ack
                                  (s nil)
                                  (r (cons a r))))))

(defun ak (x y)
  (ack x y nil))

(defun ak_terminates (x y)
  (ack_terminates x y nil))

(defun ak_measure (x y)
  (ack_measure x y nil))

(defthm ak_spec
  (equal (ak x y)
         (if (ak_terminates x y)
             (if (zp x) (+ y 1)
               (if (zp y) (ak (1- x) 1)
                 (ak (1- x) (ak x (1- y)))))
           (+ y 1)))
  :rule-classes nil)

(defthm ak_measure_spec
  (implies
   (ak_terminates x y)
   (equal (ak_measure x y) 
          (if (zp x) (o)
            (if (zp y) (1+ (ak_measure (1- x) 1))
              (+ 1 (ak_measure x (1- y))
                 (ak_measure (1- x) (ak x (1- y))))))))
  :hints (("goal" :in-theory (disable OPEN_ACK_TERMINATES-1))))

(in-theory
 (disable
  ak
  ak_measure
  ak_terminates
  ))

(defun o () 1)
(defun inx (x m)
  (declare (ignore x))
  (+ 1 (nfix m)))

(defun unbundle (args list)
  (if (consp args)
      (cons `(,(car args) (car ,list))
            (unbundle (cdr args) `(cdr ,list)))
    nil))

(defun args-syntax-guard (args)
  (if (consp args)
      (cons `(or (symbolp ,(car args)) (quotep ,(car args)))
            (args-syntax-guard (cdr args)))
    nil))

(defun generate-open-theorems (fn fn-test fn-terminates fn-step-1 args head tail)
  (declare (xargs :mode :program))
  (if (consp head)
      (let ((arg (car head)))
        (cons
         `(defthmd ,(packn-pos (list "OPEN_" fn "_TERMINATES_" arg) fn)
            (implies
             (syntaxp (and ,@(args-syntax-guard (append (cdr head) tail))))
             (and (implies (not (,fn-test ,@args))
                           (iff (,fn-terminates ,@args)
                                (let ,(unbundle args `(,fn-step-1 (list ,@args)))
                                  (,fn-terminates ,@args))))
                  (implies (,fn-test ,@args)
                           (,fn-terminates ,@args)))))
         (generate-open-theorems fn fn-test fn-terminates fn-step-1 args (cdr head) (cons arg tail))))
    nil))

(defun if-formp (form)
  (declare (type t form))
  (if (consp form)
      (if (equal (car form) 'if)
          (and (consp (cdr form))
               (consp (cddr form))
               (consp (cdddr form))
               (null  (cddddr form)))
        (if (equal (car form) 'let)
            (and (consp (cdr form))
                 (consp (cddr form))
                 (null  (cdddr form))
                 (if-formp (caddr form)))
          t))
    nil))

;;
;; Some number of let's followed by an "if"
;;

(defun if-test (form)
  (declare (type (satisfies if-formp) form))
  (if (consp form)
      (if (equal (car form) 'if)
          (cadr form)
        (if (equal (car form) 'let)
            `(let ,(cadr form)
               ,(if-test (caddr form)))
          nil))
    nil))

(defun if-base (form)
  (declare (type (satisfies if-formp) form))
  (if (consp form)
      (if (equal (car form) 'if)
          (caddr form)
        (if (equal (car form) 'let)
            `(let ,(cadr form)
               ,(if-base (caddr form)))
          nil))
    nil))

(defun if-body (form)
  (declare (type (satisfies if-formp) form))
  (if (consp form)
      (if (equal (car form) 'if)
          (cadddr form)
        (if (equal (car form) 'let)
            `(let ,(cadr form)
               ,(if-body (caddr form)))
          nil))
    nil))

(defun contains-fapp-rec (fn args form)
  (declare (type t form))
  (if (consp form)
      (if args
                (or (contains-fapp-rec fn nil (car form))
              (contains-fapp-rec fn   t (cdr form)))
        (or (equal fn (car form))
            (contains-fapp-rec fn t (cdr form))))
    nil))

(defun wf-measure-body (fn form)
  (declare (type t form))
  (and (if-formp form)
       (not (iff (contains-fapp fn (if-base form))
                 (contains-fapp fn (if-body form))))))

(defun remap-fn-rec (fn fn* args form)
  (declare (type (satisfies true-listp) fn*))
  (if (consp form)
      (if args
          (cons (remap-fn-rec fn fn* nil (car form))
                (remap-fn-rec fn fn* t (cdr form)))
        (if (equal fn (car form))
            (append fn* (remap-fn-rec fn fn* t (cdr form)))
          (cons (car form) (remap-fn-rec fn fn* t (cdr form)))))
    form))

(defun replace-fn-rec (fn term args form)
  (declare (type t form))
  (if (consp form)
      (if args
          (cons (replace-fn-rec fn term nil (car form))
                (replace-fn-rec fn term t (cdr form)))
        (if (equal fn (car form))
            term
          (cons (car form) (replace-fn-rec fn term t (cdr form)))))
    form))

(defun map-replace-fn (fn list body)
  (declare (type t fn list body))
  (if (consp list)
      (cons
       (replace-fn fn (car list) body)
       (map-replace-fn fn (cdr list) body))
    nil))

(defthm true-listp-map-replace-fn
  (true-listp (map-replace-fn fn list body)))

(defun extract-fn (fn args form)
  (declare (type t form))
  (if (consp form)
      (if args
          (or (extract-fn fn nil (car form))
              (extract-fn fn t (cdr form)))
        (if (equal fn (car form)) form
          (extract-fn fn t (cdr form))))
    form))

(defun push-lets (fn body)
  (declare (type t fn body))
  (let ((fcall (extract-fn fn nil body)))
    (if (consp fcall)
        `(,fn ,@(map-replace-fn fn (cdr fcall) body))
      `(,fn))))

(defun test-base-body (fn form)
  (declare (type (satisfies if-formp) form))
  (let ((body (if-body form)))
    (if (contains-fapp fn body)        
        (mv `(not (not ,(if-test form))) (if-base form) body)
      (mv `(not ,(if-test form)) body (if-base form)))))

(defun pun-form (fn form)
  (declare (type (satisfies if-formp) form))
  (let ((body (if-body form)))
    (if (contains-fapp fn body)        
        (let ((test (if-test form))
              (base (if-base form))
              (body (push-lets fn body)))
          `(if ,test ,base ,body))
      (let ((test `(not ,(if-test form)))
            (base body)
            (body (push-lets fn (if-base form))))
        `(if ,test ,base ,body)))))

(defun first-list (list)
  (declare (type t list))
  (if (consp list)
      (if (consp (cdr list))
          (cons (car list) (first-list (cdr list)))
        nil)
    nil))

;    (declare (xargs :guard (wf-measure-body fn form)))

(defun contains-guard-declaration-rec (decl)
  (declare (type t decl))
  (if (consp decl)
      (if (consp (car decl))
          (or (equal (caar decl) 'type)
              (contains-guard-declaration-rec (cdr decl)))
        (contains-guard-declaration-rec (cdr decl)))
    nil))

(defun contains-guard-declaration (decl)
  (declare (type t decl))
  (and (consp decl)
       (equal (car decl) 'declare)
       (contains-guard-declaration-rec (cdr decl))))

(defun contain-guard-declarations (decls)
  (declare (type t decls))
  (if (consp decls)
      (or (contains-guard-declaration (car decls))
          (contain-guard-declarations (cdr decls)))
    nil))

(defun just-body (fn term)
  (declare (type t fn term))
  (if (consp term)
      (if (consp (car term))
          (if (equal (caar term) fn)
              (car term)
            (just-body fn (cdr term)))
        (just-body fn (cdr term)))
    nil))

(defun tail-body (fn form)
  (declare (type (satisfies if-formp) form))
  (if (consp form)
      (if (equal (car form) 'let)
          `(let ,(cadr form)
             ,(tail-body fn (caddr form)))
        (just-body fn form))
    nil))

(defthm vfaat_fn_to_fn_pun
  (implies
   (and
    (vfaat_fn_hyps k st)
    (vfaat_fn_induction_terminates k st))
   (equal (vfaat_fn k st)
          (vfaat_fn_pun (vfaat_fn_base) k st)))
  :rule-classes nil
  :hints (("Goal" :use (:functional-instance 
                        (:instance defxch_fn_to_fn_pun (x (list k st)))
                        (defxch_hyps       (lambda (list) (vfaat_fn_hyps (car list) (cadr list))))
                        (defxch_type       vfaat_fn_type)
                        (defxch_fn         (lambda (list) (vfaat_fn (car list) (cadr list))))
                        (defxch_fn_pun     (lambda (x list) (vfaat_fn_pun x (car list) (cadr list))))
                        (defxch_test       (lambda (list) (vfaat_fn_test (car list))))
                        (defxch_base       (lambda (r x) r))
                        (defxch_r0         vfaat_fn_base)
                        (defxch_default    vfaat_fn_default)
                        (defxch_steps      (lambda (list) (list (vfaat_fn_branch (car list) (cadr list))
                                                                (vfaat_fn_comp (car list) (cadr list)))))
                        (defxch_measure    (lambda (list) (vfaat_fn_induction_measure (car list) (cadr list))))
                        (defxch_terminates (lambda (list) (vfaat_fn_induction_terminates (car list) (cadr list))))
                        (defxch_inc        (lambda (list r) (vfaat_fn_inc (car list) (cadr list) r)))
                        ))))

(defthm vfaat_fnx_to_fn_pun
  (implies
   (and
    (vfaat_fnx_hyps k st)
    (vfaat_fnx_induction_terminates k st))
   (equal (vfaat_fnx k st)
          (vfaat_fnx_pun (vfaat_fnx_r0) k st)))
  :rule-classes nil
  :hints (("Goal" :use (:functional-instance 
                        (:instance defxch_fn_to_fn_pun (x (list k st)))
                        (defxch_hyps       (lambda (list) (vfaat_fnx_hyps (car list) (cadr list))))
                        (defxch_type       vfaat_fnx_type)
                        (defxch_fn         (lambda (list) (vfaat_fnx (car list) (cadr list))))
                        (defxch_fn_pun     (lambda (x list) (vfaat_fnx_pun x (car list) (cadr list))))
                        (defxch_test       (lambda (list) (vfaat_fnx_test (car list))))
                        (defxch_base       (lambda (r list) (vfaat_fnx_base r (car list) (cadr list))))
                        (defxch_r0         vfaat_fnx_r0)
                        (defxch_default    vfaat_fnx_default)
                        (defxch_steps      (lambda (list) (list (vfaat_fnx_branch (car list) (cadr list))
                                                                (vfaat_fnx_comp (car list) (cadr list)))))
                        (defxch_measure    (lambda (list) (vfaat_fnx_induction_measure (car list) (cadr list))))
                        (defxch_terminates (lambda (list) (vfaat_fnx_induction_terminates (car list) (cadr list))))
                        (defxch_inc        (lambda (list r) (vfaat_fnx_inc (car list) (cadr list) r)))
                        ))))

#|
ACL2:

(defthm <NAME>_to_<NAME>_pun
  (implies
   (<TERMINATES> k st)
   (equal (<NAME> k st)
          (<NAME>_pun <BASE> k st)))
  :hints (("Goal" :use (:functional-instance 
                        vfaat_fn_to_fn_pun
                        (vfaat_fn_hyp1                 kstate-p)
                        (vfaat_fn_hyp2                 st-p)
                        (vfaat_fn_type                 <TYPE3>)
                        (vfaat_fn                      <NAME>)
                        (vfaat_fn_pun                  <NAME>_pun)
                        (vfaat_fn_induction_measure    <MEASURE>)
                        (vfaat_fn_induction_terminates <TERMINATES>)
                        (vfaat_fn_test                 <EXIT>)
                        (vfaat_fn_base                 (lambda () <BASE>))
                        (vfaat_fn_default              (lambda () <DEFAULT>))
                        (vfaat_fn_branch               <BRANCH>)
                        (vfaat_fn_comp                 <COMP>)
                        (vfaat_fn_inc                  <NAME>_inc)
                        ))))

PVS:

  IMPORTING defxch[
          <TYPE1>, <TYPE2>, <TYPE3>,
          <NAME>,
          <NAME>_pun,
          <NAME>_inc,
          <EXIT>,
          <BASE>,
          <DEFAULT>,
          <BRANCH>,
          <COMP>,
          <MEASURE>,
          <TERMINATES>
          ] as <NAME>_xch

  <NAME>_to_<NAME>_pun: LEMMA
    FORALL (k: <TYPE1>, st:<TYPE2>):
      <TERMINATES> =>
        <NAME>(k,st) =
          <NAME>_pun(<BASE>,k,st)
%|- <NAME>_to_<NAME>_pun: PROOF
%|-   (auto-rewrite "<NAME>_xch.fn_to_fn_pun") (skosimp) (assert)
%|- QED  


|#

#|
(defthm joe-type
  (implies
   (integerp x)
   (integerp (joe x))))
|#
;; The following form also happens to work, since the typed arguments
;; are used as witnesses for the defchosen default value of natp.
#|
(defchoose default-natp (n) nil
  (natp n))

(defthm natp-instance-type
  (implies
   (natp n)
   (natp (default-natp)))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("Goal" :use default-natp)))

|#

; Here is an example.  Suppose we wish to admit the tail recursive
; factorial.

; (defun trfact (n a)
;   (if (equal n 0)
;       a
;     (trfact (- n 1) (* n a))))

; Using the output of this check, we introduce three defuns

; (defun test1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     (equal n 0)))

; (defun base1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     a))

; (defun step1 (x)
;   (let ((n (car x))
;         (a (cadr x)))
;     (list (- n 1) (* n a))))

; We then use the generic theorem to introduce

; (defun trfact1 (x)
;   (if (test1 x)
;       (base1 x)
;     (trfact1 (step1 x))))

; We then define

; (defun trfact (n a)
;   (trfact1 (list n a)))

(defun defpun-stn (x n)
  (if (zp n) x (defpun-stn (defpun-st x) (1- n))))

(defchoose defpun-fch (n)
  (x)
  (defpun-test (defpun-stn x n)))

(defun defpun-fn (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (defpun-test x))
      (defpun-base x)
      (defpun-fn (defpun-st x) (1- n))))

(defthm defpun-ret-type-defpun-fn
  (implies
   (defpun-arg-type x)
   (defpun-ret-type (defpun-fn x n))))

(defun defpun-f (x)
  (if (defpun-test (defpun-stn x (defpun-fch x)))
      (defpun-fn x (defpun-fch x))
    (defpun-default)))

;; Key type theorem
(defthm defpun-ret-type-defpun-f
  (implies
   (defpun-arg-type x)
   (defpun-ret-type (defpun-f x))))

(defun defpun-true (x)
  (declare (ignore x)) t)

;; The "clique" theorem
(defthm defpun-true-defpun-f
  (defpun-true (defpun-f x)))

(in-theory (disable defpun-true))
(in-theory (disable (defpun-true)))
(in-theory (disable (:type-prescription defpun-true)))

; The following encapsulate exports one constrained function, namely,
; f, with the constraint

; (DEFTHM GENERIC-TAIL-RECURSIVE-F
;   (EQUAL (defpun-f X)
;          (IF (TEST X) (DEFPUN-BASE X) (defpun-f (DEFPUN-ST X))))
;   :RULE-CLASSES NIL)

; Nothing else is exported.

(defun arity-1-tail-recursive-encap (f test base st arg-type ret-type default)

; Execution of this function produces an encapsulation that introduces
; a constrained tail recursive f with the constraint
; (equal (defpun-f x) (if (defpun-test x) (defpun-base x) (defpun-f (defpun-st x)))),
; where test, base and st are previously defined functions of arity 1.

  (declare (xargs :mode :program))

  (let ((stn (packn-pos (list f "-stn") f))
        (fch (packn-pos (list f "-fch") f))
        (fn  (packn-pos (list f "-fn") f)))

    `(encapsulate
      ((,f (x) t))
    
      (local (in-theory (disable ,test ,base ,st)))

      (local (defun-nonexec ,stn (x n)
               (if (zp n)
                   x
                 (,stn (,st x) (1- n)))))

      (local (defchoose ,fch (n) (x)
               (,test (,stn x n))))

      (local (defun-nonexec ,fn (x n)
               (declare (xargs :measure (nfix n)))
               (if (or (zp n)
                       (,test x))
                   (,base x) 
                 (,fn (,st x) (1- n)))))

      (local (defun-nonexec ,f (x)
               (if (,test (,stn x (,fch x)))
                   (,fn x (,fch x))
                 (,default))))

      (defthm ,(packn-pos (list f "-CLIQUE") f)
        (defpun-true (,f x))
        :hints (("Goal"
                 :in-theory '(,f ,test ,base ,st ,stn ,fn ,arg-type
                                 (:type-prescription ,fn))
                 :use
                 (:functional-instance defpun-true-defpun-f
                                       (defpun-arg-type ,arg-type)
                                       (defpun-ret-type ,ret-type)
                                       (defpun-f ,f)
                                       (defpun-test ,test)
                                       (defpun-base ,base)
                                       (defpun-st ,st)
                                       (defpun-stn ,stn)
                                       (defpun-fch ,fch)
                                       (defpun-fn ,fn)
                                       (defpun-default ,default)
                                       ))
                ("Subgoal 2" :in-theory '(,f ,test ,base ,st ,stn ,fn ,arg-type
                                 (:type-prescription ,fn))
                 :use ,fch)
                (and stable-under-simplificationp
                     '(:in-theory (current-theory :here))))
        :rule-classes nil)

      (defthm ,(packn-pos (list f "-DEF") f)
        (equal (,f x)
               (if (,test x) 
                   (,base x) 
                 (,f (,st x))))
        :hints (("Goal"
                 :use
                 (:functional-instance GENERIC-TAIL-RECURSIVE-F
                                       (defpun-arg-type ,arg-type)
                                       (defpun-ret-type ,ret-type)
                                       (defpun-f ,f)
                                       (defpun-test ,test)
                                       (defpun-base ,base)
                                       (defpun-st ,st)
                                       (defpun-stn ,stn)
                                       (defpun-fch ,fch)
                                       (defpun-fn ,fn)
                                       (defpun-default ,default)
                                       )))
        :rule-classes nil)

      (defthm ,(packn-pos (list f "-TYPE") f)
        (implies
         (,arg-type x)
         (,ret-type (,f x)))
        :hints (("Goal"
                 :use
                 (:functional-instance defpun-ret-type-defpun-f
                                       (defpun-arg-type ,arg-type)
                                       (defpun-ret-type ,ret-type)
                                       (defpun-f ,f)
                                       (defpun-test ,test)
                                       (defpun-base ,base)
                                       (defpun-st ,st)
                                       (defpun-stn ,stn)
                                       (defpun-fch ,fch)
                                       (defpun-fn ,fn)
                                       (defpun-default ,default)
                                       )))
        :rule-classes nil)
      )
      
    ))

; Second, we recognize probably tail-recursive definitions and introduce
; the appropriate functions of arity 1.

; Note that probably-tail-recursivep and destructure-tail-recursion should be
; kept in sync.

(defun probably-tail-recursivep (f vars body)
  (and (symbolp f)
       (symbol-listp vars)
       (true-listp body)
       (eq (car body) 'IF)
       (or (and (consp (caddr body))
                (eq (car (caddr body)) f))
           (and (consp (cadddr body))
                (eq (car (cadddr body)) f)))))

(defun destructure-tail-recursion-aux (vars x)
  (declare (xargs :mode :program))
  (cond ((endp vars) nil)
        (t (cons (list (car vars)
                       (list 'car x))
                 (destructure-tail-recursion-aux (cdr vars)
                                               (list 'cdr x))))))

(defun destructure-tail-recursion (f vars body)
  (declare (xargs :mode :program))
  (cond
   ((and (consp (caddr body))
         (eq (car (caddr body)) f))
    (mv (destructure-tail-recursion-aux vars 'x)
        (list 'NOT (cadr body))
        (cadddr body)
        (cons 'LIST (cdr (caddr body)))))
   (t
    (mv (destructure-tail-recursion-aux vars 'x)
        (cadr body)
        (caddr body)
        (cons 'LIST (cdr (cadddr body)))))))

(defun arbitrary-tail-recursive-encap (f vars body arg-type ret-type default keypairs)
  (declare (xargs :mode :program))
  (mv-let
   (bindings test-body base-body step-body)
   (destructure-tail-recursion f vars body)
   (let ((f1    (packn-pos (list f "-arity-1") f))
         (type1 (packn-pos (list f "-arity-1-type") f))
         (test1 (packn-pos (list f "-arity-1-test") f))
         (base1 (packn-pos (list f "-arity-1-base") f))
         (step1 (packn-pos (list f "-arity-1-step") f)))
     `(encapsulate
          ()
        (encapsulate
            ((,f ,vars t))
          (set-ignore-ok t)
          (set-irrelevant-formals-ok t)
          (local (defun-nonexec ,test1 (x) (let ,bindings ,test-body)))
          (local (defun-nonexec ,base1 (x) (let ,bindings ,base-body)))
          (local (defun-nonexec ,step1 (x) (let ,bindings ,step-body)))
          (local (defun-nonexec ,type1 (x) (let ,bindings ,arg-type)))
          (local ,(arity-1-tail-recursive-encap f1 test1 base1 step1 type1 ret-type `(lambda () ,default)))
          (local (defun-nonexec ,f ,vars (,f1 (list ,@vars))))
          (defthm ,(packn-pos (list f "-DEF") f)
            (equal (,f ,@vars) ,body)
            :hints (("Goal" :use (:instance ,(packn-pos (list f1 "-DEF") f)
                                            (x (list ,@vars)))))
            ,@keypairs)

          ,@(and arg-type
                 `((defthm ,(packn-pos (list f "-TYPE") f)
                     (implies
                      ,arg-type
                      (,ret-type (,f ,@vars)))
                     :hints (("Goal" :use (:instance ,(packn-pos (list f1 "-TYPE") f)
                                                     (x (list ,@vars))))))))
          
          )
        ;;
        ;; DAG -- In most circumstances, the following rule appears to
        ;; work much better than the :definition rule above.
        ;; 
        ;; Nonetheless, I have it disabled for now.
        ;;
        (defthmd ,(packn-pos (list "OPEN-" f) f)
          (and
           (implies
            ,test-body
            (equal (,f ,@vars) ,base-body))
           (implies
            (not ,test-body)
            (equal (,f ,@vars) ,(cons f (cdr step-body)))))
          :hints (("Goal" :in-theory (theory 'minimal-theory)
                   :use ,(packn-pos (list f "-DEF") f))))
        ))))

(defun remove-xargs-domain-and-measure (dcl)
  (case-match dcl
              (('declare ('xargs ':domain dom-expr
                                 ':measure measure-expr
                                 . rest))
               (mv nil dom-expr measure-expr rest))
              (('declare ('xargs ':gdomain dom-expr
                                 ':measure measure-expr
                                 . rest))
               (mv t dom-expr measure-expr rest))
              (& (mv nil nil 0 nil))))

(mutual-recursion
 (defun subst-fn-into-pseudo-term (new-fn old-fn pterm)
   (declare (xargs :mode :program))
   (cond
    ((atom pterm) pterm)
    ((eq (car pterm) 'quote) pterm)
    ((or (eq (car pterm) 'let)
         (eq (car pterm) 'let*))
     (list (car pterm)
           (subst-fn-into-pseudo-bindings new-fn old-fn (cadr pterm))
           (subst-fn-into-pseudo-term new-fn old-fn (caddr pterm))))
    ((eq (car pterm) 'cond)
     (cons 'cond
           (subst-fn-into-pseudo-cond-clauses new-fn old-fn (cdr pterm))))
    (t
     (cons (if (eq (car pterm) old-fn)
               new-fn
             (car pterm))
           (subst-fn-into-pseudo-term-list new-fn old-fn (cdr pterm))))))
 
 (defun subst-fn-into-pseudo-bindings (new-fn old-fn pbindings)
   (declare (xargs :mode :program))
   (cond
    ((atom pbindings) pbindings)
    (t (cons (list (car (car pbindings))
                   (subst-fn-into-pseudo-term new-fn old-fn
                                              (cadr (car pbindings))))
             (subst-fn-into-pseudo-bindings new-fn old-fn (cdr pbindings))))))

 (defun subst-fn-into-pseudo-cond-clauses (new-fn old-fn pclauses)
   (declare (xargs :mode :program))
   (cond
    ((atom pclauses) pclauses)
    (t (cons (list (subst-fn-into-pseudo-term new-fn old-fn
                                              (car (car pclauses)))
                   (subst-fn-into-pseudo-term new-fn old-fn
                                              (cadr (car pclauses))))
             (subst-fn-into-pseudo-cond-clauses new-fn old-fn
                                                (cdr pclauses))))))

 (defun subst-fn-into-pseudo-term-list (new-fn old-fn list)
   (declare (xargs :mode :program))
   (cond
    ((atom list) list)
    (t (cons (subst-fn-into-pseudo-term new-fn old-fn (car list))
             (subst-fn-into-pseudo-term-list new-fn old-fn (cdr list)))))))

(defun default-defpun-rule-classes (keyword-alist)

; We add :rule-classes :definition to keyword-alist if :rule-classes is
; not mentioned in it.

  (cond
   ((keyword-value-listp keyword-alist)
    (cond ((assoc-keyword :rule-classes keyword-alist)
           keyword-alist)
          (t (list* :rule-classes :definition keyword-alist))))
   (t keyword-alist)))

(defun destructure-dcl-body-keypairs (lst)

; Lst is the tail of some defpun.  It optionally contains a DECLARE
; form, a body, and some keyword binding pairs, in that order.  We
; return the three components.  Body must be present, and if keyword
; binding pairs are present, the length of that part of the list must
; be even.  So the parity of the length of the list determines which
; optional components are present.

; 0. illegal - never allowed to happen
; 1. body
; 2. dcl body
; 3. body :rule-classes classes
; 4. dcl body :rule-classes classes
; 5. body :rule-classes classes :hints hints
; 6. dcl body :rule-classes classes :hints hints
; etc.
; If rule-classes is unspecified it defaults to :definition.

  (cond
   ((evenp (length lst))
    (mv (car lst)
        (cadr lst)
        (default-defpun-rule-classes (cddr lst))))
   (t (mv nil
          (car lst)
          (default-defpun-rule-classes (cdr lst))))))

(defun defpun-syntax-er nil
  '(er soft 'defpun
       "The proper shape of a defpun event is~%~
        (defpun g (v1 ... vn) body).~%~
        A single optional declare form may be present ~
        before the body.  If present, the form must be one of three:~%~
        (DECLARE (XARGS :witness fn))~%~
        or~%~
        (DECLARE (XARGS :domain dom-expr :measure m . rest))~%~
        or~%~
        (DECLARE (XARGS :gdomain dom-expr :measure m . rest)).~%~
        An optional keyword alist may be ~
        present after the body.  The declare form is used during the ~
        admission of the witness function.  The keyword alist is ~
        attached to the equality axiom constraining the new function ~
        symbol.  If the :rule-classes keyword is not specified by the ~
        keyword alist, :definition is used."))

(defun extract-pair (a plist)
  (if (and (consp plist)
           (consp (cdr plist)))
      (let ((key (car plist))
            (val (cadr plist)))
        (if (equal a key)
            (mv (cons key val) (cddr plist))
          (mv-let
           (pair plist) (extract-pair a (cddr plist))
           (mv pair (list* key val plist)))))
    (mv nil nil)))
          
(defun extract-type-info (keypairs)
  (declare (xargs :mode :program))
  (mv-let 
   (pair keypairs) (extract-pair :argtypes keypairs)
   (let ((argtype (if (consp pair) (cdr pair) nil)))
     (mv-let
      (pair keypairs) (extract-pair :valtype keypairs)
      (if (consp pair)
          (let ((rettype (cdr pair)))
            (mv-let 
             (pair keypairs) (extract-pair :default keypairs)
             (if (consp pair) 
                 (let ((default (cdr pair)))
                   (mv argtype rettype default keypairs))
               (let ((default `(,(packn-pos (list "DEFAULT-" rettype) rettype))))
                 (mv argtype rettype default keypairs)))))
        (let ((rettype '(lambda (x) t)))
          (mv-let 
           (pair keypairs) (extract-pair :default keypairs)
           (let ((default (if (consp pair) (cdr pair) 'nil)))
             (mv argtype rettype default keypairs)))))))))

(defstub steq (x) nil)

;; DAG : We might want to further constrain this so that the tesq is
;; boolean.  Alternately, we could have another predicate over test
;; that we later functionally instantiate over terminates.  ie: if
;; test satisfies some predicate, so does terminates.

(defstub tesq (x) nil)
(defstub basq (x) nil)

;; Generate this stuff ..

(DEFUN pun-stn (X N)
  (if (ZP N) x
    (pun-stn (steq X)
             (1- N))))

(defthm open-pun-stn
  (implies
   (not (zp n))
   (equal  (pun-stn x n) (pun-stn (steq x) (1- n)))))
      
(DEFCHOOSE pun-fch (N)
  (X)
  (tesq (pun-stn X n)))



(defthm pun-fch-prop
  (IMPLIES 
   (TESQ (PUN-STN x n))
   (TESQ (PUN-STN x (PUN-FCH x))))
  :hints (("goal" :use (:instance pun-fch))))

(defthm test-non-existence
  (implies
   (and
    (not (tesq a))
    (zp (pun-fch a)))
   (not (tesq (pun-stn a n))))
  :rule-classes nil
  :hints (("goal" :induct (pun-stn a n))
          ("Subgoal *1/2" :use (:instance pun-fch-prop (x a)))))

(defthm test-non-existence-instance
  (implies
   (and
    (not (tesq a))
    (zp (pun-fch a)))
   (not (tesq (pun-stn (steq a) n))))
  :hints (("goal" :use (:instance test-non-existence (n (1+ (nfix n)))))))

(defthm generalized-test-non-existence
  (implies
   (and
    (not (tesq a))
    (not (tesq (pun-stn a (pun-fch a)))))
   (not (tesq (pun-stn a n))))
  :rule-classes nil
  :hints (("goal" :induct (pun-stn a n))))

(defthm generalized-test-non-existence-instance
  (implies
   (and
    (not (tesq a))
    (not (tesq (pun-stn a (pun-fch a)))))
   (not (tesq (pun-stn (steq a) n))))
  :hints (("goal" :use (:instance generalized-test-non-existence (n (1+ (nfix n)))))))

(defthm  tesq_step_from_tesq
  (implies
   (not (tesq a))
   (iff (tesq (pun-stn a (pun-fch a)))
        (tesq (pun-stn (steq a) (pun-fch (steq a))))))
  :hints (("Goal''" :expand (PUN-STN A (pun-fch a)))))

(defun fch-term(a) (tesq (pun-stn a (pun-fch a))))

(defthm fch-term_step_from_fch-term
  (and
   (implies
    (not (tesq a))
    (iff (fch-term a)
         (fch-term (steq a))))
   (implies
    (tesq a)
    (fch-term a)))
  :hints (("goal" :use (:instance pun-fch-prop (n 0) (x a)))))
 
(defun xtesq (args) (tesq (car args)))
(defun xbasq (args) (cdr args))
(defun xsteq (args) (cons (steq (car args)) (inc (car args) (cdr args))))

;; (encapsulate
;;  (
;;   ((xun *) => *)
;;   )
 
;;  (local
;;   (encapsulate
;;    ()
   
(LOCAL 
 (IN-THEORY (DISABLE xtesq xbasq xsteq)))

(DEFUN xun-stn (X N)
  (IF (ZP N) X
      (xun-stn (xsteq X) (1- N))))

(defthm xunstn_to_punstn
  (equal (car (xun-stn x n))
         (pun-stn (car x) n))
  :hints (("goal" :in-theory (enable xsteq)
           :do-not '(eliminate-destructors))))

(defun xun-fch-fn (x)
  (pun-fch (car x)))

(defthm xun-fch
  (IMPLIES (XTESQ (XUN-STN X N))
           (LET ((N (XUN-FCH-fn X)))
                (XTESQ (XUN-STN X N))))
  :hints (("goal" :in-theory (enable xtesq))))

(DEFUN xun-fn (X N)
  (DECLARE (XARGS :MEASURE (NFIX N)))
  (IF (OR (ZP N) (xtesq X))
      (xbasq X)
      (xun-fn (xsteq X)
              (1- N))))

(DEFUN
  xun (X)
  (IF (xtesq (xun-stn X (xun-fch-fn X)))
      (xun-fn X (xun-fch-fn X))
      nil))

(defthm push_inc_into_fn
  (equal (inc v (xun-fn a n))
         (xun-fn (cons (car a) (inc v (cdr a))) n))
  :hints (("goal" :in-theory (enable xbasq xsteq xtesq))))

;;   ))

(defthm push_inc_into_xun
  (implies
   (tesq (pun-stn (car a) n))
   (equal (inc v (xun a))
          (xun (cons (car a) (inc v (cdr a)) ))))
  :hints (("goal" :in-theory (enable xun xtesq))))

(in-theory
 (disable
  xun
  ))
 
;; )

(defun xch-pun (r x) (xun (cons x r)))

(defthm xch-pun-def
  (equal (xch-pun r x)
         (if (tesq x) r
           (xch-pun (inc x r) (steq x))))
  :rule-classes (:definition)
  :hints (("goal" :in-theory (enable XSTEQ xbasq xtesq))))

(defun xch (a)
  (xun (cons a (r0))))

(defthm open-xun
  (and
   (implies
    (not (xtesq x))
    (equal (xun x) (xun (xsteq x))))
   (implies
    (xtesq x)
    (equal (xun x) (xbasq x)))))
   
(defthm xch_prop
  (implies
   (fch-term a)
   (equal (xch a)
          (if (tesq a) (r0)
            (inc a (xch (steq a))))))
  :hints (("goal" :in-theory (enable xsteq xbasq xtesq))
          (and acl2::stable-under-simplificationp
               `(:use ((:instance PUSH_INC_INTO_XUN
                                  (v a)
                                  (n (pun-fch (steq a)))
                                  (a (cons (steq a) (r0)))))))))

(defthm xch-pun-prop
  (implies
   (fch-term a)
   (equal (xch-pun (r0) a)
          (if (tesq a) (r0)
            (inc a (xch-pun (r0) (steq a))))))
  :hints (("goal" :use (:instance xch_prop))))

(defthm xch-xch-pun-reduction
  (equal (xch a) (xch-pun (r0) a)))

(defthm inc-pred-xch
  (implies
   (fch-term a)
   (inc-pred (xch a)))
  :hints (("goal" :in-theory '(xch_prop inc-pred-inc inc-pred-ro))))

