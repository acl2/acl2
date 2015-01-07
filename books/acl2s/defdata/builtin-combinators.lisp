#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
builtin combinators (oneof, member, range) in core defdata language
author: harshrc
file name: builtin-combinators.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "tools/bstar" :dir :system)

(table defdata-defaults-table nil 
       '((:debug       .  nil)
         (:print-commentary . t)
         (:print-summary  . nil)
         (:time-track     . t)
         (:testing-enabled . :naive)
         (:disable-non-recursive-p . nil)

; The following are quite stable and there is no reason for these to be overridden
         (:pred-suffix . "p") ;unused
         ;; (:pred-prefix . "")
         ;; (:enum-prefix . "nth-")
         ;; (:enum-suffix . "")
         ;; (:enum/acc-prefix . "nth-")
         ;; (:enum/acc-suffix . "/acc")
         (:pred-guard  .  (lambda (x) t))
         (:enum-guard  .  (lambda (x) (natp x)))
         (:enum/acc-guard . (lambda (m seed) (and (natp m) (unsigned-byte-p 31 seed))))
         

; The following 4 defaults shouldnt be overridden by user (of defdata
; macro) but only by implementors and extenders of defdata framework.
         (:pre-pred-hook-fns . nil) 
         (:post-pred-hook-fns . nil) 
         (:pre-hook-fns . nil) 
         (:post-hook-fns . nil) 
         )
       :clear)


; BUILTIN COMBINATOR TABLE

(defun member-pred-I (x s) `(and (member-equal ,x ,(cadr s)) t))
(defun member-enum-I (i s) `(nth (mod ,i (len ,(cadr s))) ,(cadr s)))
(defun member-enum/acc-I (i s) (declare (ignorable i))
  `(mv-let (idx _SEED) (random-index-seed (len ,(cadr s)) _SEED)
           (mv (nth idx ,(cadr s)) (the (unsigned-byte 31) _SEED))))

    
       
(defun get-tau-int (domain rexp)
  (let ((dom (if (eq domain 'integer)
                 'acl2::integerp
               'acl2::rationalp)))
  (case-match rexp
    ((lo lo-rel-sym '_ hi-rel-sym hi)
     (b* ((lo-rel (eq lo-rel-sym '<))
          (hi-rel (eq hi-rel-sym '<)))
       (acl2::make-tau-interval dom lo-rel lo hi-rel hi))))))

(defun make-acl2-range-constraints (x domain rexp)
  (let ((dom (if (eq domain 'integer)
                 'acl2::integerp
               'acl2::rationalp)))
  (case-match rexp
    ((lo lo-rel-sym '_ hi-rel-sym hi) `((,dom ,x)
                                        ,@(and (rationalp lo) `((,lo-rel-sym ,lo ,x)))
                                        ,@(and (rationalp hi) `((,hi-rel-sym ,x  ,hi))))))))
                                            

;(defun range-pred-I (x s) `(acl2::in-tau-intervalp ,x ',(get-tau-int (cadr s) (third s))))
(defun range-pred-I (x s) `(AND . ,(make-acl2-range-constraints x (cadr s) (third s))))

(defun make-enum-body-for-range (r domain tau-interval)
  (b* ((lo (tau-interval-lo tau-interval))
       (hi (tau-interval-hi tau-interval))
       (lo-rel (tau-interval-lo-rel tau-interval))
       (hi-rel (tau-interval-hi-rel tau-interval)))
    (case domain
      (acl2::integer (let ((lo (and lo (if lo-rel (1+ lo) lo))) ;make both inclusive bounds
                           (hi (and hi (if hi-rel (1- hi) hi))))
                       (cond ((and lo hi)
                              `(acl2::nth-integer-between ,r ,lo ,hi))
                             
                             (lo ;hi is positive infinity
                              `(+ ,lo ,r))

                             ((posp hi) ;lo is neg infinity and hi is >=1
                              `(let ((i-ans (acl2::nth-integer ,r)))
                                 (if (> i-ans ,hi)
                                     (mod i-ans (1+ ,hi))
                                   i-ans)));ans shud be less than or equal to hi
                             
                             
                             (t ;lo is neg inf, and hi is <= 0
                              `(- ,hi ,r))))) ;ans shud be less than or equal to hi
      
      (otherwise  (cond ((and lo hi) ;ASSUME inclusive even when you have exclusive bounds
                         `(acl2::nth-rational-between ,r ,lo ,hi))
                        
                        (lo ;hi is positive infinity
                         `(+ ,lo (acl2::nth-positive-rational ,r)))
                        
                        ((> hi 0) ;lo is neg infinity and hi is is >= 1
                         `(let ((rat-ans (acl2::nth-rational ,r)))
                            (if (> rat-ans ,hi)
                                (mod rat-ans (1+ ,hi))
                              rat-ans)));ans shud be less than or equal to hi
                        
                        (t;lo is neg infinity and hi is is <= 0
                         `(- ,hi (acl2::nth-positive-rational ,r))))))))

(defun range-enum-I (i s) (make-enum-body-for-range i (cadr s) (get-tau-int (cadr s) (third s))))
(defun range-enum/acc-I (i s) 
  (declare (ignorable i))
  `(mv-let (i _SEED) (random-natural-seed _SEED)
           (mv ,(range-enum-I 'i s) (the (unsigned-byte 31) _SEED))))

(include-book "defdata-util")
(defun make-defconst-event1 (p top-kwd-alist wrld)
  (declare (ignorable top-kwd-alist wrld))
  (b* (((cons tname A) p)
       ((acl2::assocs ndef) A)
       (nbody ndef))
    (if (and (consp nbody) (eq 'member (car nbody)))
        `((acl2::defconst-fast ,(modify-symbol "*" tname "-VALUES*") ',(cadr nbody)))
      '())))


(defloop member-defconst-event (ps kwd-alist wrld)
  (for ((p in ps)) (append (make-defconst-event1  p kwd-alist wrld))))
  
(add-pre-post-hook defdata-defaults-table :pre-pred-hook-fns '(member-defconst-event))

(table builtin-combinator-table nil
       '((or . ((:aliases . (oneof or anyof))
                (:arity . t)
                (:pred-I . nil) ; no special handling.
                (:pred-inverse-I . nil)
                (:enum-I . nil)
                (:enum/acc-I . nil)))
         
         (member . ((:aliases . (enum member member-eq member-equal in))
                    (:arity . 1)
                    (:pred-I . member-pred-I) 
                    (:pred-inverse-I . nil)
                    (:enum-I . member-enum-I)
                    (:enum/acc-I . member-enum/acc-I)
                    ))

         (range . ((:aliases . (range between))
                   (:arity . 2)
                   (:pred-I . range-pred-I) 
                   (:pred-inverse-I . nil)
                   (:enum-I . range-enum-I)
                   (:enum/acc-I . range-enum/acc-I))))

       :clear)


(set-ignore-ok t)
(defun parse-range-exp1 (rexp)
  (case-match rexp
       ((lo '< '_ '< hi) rexp)
       ((lo '< '_ '<= hi) rexp)
       ((lo '<= '_ '< hi) rexp)
       ((lo '<= '_ '<= hi) rexp)

       ((lo '< '_) `(,lo < _ < nil))
       (('_ '< hi) `(nil < _ < ,hi))
       
       
       ((lo '<= '_) `(,lo <= _ < nil))
       (('_ '<= hi) `(nil < _ <= ,hi))
       (& rexp)))
(set-ignore-ok nil)


;copied from cgen./utilities


(mutual-recursion
;(ev-fncall-w FN ARGS W SAFE-MODE GC-OFF HARD-ERROR-RETURNS-NILP AOK)
;I use sumners default values for
;               nil    ; safe-mode
;               t      ; gc-off
;               nil    ; hard-error-returns-nilp
;               nil    ; aok


(defun my-ev-w (term alist ctx w hard-error-returns-nilp)
"special eval function that does not need state and 
cannot handle if, return-last,mv-list, stobjs, wormhole etc
very restrictive
Mainly to be used for evaluating enum lists "
;Close to ev-rec in translate.lisp
(declare (xargs :mode :program
                :guard (and (acl2::termp term w)
                            (plist-worldp w)
                            (symbol-alistp alist)
                            (booleanp hard-error-returns-nilp))))
 
(b* (((when (acl2::variablep term))
;variable expression
      (let ((v (assoc-eq term alist))) ;bugfix (removed cdr).
;(earlier, if term had a value NIL, we were errorneusly
;crashing!!!
        (if v ;not null 
          (mv nil (cdr v))
          (prog2$
           (er hard ctx "Unbound variable ~x0.~%" term)
           (mv t term)))))
;quoted expression
     ((when (acl2::fquotep term))
      (mv nil (cadr term)))
;if expression
     ((when (eq (car term) 'if))
      (prog2$ 
       (er hard ctx "IF expressions not supported at the moment.~%")
       (mv t term)))
;function expression
     ((mv args-er args)
      (my-ev-w-lst (cdr term) alist ctx
                   w hard-error-returns-nilp))
     ((when args-er)
      (prog2$ 
       (er hard ctx "Eval args failed~%")
       (mv t term)))
     ((when (acl2::flambda-applicationp term))
      (my-ev-w (acl2::lambda-body (car term))
               (acl2::pairlis$ (acl2::lambda-formals (car term)) args)
               ctx w hard-error-returns-nilp)))
    (acl2::ev-fncall-w (car term) args w
                       nil nil t hard-error-returns-nilp nil)))

(defun my-ev-w-lst (term-lst alist 
                             ctx w hard-error-returns-nilp)
"special eval function that does not need state and 
cannot handle return-last,mv-list, stobjs, wormhole etc
very restrictive
Mainly to be used for evaluating enum lists "
;Close to ev-rec-lst in translate.lisp
(declare (xargs :mode :program
                :guard (and (acl2::term-listp term-lst w)
                            (plist-worldp w)
                            (symbol-alistp alist)
                            (booleanp hard-error-returns-nilp))))
(if (endp term-lst)
    (mv nil nil)
  (b* (((mv erp1 car-ans) 
        (my-ev-w (car term-lst) alist 
                 ctx w hard-error-returns-nilp))
       ((when erp1) 
        (prog2$ 
         (er hard ctx "eval ~x0 failed~%" (car term-lst))
         (mv t term-lst)))
       ((mv erp2 cdr-ans) 
        (my-ev-w-lst (cdr term-lst) alist 
                     ctx w hard-error-returns-nilp))
       ((when erp2) 
        (prog2$ 
         (er hard ctx "eval failed~%")
         (mv t term-lst))))
    (mv nil (cons car-ans cdr-ans)))))
)
  

(defun trans-my-ev-w (form ctx w hard-error-returns-nilp)
(declare (xargs :mode :program
                :guard (and (plist-worldp w)
                            (booleanp hard-error-returns-nilp))))

  (mv-let 
   (erp term x) 
   (acl2::translate11 form nil nil nil nil nil
                ctx w (acl2::default-state-vars nil))
   (declare (ignore x))
   (if erp
       (if hard-error-returns-nilp
           (mv erp form)
         (prog2$ 
          (er hard ctx "~x0 could not be translated.~%" form)
          (mv erp form)))
     (my-ev-w term nil ctx w hard-error-returns-nilp))))


(defun parse-range-exp (rexp1 domain ctx wrld)
  (declare (xargs :mode :program))
  (let ((rexp (parse-range-exp1 rexp1)))
  (case-match rexp
    ((lo-sym lo-rel-sym '_ hi-rel-sym hi-sym)
     (b* ((lo-rel (eq lo-rel-sym '<))
          (hi-rel (eq hi-rel-sym '<))
          ((mv erp hi) 
           (trans-my-ev-w hi-sym ctx wrld nil))
          ((when erp)
           (er hard ctx "Evaluating rational expression ~x0 failed!~%" hi-sym))
          ((mv erp lo) 
           (trans-my-ev-w lo-sym ctx wrld nil))
          ((when erp)
           (er hard ctx "Evaluating rational expression ~x0 failed!~%" lo-sym))
          ((unless (and (or (null lo) (if (eq domain 'integer) (integerp lo) (rationalp lo)))
                        (or (null hi) (if (eq domain 'integer) (integerp hi) (rationalp hi)))))
           (er hard ctx "~|Syntax error: lo and hi in range expressions should evaluate to rationals, ~ 
but instead got lo=~x0 and hi=~x1~%" lo hi))
          
          ((mv lo lo-rel) (if (eq domain 'integer)
                              (if (and lo lo-rel)
                                  (mv (+ lo 1) nil)
                                (mv lo nil))
                            (mv lo lo-rel)))
          ((mv hi hi-rel) (if (eq domain 'integer)
                              (if (and hi hi-rel)
                                  (mv (- hi 1) nil)
                                (mv hi nil))
                            (mv hi hi-rel)))
          (lo-rel-sym (if lo-rel '< '<=))
          (hi-rel-sym (if hi-rel '< '<=)))
       
       (list lo lo-rel-sym '_ hi-rel-sym hi)))
    (& (er hard? ctx 
"~| Range exp ~x0 should be of following form: ~
     ~| (lo < _ < hi) or (lo < _ < hi) ~
     ~| <= can also be used in place of < and ~
     ~| one of the bounds can be dropped.~%" rexp1)))))


(defun parse-enum-exp (eexp ctx w)
  (declare (xargs :mode :program))
  (b* (((when (proper-symbolp eexp)) eexp) ;name TODO.Bug -- But what if its not a name! We should catch this error...
       ((mv erp list-val) (trans-my-ev-w eexp ctx w nil))
       ((when erp)
        (er hard ctx "Evaluating list expression ~x0 failed!~%" eexp))
       ((unless (true-listp list-val))
        (er hard ctx "Enum argument ~x0 expected to be a list expression.~%" eexp)))
    (kwote list-val)))
