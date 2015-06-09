#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
builtin combinators (oneof, member, range) in core defdata language
author: harshrc
file name: builtin-combinators.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "std/util/bstar" :dir :system)

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
  (let ((dom (if (eq domain 'acl2s::integer)
                 'acl2::integerp
               'acl2::rationalp)))
  (case-match rexp
    ((lo lo-rel-sym '_ hi-rel-sym hi)
     (b* ((lo-rel (eq lo-rel-sym '<))
          (hi-rel (eq hi-rel-sym '<)))
       (acl2::make-tau-interval dom lo-rel lo hi-rel hi))))))

(defun make-acl2-range-constraints (x domain rexp)
  (let ((dom (if (eq domain 'acl2s::integer)
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
      (acl2s::integer (let ((lo (and lo (if lo-rel (1+ lo) lo))) ;make both inclusive bounds
                           (hi (and hi (if hi-rel (1- hi) hi))))
                       (cond ((and lo hi)
                              `(acl2s::nth-integer-between ,r ,lo ,hi))
                             
                             (lo ;hi is positive infinity
                              `(+ ,lo ,r))

                             ((posp hi) ;lo is neg infinity and hi is >=1
                              `(let ((i-ans (acl2s::nth-integer ,r)))
                                 (if (> i-ans ,hi)
                                     (mod i-ans (1+ ,hi))
                                   i-ans)));ans shud be less than or equal to hi
                             
                             
                             (t ;lo is neg inf, and hi is <= 0
                              `(- ,hi ,r))))) ;ans shud be less than or equal to hi
      
      (otherwise  (cond ((and lo hi) ;ASSUME inclusive even when you have exclusive bounds
                         `(acl2s::nth-rational-between ,r ,lo ,hi))
                        
                        (lo ;hi is positive infinity
                         `(+ ,lo (acl2s::nth-positive-rational ,r)))
                        
                        ((> hi 0) ;lo is neg infinity and hi is is >= 1
                         `(let ((rat-ans (acl2s::nth-rational ,r)))
                            (if (> rat-ans ,hi)
                                (mod rat-ans (1+ ,hi))
                              rat-ans)));ans shud be less than or equal to hi
                        
                        (t;lo is neg infinity and hi is is <= 0
                         `(- ,hi (acl2s::nth-positive-rational ,r))))))))

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
       (nbody ndef)
       (curr-pkg (get1 :current-package top-kwd-alist))
       (name (s+ "*" tname "-VALUES*" :pkg curr-pkg)))
    (if (and (consp nbody) (eq 'acl2s::member (car nbody)))
        `((acl2::defconst-fast ,name ,(cadr nbody)))
      '())))


(defloop member-defconst-event (ps kwd-alist wrld)
  (for ((p in ps)) (append (make-defconst-event1  p kwd-alist wrld))))
  
(add-pre-post-hook defdata-defaults-table :pre-pred-hook-fns '(member-defconst-event))

#!ACL2S
(table defdata::builtin-combinator-table nil
       '((or . ((:aliases . (oneof or anyof acl2::or acl2::oneof acl2::anyof))
                (:arity . t)
                (:pred-I . nil) ; no special handling.
                (:pred-inverse-I . nil)
                (:enum-I . nil)
                (:enum/acc-I . nil)))
         
         (member . ((:aliases . (enum member member-eq member-equal in acl2::enum acl2::in))
                    (:arity . 1)
                    (:pred-I . defdata::member-pred-I) 
                    (:pred-inverse-I . nil)
                    (:enum-I . defdata::member-enum-I)
                    (:enum/acc-I . defdata::member-enum/acc-I)
                    ))

         (range . ((:aliases . (range between acl2::range acl2::between))
                   (:arity . 2)
                   (:pred-I . defdata::range-pred-I) 
                   (:pred-inverse-I . nil)
                   (:enum-I . defdata::range-enum-I)
                   (:enum/acc-I . defdata::range-enum/acc-I))))

       :clear)




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


(defun bad-range-syntax (rexp)
  (er hard? 'parse-range-exp
"~| Range exp ~x0 is not of the following form: ~
     ~| (lo < _ < hi) or (lo < _ < hi)  where ~
     ~| <= can be used as the comparison relation and one of the comparisons can be dropped i.e ~
     ~| (lo <= _), (_ <= hi) etc.~%" rexp))


(set-ignore-ok t)
;TODO BAD idea to rely on symbols for < and <= (ACL2S B::< is different from <
;here -- this caused a bug)
;; (defun preprocess-range-exp (rexp)
;;   (case-match rexp
;;     ((lo '< '_ '< hi) rexp)
;;     ((lo '< '_ '<= hi) rexp)
;;     ((lo '<= '_ '< hi) rexp)
;;     ((lo '<= '_ '<= hi) rexp)

;;     ((lo '< '_) `(,lo < _ < nil))
;;     (('_ '< hi) `(nil < _ < ,hi))
    
    
;;     ((lo '<= '_) `(,lo <= _ < nil))
;;     (('_ '<= hi) `(nil < _ <= ,hi))
;;     (& rexp)))

(defun pp-rel (rel-sym)
  (if (equal (symbol-name rel-sym) "<")
      '<
    '<=))

(defun pp-range-exp (rexp)
  "preprocess range expression"
  (case-match rexp
    ((lo lo-rel '_ hi-rel hi) (list lo (pp-rel lo-rel) '_ (pp-rel hi-rel) hi))
    ((lo lo-rel '_)           (list lo (pp-rel lo-rel) '_ '< nil))
    (('_ hi-rel hi)           (list nil '< '_ (pp-rel hi-rel) hi))
    
    (& (bad-range-syntax rexp))))

(set-ignore-ok nil)

(defun parse-range-exp (rexp1 domain ctx wrld)
  (declare (xargs :mode :program))
  (let ((rexp (pp-range-exp rexp1)))
  (case-match rexp
    ((lo-sym lo-rel-sym '_ hi-rel-sym hi-sym)
     (b* ((lo-rel (not (eq lo-rel-sym '<=)))
          (hi-rel (not (eq hi-rel-sym '<=)))
          ((mv erp hi) 
           (trans-my-ev-w hi-sym ctx wrld nil))
          ((when erp)
           (er hard ctx "Evaluating rational expression ~x0 failed!~%" hi-sym))
          ((mv erp lo) 
           (trans-my-ev-w lo-sym ctx wrld nil))
          ((when erp)
           (er hard ctx "Evaluating rational expression ~x0 failed!~%" lo-sym))
          ((unless (and (or (null lo) (if (eq domain 'acl2s::integer) (integerp lo) (rationalp lo)))
                        (or (null hi) (if (eq domain 'acl2s::integer) (integerp hi) (rationalp hi)))
                        (not (and (null lo) (null hi)))))
           (er hard ctx "~| lo and hi in range expressions should evaluate to rationals, but instead got lo = ~x0 and hi = ~x1~%" lo hi))

          ((mv lo lo-rel) (if (eq domain 'acl2s::integer)
                              (if (and lo lo-rel)
                                  (mv (+ lo 1) nil)
                                (mv lo nil))
                            (mv lo lo-rel)))
          ((mv hi hi-rel) (if (eq domain 'acl2s::integer)
                              (if (and hi hi-rel)
                                  (mv (- hi 1) nil)
                                (mv hi nil))
                            (mv hi hi-rel)))
          
          ((when (and lo hi (eq domain 'acl2s::integer) (> lo hi)))
           (er hard ctx "~| lo <= hi should hold. But it does not: lo = ~x0 and hi = ~x1" lo hi))

          ((when (and lo hi (not lo-rel) (not hi-rel) (= lo hi))) lo)

          ((when (and lo hi (or lo-rel hi-rel) (>= lo hi)))
           (er hard ctx "~| lo < hi should hold. But it does not: lo = ~x0 and hi = ~x1" lo hi))

          (lo-rel-sym (if lo-rel '< '<=))
          (hi-rel-sym (if hi-rel '< '<=)))
       
       (list 'acl2s::range domain (list lo lo-rel-sym '_ hi-rel-sym hi))))
    (& (bad-range-syntax rexp1)))))


(defun parse-enum-exp (eexp ctx w)
  (declare (xargs :mode :program))
  (b* (((when (proper-symbolp eexp)) eexp) ;name TODO.Bug -- But what if its not a name! We should catch this error...
       ((mv erp list-val) (trans-my-ev-w eexp ctx w nil))
       ((when erp)
        (er hard ctx "Evaluating list expression ~x0 failed!~%" eexp))
       ((unless (and (true-listp list-val) (consp list-val)))
        (er hard ctx "Enum argument ~x0 expected to be a non-empty list expression.~%" eexp)))
    (list 'acl2s::member (kwote list-val))))
