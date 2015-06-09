#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
Generate enumerator and enum/acc (uniform enumerators) events (for core defdata language)
author: harshrc
file name: enumerators-gen.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "std/util/da-base" :dir :system)
(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "defdata-util")
(include-book "data-structures/utilities" :dir :system)




; Generate Enumerator/acc defun bodies
  
;lets forbid some names to be used in defdata body
(defun forbidden-names-enum () '(_seed _v _i _choice))
(verify-guards forbidden-names-enum)
(defattach forbidden-names forbidden-names-enum)


;; (defmacro split (k i)
;;   `(let ((i1-k (split-nat ,k ,i)))
;;      (mv . ,(pair-prefix 'nth (list-up-lists (make-numlist-from 0 k) 
;;                                        (make-list k :initial-element 'i1-k))))))



; TODO [2014-09-24 Wed] REVISIT LATER
; Give less weight to the first base case. This handles the normal
; case of lists and alists, with giving more weight to for data to be
; more listy as opposed to now giving a nil with 0.5 probability
(defmacro switch (k i)
  `(defdata::weighted-switch-nat ',(cons 1 (make-list (1- k) :initial-element 5)) ,i))


(defmacro make-enum-I... (s x)
  `(make-enum-I ,s ,x kwd-alist M C B wrld))
(defmacro make-enum-Is... (ss xs)
  `(make-enum-Is ,ss ,xs kwd-alist M C B wrld))

(program)
(mutual-recursion
(defun make-enum-I (s i   kwd-alist M C B wrld)
  "Make enumerator interpretation for core defdata exp s.
 where
 i is the name of the current indicial argument (dont confuse with an integer)
 kwd-alist gives some defaults.
 M is type metadata table + some basic info for the clique of types being defined.
 C is the constructor table + some basic info for new constructors.
 B is the builtin combinator table."

  (cond ((possible-constant-value-p s) (if (quotep s) s (list 'QUOTE s))) ;its already quoted, dont quote it furthur.

        ((proper-symbolp s) (if (assoc-eq s M) `(,(get2 s :enumerator M) ,i)  s))

        ((not (true-listp s)) (car s));(make-enum-I (cdr s) i kwd-alist M C B wrld))  ;name decl

        ((assoc-eq (car s) B) ;builtin combinator
         (b* ((enum-I-fn (get2 (car s) :enum-I B))
              (k (len (cdr s)))) ;num args
           (if enum-I-fn
               ;special cases like range, member
               (funcall-w enum-I-fn (list i s) 'make-enum-I wrld)
             (if (eq (car s) 'OR)
;CHECK: It is very important for union constituents to have base cases first!
                 `(MV-LET (_CHOICE ,i)
                          (SWITCH ,k ,i)
                      (CASE _CHOICE
                            . ,(list-up-lists (make-numlist-from 0 k)
                                        (make-enum-Is... (cdr s) (make-list k :initial-element i)))))
               nil)))) ;unsupported -- raise catchable error.

        ((assoc-eq (car s) C) ;constructor
         (b* ((k (len (cdr s)))
              (i1--ik (numbered-vars 'i k))
              (enum-arg-exprs (make-enum-Is... (remove-names-lst (cdr s)) i1--ik))
              (binding (bind-names-vals (cdr s) enum-arg-exprs))
              (?satisfies-exprs (get-all :satisfies kwd-alist))
              (rst (make-enum-Is... (keep-names-lst (cdr s)) i1--ik)))

           `(B* (((list . ,i1--ik) (SPLIT-NAT ,k ,i))) ;TODO: This needlessly splits seeds for constant texps too!!
                    ,(if binding
                         `(B* ,binding (,(car s) . ,rst))
                       `(,(car s) . ,rst)))))
        (t
; possible dependent expr?
         `(,(car s) . ,(make-enum-Is... (cdr s) (make-list (len (cdr s)) :initial-element i))))))
         
(defun make-enum-Is (texps is   kwd-alist M C B wrld)
  (declare (ignorable kwd-alist))
  (if (endp texps)
      '()
    (b* ((car-enum-I (make-enum-I... (car texps) (car is))))
      (and car-enum-I ;abort  gracefully if error
           (cons car-enum-I (make-enum-Is... (cdr texps) (cdr is)))))))
)


(defun mv2-let-seq (bs vals body)
  (if (endp bs)
      body
    (list 'MV-LET 
          (car bs)
          (car vals)
          (mv2-let-seq (cdr bs) (cdr vals) body))))



(defloop bind-mv2-names-enum/acc-calls (texps vals temp-names acc-exp)
  "b* mv binding for each name decl texp -> corresponding val, albeit when not named, take a temp name"
  (for ((texp in texps) (val in vals) (nm in temp-names)) 
       (collect (if (named-defdata-exp-p texp)
                    (list (list 'MV (car texp) acc-exp) val)
                  (list (list 'MV nm acc-exp) val)))))

(mutual-recursion
 (defun has-recursive-reference-p (texp new-names)
   (cond ((possible-constant-value-p texp) nil)
         ((proper-symbolp texp) (member-eq texp new-names))

         ((not (true-listp texp)) (member-equal (cdr texp) new-names))
         (t (has-recursive-reference-lst-p (cdr texp) new-names))))
 (defun has-recursive-reference-lst-p (texps new-names)
   (if (endp texps)
       nil
     (or (has-recursive-reference-p (car texps) new-names)
         (has-recursive-reference-lst-p (cdr texps) new-names))))
 )

(defun bound-seeds-to-recursive-calls (i i1--ik texps new-names)
  (if (endp texps)
      '()
    (b* ((i_current (car i1--ik))
         (texp (car texps)))
      (cons 
       (if (has-recursive-reference-p texp new-names)
           `(if (or (zp ,i_current) (< ,i_current ,i)) ,i_current (1- ,i_current))
         i_current)
       (bound-seeds-to-recursive-calls i (cdr i1--ik) (cdr texps) new-names)))))
          
         
    

(defmacro make-enum/acc-I... (s x)
  `(make-enum/acc-I ,s ,x kwd-alist new-names M C B wrld))
(defmacro make-enum/acc-Is... (ss xs)
  `(make-enum/acc-Is ,ss ,xs kwd-alist new-names M C B wrld))

(mutual-recursion
 (defun make-enum/acc-I (s i kwd-alist new-names M C B wrld)
   (declare (ignorable new-names))
   "enumerator/acc interpretation for core defdata exp s.
i is the name of the current indicial argument (dont confuse with an integer) that is used as recursion measure.
kwd-alist gives some defaults.
new-names is self-explanatory (imp to find recursive references)
M is type metadata table + some basic info for the clique of types being defined.
C is the constructor table + some basic info for new constructors.
B is the builtin combinator table."

   (cond ((possible-constant-value-p s) `(MV ,(if (quotep s) s (list 'QUOTE s)) _SEED))
         ((proper-symbolp s) (if (assoc-eq s M) 
                                `(,(get2 s :enum/acc M) ,i _SEED)
                              `(MV ,s _SEED)))

         ((not (true-listp s)) (car s)) ;(make-enum/acc-I (cdr s) i kwd-alist M C B wrld)) ;name decl   ;TODO.check -- seems wrong!!

         ((assoc-eq (car s) B) ;builtin combinator
          (b* ((enum/acc-I-fn (get2 (car s) :enum/acc-I B))
               (k (len (cdr s)))) ;num args
            (if enum/acc-I-fn
;special cases like range, member
                (funcall-w enum/acc-I-fn (list i s) 'make-enum/acc-I wrld)
              (if (eq (car s) 'OR)
;CHECK: It is very important for union constituents to have base cases first!
                  `(B* (((MV _CHOICE ,i) (SWITCH ,k ,i)))
; 22 Aug 2014
; Shifting to switch instead of random-index-seed, due to poor performance for nth-formula/acc in nnf/simplify test in the regression.
;                           (RANDOM-INDEX-SEED (MIN ,k ,i) _SEED) ;i forces termination
                           (CASE _CHOICE
                                 . ,(append (list-up-lists (make-numlist-from 0 k)
                                                     (make-enum/acc-Is... (cdr s) (make-list k :initial-element i)))
                                            '((OTHERWISE (mv nil _SEED))))))

                nil)))) ;unsupported -- raise catchable error.

         ((assoc-eq (car s) C)
          (b* ((k (len (cdr s)))
               (i1--ik (numbered-vars 'i k))
               (enum/acc-exprs (make-enum/acc-Is... (remove-names-lst (cdr s)) i1--ik))
               (_v1--_vk (numbered-vars '_V k))
               (binding (bind-mv2-names-enum/acc-calls (cdr s) enum/acc-exprs _v1--_vk '_SEED))
               (names (replace-calls-with-names _v1--_vk (cdr s))))
               
            `(B* (((mv (list . ,i1--ik) _SEED) (RANDOM-INDEX-LIST-SEED ,k ,i _SEED))) ;TODO.check later. random-indexes less that i force termination.
                  ;((list . ,i1--ik) (list ,@(bound-seeds-to-recursive-calls i i1--ik (cdr s) new-names))))
                 
                 (B* ,binding (MV (,(car s) . ,names) _SEED)))))
         (t
; possible dependent expr?
          `(,(car s) . ,(make-enum/acc-Is... (cdr s) (make-list (len (cdr s)) :initial-element i))))))
 
 (defun make-enum/acc-Is (texps is kwd-alist new-names M C B wrld)
   (declare (ignorable kwd-alist))
   (if (endp texps)
       '()
     (b* ((car-enum-I (make-enum/acc-I... (car texps) (car is))))
       (and car-enum-I ;abort  gracefully if error
            (cons car-enum-I (make-enum/acc-Is... (cdr texps) (cdr is)))))))
 )



(defun make-enum-declare-forms (ivar kwd-alist)
  (b* ((guard-lambda (get1 :enum-guard kwd-alist)) ;its a lambda
       (actuals (list ivar))
       (?term-method (get1 :termination-method kwd-alist))
       (measure-decl-forms nil)
        ;; (if term-method
        ;;     `((DECLARE (XARGS :CONSIDER-ONLY-CCMS ((nfix ,ivar)))))
        ;;   `((DECLARE (XARGS :MEASURE (nfix ,ivar))))))
       (guard-decl-forms (and guard-lambda `((DECLARE (XARGS :MODE :PROGRAM ;hack
                                                             :GUARD ,(expand-lambda (cons guard-lambda actuals))))))))
    (append measure-decl-forms guard-decl-forms)))
    
(defun make-enum/acc-declare-forms (ivar kwd-alist)
  (b* ((guard-lambda (get1 :enum/acc-guard kwd-alist)) ;its a lambda
       (actuals (list ivar '_SEED)))
    (if guard-lambda
        `((DECLARE (XARGS :MODE :PROGRAM
                          :GUARD ,(expand-lambda (cons guard-lambda actuals)))))
      '())))

(defun enum-event (p top-kwd-alist wrld)
  "make a enumerator defun event."
  (b* (((cons name A) p)
       ((acl2::assocs ndef N new-constructors new-types kwd-alist) A)
       (C (append new-constructors (table-alist 'data-constructor-table wrld)))
       (M (append new-types (table-alist 'type-metadata-table wrld)))
       (B (table-alist 'builtin-combinator-table wrld))
       (kwd-alist (append kwd-alist top-kwd-alist))
       (avoid-lst (append (forbidden-names) (strip-cars N)))
       (ivar (if (member-eq 'i avoid-lst) 'i (acl2::generate-variable 'i avoid-lst nil nil wrld)))
       (enum-body (make-enum-I ndef ivar kwd-alist M C B wrld))
       (enum-decls (make-enum-declare-forms ivar kwd-alist))
       )
    
    `(defun ,(enumerator-name name M) (,ivar)
       ,@enum-decls
       ,enum-body)))

(defloop enum-events (ps kwd-alist wrld)
  (for ((p in ps)) (collect (enum-event p kwd-alist wrld))))

(defun enumerator-events (D kwd-alist wrld)
  (b* ((enum-events (enum-events D kwd-alist wrld))
       (p? (get1 :print-commentary kwd-alist)))
    (if (consp (cdr D)) ;len = 2
        `((commentary ,p? "~| Enumerator events...~%")
          (mutual-recursion ,@enum-events))
      (cons `(commentary ,p? "~| Enumerator events...~%")
            enum-events))))


(defun enum/acc-event (p top-kwd-alist wrld)
  "make a enumerator/acc defun event."
  (b* (((cons name A) p)
       ((acl2::assocs ndef N new-constructors new-types kwd-alist) A)
       (C (append new-constructors (table-alist 'data-constructor-table wrld)))
       (M (append new-types (table-alist 'type-metadata-table wrld)))
       (B (table-alist 'builtin-combinator-table wrld))
       (kwd-alist (append kwd-alist top-kwd-alist))
       (avoid-lst (append (forbidden-names) (strip-cars N)))
       (ivar (if (member-eq 'i avoid-lst) 'i (acl2::generate-variable 'i avoid-lst nil nil wrld)))
       (enum/acc-body (make-enum/acc-I ndef ivar kwd-alist (strip-cars new-types) M C B wrld))
       (enum/acc-decls (make-enum/acc-declare-forms ivar kwd-alist))
       )
    
    `(defun ,(get2 name :enum/acc M) (,ivar _SEED)
       ,@enum/acc-decls
       ,enum/acc-body)))

;meta variable -- ps is pairs, p is pair
(defloop enum/acc-events (ps kwd-alist wrld)
  (for ((p in ps)) (collect (enum/acc-event p kwd-alist wrld))))

(defun enumerator/acc-events (D kwd-alist wrld)
  (b* ((enum/acc-events (enum/acc-events D kwd-alist wrld))
       ;(- (cw? (get1 :print-commentary kwd-alist) "~| Enumerator (uniform) events...~%"))
       )
    (if (consp (cdr D)) ;len = 2
        `((mutual-recursion ,@enum/acc-events))
      enum/acc-events)))


(add-pre-post-hook defdata-defaults-table :cgen-hook-fns '(enumerator-events enumerator/acc-events))
