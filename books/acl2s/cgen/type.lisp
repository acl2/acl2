#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

(in-package "CGEN"
)

(include-book "basis")
(include-book "../defdata/defdata-util")

;;; For use by testing hints
;;; Get the type information from the ACL2 type alist

#!ACL2
(mutual-recursion
 (defun get-type-from-type-set-decoded (ts-decoded)
   ;(declare (xargs :guard (symbolp ts-decoded)))
   (cond   ;primitve types
    ((eq ts-decoded '*TS-ZERO*)                  '('0) )
    ((eq ts-decoded '*TS-POSITIVE-INTEGER*)      '(acl2s::pos) )     ;;; positive integers
    ((eq ts-decoded '*TS-POSITIVE-RATIO*)        '(acl2s::positive-ratio) )     ;;; positive non-integer rationals
    ((eq ts-decoded '*TS-NEGATIVE-INTEGER*)      '(acl2s::neg) ) ;;; negative integers
    ((eq ts-decoded '*TS-NEGATIVE-RATIO*)        '(acl2s::negative-ratio) ) ;;; negative non-integer rationals
    ((eq ts-decoded '*TS-COMPLEX-RATIONAL*)      '(acl2s::complex-rational) );;; complex rationals
    ((eq ts-decoded '*TS-NIL*)                   '('nil) );;; {nil}
    ((eq ts-decoded '*TS-T*)                     '('t) );;; {t}
    ((eq ts-decoded '*TS-NON-T-NON-NIL-SYMBOL*)  '(acl2s::symbol) );;; symbols other than nil, t
    ((eq ts-decoded '*TS-PROPER-CONS*)           '(acl2s::proper-cons) );;; null-terminated non-empty lists
    ((eq ts-decoded '*TS-IMPROPER-CONS*)         '(acl2s::improper-cons) );;; conses that are not proper
    ((eq ts-decoded '*TS-STRING*)                '(acl2s::string) );;; strings
    ((eq ts-decoded '*TS-CHARACTER*)             '(acl2s::character) );;; characters
    
;non-primitive types but defined in ground acl2 theory and base.lisp
    ((eq ts-decoded '*TS-UNKNOWN*)               '(acl2s::all) );should give out error?
    ((eq ts-decoded '*TS-NON-NIL* )              '(acl2s::all-but-nil))
    ((eq ts-decoded '*TS-ACL2-NUMBER*)           '(acl2s::acl2-number) )
    ((eq ts-decoded '*TS-RATIONAL-ACL2-NUMBER*)  '(acl2s::acl2-number) )
    ((eq ts-decoded '*TS-RATIONAL* )             '(acl2s::rational) )
    ((eq ts-decoded '*TS-TRUE-LIST-OR-STRING*)   '(acl2s::true-list acl2s::string)) 
    ((eq ts-decoded '*TS-SYMBOL*   )             '(acl2s::symbol) )
    ((eq ts-decoded '*TS-INTEGER*   )            '(acl2s::integer) )
    ((eq ts-decoded '*TS-NON-POSITIVE-RATIONAL*) '(acl2s::negative-rational '0))
    ((eq ts-decoded '*TS-NON-NEGATIVE-RATIONAL*) '(acl2s::positive-rational '0))
    ((eq ts-decoded '*TS-NEGATIVE-RATIONAL* )    '(acl2s::negative-rational) )
    ((eq ts-decoded '*TS-POSITIVE-RATIONAL* )    '(acl2s::positive-rational) )
    ((eq ts-decoded '*TS-NON-NEGATIVE-INTEGER*)  '(acl2s::nat));(0 pos)) 
    ((eq ts-decoded '*TS-NON-POSITIVE-INTEGER*)  '(acl2s::neg '0)) 
    ((eq ts-decoded '*TS-RATIO*)                 '(acl2s::ratio) )
    ((eq ts-decoded '*TS-CONS*  )                '(acl2s::cons) )
    ((eq ts-decoded '*TS-BOOLEAN*)               '(acl2s::boolean) )
    ((eq ts-decoded '*TS-TRUE-LIST*)             '(acl2s::true-list) )
    
    ((eq ts-decoded '*TS-EMPTY*)                 '(acl2s::empty));is it possible?
    (t  (if (consp ts-decoded)
            (cond 
             ((equal 'TS-UNION (car ts-decoded))
              (get-types-from-type-set-decoded-lst (cdr ts-decoded) nil))
             ((and (equal 'TS-COMPLEMENT (car ts-decoded))
                   (equal (cadr ts-decoded) '*TS-CONS*))
              '(acl2s::atom))
             (t '(acl2s::all)))
          '(acl2s::all)))))
 
(defun get-types-from-type-set-decoded-lst (ts-lst ans)
   (if (endp ts-lst)
     ans
     (get-types-from-type-set-decoded-lst 
      (cdr ts-lst) 
      (append (acl2::get-type-from-type-set-decoded (car ts-lst))
              ans))))
 )


(defun get-type-list-from-type-set (ts)
  (declare (xargs :mode :program
                  :guard (integerp ts)))
  (let ((typ (acl2::get-type-from-type-set-decoded (acl2::decode-type-set ts))))
    (if (proper-consp typ)
      typ
      (list typ))))

(defun get-types-from-type-set-lst (ts-lst)
  (declare (xargs :mode :program 
                  :guard (integer-listp ts-lst)))
  (if (endp ts-lst)
    nil
    (append (get-type-list-from-type-set (car ts-lst))
            (get-types-from-type-set-lst (cdr ts-lst)))))



; for each var in freevars, look into the type-alist
; and build a no-dup vt-al(var-types-alist)
; Note: we can get a list of types which means TS-UNION
(defun get-var-types-from-type-alist (acl2-type-alist freevars ans)
  (declare (xargs :mode :program
                  :guard (and (alistp acl2-type-alist)
                              (symbol-listp freevars))))
  (if (endp freevars)
      ans
    (b* ((var (car freevars))
; CHECK: Can acl2-type-alist have duplicate keys?
         (ts-info (assoc-eq var acl2-type-alist))
         (ts (if (consp ts-info) (cadr ts-info) nil)))
     (if ts
         (let ((types (get-type-list-from-type-set ts)))
          (get-var-types-from-type-alist acl2-type-alist 
                                          (cdr freevars) 
                                          (acons var types ans)))
       (get-var-types-from-type-alist acl2-type-alist 
                                       (cdr freevars) ans)))))

(defun decode-acl2-type-alist (acl2-type-alist freevars)
  (declare (xargs :mode :program
                  :guard (and (alistp acl2-type-alist)
                              (symbol-listp freevars))))
  (if (endp acl2-type-alist)
      '()
    (get-var-types-from-type-alist acl2-type-alist freevars '())))



(set-verify-guards-eagerness 0)

(verify-termination acl2::quote-listp)
(verify-termination acl2::cons-term1)
(verify-termination acl2::cons-term); ASK MATT to make these logic mode
(set-verify-guards-eagerness 1)


(defun make-dumb-type-alist (vars)
  "the default dumb type-alist with all variables associated with TOP i.e acl2s::all"
  (declare (xargs :guard (symbol-listp vars))) ;use proper-symbol-listp
  (pairlis$ vars (make-list (len vars)
                            :initial-element 
                            (list 'ACL2S::ALL))))


(defun get-acl2-type-alist-fn (cl vars ens state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((mv erp type-alist &)
       (acl2::forward-chain cl
                            (acl2::enumerate-elements cl 0)
                            nil ; do not force
                            nil ; do-not-reconsiderp
                            (w state)
                            ens
                            (acl2::match-free-override (w state))
                            state))
;Use forward-chain ACL2 system function to build the context
;This context, gives us the type-alist ACL2 inferred from the
;the current subgoal i.e. cl
       (vt-acl2-alst (if erp ;contradiction
                         (make-dumb-type-alist vars)
                       (decode-acl2-type-alist type-alist vars))))
   vt-acl2-alst))


(defmacro get-acl2-type-alist (cl &optional vars ens)
  `(get-acl2-type-alist-fn ,cl 
                           ,(or vars '(acl2::all-vars1-lst cl '()))
                           ,(or ens '(acl2::ens state))
                           state))





; utility fn to print if verbose flag is true 
(defmacro cw? (verbose-flag &rest rst)
  `(if ,verbose-flag
     (cw ,@rst)
     nil))

(defun collect-tau-alist (triples tau-alist type-alist pot-lst ens wrld)
(declare (xargs :mode :program))

  (if (endp triples)
      tau-alist
    (b* (((mv ?contradictionp ?mbt ?mbf tau-alist ?calist)
          (acl2::tau-assume nil (caddr (car triples))
                            tau-alist type-alist pot-lst
                            ens wrld nil))
         (- (cw? nil "~% *** tau-assume returned ~x0~%~%" tau-alist)))
      (collect-tau-alist (cdr triples)
                         tau-alist type-alist pot-lst ens wrld))))

(defun tau-alist-clause (clause sign ens wrld state)
  (declare (xargs :mode :program :stobjs (state)))
;duplicated from tau-clausep in prove.lisp.
(b* (((mv ?contradictionp type-alist pot-lst)
      (acl2::cheap-type-alist-and-pot-lst clause ens wrld state))
     (triples (acl2::merge-sort-car-<
                (acl2::annotate-clause-with-key-numbers clause
                                                        (len clause)
                                                        0 wrld)))
     (tau-alist (collect-tau-alist triples sign type-alist pot-lst
                                   ens wrld)))
  tau-alist))


;; (defun tau-alist-clauses (clauses sign ens wrld state ans)
;;   (declare (xargs :mode :program :stobjs (state)))
;;   (if (endp clauses)
;;       ans
;;     (tau-alist-clauses (cdr clauses) sign ens wrld state
;;                        (append (tau-alist-clause (car clauses) sign ens wrld state) ans))))
      


(defun all-vals (key alist)
  (declare (xargs :guard (and (symbolp key)
                              (alistp alist))))
  (if (endp alist)
      '()
    (if (eq key (caar alist))
        (cons (cdar alist) (all-vals key (cdr alist)))
      (all-vals key (cdr alist)))))

(defun make-var-taus-alist (vars tau-alist)
  (declare (xargs :guard (and (symbol-listp vars)
                              (alistp tau-alist))))
  (if (endp vars)
      '()
    (b* ((vals (all-vals (car vars) tau-alist)))
      (cons (cons (car vars) vals)
            (make-var-taus-alist (cdr vars) tau-alist)))))

(defun conjoin-tau-interval-lst (taus ans)
; [tau] * interval -> interval
  (declare (xargs :mode :program))
  (if (endp taus)
      ans
    (b* ((tau (car taus))
           (interval (acl2::access acl2::tau tau :interval)))
    (conjoin-tau-interval-lst (cdr taus) 
                              (acl2::conjoin-intervals interval ans)))))
  

(defun tau-interval-alist (var-taus-alist)
;[var . taus] -> [var . interval]
  (declare (xargs :mode :program))
  (if (endp var-taus-alist)
      '()
    (b* (((cons var taus) (car var-taus-alist))
         (interval (conjoin-tau-interval-lst taus nil)) ;nil represents the universal interval 
         )
      (if (null interval) ;universal
          (tau-interval-alist (cdr var-taus-alist))
        (cons (cons var interval)
              (tau-interval-alist (cdr var-taus-alist)))))))



(defun tau-interval-alist-clause-fn (cl vars ens state)
    (declare (xargs :mode :program :stobjs (state)))
    (b* ((wrld (w state))
         (tau-alist (tau-alist-clause cl nil ens wrld state))
         (var-taus-alist (make-var-taus-alist vars tau-alist))
         (tau-interval-alist (tau-interval-alist var-taus-alist)))
      tau-interval-alist))

(defmacro tau-interval-alist-clause (cl &optional vars ens)
  `(tau-interval-alist-clause-fn ,cl 
                                 ,(or vars '(all-vars-lst cl))
                                 ,(or ens '(acl2::ens state))
                                 state))     





(defun possible-defdata-type-p (v)
  (declare (xargs :guard T))
  (or (defdata::possible-constant-value-p v)
      (defdata::proper-symbolp v))) ;defdata type

(defun possible-defdata-type-list-p (vs)
  (declare (xargs :guard T))
  (if (consp vs)
      (and (possible-defdata-type-p (car vs))
           (possible-defdata-type-list-p (cdr vs)))
    T))

;; ;redundant from defdata.lisp
;; (defrec types-info%
;;   (size 
;;    predicate 
;;    enumerator enum-uniform
;;    enumerator-test enum-uniform-test
;;    recursivep derivedp consistentp
;;    type-class defs) NIL)
 


(defmacro   verbose-stats-flag ( vl)
  `(> ,vl 2)) 

(defmacro   debug-flag ( vl)
  `(> ,vl 3))

(def meet (typ1 typ2 vl wrld)
  (decl :sig ((symbol symbol vl plist-worldp) -> symbol)
        :doc "find smaller type in subtype hierarchy/lattice")
  (declare (xargs :verify-guards nil))
  ;; (decl :sig ((possible-defdata-type-p possible-defdata-type-p
;;                plist-world) -> possible-defdata-type-p)
  (b* (((when (or (eq 'ACL2S::EMPTY typ1)
                  (eq 'ACL2S::EMPTY typ2))) 'ACL2S::EMPTY)
       ((when (eq typ2 typ1)) typ2)
       (M (table-alist 'defdata::type-metadata-table wrld))
       ((unless (and (defdata::proper-symbolp typ1)
                     (defdata::proper-symbolp typ2)))
        (prog2$
         (cw? (verbose-stats-flag vl)
              "~|CEgen/Note: ~x0 or ~x1 not a name. ~ Meet returning universal type ALL.~|" typ1 typ2)
         'acl2s::all))
                     
       (typ1-al-entry (assoc-eq typ1 M))
       (typ2-al-entry (assoc-eq typ2 M))
       ((unless (and typ1-al-entry typ2-al-entry))
        (prog2$
         (cw? (verbose-stats-flag vl)
              "~|CEgen/Note: ~x0 or ~x1 not a defdata type. ~ Meet returning universal type ALL.~|" typ1 typ2)
         'acl2s::all))
       ((when (defdata::is-allp-alias typ1 wrld)) typ2)
       ((when (defdata::is-allp-alias typ2 wrld)) typ1)
       (P1 (cdr (assoc-eq :predicate (cdr typ1-al-entry))))
       (P2 (cdr (assoc-eq :predicate (cdr typ2-al-entry))))
     ;  (- (cw? (debug-flag vl) "~|CEgen/Debug/meet --  P1: ~x0   P2: ~x1 .~|" P1 P2))
       ((when (defdata::subtype-p P1 P2 wrld))   typ1)
       ((when (defdata::subtype-p P2 P1 wrld))   typ2)
       ((when (defdata::disjoint-p P2 P1 wrld))  'ACL2S::EMPTY) ;Should we instead define the NULL type??? Modified: so Ans is YES instead of Ans: NO, the way its used now, this is right!

;; ;give preference to custom type Non-registered custom types DEPRECATED <2014-11-01 Sat>
;;        ((when (defdata::is-a-custom-type typ1 wrld)) typ1)
;;        ((when (defdata::is-a-custom-type typ2 wrld)) typ2)

; choose the one that was defined later (earlier in 
; reverse chronological order)
       (all-types (strip-cars (table-alist 'DEFDATA::TYPE-METADATA-TABLE wrld)))
       )
   (if (< (position-eq typ1 all-types) (position-eq typ2 all-types)) 
       typ1 
     typ2)))

(def dumb-type-alist-infer-from-term (term vl wrld  ans.)
  (decl :sig ((pseudo-term-listp fixnum plist-worldp  symbol-alistp) 
              -> symbol-alistp)
        :doc "main aux function to infer type-alist from term")
  (declare (xargs :verify-guards nil))
; ans. is a type alist and has type
; (symbol . (listof possible-defdata-type-p))
  (f* ((add-eq-typ... (t1) (if (acl2::equivalence-relationp R wrld)
                               (put-assoc x (list t1) ans.)
                             ans.)))
    
; Copied from v-cs%-alist-from-term. Keep in sync!
  (case-match term
    
;the following is a rare case (I found it when the conclusion is nil
;and its negation is 'T
    (('quote c) (declare (ignore c))  ans.) ;ignore quoted constant terms 

;TODO possible field variable (i.e f is a getter/selector) Note that
; term cannot have a lambda applicaton/let, so the car of the term is
; always a function symbol if term is a consp.
    ((P (f . &)) (declare (ignore P f))  ans.)

;x has to be an atom below, otherwise, we would have caught that case above.
    (('not x)      (put-assoc x (list ''nil) ans.))
    
    ((P x)   (b* ((tname (defdata::is-type-predicate P wrld))
                  ((unless tname) ans.)
                  (curr-typs-entry (assoc-eq x ans.))
                  ((unless (and curr-typs-entry 
                                (consp (cdr curr-typs-entry))))
; no or invalid entry, though this is not possible, because we call it with
; default type-alist of ((x . ('ACL2S::ALL)) ...)
                   ans.)
                  (curr-typs (cdr curr-typs-entry))
                  (- (cw? (and (verbose-stats-flag vl) 
                               (consp (cdr curr-typs)))
                          "~|CEgen/Warning: Ignoring rest of union types ~x0 ~|" (cdr curr-typs)))
                     
                  (curr-typ (car curr-typs))
                  ((when (defdata::possible-constant-value-p curr-typ)) ans.)
                   
                  (final-typ (meet tname curr-typ vl wrld)))
               (put-assoc x (list final-typ) ans.)))

    ((R (f . &) (g . &)) (declare (ignore R f g)) ans.) ;ignore

;x has to be an atom below, otherwise, we would have caught that case
;above.
    ((R x ('quote c))    (add-eq-typ... (kwote c)))
    ((R ('quote c) x)    (add-eq-typ... (kwote c)))
    ;((R x (f . args))    (add-eq-constraint... (acl2::cons-term f args)))
    ;((R (f . args) x)    (add-eq-constraint... (acl2::cons-term f args)))
    
    ;; has to be a (R t1 t2 ...) or atomic term
    (&                   ans.))))

(def dumb-type-alist-infer-from-terms (H vl wrld  ans.)
  (decl :sig ((pseudo-term-listp fixnum plist-worldp  
                                 symbol-alistp) -> symbol-alistp)
        :doc "aux function for dumb extraction of defdata types from terms in H")
  (declare (xargs :verify-guards nil))
  (if (endp H)
      ans.
    (b* ((term (car H))
         (ans. (dumb-type-alist-infer-from-term term vl wrld  ans.)))
      (dumb-type-alist-infer-from-terms (cdr H) vl wrld ans.))))

(def dumb-type-alist-infer (H vars vl wrld)
  (decl :sig ((pseudo-term-listp proper-symbol-listp fixnum plist-worldp) 
              -> symbol-alistp)
        :doc "dumb infer defdata types from terms in H")
  (declare (xargs :verify-guards nil))
  (dumb-type-alist-infer-from-terms H vl wrld (make-dumb-type-alist vars)))

(defmacro   debug-flag  (vl)
  `(> ,vl 3))


(def meet-type-alist (A1 A2 vl wrld)
  (decl :sig ((symbol-alistp symbol-alistp fixnum plist-world)
              -> (mv erp symbol-alistp))
        :mode :program ;ev-fncall-w
        :doc "take intersection of types in the type alist")
; no duplicate keys. A1's ordering is used, it has to contain all the
; variables that the user wants in his final type-alist
; A1 and A2 and the return value have type
; (listof (cons symbolp (listof possible-defdata-type-p)))
; TODO: if val has more than 1 type, then we treat it as (list 'ACL2S::ALL)

; Usually its called with A1 as the acl2 type alist and A2 as the
; top-level type alist. so it might contain
; variables thats have been dest-elimed away
  (f* ((get-type... (types) (if (and (consp types)
                                     (null (cdr types)))
                                (car types)
                              (prog2$
                               (cw? (verbose-stats-flag vl)
                                    "~|CEGen/Warning: Ignoring rest of union types ~x0 ~|" (cdr types))
                               (car types))))
         (eval-and-get-meet (typ1 typ2) ;(quoted-constant sym)|(sym quoted-constant)
                            (b* (((mv dt st) (if (defdata::proper-symbolp typ1)
                                                 (mv typ1 typ2)
                                               (mv typ2 typ1)))
                                 (M (table-alist 'defdata::type-metadata-table wrld))
                                 (P (defdata::predicate-name dt M))
                                 
                                 ((unless (defdata::plausible-predicate-functionp P wrld)) ;abort before calling ev-fncall on non-function
                                  (prog2$ (cw? (debug-flag vl)
                                               "~|CEGen/Warning:: ~x0: Bad args to eval-and-get-meet: ~x1 ~x2. ~|" ctx typ1 typ2)
                                          (mv t st))) ;prefer singleton type
                                 ;; args to ev-fncall-w is a list of evaluated values.
                                 ((mv erp res) (acl2::ev-fncall-w P (list (if (quotep st) ;possible bug caught, what if st is not quoted!
                                                                              (acl2::unquote st)
                                                                            st)) 
                                                                  wrld nil nil t nil nil))
                                 (- (cw? (and erp (debug-flag vl))
                                         "~|CEgen/Error:: ~x0: while calling ev-fncall-w on ~x1~|" ctx (cons P (list st))))
                                 (- (cw? (and (not erp) (not res) (debug-flag vl))
                                         "~|CEgen/Debug:: ~x0 evaluated to nil~|" (cons P (list st))))
                                 ((when erp)
                                  (mv t st))) ;prefer singleton type
                              (if res (mv nil st) (mv nil 'ACL2S::EMPTY)))))
  (if (endp A1)
      (mv nil '())
    (b* (((cons var types1) (car A1))
         (typ1 (get-type... types1))
         (ctx 'meet-type-alist)
         (types2-entry (assoc-eq var A2))
         (types2 (if types2-entry (cdr types2-entry) '(ACL2S::ALL)))
         (typ2 (get-type... types2))
         ((unless (and (possible-defdata-type-p typ1) 
                       (possible-defdata-type-p typ2)))
          (mv t '()))
         ((mv erp rest) (meet-type-alist (cdr A1) A2 vl wrld ))
         ((when erp) (mv t '())))

      (cond ((and (defdata::proper-symbolp typ1) (defdata::proper-symbolp typ2))
             (mv nil (acons var (list (meet typ1 typ2 vl wrld)) rest)))

            ((and (defdata::possible-constant-value-p typ1)
                  (defdata::possible-constant-value-p typ2)
                  (equal typ1 typ2))
             (mv nil (acons var (list typ1) rest)))

            ((and (defdata::possible-constant-value-p typ1)
                  (defdata::possible-constant-value-p typ2))
             (mv nil (acons var (list 'ACL2S::EMPTY) rest)))

            (t
             (b* (((mv erp ans) (eval-and-get-meet typ1 typ2)))
               (mv erp (acons var (list ans) rest)))))))))
