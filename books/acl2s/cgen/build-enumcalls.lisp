#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t);$ACL2s-Preamble$|#


(in-package "CGEN")

;Useful Macros for concise/convenient code.
(include-book "basis")
(include-book "utilities")
(include-book "type")

;;;======================================================================
;;;============ Build enumerator expression code =================e=======
;;;======================================================================



(defrec enum-info% (size category expr expr2) NIL)
(defun enum-info%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (('enum-info% size category expr expr2) 

     (and (fixnump size)
          (member-eq category
                     '(:singleton :function :defconst :numeric-range :empty))
          (pseudo-termp expr)
          (pseudo-termp expr2)))))





(verify-termination acl2::empty-tau-intervalp )
(verify-termination acl2::singleton-tau-intervalp)

(defun singleton-tau-intervalp (interval)
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
    (and (acl2::access acl2::tau-interval interval :domain) ;int,rat,num
         (acl2::singleton-tau-intervalp lo-rel lo hi-rel hi))))

(defun non-empty-non-universal-interval-p (interval)
  (and interval
       (acl2::tau-intervalp interval)
       (acl2::access acl2::tau-interval interval :domain) ;either int,rat,num
       (or (rationalp (acl2::access acl2::tau-interval interval :lo)) ;one of bounds should be a number
           (rationalp (acl2::access acl2::tau-interval interval :hi)))
       (b* ((lo (acl2::access acl2::tau-interval interval :lo))
            (hi (acl2::access acl2::tau-interval interval :hi))
            (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
            (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
         (and (not (acl2::empty-tau-intervalp lo-rel lo hi-rel hi))
              (not (acl2::singleton-tau-intervalp lo-rel lo hi-rel hi))))))
          

(defun abs/complex (c)
  (declare (xargs :guard (complex/complex-rationalp c)))
  (complex (abs (realpart c)) (abs (imagpart c))))
  
(defun abs/acl2-number (x)
    (declare (xargs :guard (acl2-numberp x)))
  (if (complex/complex-rationalp x)
      (abs/complex x)
    (abs x)))


(defun mod/complex (c m)
  (declare (xargs :guard (and (rationalp m)
                              (> m 0)
                              (complex/complex-rationalp c))))
  (complex (mod (realpart c) m) (imagpart c)))
  
(defun mod/acl2-number (x m)
    (declare (xargs :guard (and (acl2-numberp x)
                                (rationalp m)
                                (> m 0)
                                )))
  (if (complex/complex-rationalp x)
      (mod/complex x m)
    (mod x m)))

; NOTE: The following function returns code snippets and hence cannot be type
; checked until runtime. Such functionality is extremely difficult to find
; trivial mistakes that could have been easily caught had we compiled these
; snippets.

(def make-range-enum-info% (type interval M)
  (decl :sig ((symbolp non-empty-non-universal-interval-p symbol-alist) -> enum-info%-p)
        :doc "given tau-interval interval construct an enum-info% rec with appropriate enum calls")
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
       
  (case type
    (acl2s::integer (let ((lo (and lo (if lo-rel (1+ lo) lo))) ;make both inclusive bounds
                         (hi (and hi (if hi-rel (1- hi) hi))))
                     (cond ((and lo hi)
                            (acl2::make enum-info% 
                                        :size 't ;(- hi lo)
                                        :category :numeric-range 
                                        :expr `(acl2s::nth-integer-between r ,lo ,hi)
                                        :expr2 `(defdata::random-integer-between-seed ,lo ,hi seed.)))
                           (lo ;hi is positive infinity
                            (acl2::make enum-info% 
                                        :size 't
                                        :category :numeric-range 
                                        :expr `(+ ,lo (acl2s::nth-nat-testing r))
                                        :expr2 `(mv-let (r seed.)
                                                        (defdata::random-small-natural-seed seed.)
                                                        (mv (+ ,lo r) seed.))))
                           
                           ((posp hi) ;lo is neg infinity and hi is >=1
                            (acl2::make enum-info% 
                                        :size 't
                                        :category :numeric-range 
                                        :expr `(let ((i-ans (acl2s::nth-integer r)))
                                                 (if (> i-ans ,hi)
                                                     (mod i-ans (1+ ,hi))
                                                   i-ans));ans shud be less than or equal to hi
                                                        
                                        :expr2 `(mv-let (i-ans seed.)
                                                        (defdata::random-integer-seed seed.)
                                                        (mv (if (> i-ans ,hi) 
                                                                (mod i-ans (1+ ,hi)) 
                                                              i-ans) 
                                                            seed.))))
                           (t ;lo is neg inf, and hi is <= 0
                            (acl2::make enum-info% 
                                        :size 't
                                        :category :numeric-range 
                                        :expr `(- ,hi (acl2s::nth-nat-testing r)) ;ans shud be less than or equal to hi
                                        :expr2 `(mv-let (r seed.)
                                                        (defdata::random-small-natural-seed seed.)
                                                        (mv (- ,hi r) seed.)))))))
    (otherwise  (cond ((and lo hi) ;ASSUME inclusive even when you have exclusive bounds -- rational, complex-rational, acl2-number
                            (acl2::make enum-info% 
                                        :size 't ;(- hi lo)
                                        :category :numeric-range 
                                        :expr `(acl2s::nth-number-between r ,lo ,hi :type ',type)
                                        :expr2 `(defdata::random-number-between-seed ,lo ,hi seed. :type ',type)))
                         (lo ;hi is positive infinity
                          (acl2::make enum-info% 
                                      :size 't
                                      :category :numeric-range 
                                      :expr `(+ ,lo (abs/acl2-number (,(defdata::enumerator-name type M) r)))
                                      :expr2 `(mv-let (r seed.)
                                                      (defdata::random-small-natural-seed seed.)
                                                      (mv-let (num seed.) ;TODO perhaps we should prefer test/acc over enum/acc
                                                              (,(defdata::enum/acc-name type M) r seed.)
                                                              (mv (+ ,lo (abs/acl2-number num)) seed.)))))
                         
                         ((> hi 0) ;lo is neg infinity and hi is is >= 1
                          (acl2::make enum-info% 
                                        :size 't
                                        :category :numeric-range 
                                        :expr `(let ((rat-ans (,(defdata::enumerator-name type M) r)))
                                                 (if (> rat-ans ,hi)
                                                     (mod/acl2-number rat-ans (1+ ,hi))
                                                   rat-ans));ans shud be less than or equal to hi
                                                        
                                        :expr2 `(mv-let (r seed.)
                                                        (defdata::random-small-natural-seed seed.)
                                                        (mv-let (rat-ans seed.) 
                                                                (,(defdata::enum/acc-name type M) r seed.)
                                                                (mv (if (> rat-ans ,hi)
                                                                        (mod/acl2-number rat-ans (1+ ,hi))
                                                                      rat-ans)
                                                                    seed.)))))


                         (t;lo is neg infinity and hi is is <= 0
                          (acl2::make enum-info% 
                                      :size 't
                                      :category :numeric-range 
                                      :expr `(- ,hi (abs/acl2-number (,(defdata::enumerator-name type M) r)))
                                      :expr2 `(mv-let (r seed.)
                                                      (defdata::random-small-natural-seed seed.)
                                                      (mv-let (ans seed.)
                                                              (,(defdata::enum/acc-name type M) r seed.)
                                                              (mv (- ,hi ans) seed.))))))))))
                   
                          
                         
  
              

(def get-enum-info% (type range vl wrld)
  (decl :sig ((possible-defdata-type-p tau-interval fixnum plist-world)
              -> enum-info%-p)

;TODO: union types
        :doc "to fill")
  (declare (xargs :verify-guards nil))
; returns a well-formed enum-info defrec object
; r is the free variable in the enum-expression which
; is the place-holder for the random-seed or BE arg 
  (if (defdata::possible-constant-value-p type)
      (acl2::make enum-info% :size 1 :category :singleton :expr type :expr2 `(mv ',type seed.)) 
;ALSO HANDLE SINGLETON TYPES DIRECTLY
    
    (let ((entry (assoc-eq type (table-alist 'defdata::type-metadata-table wrld))))
     
    (if entry ;if we find enum-info from type-info-table then use it
        (b* ((al (cdr entry))
             (TI.test-enumerator (cdr (assoc-eq :enum/test al)))
             (TI.test-enumerator/acc (cdr (assoc-eq :enum/test/acc al)))
             (TI.enumerator      (cdr (assoc-eq :enumerator al)))
             (TI.enum-uniform    (cdr (assoc-eq :enum/acc al)))
             (TI.size            (cdr (assoc-eq :size al)))
             (TI.pred            (cdr (assoc-eq :predicate al)))
             ((unless (or (eq 't TI.size)
                         (posp TI.size)))
              (prog2$
               (cw? (normal-output-flag vl)
                    "~|CEgen/Error: size in type-info ~x0 should be posp.~%" (cdr entry))
               (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil)))
             
; 15 July '13 added support for integer and rational ranges
; (acl2-numberp ranges reduce to rational ranges) custom types dont
; take ranges in hyps into account, since they are explicitly given by
; user, the user is burdened with the resposibility of taking them
; into account manually. In any case even defined defdata types play
; well only for integers and rationals, but then you cannot define an
; interesting numeric type, like 4divp, primep, arithmetic
; progression, etc. But you can use / constructor to define some
; interesting types, so I need to think about how to make this more general!! TODO
             ((when (and (defdata::subtype-p TI.pred 'integerp wrld)
                         (non-empty-non-universal-interval-p range)))
              (make-range-enum-info% 'acl2s::integer range (list entry)))

             ((when (and (defdata::subtype-p TI.pred 'acl2-numberp wrld)
                         (non-empty-non-universal-interval-p range)))
              (make-range-enum-info% type range (list entry))))
                                             
              
             ;first check for test-enum
         (if TI.test-enumerator
             (cond 
              ((defdata::allows-arity TI.test-enumerator 1 wrld)
;TODO. I am not checking if test enumerator is to be used or not
               (acl2::make enum-info% :size 't
                           :category :function
                           :expr (list TI.test-enumerator 'r)
                           :expr2 (list TI.test-enumerator/acc 'm 'seed.)))
              (t (prog2$
                  (cw? (normal-output-flag vl)
                       "~|CEgen/Error: ~x0 should be an enum function of arity 1.~%" TI.test-enumerator)
                  (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil))))

;common scenario: inf enumerator
           (if (eq 't TI.size);inf or custom registered (assume)
               (acl2::make enum-info% :size 't :category :function
                           :expr (list TI.enumerator 'r)
                           :expr2 (list TI.enum-uniform 'm 'seed.));inf or some enum fn
             (let ((stored-defconst 
                    (acl2-getprop TI.enumerator 'acl2::const wrld)))
              
              (if stored-defconst ;some finite set of values
                  (b* ((values (second stored-defconst))
                       (len-v (len values))
                       ((unless (posp len-v))
                        (prog2$
                         (cw? (normal-output-flag vl)
                              "~|CEgen/Error: stored-defconst ~x0 has 0 values~%" stored-defconst)
                         (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil))))
                   (acl2::make enum-info%
                               :size len-v 
                               :category (if (= len-v 1) 
                                             :singleton
                                           :defconst)
                               :expr (if (= len-v 1)  
                                         `',(car values)
                                       `(nth (mod r ,len-v) ,TI.enumerator))
                               :expr2 (if (= len-v 1)  
                                         `(mv ',(car values) seed.) ;todo check random-natural
                                       `(mv (nth (mod seed. ,len-v) ,TI.enumerator) seed.))))
;uncommon scenario, finite enumerator function        
                (if (defdata::allows-arity TI.enumerator 1 wrld) 
                    (acl2::make enum-info% :size TI.size 
                                :category :function
                                :expr (list TI.enumerator 'r)
                                :expr2 (list TI.enum-uniform 'm 'seed.));some enum fn
                  
                  (prog2$
                     (cw? (normal-output-flag vl)
                          "~|CEgen/Error: ~x0 is neither one of constant, an enum function or a values defconst.~%" TI.enumerator)
                     (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil))))))))

      ;;;o.w (possibly) custom 
      (let* ((vsym (modify-symbol "*" type "-VALUES*"))
             (values (second (acl2-getprop vsym 'acl2::const wrld))))
                    
        (if values
            (let ((len-v (len values)))
               (acl2::make enum-info%
                        :size len-v 
                        :category (if (= len-v 1) 
                                      :singleton
                                    :defconst)
                        :expr (if (= len-v 1)  
                                  `',(car values) 
                                `(nth (mod r ,len-v) ,vsym))
                        :expr2 (if (= len-v 1)  
                                  `(mv ',(car values) seed.);see todo above 
                                `(mv (nth (mod seed. ,len-v) ,vsym) seed.))))
          (let ((esym (modify-symbol "NTH-" type "")))
                
            ;;check if enum is defined in wrld
            (cond ((defdata::allows-arity esym 1 wrld) 
                   (acl2::make enum-info% 
                             :size t 
                             :category :function
                             :expr `(,esym r)
                             :expr2 `(mv-let (r seed.)
                                             (defdata::random-natural-seed seed.)
                                             (mv (,esym r) seed.))))
                  (t 
                   (prog2$
                     (cw? (normal-output-flag vl)
                          "~|CEgen/Error: ~x0 doesnt appear to be a type.~%" type)
                     (acl2::make enum-info% :size 0 :category :empty :expr nil :expr2 nil)))))))))))



;May 8 2011 OBSOLETE
;testing history data structure
;; Maps variables to vtest-history 
;; vtest-history: 
;; (record (n . current test-run-number)
;;         (rec-size . last recursion size chosen for this variable)
;;         (strategy . :random :bounded)
;;         (enum-expr . enumerator expression with holes)
;;         (enum-arg-alist . special alist to fill in the above holes)
;;         (i . determines X_i to be incremented in BE testing))
;; enum-arg-alist:
;; ((defdata::X  . (record (size . t | fin-size) (val . last val of X) ) ...)



#|
    (c nil ;dep-info record
       :hyps hyps-new 
       :concl concl-new 
       :hyp-vars hyp-vars
       :concl-vars concl-vars
       :vars vars
       :var-type-expr-alist new-var-te-alist
       :var-dependency-adj-list dgraph
       :var->ccnum var-quotient-alst
       :connected-vertices-ordered-list connected-vs-lst)
       ))
|#


(defun symbol-unsigned-29bits-alistp (v)
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (consp (car v))
         (symbolp (caar v))
         (unsigned-29bits-p (cdar v))
         (symbol-unsigned-29bits-alistp (cdr v)))))

(defthm symbol-unsigned-29bits-alistp-forwards-to-symbol-alistp
  (implies (symbol-unsigned-29bits-alistp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining)

; (random-natural-seed seed.) => (mv random-nat new-seed)
#||
function to compute next BE seed tuple
Precondition: BE. is a consp, i.e at least one free variable
Here is the simple scheme:
((x 0) (y 0) (z 0)) -> 
((y 0) (z 0) (x 1)) -> 
((z 0) (x 1) (z 1)) -> 
((x 0) (y 0) (z 0)) -> 
((x 0) (y 0) (z 0)) ->
((x 0) (y 0) (z 0)) ->
((x 0) (y 0) (z 0)) 

The above algo is O(n) in num of free vars. but simple to implement.
Arrays or a stobj can make this constant time operation.  

Alternative algo: Traverse the enumeration tree in BFS order.  Hvent
thought about how to implement it.
||#

;;; (symbol-unsigned-29bits-alistp) -> symbol-unsigned-29bits-alistp)
;; update 29th April '12
;; let cut the optimization to get guards to verify
(defun |next BE args| (BE.)
  "naive bounded exhaustive enumeration."
  (declare (xargs :guard (and (true-listp BE.)
                              (consp BE.)
                              (symbol-alistp BE.))))
                          
  (b* (((cons v ;; (the (unsigned-byte 29)
                  m) (car BE.))
       (;; (the (unsigned-byte 29) 
        m~ (;; acl2::|1+F|
            1+  (nfix m))))
   (append (cdr BE.) (list (cons v m~)))))
            
     
;(defconst *recursive-uniform-enum-measure* 8)
       

(def make-next-sigma_mv-let (var-enumcalls-alist body)
  (decl :sig ((symbol-alistp all) -> all)
        :doc "helper function to make-next-sigma")
  (f* ((_mv-value (v exp exp2) 
          `(case sampling-method 
             (:uniform-random (b* (((mv ?m seed.) 
                                    (defdata::random-natural-seed seed.))
; 22 Aug 2014 -- The measure generated was too small for nth-formula/acc in simplify/nnf example to give good testdata.
;                                   (defdata::random-index-seed *recursive-uniform-enum-measure* seed.))
                                   ((mv val seed.) ,exp2))
                        (mv seed. BE. val)))
             (:random 
              (b* (((mv ?r seed.) (defdata::random-natural-seed seed.)))
                (mv seed. BE. ,exp)))
             ;; bugfix - It is possible that r is not in exp
             ;; this is the case when exp is a eq-constraint
             (:be (b* ((?r (cdr (assoc-eq ',v BE.))))
                   (mv seed. (|next BE args| BE.) ,exp)))
             (otherwise (mv seed. BE. '0)))))
                           
  (if (endp var-enumcalls-alist)
      body
    (b* (((cons var ecalls) (first var-enumcalls-alist)))
;    in 
     `(mv-let (seed. BE. ,var)
              ,(_mv-value var (first ecalls) (second ecalls))
            ,(make-next-sigma_mv-let (rest var-enumcalls-alist) body))))))

(def make-guard-var-member-eq (vars alst)
  (decl :sig ((symbol-alistp symbol) -> all)
        :doc "helper function to make-next-sigma")
  (if (endp vars)
      nil
    (cons `(member-eq ',(car vars) ,alst)
          (make-guard-var-member-eq (cdr vars) alst))))
  
(def cs%-enumcalls (cs% vl wrld computed-vars)
  (decl :sig ((cs%-p fixnump plist-worldp  symbol-listp) 
              -> (mv fixnum (cons pseudo-termp pseudo-termp)))
        :doc "for each cs% record we translate it into the a (mv
  size (list enumcall enumcall2)), where the enumcall is an expression
  that when evaluated gives a value (with random distribution) of
  correct type/constraint and size is the size of the type i.e the set
  of value satisfied by the constraint. enumcall2 is a similar
  expression but with the random seed accumulated/threaded
  uniformly. Return value of (mv 0 nil) stands for an error and is
  recognized by the caller function as such.")
  (declare (xargs :verify-guards nil))
;;; TODO: optimize/complete here using extra information in
;;; spilled-types and additional-constraints
  (case-match cs%
;('cs% defdata-type spilled-types eq-constraint interval additional-constraints)
    (('cs% defdata-type & 'defdata::empty-eq-constraint range 'defdata::empty-mem-constraint &)
; ACHTUNG: cs% defrec exposed
     (b* ((enum-info% (get-enum-info% defdata-type range vl wrld )))
      (mv (access enum-info% size) (list (access enum-info% expr)
                                         (access enum-info% expr2)))))

; if we see a equality constraint, we give preference to it over a
; defdata type, but only if the variables in the eq-constraint are
; already computed i.e already have an enumcall in the final answer
    (('cs% defdata-type & eq-constraint range 'defdata::empty-mem-constraint &)
     (b* ((eq-vs (all-vars eq-constraint))
          (remaining (set-difference-eq eq-vs computed-vars)))
      (if remaining
          (b* ((enum-info% (get-enum-info% defdata-type range vl wrld)))
           (mv (access enum-info% size) (list (access enum-info% expr)
                                              (access enum-info% expr2))))
        (mv 1 (list eq-constraint (list 'mv eq-constraint 'seed.))))))
    
    (('cs% defdata-type & 'defdata::empty-eq-constraint range mem-constraint &)
     (b* ((mem-vs (all-vars mem-constraint))
          (remaining (set-difference-eq mem-vs computed-vars))
          (enum-info% (get-enum-info% defdata-type range vl wrld)))
      (if remaining
          (mv (access enum-info% size) (list (access enum-info% expr)
                                              (access enum-info% expr2)))
        (mv :mem (list `(let ((len-v (len ,mem-constraint)))
                          (if (zp len-v)
                              ,(access enum-info% expr)
                            (nth (mod r len-v) ,mem-constraint)))
                       `(let ((len-v (len ,mem-constraint)))
                          (if (zp len-v)
                              ,(access enum-info% expr2)
                            (mv (nth (mod seed. len-v) ,mem-constraint) seed.))))))))
  
    (& (prog2$ 
        (cw? (normal-output-flag vl) "~|CEgen/Error: BAD record cs% passed to cs%-enumcalls")
        (mv 0 NIL)))))
               
     
(def make-enumerator-calls-alist (v-cs%-alst vl wrld  ans.)
  (decl :sig ((symbol-cs%-alist fixnum plist-world  symbol-alist) 
              -> (mv erp symbol-alist))
        :doc 
        "given an alist mapping variables to cs% records (in dependency order),
  we walk down the alist, translating each type constraint to the corresponding
enumerator call expression")
  (declare (xargs :verify-guards nil))
  (if (endp v-cs%-alst)
      (mv nil (reverse ans.)) ;dont change the original dependency order
    (b* (((cons x cs%) (car v-cs%-alst))
         ((mv size calls) (cs%-enumcalls cs% vl wrld  (strip-cars ans.)))

; simple bug July 9 2013: below comparison, replaced int= with equal,
; this could have been caught by type-checking/guard-verif
         ((when (equal size 0)) (mv t '()))) 
;    in
     (make-enumerator-calls-alist (cdr v-cs%-alst) vl wrld
                                 ;; add in reverse order
                                 (cons (cons x calls) ans.)))))
    
(defun displayed-range (interval)
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel)))
    (cond ((and lo hi)
           `(,lo ,(if lo-rel '< '<=) 'acl2::_  ,(if hi-rel '< '<=) ,hi))
          (lo
           `(,(if lo-rel '> '>=) ,lo))
          (t `(,(if hi-rel '< '<=) ,hi)))))


; DUPLICATION
(def displayed-defdata-type/eq-constraint (cs% computed-vars)
  (decl :sig ((cs%-p symbol-listp) 
              -> (mv fixnum pseudo-termp))
        :doc "for each cs% record we translate it to defdata-type or 
equality constraint that will be used for enumeration. it shadows cs%-enumcall")
  (case-match cs%
;('cs% defdata-type spilled-types eq-constraint range additional-constraints)
    (('cs% defdata-type & 'defdata::empty-eq-constraint range 'defdata::empty-mem-constraint &) 
; ACHTUNG: cs% defrec exposed
     (if (non-empty-non-universal-interval-p range)
         (list :type defdata-type :range (displayed-range range))
       defdata-type))
    (('cs% defdata-type & eq-constraint range 'defdata::empty-mem-constraint &)
     (b* ((eq-vs (all-vars eq-constraint))
          (remaining (set-difference-eq eq-vs computed-vars)))
      (if remaining
          (if (non-empty-non-universal-interval-p range)
              (list :type defdata-type :range (displayed-range range))
            defdata-type)
        eq-constraint)))
    (('cs% defdata-type & 'defdata::empty-eq-constraint range mem-constraint &)
     (b* ((mem-vs (all-vars mem-constraint))
          (remaining (set-difference-eq mem-vs computed-vars)))
      (if remaining
          (if (non-empty-non-universal-interval-p range)
              (list :type defdata-type :range (displayed-range range))
            defdata-type)
        (list :enum mem-constraint))))
    (& 'bad-type)))

(def displayed-enum-alist (v-cs%-alst ans.)
  (decl :sig ((symbol-cs%-alist symbol-alist) 
              -> symbol-alist)
        :doc 
        "given an alist mapping variables to cs% records (in dependency order),
  we walk down the alist, translating each type constraint to the corresponding
enumerator type/expr to be displayed in verbose mode")
  (if (endp v-cs%-alst)
      (reverse ans.) ;dont change the original dependency order
    (b* (((cons x cs%) (car v-cs%-alst))
         (type (displayed-defdata-type/eq-constraint cs% (strip-cars ans.))))
     
     (displayed-enum-alist (cdr v-cs%-alst)
                           ;; add in reverse order
                           (cons (cons x type) ans.)))))



