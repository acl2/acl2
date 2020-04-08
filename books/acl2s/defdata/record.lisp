#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
record/struct support in core defdata language
author: harshrc
file name: record/struct.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "data-structures/utilities" :dir :system)
(include-book "register-combinator")
(include-book "register-data-constructor")


;; generate Record Pred (RECOG) event



(defun build-dex-mset-call (dex-names dex-var-names)
  (declare (xargs :guard (and (symbol-listp dex-names)
                              (symbol-listp dex-var-names)
                                 )))
                  
  (if (endp dex-names)
    nil
    (let* ((dname (car dex-names))
           (dvar-name (car dex-var-names))
           (d-keyword-name (intern (symbol-name dname) "KEYWORD")))
      `(mset ,d-keyword-name ,dvar-name
          ,(build-dex-mset-call (cdr dex-names) (cdr dex-var-names))))))


(defun build-dex-recordImpl-bindings (dex-names dex-var-names rec-expr)
  (if (endp dex-names)
    nil
    (let* ((dname (car dex-names))
           (dname-var (car dex-var-names))
           (d-keyword-name (intern (symbol-name dname) "KEYWORD")))
      (cons (list dname-var (list 'mget d-keyword-name rec-expr))
            (build-dex-recordImpl-bindings (cdr dex-names) (cdr dex-var-names) rec-expr)))))


;;make a constructor defun and corresponding predicate
(defun make-constructor-predicate (conx-name dex-pairs kwd-alist)
  (declare (ignorable kwd-alist))
  (b* ((dex-orig-names (strip-cars dex-pairs))
       (curr-pkg (get1 :current-package kwd-alist))
       (prefix (get-dest-prefix conx-name))
       (dex-names (modify-symbol-lst prefix dex-orig-names "" curr-pkg)) ;make new prefixed destr names
       (dex-var-names (modify-symbol-lst "VAR-" dex-names "" curr-pkg))
       (dex-preds (strip-cdrs dex-pairs))
       (dex-prex-calls (build-one-param-calls dex-preds dex-var-names))
       (dex-mset-call (build-dex-mset-call dex-orig-names dex-var-names))
       (dex-bindings (build-dex-recordImpl-bindings dex-orig-names dex-var-names 'v))
       (conx-pred (make-predicate-symbol conx-name curr-pkg)))
    `((defund ,conx-pred (v) ;disabled def 
        (declare (xargs :guard t))
        (if (not (acl2::non-empty-good-map v));for guards and termination (CCG)
            nil
          (let ,dex-bindings 
            (and  (equal v (mset :0tag ',conx-name ,dex-mset-call))
                  ,@dex-prex-calls 
                  )))))))

(defloop cons-up-conx-prex-ev (new-constructors kwd-alist)
  (for ((cx in new-constructors)) (append (make-constructor-predicate (car cx) (get1 :field-pred-alist (cdr cx)) kwd-alist))))

(defun conx-pred-events--recur/non-recur (recp p top-kwd-alist wrld)

  (b* (((cons ?name A) p)
       ((acl2::assocs new-constructors new-types kwd-alist) A)

       (M (append new-types (table-alist 'type-metadata-table wrld)))
       (AT (table-alist 'type-alias-table wrld))
       (kwd-alist (append kwd-alist top-kwd-alist))

; recursive conx pred
       (new-preds (predicate-names (strip-cars new-types) AT M))
       (conx-recursive-alst (find-recursive-records new-preds new-constructors))
       (conx-non-recur-alst (set-difference-eq new-constructors conx-recursive-alst))
       )
    (if recp 
        (cons-up-conx-prex-ev conx-recursive-alst kwd-alist)
      (cons-up-conx-prex-ev conx-non-recur-alst kwd-alist))))


(defloop conx-non-recur-pred-events (ps kwd-alist wrld)
  (for ((p in ps)) (append (conx-pred-events--recur/non-recur nil p kwd-alist wrld))))

(defloop conx-recur-pred-events (ps kwd-alist wrld)
  (for ((p in ps)) (append (conx-pred-events--recur/non-recur t p kwd-alist wrld))))





;; RECORD CONX DEX BSTAR REG EVENTS
; copied from defdata

;make the event for defining constructor
(defun make-constructor (conx-name dex-pairs kwd-alist)
  (declare (ignorable kwd-alist))
  (b* ((dex-orig-names (strip-cars dex-pairs))
       (curr-pkg (get1 :current-package kwd-alist))
       (prefix (get-dest-prefix conx-name))
       (dex-names (modify-symbol-lst prefix dex-orig-names "" curr-pkg))
       (dex-var-names (modify-symbol-lst "VAR-" dex-names "" curr-pkg))
       (dex-prex (strip-cdrs dex-pairs))
       (dex-prex-calls (build-one-param-calls dex-prex dex-var-names))
       (dex-mset-call (build-dex-mset-call dex-orig-names dex-var-names)))
    `((defun ,conx-name ,dex-var-names
        (declare (xargs :guard (and . ,dex-prex-calls)))
        (mset :0tag ',conx-name ,dex-mset-call)))))

;cons up events that define destructor functions
(defun cons-up-dex-defuns (conx-pred selector-fn-names dex-names)
  (declare ;(ignore conx-pred)
           (xargs :guard (and (symbol-listp selector-fn-names)
                              (symbol-listp dex-names)
                              (equal conx-pred conx-pred))))
  (if (endp dex-names)
    nil
    (let* ((sel-fn-name (car selector-fn-names))
           (dname (car dex-names))
           (d-keyword-name (intern (symbol-name dname) "KEYWORD")))
    (cons `(defun ,sel-fn-name (v)
             (declare (xargs :guard (,conx-pred v))) ;not working with new record impl
                             ;:verify-guards nil))
             (mget ,d-keyword-name v))
          (cons-up-dex-defuns conx-pred
                              (cdr selector-fn-names)
                              (cdr dex-names))))))
      
(defun destructor-function-names (conx-name dex-pairs kwd-alist)
  (declare (ignorable kwd-alist))
  (let* ((dex-names (strip-cars dex-pairs))
         (curr-pkg (get1 :current-package kwd-alist))
         (prefix (get-dest-prefix conx-name)))
    (modify-symbol-lst prefix dex-names "" curr-pkg)))
  
(defun make-destructors (conx-name dex-pairs kwd-alist)
  (let* ((dex-names (strip-cars dex-pairs))
         (selector-fn-names (destructor-function-names conx-name dex-pairs kwd-alist))
         (curr-pkg (get1 :current-package kwd-alist))
         (conx-pred (make-predicate-symbol conx-name curr-pkg)))
    (cons-up-dex-defuns conx-pred selector-fn-names dex-names)))

(defun cons-up-mod-defuns (conx-pred modifier-fn-names dex-names)
  (declare ;(ignore conx-pred)
           (xargs :guard (and (symbol-listp modifier-fn-names)
                              (symbol-listp dex-names)
                              (equal conx-pred conx-pred))))
  (if (endp dex-names)
    nil
    (let* ((mod-fn-name (car modifier-fn-names))
           (dname (car dex-names))
           (d-keyword-name (intern (symbol-name dname) "KEYWORD")))
    (cons `(defun ,mod-fn-name (new v)
             (declare (xargs :guard (,conx-pred v))) ;not working with new record impl
                             ;:verify-guards nil))
             (mset ,d-keyword-name new v))
          (cons-up-mod-defuns conx-pred
                              (cdr modifier-fn-names)
                              (cdr dex-names))))))

(defun modifier-function-names (conx-name dex-pairs kwd-alist)
  (declare (ignorable kwd-alist))
  (let* ((dex-names (strip-cars dex-pairs))
         (curr-pkg (get1 :current-package kwd-alist))
         (prefix (get-modifier-prefix conx-name)))
    (modify-symbol-lst prefix dex-names "" curr-pkg)))
  


(defun make-modifiers (conx-name dex-pairs kwd-alist)
  (let* ((dex-names (strip-cars dex-pairs))
         (modifier-fn-names (modifier-function-names conx-name dex-pairs kwd-alist))
         (curr-pkg (get1 :current-package kwd-alist))
         (conx-pred (make-predicate-symbol conx-name curr-pkg)))
    (cons-up-mod-defuns conx-pred modifier-fn-names dex-names)))



(defun conx/dex/mod/record-events1 (cx kwd-alist)
  (b* (((cons conx-name conx-al) cx)
       (dest-pred-alist (get1 :dest-pred-alist conx-al))
       (field-pred-alist (get1 :field-pred-alist conx-al))
       (theory-name (get1 :theory-name kwd-alist))
       (pkg (get1 :current-package kwd-alist))

       (dest-defs-ruleset-name
        (s+ theory-name "DEST-DEFS" :separator "/" :pkg pkg))
       )
       
    (append
     `((local (in-theory (enable ,(get1 :recog conx-al)))))
     (make-constructor conx-name field-pred-alist kwd-alist)
     (make-destructors conx-name field-pred-alist kwd-alist)
     
     (make-modifiers conx-name field-pred-alist kwd-alist)
     ;; `((acl2::def-ruleset! ,(s+ theory-name "ALL-DEFS" :separator "/")
     ;;                       ',(append (list conx-name)
     ;;                               (destructor-function-names field-pred-alist kwd-alist)
     ;;                               (modifier-fn-names field-pred-alist kwd-alist))))
     `((acl2::def-ruleset!
        ,dest-defs-ruleset-name
        ',(destructor-function-names conx-name field-pred-alist kwd-alist)))
     
     `((acl2::def-patbind-macro ,conx-name ,(strip-cars dest-pred-alist))))))
   

(defloop conx/dex/mod/record-events (new-constructors kwd-alist)
  (for ((cx in new-constructors)) (append (conx/dex/mod/record-events1 cx kwd-alist))))

(defun new-conx/record-events1 (p top-kwd-alist)
  (b* (((cons ?name A) p)
       ((acl2::assocs new-constructors kwd-alist) A)
       (kwd-alist (append kwd-alist top-kwd-alist)))
    (conx/dex/mod/record-events new-constructors kwd-alist)))

(defloop new-conx/record-events0 (ps kwd-alist wrld)
  (declare (ignorable wrld))
  (for ((p in ps)) (append (new-conx/record-events1 p kwd-alist))))


(defun new-conx/record-events (ps kwd-alist wrld)
  (b* ((events (new-conx/record-events0 ps kwd-alist wrld)))
    (and (consp events)
         (append
          `((commentary ,(get1 :print-commentary kwd-alist) "~| Record constructor/destructor/modifier events...~%"))
          events))))


;register record constructor event is separate for ordering reasons (we submit it after the theory events)

(defun register-conx-ev (conx-name dex-pairs kwd-alist) 
  (let* ((dex-orig-names (strip-cars dex-pairs))
         (curr-pkg (get1 :current-package kwd-alist))
         (prefix (get-dest-prefix conx-name))
         (conx-pred (make-predicate-symbol conx-name curr-pkg))
         (dex-names (modify-symbol-lst prefix dex-orig-names "" curr-pkg));make new prefixed destr names
         (dex-prex (strip-cdrs dex-pairs)))

    `((register-data-constructor ,(list conx-pred conx-name) 
                                 ,(list-up-lists dex-prex dex-names)
                                 :recordp t
                                 :rule-classes (:rewrite)
                                 :verbose ,(get1 :verbose kwd-alist)
                                 :hints (("Goal" :in-theory (e/d (,conx-pred) 
                                                                 (acl2::mset-diff-mset 
                                                                  ,@(remove-duplicates dex-prex)))))))))

(defloop reg-record-conx-events (new-constructors kwd-alist)
  (for ((cx in new-constructors)) (append (register-conx-ev (car cx) (get1 :field-pred-alist (cdr cx)) kwd-alist))))

(defun register-record-conx-events1 (p top-kwd-alist)
  (b* (((cons ?name A) p)
       ((acl2::assocs new-constructors kwd-alist) A)
       (kwd-alist (append kwd-alist top-kwd-alist)))
    (reg-record-conx-events new-constructors kwd-alist)))

(defloop register-record-conx-events (ps kwd-alist wrld)
  (declare (ignorable wrld))
  (for ((p in ps)) (append (register-record-conx-events1 p kwd-alist))))



(defmacro curr-pkg-s+ (&rest args)
  `(s+ ,@args :separator "-" :pkg curr-pkg))

(defun record-local-theory-events (pred conx fnames disabled-runes curr-pkg)
  (b* ((dex-calls (apply-mget-to-x-lst fnames '())))
    
    `((defthm ,(curr-pkg-s+ pred 'tag-bridge-lemma1)
        (implies (,pred x)
                 (equal (EQUAL x (,conx  ,@dex-calls))
                        t))
        :hints (("Goal" :in-theory (e/d (,pred) (,@disabled-runes))))
        :rule-classes nil)
      
      (defthm ,(curr-pkg-s+ pred 'tag-bridge-lemma2)
        (implies (EQUAL x (,conx ,@fnames));AA-KEY  AA-LEVEL AA-LEFT AA-RIGHT))
                 (mget :0tag x))
        :hints (("Goal" :in-theory (e/d (,pred) (,@disabled-runes))))
        :rule-classes nil)
      
      (defthm ,(curr-pkg-s+ pred 'tag-is-non-empty)
        (implies (,pred x)
                 (mget :0tag x))
        :hints (("goal" :in-theory (e/d (,pred) (,@disabled-runes))
                 :use ((:instance ,(curr-pkg-s+ pred 'tag-bridge-lemma1))
                       (:instance ,(curr-pkg-s+ pred 'tag-bridge-lemma2)))))
        :rule-classes (:forward-chaining))
      
       (defthm ,(curr-pkg-s+ pred 'def-crux)
         (implies (,pred x)
                  (equal x  (,conx  ,@dex-calls)))
         :hints (("Goal" :in-theory (e/d (,pred) (,@disabled-runes))))
         :rule-classes nil)
      )))
    

(defun record-predicate-theory-events (pred conx disabled-runes curr-pkg)
  `((defthm ,(curr-pkg-s+ pred 'unique-tag)
      (implies (,pred x)
               (equal (mget :0tag x) ',conx))
        :hints (("goal" :expand ((,pred x))
                        :in-theory (e/d () (,@disabled-runes))))
        :rule-classes (;(:rewrite :backchain-limit-lst 1)
                       :forward-chaining :type-prescription))

      (defthm ,(curr-pkg-s+ pred 'implies-consp)
        (implies (,pred x)
                 (consp x))
        :rule-classes (;(:rewrite :backchain-limit-lst 1)
                       :forward-chaining :compound-recognizer))

      (defthm ,(curr-pkg-s+ pred 'implies-good-map)
        (implies (,pred x)
                 (acl2::good-map x))
        :hints (("goal" :in-theory (e/d (,pred))))
        :rule-classes (;(:rewrite :backchain-limit-lst 1) 
                       (:forward-chaining)))
      
      (defthm ,(curr-pkg-s+ pred 'excludes-atom-list)
        (implies (,pred x)
                 (not (atom-listp x)))
        :hints (("goal" :in-theory (e/d (,pred acl2::good-map) (,@disabled-runes))))
        :rule-classes (:tau-system))
      ))

(defun record-per-field-selector-theory-events (fname dpred pred disabled-runes curr-pkg)
  (b* ((kname (keywordify fname)))
    `((defthm ,(curr-pkg-s+ pred  fname 'selector)
        (implies (,pred x)
                 (,dpred (mget ,kname x)))
        :hints (("Goal" :in-theory (e/d (,pred) (,@disabled-runes))))
        :rule-classes (:rewrite 
                       (:forward-chaining
                        :trigger-terms ((mget ,kname x))))))))
   
(defun record-per-field-modifier-theory-events (fname dpred pred disabled-runes curr-pkg) 
  (b* ((kname (keywordify fname)))
    `((defthm ,(curr-pkg-s+ pred fname 'modifier)
        (implies (and (,pred x)
                      (,dpred v))
                 (,pred (mset ,kname v x)))
        :hints (("Goal" :use ((:instance ,(curr-pkg-s+ pred 'tag-is-non-empty)))
                 :expand (,pred (mset ,kname v x))
                 :in-theory (e/d (acl2::mset-diff-entry-non-empty-good-map-is-non-nil
                                  acl2::mset-diff-entry-non-empty-good-map-is-consp) 
                                 (,pred 
                                  ,(curr-pkg-s+ pred 'unique-tag)
                                  (:executable-counterpart acl2::mset)
                                  ,@disabled-runes)))
                (and acl2::stable-under-simplificationp
                     '(:use ((:instance ,(curr-pkg-s+ pred 'def-crux))))))
        :rule-classes (:rewrite 
                       (:forward-chaining
                        :trigger-terms ((mset ,kname v x))))))))


(defun  record-per-field-inverse-def-theory-events (conx-name fname pred disabled-runes kwd-alist)
   (declare (ignorable kwd-alist))
  (b* ((kname (keywordify fname))
       (curr-pkg (get1 :current-package kwd-alist))
       (sel-name (s+ (get-dest-prefix conx-name) fname :separator "" :pkg curr-pkg)))
    `((defthm ,(curr-pkg-s+ pred  fname 'inverse-def)
        (implies (,pred x) ;earlier it was unconditional, but this leads to erroneous/unwanted dest-elim applications
;         (syntaxp (atom x))  ;this doesnt work for nested dest-elim in one elim process
         (equal (mget ,kname x) (,sel-name x)))
        :hints (("Goal" :in-theory (e/d () (,@disabled-runes) (,sel-name))))))))

(defloop collect-inverse-def-theory-events (conx fnames pred disabled-runes kwd-alist)
  (for ((fname in fnames)) 
       (append (record-per-field-inverse-def-theory-events conx fname pred disabled-runes kwd-alist))))
  

(defun collect-per-field-record-events (fnames dprex pred disabled-runes curr-pkg flag)
  (if (endp fnames)
      '()
    (b* ((fname (car fnames))
         (dpred (car dprex)))
      (append (case flag
                (:sel (record-per-field-selector-theory-events fname dpred pred disabled-runes curr-pkg))
                (:mod (record-per-field-modifier-theory-events fname dpred pred disabled-runes curr-pkg))
                (t '()))
      (collect-per-field-record-events (cdr fnames) (cdr dprex) pred disabled-runes curr-pkg flag)))))
         
;This is already produced by register-data-constructor event, so why bother here.
;; (defun record-constructor-events (nm conx tpred dprex fnames disabled)
;;   `((defthm ,nm ;TODO: of no use if cname is not disabled!
;;      (implies (and ,@(build-one-param-calls dprex fnames))
;;               (,tpred (,conx . ,fnames)))
;;      :hints (("Goal" :in-theory (e/d (,tpred ,conx) (,@disabled acl2::mset-diff-mset)))))))



(defun record-theory-events-builtin (name field-pred-alist new-types kwd-alist wrld)
  (b* ((M (append new-types (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (curr-pkg (get1 :current-package kwd-alist))
       (pred (or (predicate-name name A M)
                 (make-predicate-symbol name curr-pkg))) ;TODO -- Inconsistent across rest of u combinators
       ((when (not (proper-symbolp pred))) (er hard? 'record-theory-events "~| Couldnt find predicate name for ~x0.~%" name))


       (conx name)
       (dprex (strip-cdrs field-pred-alist))
       (fnames (strip-cars field-pred-alist))

       (disabled (get1 :disabled kwd-alist))
;program mode function commented out (runes-to-be-disabled dprex wrld)
       (disabled-runes (union-eq disabled dprex))
       ;(time-trackp (get1 :time-track kwd-alist))
      
       
;       (constructor-defthms (record-constructor-events (s+ pred "CONSTRUCTOR") conx pred dprex fnames disabled-runes))
       (record-pred-defthms (record-predicate-theory-events pred conx disabled-runes curr-pkg))
       (sel-defthms (collect-per-field-record-events fnames dprex pred disabled-runes curr-pkg :sel))
       (mod-defthms (collect-per-field-record-events fnames dprex pred disabled-runes curr-pkg :mod))
       
       (inverse-def-rules (collect-inverse-def-theory-events conx fnames pred disabled-runes kwd-alist))
       
       (export-thm-events (append ;constructor-defthms
                                  record-pred-defthms
                                  sel-defthms
                                  mod-defthms))
                                  
       (all-defthm-names (get-event-names export-thm-events))
       (theory-name (get1 :theory-name kwd-alist))
       (inv-ruleset-name
        (s+ theory-name "INVERSE-DEST-DEF-RULES" :separator "/" :pkg curr-pkg))
       )
;   in
    `(;,@(and time-trackp `((value-triple (prog2$ (time-tracker :record-theory-events :start) :invisible))))
      (local (progn . ,(record-local-theory-events pred conx fnames disabled-runes curr-pkg)))
      ,@export-thm-events
      ;; ,@(and time-trackp `((value-triple (progn$ 
      ;;                                     (time-tracker :record-theory-events :print?)
      ;;                                     (time-tracker :record-theory-events :stop)
      ;;                                     :invisible))))
      (acl2::def-ruleset! ,theory-name ',all-defthm-names)

      ,@inverse-def-rules
      (acl2::def-ruleset! ,inv-ruleset-name ',(get-event-names inverse-def-rules))
      (in-theory (acl2::disable* ,inv-ruleset-name))
      )))

(defun record-theory-events-builtin-gv (name field-pred-alist new-types kwd-alist wrld)
  (declare (xargs :guard t))
  (ec-call (record-theory-events-builtin name field-pred-alist new-types kwd-alist wrld)))
   
(defstub record-theory-events (* * * * *) => *)
(defattach record-theory-events record-theory-events-builtin-gv)


(defloop record-theory-ev-lst (new-constructors new-types kwd-alist wrld)
  (for ((cx in new-constructors)) 
       (append (record-theory-events (car cx) (get1 :field-pred-alist (cdr cx)) new-types kwd-alist wrld))))

(defun user-record-theory-ev1 (p top-kwd-alist wrld)
  (b* (((cons name A) p)
       ((acl2::assocs pdef new-constructors new-types kwd-alist) A) ;what about pdef?
       (kwd-alist (append kwd-alist top-kwd-alist)))
       
    (case-match pdef
      (('RECORD . fname-tname-alist) (b* ((tnames (strip-cdrs fname-tname-alist))
                                          ;(- (assert$ (proper-symbol-listp tnames) nil))
                                          (dprex (predicate-names tnames))
                                          (field-pred-alist (pairlis$ (strip-cars fname-tname-alist) dprex)))
                                       (record-theory-events name field-pred-alist new-types kwd-alist wrld)))
      (& (if new-constructors
             (record-theory-ev-lst new-constructors new-types kwd-alist wrld)
           '())))))
             

(defloop user-record-theory-ev (ps kwd-alist wrld)
  (for ((p in ps)) (append (user-record-theory-ev1 p kwd-alist wrld))))

(defun user-record-theory-events (ps kwd-alist wrld)
  (b* ((events (user-record-theory-ev ps kwd-alist wrld)))
    (and (consp events)
         (append
          `((commentary ,(get1 :print-commentary kwd-alist) "~| Record theory events...~%")
            ;; (value-triple
            ;;  (progn$
            ;;   (time-tracker :record-theory-events :end)
            ;;   (time-tracker :record-theory-events :init
            ;;                 :times '(2 7)
            ;;                 :interval 5
            ;;                 :msg "Elapsed runtime in theory events for records is ~st secs;~|~%")
            ;;   :invisible))
            )
          events))))

(deflabel record)
(register-user-combinator record
                          :arity t :verbose t
                          :expansion (lambda (_name _s) (cons _name _s))
                          :syntax-restriction-fn nil ; taken care of by respective parse fun
                          :aliases (struct acl2::struct acl2::record)
                          ;; :local-theory-template *record-local-theory-template*
                          ;; :theory-template *record-theory-template*
                          :pre-pred-hook-fns (conx-non-recur-pred-events)
                          :in-pred-hook-fns (conx-recur-pred-events)
                          ;; order matters
                          :post-pred-hook-fns (new-conx/record-events user-record-theory-events register-record-conx-events)
                          )




; RECORD DEST-ELIM support (Ideas influenced by Pete and Sol)
; We will maintain a set of rules which do the foll inverse transformation:
; (mget :dex-name x) ==> (dex-name x)

; For each record, we will add such rules to
; record-inverse-dest-def-rules ruleset which will be disabled by
; default.

; We will arrange this ruleset to be enabled at
; Stable-under-Simplification, at which point, the destructor
; definitions also disabled, dest-elim will take its proper course.

(defun listify (x)
  (declare (xargs :guard t))
  (if (true-listp x) x (list x)))

(defun add-assoc (key vals al); &key (setp 't) to-front)
  (declare (xargs :guard (and (true-listp vals)
                              (eqlable-alistp al))))
  "union vals onto the back of existing entry of key in al. "
;macro:  if to-front is t then add to front, if unionp is t, then use union-equal insteada.
  (put-assoc key (union-equal (listify (get1 key al)) vals) al))

;Note: Here clearly, accumulator-style definition is simpler and more intuitive to write.
(mutual-recursion
(defun collect-mget-var->field-names (e A.)
  "collect (mget :field1 x) terms in e into alist A. mapping x to (:field1 ...)"
  (declare (xargs :verify-guards nil
                  :guard (pseudo-termp e)))
  (cond ((acl2::variablep e) A.)
        ((acl2::fquotep e) A.)
        (t (if (and (eq 'acl2::mget (acl2::ffn-symb e))
                    (= (len e) 3)
                    (= 2 (len (second e)));otherwise fquotep doesnt typecheck.
                    (acl2::fquotep (second e))
                    (keywordp (acl2::unquote (second e)))
                    (acl2::variablep (third e)))
               (add-assoc (third e) (list (acl2::unquote (second e))) A.)
             (collect-mget-var->field-names-lst  (acl2::fargs e) A.)))))

(defun collect-mget-var->field-names-lst (es A.)
  (declare (xargs :guard (pseudo-term-listp es)))
  (if (endp es)
      A.
    (collect-mget-var->field-names-lst (cdr es) 
                                       (collect-mget-var->field-names (car es) A.))))
    
)


;TODO check: proper-symbol-listp is looping (rewrites)
(mutual-recursion
(defun predicate-mapping-for-vars-in-term (e vars A.)
  "return x -> (P1 ...) alist where (P1 x) occurs in e"
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-listp vars)
                              (pseudo-termp e))))
  (cond ((acl2::variablep e) A.)
        ((acl2::fquotep e) A.)
        (t (if (and (= (len e) 2)
                    (acl2::variablep (second e))
                    (member (second e) vars))
               (add-assoc (second e) (list (first e)) A.)
             (predicate-mapping-for-vars-in-terms  (acl2::fargs e) vars A.)))))

(defun predicate-mapping-for-vars-in-terms (es vars A.)
  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-term-listp es))))
  (if (endp es)
      A.
    (predicate-mapping-for-vars-in-terms (cdr es) vars 
                                         (predicate-mapping-for-vars-in-term (car es) vars A.))))

)

; Note 20 Aug 2014 (dest elim complaint)
; Due to the dest-elim heuristic, I need to lay out the entire nested record
; structure for the dest-elim process to complete the nested elim of a clause.
; So for in addition to the record type name, I need to also return all its
; constituent record type names.

(defmacro deffilter (nm arglst filter-fn) ;the first arg is the one to recur on
  `(defloop ,nm (,@arglst)
     (for ((x in ,(car arglst))) (append (and (,filter-fn x) (list x))))))

(deffilter filter-top-level-types (tnames kind wrld) 
  (lambda (x) 
    (b* ((pdef (get2 x :prettyified-def (table-alist 'type-metadata-table wrld))))
      (and (consp pdef)
           (eq kind (car pdef))))))

(program)

;The following function without acc is tricky to get right.
(mutual-recursion
 (defun constituent-types-closure1 (tname wrld ans.)
   (b* ((md (get1 tname (table-alist 'type-metadata-table wrld)))
        (ndef (get1 :normalized-def md))
        (cnames (texp-constituent-types ndef (get1 :clique md) wrld))
        (cnames (remove-duplicates cnames)))
     
     (constituent-types-closure-lst cnames wrld (union-eq cnames ans.))))

 (defun constituent-types-closure-lst (tnames wrld ans.)
   (if (endp tnames)
       ans.
     (constituent-types-closure-lst (cdr tnames) wrld (union-eq ans. (constituent-types-closure1 (car tnames) wrld  ans.)))))
 )

(defun constituent-types-closure (tname wrld)
  "return closure of all constituent types including itself"
  (constituent-types-closure1 tname wrld (list tname)))

(defun nested-eliminable-types (tname wrld)
  (filter-top-level-types (constituent-types-closure tname wrld) 'record wrld))
  



;TODO check if node of tree satisfies this:
(defun find-record-name3 (P fields wrld)
  (b* ((tname (type-name P wrld))
       ((when (null tname)) '())
       (md (get1 tname (table-alist 'type-metadata-table wrld)))
       (pdef (get1 :prettyified-def md))

       ;; (- (cw? t "~| P: ~x0   pdef: ~x1 ~%" P pdef))
       )
    ;;in
    (and (consp pdef)
         (eq 'record (car pdef))
         (subsetp-equal (symbol-names fields) (symbol-names (strip-cars (cdr pdef)))) ;BUGFIX: args were not eqlable-listp
         (nested-eliminable-types tname wrld))))
       

(defloop find-record-name2 (Ps fields wrld)
  (for ((P in Ps)) (append (find-record-name3 P fields wrld))))

(defloop find-record-name1 (xs fields{} Ps{} wrld)
  (for ((x in xs)) (append (find-record-name2 (get1 x Ps{}) (get1 x fields{}) wrld))))

(defun find-record-names (fields{} Ps{} wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-alistp fields{})
                              (symbol-alistp Ps{})
                              (acl2::plist-worldp wrld))))
  (remove-duplicates-equal (find-record-name1 (strip-cars fields{}) fields{} Ps{} wrld)))


;; (defloop get-all-lst (key Ds) ;D is a dictionary/alist
;;   (for ((D in Ds)) (append (get-all key D))))

;; (defmacro deffilter (nm arglst mfilter-fn) ;the first arg is the one to recur on
;;   `(defloop ,nm (,arglst)
;;      (for ((x in ,(car arglst))) (append (and (,filter-fn x ,@(cdr arglst)) (list x))))))

;; (deffilter filter-keywords (xs) keywordp)
;; (deffilter filter-variables (xs) proper-symbolp)

;; (deffilter filter-by-key-in-vals (xs key in-vals) (lambda (x key in-vals) (member (get1 key x) in-vals)))

;; More detail.
;; The forementioned record dest-elim support is implemented as an override-hint.

;; First we find (mget :field x) like terms.
;; We then find all Predicate expressions on x.
;; We then find the corresponding (record) types and inverse-dest-def rulesets to enable.
;; ACHTUNG: What if multiple rulesets get enabled? And even worse, what if they overlap?

(defloop inverse-dest-rulesets (tnames wrld)
  (for ((tname in tnames))
       (collect (s+ (get2 tname :theory-name
                          (table-alist 'type-metadata-table wrld))
                    "INVERSE-DEST-DEF-RULES" :separator "/"))))

(defloop dest-defs-rulesets (tnames wrld)
  (for ((tname in tnames)) 
       (collect (s+ (get2 tname :theory-name
                          (table-alist 'type-metadata-table wrld))
                    "DEST-DEFS" :separator "/"))))

(defun record-dest-elim-support-fn
    (stable-under-simplificationp clause keyword-alist world)
  (b* ((var->fnames (collect-mget-var->field-names-lst clause '()))
       (var->Ps (predicate-mapping-for-vars-in-terms clause (strip-cars var->fnames) '()))
       (record-names (find-record-names var->fnames var->Ps world))

       (enabled (inverse-dest-rulesets record-names world))
       (disabled (union-equal
                  record-names
                  (dest-defs-rulesets record-names world)))
;HACK: Lets disable constructors too ASSUMING record name and constructor name match)
       ;; (- (cw? record-names "~| record-names: ~x0    enabled: ~x1   disabled: ~x2~%" record-names enabled disabled))
       )
    (if (and stable-under-simplificationp (consp record-names))
        (list* ':in-theory `(acl2::e/d* ()
                                        (,@disabled)
                                        (,@enabled)) ; acl2::map-elim-rule)) [2015-08-29 Sat] Too cumbersomely done by ACL2's dest elim
               keyword-alist)
      keyword-alist)))


(logic)
; NOTE: It is unfortunate that record-dest-elim-support-fn is program-mode. It
; does not have the protection of logic mode where there is less likelihood of
; running into Lisp Abort errors.
(defmacro record-dest-elim-support ()
  `(record-dest-elim-support-fn acl2::stable-under-simplificationp acl2::clause acl2::keyword-alist acl2::world))

(defmacro enable-record-dest-elim ()
  `(progn (acl2::remove-override-hints! '((record-dest-elim-support)))
          (acl2::add-override-hints! '((record-dest-elim-support)))))

(enable-record-dest-elim)
