#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

(in-package "CGEN")

(include-book "std/util/bstar" :dir :system)
(include-book "acl2s/utilities" :dir :system)

;;;;naming convention (only for readability):
;;;;  function: end with $ for each stobj updating/creating function
;;;;            end with % for each defrec updating/creating function
;;;;            end with . for each update, action-object naming with each
;;;;                argument (except stobjs) thats updated ending with a dot
;;;;            end with -p for bool-returning fns (except defdata type pred which end in p)
;;;;            use object-property/attribute naming convention for Read-only
;;;;  variable: end with $ is a stobj.
;;;;            end with % is a defrec.
;;;;            i,j,k are integers or naturals
;;;;            m,n,idx,ctr are naturals or pos
;;;;            f,g,h are functions
;;;;            e,x,y,z,s,t are elements of lists/sets
;;;;            L,X,Y,Z,xs,ys,zs,S,T are lists/sets
;;;;            P,Q,R is a alist (pairs alist)
;;;;            A,B,C are doublet-lists (2 element lists)
;;;;            G is a graph adj list
;;;;            D,H is a dictionary/hashtable
;;;;            K is keyword value list
;;;;            suffix A_1 indicates A1 is the first argument
;;;;            A~ is sometimes used to denote a modified A, but
;;;;              sometimes I use A1, A2, ideally I would like to use
;;;;              A', A'', to denote such things, but Sedan doesnt
;;;;              like this syntax, I shud check CLTL

;;;; Discipline/Style:
;;;;    1. return signatures: * > (mv fixnum *) > (mv * *) > (mv erp * state)
;;;;       > (mv erp * state stobj_1 stobj_2 stobj_3 ...)
;;;;       and so on where stobj_i were introduced in chronological order
;;;;    2. integers are always fixnumed if possible
;;;;    3. guards carry atleast type information and are stored
;;;;    4. return types also stored for each function.
;;;;    5. try to provide (declare (type ...)) automatically
;;;;    6. if state appears, then wrld shud be the name of the arg
;;;;    preceding it and shud be the current-acl2-world at the point
;;;;    of call.
;;;;    7. Use defattach to hide a decision and provide flexibility
;;;;  X 8. Use defattach to hide implementation and versions, this way
;;;;       I can release a new version of ACL2s without requiring a new
;;;;       ACL2 build, which will be required once these books are moved
;;;;       to acl2-books repository.
;;;;    9. Maintain a table with signatures of each function
;;;;       introduced and if possible of those ACL2 functions (primitives)
;;;;       used by the introduced functions.
;;;;    10. Use list comprehension syntax and function arguments " as "
;;;;        syntax using || trick.
;;;;    11. Use nested helper functions with f* syntax (note that f*
;;;;        is not a macro).
;;;;    12. Use anonymous functions only inside list comprehensions and
;;;;        all maps and filters are to be used only via LC syntax.
;;;;    13. All the above fancy stuff is to be done within the def
;;;;        macro, dont modify b* which can be nested. Thus we are
;;;;        assured of the top-level variable-free scope in which we
;;;;        apply our synatx customization.

;;;;debug/print,trace,stats/log

;; NOTE: [2015-02-04 Wed] Using names that are english words, makes fgrep
;; harder. Either make fgrep more intelligent, or use non-english-dict
;; names. Function names are fine since we can grep using "(fun-name ". The
;; important point to be kept at the back of the mind is that sometimes we need
;; to write our programs in a way that nicely supports our tools.



;========================Function Metadata table <=======================
; This table stores metadata about the functions introduced using def in
; our testing framework. We will also populate the data for each ACL2
; function the framework uses. This table stores properties of the
; introduced functions just like world, so perhaps this too will be folded
; into the acl2 world. The following defrec will explain these properties.

; input-arg-types is a list of types (monadic predicates). Ideally,
; they will be found in defdata::types-table.
; output-arg-type is either a type or a list of types starting with mv
(defrec type-sig% (input-arg-types . output-arg-type) T)

(defun type-sig%-p (v)
  (declare (xargs :guard T))
  (case-match v
    ((input-arg-typs . output-arg-type) (and (symbol-listp input-arg-typs)
                                             (or (symbolp output-arg-type)
                                                 ;; or mv type
                                                 (and (consp output-arg-type)
                                                      (eq 'mv (car output-arg-type))
                                                      (symbol-listp output-arg-type)))))))

(defrec def-metadata%
  (actual-name  ;name of currently attached  actual defun
                ; of type: symbolp (UNUSED)
   call-name    ;subtitute key (visible name) with this name
                ; when calling this function (UNUSED)
                ; of type: symbolp
   ;mult         ;multiplicity i.e. number of arguments of the actual defun
   type-sig     ;type signature of the actual function
                ; of type: (type-sigp x)
   mode         ;of type: (in :program :logic)
   inline?      ;of type: Boolean
   trace
;;; nil  -> this function wont be traced
;;; t    -> this function will be traced on system-debug flag
;;; spec -> see trace$ for form of spec, fun will be traced on system-debug
;;;
   )
  T);unTAGGED defrec

(defun def-metadata%-p (v)
  (declare (xargs :guard T))
  (case-match v
    ((an cn tsig m inline? trace)  (and (symbolp an)
                                        (symbolp cn)
                                        (type-sig%-p tsig)
                                        (member-eq m '(:program :logic))
                                        (booleanp inline?)
;TODO - extend to trace specs
                                        (booleanp trace)))))





; A table storing properties associated with a def (key)
; Keys are the visible names of the def functions
; Values are of shape def-metadata record defined above
; The table is populated at compile time, i.e at the time when def events
; are submitted to acl2. Once all def events have been submitted, this
; table is read-only.
(table def-metadata-table nil nil :guard (and (symbolp acl2::key)
                                              (def-metadata%-p acl2::val)))

;========================Function Metadata table >=======================


(defmacro def  (&rest def)     `(make-event (defs-fn (list ',def)
                                              '() '()  'def (w state) state)))

(defmacro defs (&rest def-lst) `(make-event (defs-fn ',def-lst
                                              '() '()  'defs (w state) state)))

(defun triplelis$ (xs ys zs)
  "similar to pairlis$, except now we have 3 lists to zip
  == [(cons x (cons y z)) | x in xs, y in ys, z in zs]"
  (declare (xargs :guard (and (true-listp xs)
                              (true-listp ys)
                              (true-listp zs)
                              (= (len xs) (len ys))
                              (= (len xs) (len zs)))))
  (if (endp xs)
      '()
    (cons (cons (car xs)
                (cons (car ys)
                      (car zs)))
          (triplelis$ (cdr xs) (cdr ys) (cdr zs)))))

(defun str/sym-listp (x)
  (declare (xargs :guard T))
  (if (atom x)
    (null x)
    (and (or (stringp (car x)) (symbolp (car x)))
         (str/sym-listp (cdr x)))))


;;; foll 2 funs adapted from cutil/deflist.lisp
(defun concatenate-names (x)
  (declare (xargs :guard (str/sym-listp x)))
  (if (consp x)
      (acl2::concatenate 'string
                         (if (symbolp (car x))
                             (symbol-name (car x))
                           (car x))
                         (concatenate-names (cdr x)))
    ""))
(defthm concatenate-names-is-stringp
  (stringp (concatenate-names x)))

(local (in-theory (disable concatenate-names)))

;;; mksym-package-symbol will be captured by calling lexical environment
(defmacro mksym (&rest args)
  "given a sequence of symbols or strings as args,
   it returns the concatenated symbol"
  `(acl2s::fix-intern-in-pkg-of-sym
    (concatenate-names (list ,@args))
    mksym-ps));mksym-package-symbol

;;-- create a new symbol with prefix or suffix appended
;;-- if its a common-lisp symbol then attach acl2 package name to it
;;-- example:
;;-- (modify-symbol "NTH-" 'bool "") ==> NTH-BOOL
;;-- (modify-symbol "NTH-" 'boolean "") ==> ACL2::NTH-BOOLEAN
(defun modify-symbol (prefix sym postfix)
  (declare (xargs :guard (and (symbolp sym)
                              (stringp postfix)
                              (stringp prefix))))
  (let* ((name (symbol-name sym))
         (name (string-append prefix name))
         (name (string-append name postfix)))
    (if (member-eq sym *common-lisp-symbols-from-main-lisp-package*)
      (acl2s::fix-intern-in-pkg-of-sym name 'acl2::acl2-pkg-witness)
      (acl2s::fix-intern-in-pkg-of-sym name sym))))

(defun modify-symbol-lst (prefix syms postfix)
  (declare (xargs :guard (and (symbol-listp syms)
                              (stringp prefix)
                             (stringp postfix))))
  (if (endp syms)
    nil
    (cons (modify-symbol prefix (car syms) postfix)
          (modify-symbol-lst prefix (cdr syms) postfix))))


(defthm modified-symbol-satisfies-symbolp
         (implies (and (symbolp sym)
                       (stringp pre)
                      (stringp post))
                  (symbolp (modify-symbol pre sym post)))
         :rule-classes :type-prescription)

(in-theory (disable modify-symbol))
(defthm modified-symbol-lst-satisfies-symbol-listp
         (implies (and (symbol-listp syms)
                      (stringp pre)
                       (stringp post))
                  (symbol-listp (modify-symbol-lst pre syms post)))
         :rule-classes (:rewrite :type-prescription))
(defthm modified-symbol-lst-len
  (= (len (modify-symbol-lst pre syms post))
     (len syms)))

(in-theory (disable modify-symbol-lst))


;; ;most functions are taken from either the COI books or rtl radix book
;; (defthm character-listp-explode-nonnegative-integerp
;;   (implies
;;    (character-listp list)
;;    (character-listp (explode-nonnegative-integer number 10 list))))

;; ;Convert a string|symbol|integer to a string, all other are coerced to ""
;; (defund to-string (entry)
;;   (declare (type t entry))
;;   (cond
;;    ((symbolp entry) (symbol-name entry))
;;    ((integerp entry)
;;     (if (<= 0 entry)
;;         (coerce (explode-nonnegative-integer entry 10 nil) 'acl2::string)
;;       (acl2::concatenate 'acl2::string "-"
;;                    (coerce (explode-nonnegative-integer (- entry) 10 nil) 'acl2::string))))
;;    ((stringp entry) entry)
;;    (t "")))


(defun fn-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (symbolp (first x))
       (consp (cdr x))
       (symbol-listp (second x))
       (consp (cddr x))))

(defun fn-list-p (x)
  (declare (xargs :guard t))
  (if (consp x)
    (and (fn-p (car x))
         (fn-list-p (cdr x)))
    (equal x '())))

(defthm strip-cars-doesnt-change-length
  (implies (true-listp xs)
           (= (len (strip-cars xs))
                   (len xs))))

(defthm strip-cdrs-doesnt-change-length
   (implies (true-listp xs)
            (= (len (strip-cdrs xs))
               (len xs))))

;; this shud be taken care automatically by some type-relationship inference algo
(defthm fn-list-p-implies-alistp
  (implies (fn-list-p fns)
           (alistp fns))
  :rule-classes :forward-chaining)

(defthm fn-list-p-strip-cars-is-symbol-listp
  (implies (fn-list-p fns)
           (symbol-listp (strip-cars fns)))
  :rule-classes (:rewrite :forward-chaining))

(defthm true-listp-of-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (true-listp ac)
                           (true-listp (make-list-ac n val ac))))))
(defthm len-of-make-list-ac
  (implies (natp n)
           (equal (len (make-list-ac n val ac))
                  (+ n (len ac)))))

(defthm pairlis$-eqlable-symbol-lists
  (implies (and (symbol-listp xs)
                (symbol-listp ys))
           (eqlable-alistp (pairlis$ xs ys))))
  ;:rule-classes :forward-chaining)
(local (in-theory (disable pairlis$)))
#| add to test regression, there is a bug in the following guard conjecture
(IMPLIES
 (AND (SYMBOLP NM) (FN-LIST-P FNS))
 (LET
  ((MKSYM-PS NM))
  (AND
   (STR/SYM-LISTP (LIST "_" NM))
   (SYMBOLP MKSYM-PS)
   (LET
    ((PREFIX (ACL2S::FIX-INTERN-IN-PKG-OF-SYM (CONCATENATE-NAMES (LIST "_" NM))
                                          MKSYM-PS)))
    (AND
     (ALISTP FNS)
     (LET
      ((OLD-NAMES (STRIP-CARS FNS)))
      (AND
       (SYMBOL-LISTP OLD-NAMES)
       (STRINGP PREFIX)
       (LET
        ((NEW-NAMES (MODIFY-SYMBOL-LST PREFIX OLD-NAMES "")))
        (AND
         (INTEGERP (LEN FNS))
         (<= 0 (LEN FNS))
         (ALISTP FNS)
         (EQUAL (LEN (MAKE-LIST-AC (LEN FNS) 'DEFABBREV NIL))
                (LEN (STRIP-CDRS FNS)))
         (TRUE-LISTP (STRIP-CDRS FNS))
         (TRUE-LISTP NEW-NAMES)
         (EQUAL (LEN (MAKE-LIST-AC (LEN FNS) 'DEFABBREV NIL))
                (LEN NEW-NAMES))
         (LET
             NIL
             (AND (TRUE-LISTP OLD-NAMES)
                  (TRUE-LISTP NEW-NAMES)
                  (EQLABLE-ALISTP (PAIRLIS$ OLD-NAMES NEW-NAMES)))))))))))))
|#

(defun mk-f*-events (fns nm)
  "for given functions return defabbrev events and a substitution
   mapping original names to inlined actual defabbrev names"
  (declare (xargs :guard (and (fn-list-p fns)
                              (symbolp nm))))
  ;;we need to satisfy some invariants for avoiding bugs (especially
  ;;unwanted variable capture - TODO
  (b*  ((mksym-ps    nm) ;for use in macro mksym
        (prefix      (mksym "_" nm))
        (old-names   (strip-cars fns))
        (new-names   (modify-symbol-lst (symbol-name prefix) old-names ""))
        (def-events  (triplelis$ (make-list (len fns)
                                   :initial-element 'defabbrev)
                                 new-names
                                 (strip-cdrs fns)))
        (P           (pairlis$ old-names new-names))
        (def-events~ (sublis P def-events))) ;possible variable capture
   ;;in
   (mv def-events~ P)))


(defconst *stobjs* '(state R$ types-ht$)) ;ACHTUNG: Keep in sync!

(defun mk-declare (K)
  (declare (xargs :guard (and (keyword-value-listp K)
                              ;;phew how ugly is this guard. u make code pretty with b* and u lose with guards
                              (assoc-keyword :sig K)
                              (equal :sig (car (assoc-keyword :sig K)))
                              (true-listp (cadr (assoc-keyword :sig K)))
                              (= 3 (len (cadr (assoc-keyword :sig K))))
                              (true-listp (caadr (assoc-keyword :sig K))))))
  "?: make a declare form from the fields of decl keyword value list "
  (b* (
       ((list & mode)     (or (assoc-keyword :mode K)
                                    '(:mode :logic)))
;:sig ((state ts$) -> (mv erp (oneof -1 boolean) state ts$)))
      (`(:sig (,in & &)) (assoc-keyword :sig K))
       (stobjs           (intersection-eq *stobjs* in)))
  `(declare (xargs :mode ,mode
                   :stobjs ,stobjs))))

(set-verify-guards-eagerness 0)


(defun trans-body (B nm)
  "translate body, by making defun events for each f* binding"
  (declare (xargs :guard (and (symbolp nm)
                             )))
  #||
  (f* ((double (x) (* 2 x))
         (sq (y) (* y y))
         (ntimes (x) (* n x))) ;capture n from surrounding context
    body)
  ==>
  (mv
   ((defabbrev _nm-double (x) (* 2 x))
    (defabbrev _nm-sq (y) (* y y))
    (defabbrev _nm-ntimes (x) (* n x)))
   body')
  where body' = body[subst real names of introduced inline functions]
||#

  (case-match B
    (('f* fns body)   (b* (((mv evts P) (mk-f*-events fns nm))
                             (body~       (sublis P body)))
                         (mv evts body~)))
    ;;ignore otherwise
    (&                  (mv nil B))))



(defun trans-arglist (A )
  (declare (xargs :guard (and (true-listp A)

                              )))
  "not implemented at the moment i.e noop"
; (|x as (list a b ...)| x2 x3
;  |ts$ as {curr-subgoal-idx, cur-run-idx, ...}|)
;  =>
;  (mv (X X2 X3 TS$)
;      (((list a b . &) x)
;       (curr-run-idx (cur-run-idx ts$))
;       (curr-subgoal-idx (curr-subgoal-idx ts$)))
  (mv A nil))

(deflabel f*)



(defconst   *acl2s-version* "1.0.2.1")

(defun def-fn1 (name arglist decl-kv-list decls body ctx wrld state)
  (declare (ignorable wrld state))
  (declare (xargs :stobjs (state)
                  :guard (and (symbolp name)
                              (symbolp ctx)
                              (true-listp arglist)
                              (keyword-value-listp decl-kv-list)
                              (true-listp decls)
                              (plist-worldp wrld))))

  (let ((K decl-kv-list)
        (A arglist)
        (B body))
  ;;in
   (b* (((unless (keyword-value-listp K))
        (er hard ctx "~|~x0 is not a keyword value list.~%" K))
       ((unless (assoc-keyword :sig K))
        (er hard ctx "~|:sig not found in ~x0.~%" K))
; make a declaration form
       (decl (mk-declare K))
; get doc string
       ((list & doc) (or (assoc-keyword :doc K) '(:doc "n/a")))

; translate arglist to get the actual arglist and a list of b* bindings
       ((mv A1 b*-bindings) (trans-arglist A))
; translate body to get events for nested defuns and actual body
       ((mv aux-events B~)  (trans-body B name))
       (B~1 (if b*-bindings
                `(b* ,b*-bindings B~)
              B~)))
    ;;in
    (list aux-events `(,name ,A1 ,doc ,@(cons decl decls) ,B~1)))))

(defun def-fn (def ctx wrld state)
  (declare (ignorable wrld state))
  (declare (xargs :stobjs (state)
                  :guard (and (symbolp ctx)
                              (plist-worldp wrld))))
  (case-match def
    ((nm A ('decl . K) ('declare . ds) B)
     ;; =>
     (def-fn1 nm A K (list (cons 'declare ds)) B ctx wrld state))

    ((nm A ('decl . K) B)
     ;; =>
     (def-fn1 nm A K '() B ctx wrld state))

    (& (er hard ctx "~|Ill-formed def form. ~
General form: ~
(def name arglist decl [declare] body)~%"))))

(defun defs-fn (def-lst aux-events. defuns-tuples. ctx wrld state)
  "my own defun for storing type metadata for later type-checking.
1. possible nested (local) defuns
2. list comprehensions
3. destructuring arg list"
;;; accumulate the list of event forms to be submitted in ans. parameter
  (declare (xargs :stobjs (state)
                  :guard (and (true-listp def-lst)
                              (true-listp aux-events.)
                              (symbolp ctx)
                              (plist-worldp wrld))))
  (if (endp def-lst)
      `(progn ,@aux-events.
              ,(if (null (cdr defuns-tuples.));singleton
                   `(defun . ,(car defuns-tuples.))
                 `(defuns . ,defuns-tuples.)))
    ;;else
    (b* (((list ae def-tuple);ae: aux-events
           (def-fn (first def-lst) ctx wrld state)))

      (defs-fn (rest def-lst)
               (append ae aux-events.)
               (append defuns-tuples. (list def-tuple)) ctx wrld state))))




;; #!ACL2  ;;copied from Sol Swords.
;; (progn
;;   (defun access-b*-bindings (recname var pairs)
;;     (if (atom pairs)
;;         nil
;;       (cons
;;        (if (atom (car pairs))
;;            (list (car pairs) `(acl2::access ,recname ,var
;;                                             ,(acl2s::fix-intern-in-pkg-of-sym
;;                                              (symbol-name (car pairs))
;;                                              :keyword)))
;;          (list (caar pairs) `(acl2::access ,recname ,var
;;                                            ,(acl2s::fix-intern-in-pkg-of-sym
;;                                             (symbol-name (cadar pairs))
;;                                             :keyword))))
;;        (access-b*-bindings recname var (cdr pairs)))))

;;   (def-b*-binder
;;     access
;;     `(b* ,(access-b*-bindings (car args) (car forms) (cdr args))
;;        ,rest-expr)))




(defconst   *primitives*
  '(+f   *f   |1+f|   =  |1-f|   -f   /=  <=  <  >  >=
    plus-mod-m31 double-mod-m31 times-expt-2-16-mod-m31 times-mod-m31
    mod mod^ floor floor^ expt expt^
    min min^ max max^
    logand logand^ logior logior^
    lognot lognot^ logxor logxor^
    ash ash^
    mask^ mv mv^ my-fixnum the-fixnum
    er er0 prog2$ cw ev-fncall-w
    fn-count-evg lexorder
    if not implies and or iff
    acl2-numberp rationalp integerp consp
    characterp symbolp stringp
    booleanp termp keywordp
    true-listp symbol-listp
    cons null atom endp list list* push-lemma
    car cdr caar cdar cadr cddr cadar
    first second third fourth fifth
    sixth seventh eighth ninth tenth
    rest last butlast nth nthcdr update-nth
    append length reverse revappend string-append
    acons assoc assoc-eq assoc-equal assoc-keyword
    strip-cars strip-cdrs
    numerator denominator realpart imagpart
    char-code char code-char
    symbol-name symbol-package-name
    intern intern-in-package-of-symbol
    symbol-append bozo
    equal eql eq
    member-eq member member-equal

    list-lis ffnnamep subsequencep
    legal-variable-or-constant-namep genvar collect-non-x
    arglistp cons-term match-tests-and-binding
    er-hard-val the-fixnum! the-signed-byte! xxxjoin xxxjoin-fixnum
    number-of-digits lambda-body flambdap  make-lambda  make-let
    flambda-applicationp
    doublet-listp singleton-list-p ascii-code!
    formals arity def-body program-termp equivalence-relationp
    >=-len all->=-len strip-cadrs strip-cddrs sublis-var subcor-var
    new-namep global-symbol symbol-doublet-listp remove1-eq pair-lis$
    add-to-set-eq pseudo-termp all-vars ffn-symb fargs
    translate-and-test intersectp check-vars-not-free position
    collect-cdrs-when-car-eq restrict-alist substitute sublis
    ;; added remove1-assoc here, after the change in commit 374edd977999637845227330eb8e99985529b1fc:
    remove1-assoc function-symbolp the 32-bit-integerp
    32-bit-integer-listp with-live-state state-global-let*
    integer-range-p signed-byte-p unsigned-byte-p boole$
    make-var-lst the-mv nth-aliases fix-true-list
    duplicates evens odds resize-list conjoin2
    conjoin-untranslated-terms search count our-multiple-value-prog1
    all-calls filter-atoms unprettyify variantp free-vars-in-hyps
    destructors  alist-to-keyword-alist
    occur

;linear-a.lisp
    dumb-occur

    ;other-processes.lisp
    sublis-expr generate-variable
    ; tau.lisp
    subst-var subst-var-lst
    ))

(defconst   *special-forms*
  '(b* let mv-let cond case case-match defabbrev defun defmacro
    ))




; NOTE on what is stored in the acl2 world for
; Functions
; in Raw lisp do the following
#||
(get 'acl2::binary-append *current-acl2-world-key*)
==>
((COARSENINGS NIL)

 (RUNIC-MAPPING-PAIRS ((620 :DEFINITION BINARY-APPEND)
                       (621 :EXECUTABLE-COUNTERPART BINARY-APPEND)
                       (622 :TYPE-PRESCRIPTION BINARY-APPEND)
                       (623 :INDUCTION BINARY-APPEND)))
 (DEF-BODIES (((620 NIL IF (CONSP X) (CONS (CAR X) (BINARY-APPEND (CDR X) Y)) Y)
               (BINARY-APPEND)
               (X Y)
               (:DEFINITION BINARY-APPEND)
               (BINARY-APPEND T NIL))))
(TYPE-PRESCRIPTIONS ...)

(CONGRUENCES NIL)

(SYMBOL-CLASS :COMMON-LISP-COMPLIANT :COMMON-LISP-COMPLIANT
              :ACL2-PROPERTY-UNBOUND :PROGRAM :PROGRAM)

(LEMMAS  ...)

(STOBJS-OUT (NIL) :ACL2-PROPERTY-UNBOUND (NIL))

(FORMALS (X Y) :ACL2-PROPERTY-UNBOUND (X Y))

(PRIMITIVE-RECURSIVE-DEFUNP T)

(LEVEL-NO 1)

(UNNORMALIZED-BODY (IF (ENDP X) Y (CONS (CAR X) (BINARY-APPEND (CDR X) Y))))

(QUICK-BLOCK-INFO (SELF-REFLEXIVE UNCHANGING))

(JUSTIFICATION (JUSTIFICATION (X) (NIL O-P . O<)
                              ((ACL2-COUNT X) MV-LIST RETURN-LAST)))

(INDUCTION-MACHINE ((TESTS-AND-CALLS ((ENDP X)))
                    (TESTS-AND-CALLS ((NOT (ENDP X)))
                                     (BINARY-APPEND (CDR X) Y))))
(RECURSIVEP (BINARY-APPEND))

(REDEFINED (:RECLASSIFYING-OVERWRITE BINARY-APPEND (X Y) (NIL NIL) (NIL)))

(ABSOLUTE-EVENT-NUMBER 6858 :ACL2-PROPERTY-UNBOUND 227)
(PREDEFINED T T)
(GUARD (TRUE-LISTP X) :ACL2-PROPERTY-UNBOUND (TRUE-LISTP X))

(STOBJS-IN (NIL NIL) :ACL2-PROPERTY-UNBOUND (NIL NIL)))
||#

;Macros:
#||
(get 'acl2::append *current-acl2-world-key*)
==>

((MACRO-BODY (IF (NULL RST)
                 'NIL
                 (IF (NULL (CDR RST))
                     (CAR RST)
                     (XXXJOIN 'BINARY-APPEND RST))))
 (ABSOLUTE-EVENT-NUMBER 228)
 (PREDEFINED T)
 (MACRO-ARGS (&REST RST)))
||#
