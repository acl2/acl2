#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")

;;Bunch of utility functions for use by just defdata
(acl2::begin-book t);$ACL2s-Preamble$|#

(in-package "DEFDATA")

(set-verify-guards-eagerness 2)
(include-book "std/util/bstar" :dir :system)
(include-book "acl2s/utilities" :dir :system)

;; (defun modify-symbol (prefix sym postfix)
;;   (declare (xargs :guard (and (symbolp sym)
;;                               (stringp postfix)
;;                               (stringp prefix))))
;;   (let* ((name (symbol-name sym))
;;          (name (string-append prefix name))
;;          (name (string-append name postfix)))
;;     (if (member-eq sym *common-lisp-symbols-from-main-lisp-package*)
;;       (intern-in-package-of-symbol name 'acl2::acl2-pkg-witness)
;;       (intern-in-package-of-symbol name sym))))

(defun str/sym-listp (x)
  (declare (xargs :guard T))
  (if (atom x)
    (null x)
    (and (or (stringp (car x)) (symbolp (car x)))
         (str/sym-listp (cdr x)))))

;;; foll 2 funs adapted from cutil/deflist.lisp
(defun join-names (xs separator)
  (declare (xargs :guard (and (str/sym-listp xs)
                              (stringp separator))))
(if (endp xs)
    ""
  (if (endp (cdr xs))
      (acl2::concatenate 'string
                         (if (symbolp (car xs))
                             (symbol-name (car xs))
                           (car xs))
                         "")
    (acl2::concatenate 'string
                       (if (symbolp (car xs))
                           (symbol-name (car xs))
                         (car xs))
                       (acl2::concatenate 'string
                                          separator
                                          (join-names (cdr xs) separator))))))

(defthm join-names-is-stringp
  (stringp (join-names x sep)))

(in-theory (disable join-names))

(defun extract-kwd-val-fn (key args default)
  (declare (xargs :guard (and (keywordp key)
                              (true-listp args))))
  (let* ((lst (member key args))
         (val (and (consp lst) (consp (cdr lst)) (cadr lst))))
    (or val default)))

(defmacro extract-kwd-val (key args &key default)
  `(extract-kwd-val-fn ,key ,args ,default))

(defun keyword-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (keywordp (car x))
         (keyword-listp (cdr x)))))

(defun remove-keywords (keys kwd-val-list)
  (declare (xargs :guard (and (keyword-listp keys)
                              (keyword-value-listp kwd-val-list))))
  (if (endp keys)
      kwd-val-list
    (remove-keywords (cdr keys) (acl2::remove-keyword (car keys) kwd-val-list))))

(defun remove-keywords-from-args (keys args)
  (declare (xargs :guard (and (keyword-listp keys)
                              (true-listp args))))
  (if (endp args)
      '()
    (if (keyword-value-listp args)
        (remove-keywords keys args)
      (cons (car args) (remove-keywords-from-args keys (cdr args))))))

;pre-condition: args should be consp
(defmacro s+ (&rest args)
  "string/symbol(s) concat to return a symbol.
  :pkg and :separator keyword args recognized."
  (let* ((sep (extract-kwd-val :separator args :default ""))
         (pkg (extract-kwd-val :pkg args))
         (args (remove-keywords-from-args '(:separator :pkg) args)))
    `(s+-fn (list ,@args) ,sep ,pkg)))

(defun s+-fn (ss sep pkg)
  (declare (xargs :guard (and (str/sym-listp ss)
                              (stringp sep))))
  (b* (((unless (consp ss)) (er hard? 's+ "~| Expect at least one string/symbol arg, but given ~x0 ~%" ss))
       (s1 (car ss))
       (pkg~ (or (and (pkgp pkg) pkg)
                 (and (symbolp s1) (symbol-package-name s1))
                 "DEFDATA"))
       ;; (- (cw "~| pkg to be used is : ~x0~%" pkg~))
       )
  (acl2s::fix-intern$ (join-names ss sep) pkg~)))

(defun modify-symbol-lst (prefix syms postfix pkg)
  (declare (xargs :guard (and (symbol-listp syms)
                              (stringp prefix)
                              (stringp postfix)
                              (pkgp pkg))))
  (if (endp syms)
    nil
    (cons (s+ prefix (car syms) postfix :pkg pkg)
          (modify-symbol-lst prefix (cdr syms) postfix pkg))))


(defun get-dest-prefix (conx-name)
  (declare (xargs :guard (symbolp conx-name)))
  (concatenate 'string (symbol-name conx-name) "-"))

(defun get-modifier-prefix (conx-name)
  (declare (xargs :guard (symbolp conx-name)))
  (concatenate 'string "SET-" (symbol-name conx-name) "-"))


(include-book "data-structures/utilities" :dir :system)

(defloop symbol-names (syms)
  (declare (xargs :guard (symbol-listp syms)))
  (for ((sym in syms)) (collect (symbol-name sym))))

(verify-termination ACL2::>=-LEN)
(verify-termination ACL2::ALL->=-LEN)
; Commented out by Matt K., 12/23/2018.  The following is ill-formed, but was
; formerly accepted as redundant.  Now it is rejected, so I'm commenting it
; out.  Presumably its intended effect was already accomplished by the two
; verify-termination forms just above, which in turn are not necessary since
; ACL2 comes up with the two indicated functions already in :logic mode.
; (verify-termination ACL2::>=-LEN ACL2::ALL->=-LEN)

(defun strip-cadrs (x)
  (declare (xargs :guard (acl2::all->=-len x 2)))
  (cond ((endp x) nil)
        (t (cons (cadar x)
                 (strip-cadrs (cdr x))))))

(def-const *defthm-aliases*
  '(acl2::defthm acl2::defthmd acl2::defthm+ acl2::defrule
                 acl2::defaxiom acl2s::test-then-skip-proofs acl2::defcong
                 acl2::defrefinement acl2::defequiv acl2::skip-proofs
                 acl2s::defthm-no-test acl2s::defthm-test-no-proof))

(defloop get-event-names (xs)
  "get names from defthm events"
  (declare (xargs :guard (acl2::all->=-len xs 2)))
  (for ((x in xs)) (append (and (member-eq (car x) *defthm-aliases*)
                                (list (cadr x))))))

(defun keywordify (sym)
  (declare (xargs :guard (symbolp sym)))
  (acl2s::fix-intern-in-pkg-of-sym (symbol-name sym) :a))

(defmacro acl2-getprop (name prop w &key default)
 `(getprop ,name ,prop ,default 'acl2::current-acl2-world ,w))

(defun list-up-lists (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2)
                              (= (len l1) (len l2)))))
  "same as listlis"
  (if (endp l1)
    nil
    (cons (list (car l1) (car l2))
          (list-up-lists (cdr l1) (cdr l2)))))

(verify-termination acl2::LEGAL-VARIABLE-OR-CONSTANT-NAMEP)
(verify-termination acl2::legal-constantp)
(verify-termination acl2::legal-variablep)
;;-- convert function lambda-keywordp from :program mode to :logic mode
(verify-termination acl2::lambda-keywordp)
(verify-guards  acl2::lambda-keywordp)
(verify-guards acl2::legal-constantp)

; We do not use legal-variablep because we want to register
; constructors such as /, which is not a legal-variablep.
(defun proper-symbolp (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (or (keywordp x);a keyword
                (booleanp x);t or nil
                (acl2::legal-constantp x)))))

(defthm keyword-list-is-symbol-list
  (implies (keyword-listp x)
           (symbol-listp x))
  :rule-classes (:forward-chaining))

(defthm proper-symbol-is-symbol
  (implies (proper-symbolp x)
           (symbolp x))
  :rule-classes (:compound-recognizer
                 :forward-chaining))

(defthm proper-symbol-disjoint-with-keys
  (implies (keywordp x)
           (not (proper-symbolp x)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm proper-symbol-disjoint-with-bool
  (implies (booleanp x)
           (not (proper-symbolp x)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(in-theory (disable proper-symbolp))

(defun proper-symbol-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (null xs)
    (and (proper-symbolp (car xs))
         (proper-symbol-listp (cdr xs)))))

(defthm proper-symbol-listp-is-symbol-list
  (implies (proper-symbol-listp x)
           (symbol-listp x))
  :rule-classes (:forward-chaining
                 (:rewrite :backchain-limit-lst 1)))

(in-theory (disable proper-symbol-listp))

(defun tau-predicate-p (pred world)
  (declare (xargs :mode :program))
  (b* ((td (acl2::tau-data-fn pred world))
       ((unless (consp td)) nil)
       (entry (assoc-eq 'acl2::recognizer-index (cdr td)))
       ((unless (and (consp entry) (consp (cdr entry)))) nil))
    (natp (cadr entry))))


; DEFDATA TABLES

; TYPE METADATA TABLE
(table type-metadata-table nil nil :clear)

; TYPE ALIAS TABLES
(table pred-alias-table nil nil :clear)
(table type-alias-table nil nil :clear)

(defun type-metadata-table (wrld)
  "api to get the alist representing defdata type metadata table"
  (declare (xargs :guard (plist-worldp wrld)))
  (table-alist 'defdata::type-metadata-table wrld))

(defun type-alias-table (wrld)
  "api to get the alist representing defdata type-alias table"
  (declare (xargs :guard (plist-worldp wrld)))
  (table-alist 'defdata::type-alias-table wrld))

(defun pred-alias-table (wrld)
  "api to get the alist representing defdata pred-alias table"
  (declare (xargs :guard (plist-worldp wrld)))
  (table-alist 'defdata::pred-alias-table wrld))


; Doesnt work
;; (defthm table-alist-are-alists
;;   (implies (and (plist-worldp w)
;;                 (symbolp x))
;;            (alistp (table-alist x w))))

(defun sym-aalist1p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (symbolp (caar x))
           (symbol-alistp (cdar x))
           (sym-aalist1p (cdr x)))
    (null x)))

(defun base-alias-type (type A)
  (declare (xargs :guard (sym-aalist1p A)))
  (b* (((unless (symbolp type)) type)
       (atype (assoc-equal :type (acl2s::get-alist type A))))
    (if (consp atype)
        (cdr atype)
      type)))

(defun base-alias-pred (pred ptbl)
  (declare (xargs :guard (sym-aalist1p ptbl)))
  (b* (((unless (symbolp pred)) pred)
       (ppred (assoc-equal :predicate (acl2s::get-alist pred ptbl))))
    (if (consp ppred)
        (cdr ppred)
      pred)))

(defun is-allp-alias (P wrld)
  "is predicate P an alias of allp?"
  ;; (declare (xargs :guard (and (proper-symbolp P)
  ;;                             (plist-worldp wrld))))
  (declare (xargs :verify-guards nil))
  (b* ((ptbl (table-alist 'pred-alias-table wrld))
       (P (base-alias-pred P ptbl)))
    (or (eq P 'acl2s::allp)
        (assoc P (table-alist 'defdata::allp-aliases-table wrld)))))

; TODO -- use this in places where we check for Top type.
(defun is-top (typename wrld)
  "is typename an alias of acl2s::all?"
  ;; (declare (xargs :guard (and (proper-symbolp P)
  ;;                             (plist-worldp wrld))))
  (declare (xargs :verify-guards nil))
  (b* ((atbl (table-alist 'type-alias-table wrld))
       (typename (base-alias-type typename atbl)))
    (or (eq typename 'acl2s::all)
        (rassoc typename (table-alist 'defdata::allp-aliases-table wrld)))))

; CHECK with J. TODO What if there is some information in pos-implicants of P1,
; that is missed below!?
(defun subtype-p (P1 P2 wrld)
  "Is P1 => P2 in tau-database?"
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp P1)
                              (symbolp P2)
                              (plist-worldp wrld))))
  (b* (
       ;((unless (tau-predicate-p P1 wrld)) nil)
       ;((unless (tau-predicate-p P2 wrld)) nil) ;expensive calls
       ((when (is-allp-alias P2 wrld)) t)
       ((when (eq P1 P2)) t)
       (P2-neg-implicants-tau (getprop P2 'acl2::neg-implicants acl2::*tau-empty* 'acl2::current-acl2-world wrld))
       (P2-neg-pairs (acl2::access acl2::tau P2-neg-implicants-tau :neg-pairs)))
    ;guard verif fails since, we dont know if P2-neg-implicants is a alist.
    (rassoc-eq P1 P2-neg-pairs)))

(verify-termination ACL2::UPPER-BOUND-<)
(verify-termination ACL2::LOWER-BOUND->)
(verify-termination ACL2::SQUEEZE-K)
(set-verify-guards-eagerness 1)
(verify-termination acl2::conjoin-intervals)
(set-verify-guards-eagerness 2)

(defun range-subtype-p (interval1 interval2)
  (declare (xargs :verify-guards nil))
  (equal (acl2::conjoin-intervals interval1 interval2)
         interval1))

(defun disjoint-p (P1 P2 wrld)
  "Is P1 x => (not (P2 x)) in tau-database?"
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp P1)
                              (symbolp P2)
                              (plist-worldp wrld))))
  (b* (
       ;((unless (tau-predicate-p P1 wrld)) nil)
       ;((unless (tau-predicate-p P2 wrld)) nil) ;expensive calls
       ((when (or (is-allp-alias P1 wrld) (is-allp-alias P2 wrld))) nil)
       ((when (eq P1 P2)) nil)
       (P1-pos-implicants-tau (getprop P1 'acl2::pos-implicants acl2::*tau-empty* 'acl2::current-acl2-world wrld))
       (P1-neg-pairs (acl2::access acl2::tau P1-pos-implicants-tau :neg-pairs)))
    ;guard verif fails since, we dont know if P2-pos-implicants is a alist.
    (rassoc-eq P2 P1-neg-pairs)))

;----------above is copied from utilities.lisp -----------------------

(local
 (defthm valid-subseq-of-string-is-string
   (implies (and (stringp pname)
                 (< x (length pname))
                 (< y (length pname))
                 (<= x y))
            (stringp (subseq pname x y)))
   :rule-classes :type-prescription))

;;inverse operation of the above --added by harshrc
(defun get-typesymbol-from-pred-P-naming-convention (sym)
  (declare (xargs :guard (and (symbolp sym))
                  :guard-hints (("Goal" :in-theory (disable acl2::length acl2::subseq)))))
  (let* ((pred-name (acl2::symbol-name sym))
        (len-predname (acl2::length pred-name)))
    (if (and
         (< 1 len-predname) ;atleast have "p" and one more char
         (equal #\P (acl2::char pred-name (1- len-predname)))) ;WTF, smallcase p wouldnt work
      (let ((typename (acl2::subseq pred-name 0 (1- len-predname))));strip last char which is 'p'
        (acl2s::fix-intern-in-pkg-of-sym typename sym))
      NIL))) ;TODO.Beware
      ;(er hard 'get-typesymbol-from-pred "~x0 doesnt follow our convention of predicates ending with 'p'.~%" sym))))

;;-- (make-predicate-symbol 'integer "ACL2S B") ==> ACL2S B::INTEGERP
(defun make-predicate-symbol (sym pkg)
  (declare (xargs :guard (and (symbolp sym)
                              (pkgp pkg))))
  (s+ sym "P" :pkg pkg))

(defun make-predicate-symbol-lst (syms pkg)
  (declare (xargs :guard (and (symbol-listp syms)
                              (pkgp pkg))))
  (if (endp syms)
    nil
    (cons (make-predicate-symbol (car syms) pkg)
          (make-predicate-symbol-lst (cdr syms) pkg))))


(defun make-enumerator-symbol (sym pkg)
  (declare (xargs :guard (and (symbolp sym)
                              (pkgp pkg))))
  (s+ "NTH-" sym :pkg pkg))

(defun make-uniform-enumerator-symbol (sym pkg)
  (declare (xargs :guard (and (symbolp sym)
                              (pkgp pkg))))
  (s+ "NTH-" sym "/ACC" :pkg pkg))

;;--check arity of macro optional arguments
(defun optional-macro-args-allow-arity (margs n)
  (declare (xargs :guard (and (true-listp margs) (integerp n))))
  (cond ((<= n 0)
         t)
        ((endp margs)
         nil)
        ((member-eq (car margs) '(&rest &body))
         t)
        ((acl2::lambda-keywordp (car margs))
         nil)
        (t
         (optional-macro-args-allow-arity (cdr margs) (1- n)))))

;;-- check arity of a macro
(defun macro-args-allow-arity (margs n)
  (declare (xargs :guard (and (true-listp margs) (integerp n))))
  (cond ((< n 0)
         nil)
        ((endp margs)
         (= n 0))
        ((acl2::lambda-keywordp (car margs))
         (cond ((eq (car margs) '&whole)
                (macro-args-allow-arity (cdr margs) (1+ n)))
               ((eq (car margs) '&optional)
                (optional-macro-args-allow-arity (cdr margs) n))
               ((member-eq (car margs) '(&rest &body))
                t)
               ((member-eq (car margs) '(&key &allow-other-keys))
                (= n 0))
               (t
                nil)))
        (t
         (macro-args-allow-arity (cdr margs) (1- n)))))

;;-- check arity of any function or macro
(defun allows-arity (name n world)
  (declare (xargs :guard (and (symbolp name)
                              (natp n)
                              (plist-worldp world))))
  (if (function-symbolp name world)
    (= n (len (acl2-getprop name 'acl2::formals world)))
    (let ((margs (acl2-getprop name 'acl2::macro-args world
                               :default :undefined)))
      (and (true-listp margs)
           (macro-args-allow-arity margs n)))))

;EXTREMELY SLOW CALL because of getprop
(defun defined-fun-or-macrop (name world)
  (declare (xargs :guard (plist-worldp world)))
  (and (symbolp name)
       (or (function-symbolp name world)
           (true-listp (acl2-getprop name 'acl2::macro-args world
                                     :default :undefined)))))

(defun allow-arity-lst (name-lst n world)
  (declare (xargs :guard (and (symbol-listp name-lst)
                              (natp n)
                              (plist-worldp world))))
  (or (endp name-lst)
      (and (allows-arity    (car name-lst) n world)
           (allow-arity-lst (cdr name-lst) n world))))

;;--check if 'name' is a predicate function
(defun plausible-predicate-functionp (name world)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp world))))
  (allows-arity name 1 world))

(defun plausible-predicate-function-listp (name-lst world)
  (declare (xargs :guard (and (symbol-listp name-lst)
                              (plist-worldp world))))
  (or (endp name-lst)
      (and (plausible-predicate-functionp      (car name-lst) world)
           (plausible-predicate-function-listp (cdr name-lst) world))))

(defun possible-constant-value-p (def)
  (declare (xargs :guard t))
  (if (consp def)
    ;quoted constant
    (and (eq 'quote (car def))
         (consp (cdr def))
         (null (cddr def)))
    (or (not (symbolp def));either acl2-number character string
        (keywordp def);a keyword
        (booleanp def);t or nil
        (legal-constantp def))))

(defun put2-fn (nm key val al)
  (declare (xargs :guard (eqlable-alistp al)))
  (let ((lookup1 (assoc nm al)))
    (if (and (consp lookup1)
             (eqlable-alistp (cdr lookup1)))
        (put-assoc nm (put-assoc key val (cdr lookup1)) al)
      al)))

(defun get2-fn (nm key al default)
  (declare (xargs :guard (eqlable-alistp al)))
  (let ((lookup1 (assoc nm al)))
    (if (and (consp lookup1)
             (eqlable-alistp (cdr lookup1)))
        (let ((lookup2 (assoc key (cdr lookup1))))
          (or (and lookup2
                   (cdr lookup2))
              default))
      default)))

(defmacro get2 (name key al &optional default)
  `(get2-fn ,name ,key ,al ,default))

(defun get1-fn (key al default)
  (declare (xargs :guard (eqlable-alistp al)))
  (let* ((lookup (assoc key al)))
    (or (and lookup
             (cdr lookup))
        default)))

(defmacro get1 (key  kwd-alist &optional default)
  `(get1-fn ,key ,kwd-alist ,default))

(defloop rget2 (key2 val2 al)
  "return the key which has alist containing key2=val2"
  (declare (xargs :verify-guards nil))
  (for ((entry in al))
       (when (eql val2 (get1 key2 (cdr entry)))
         (return (car entry)))))

(defun type-name (pred wrld)
  (declare (xargs :verify-guards nil))
  (b* ((M (type-metadata-table wrld))
       (ptbl (table-alist 'pred-alias-table wrld))
       (ptype (assoc-equal :type (acl2s::get-alist pred ptbl))))
    (if ptype
        (cdr ptype)
      (rget2 :predicate pred M))))

;; (defmacro table-add-event (nm key val &key (splice 't))
;;   "add (append if splice is t) val onto the existing entry at key in table nm. top-level-event"
;;   `(make-event
;;     (b* ((al (table-alist ',nm (w state)))
;;          ((mv nm key val splice) (mv ',nm ,key ,val ,splice))
;;       ;   ((unless (eqlable-alistp al)) (er hard? ctx "~| Table ~x0 is not eqlable-alist. ~%" ',nm))
;;          (existing-val (get1 key al))
;;          (new-val (cond ((not (true-listp existing-val)) ;just override
;;                          val)
;;                         ((and splice (true-listp val)) (append existing-val val))
;;                         (t (append existing-val (and val (list val)))))))
;;       `(table ,nm ',key ',new-val))))

(defmacro add-pre-post-hook (nm key val)
  "top-level table event. append val onto entry of key in table nm"
  `(make-event
    '(table ,nm ,key (union-equal (cdr (assoc ,key (table-alist ',nm world))) ,val))))

(defun get-all (key D) ;D is a dictionary/alist
  (declare (xargs :guard (eqlable-alistp D)))
  (if (endp D)
      '()
    (if (eql key (caar D))
        (cons (cdar D) (get-all key (cdr D)))
      (get-all key (cdr D)))))

(defun apply-mget-to-x-lst (fields quotep)
  (declare (xargs :guard (and (booleanp quotep)
                              (symbol-listp fields))))
  (if (endp fields)
    nil
    (let ((d-keyword-name (intern (symbol-name (car fields)) "KEYWORD")))
      (cons (list 'acl2::mget (if quotep (kwote d-keyword-name) d-keyword-name) 'x)
            (apply-mget-to-x-lst (cdr fields) quotep)))))

;find recursive records
(defun find-recursive-records (preds new-constructors)
  (declare (xargs :guard (and (eqlable-alistp new-constructors)
                              (symbol-listp preds))))
  (if (endp new-constructors)
    nil
    (b* (((cons & conx-al) (car new-constructors))
         (ctx 'find-recursive-records)
         ((when (not (eqlable-alistp conx-al)))
          (er hard? ctx "~| ~x0 is not eqlable-alist. ~%" conx-al))
         (dex-pairs (get1 :dest-pred-alist conx-al))
         ((when (not (eqlable-alistp dex-pairs)))
          (er hard? ctx "~| ~x0 is not eqlable-alist. ~%" dex-pairs)))
    (if (intersection-eq preds (strip-cdrs dex-pairs));TODO CHECK
        (cons (car new-constructors) (find-recursive-records preds (cdr new-constructors)))
      (find-recursive-records preds (cdr new-constructors))))))

;(verify-termination acl2::rule-name-designatorp)
(defun runes-to-be-disabled1 (names wrld ans)
  (declare (xargs :mode :program))
  (if (endp names)
      ans
    (b* ((name (car names)))
      (if (acl2::rule-name-designatorp name nil wrld) ;filter runes
          (runes-to-be-disabled1 (cdr names) wrld (cons name ans))
        (runes-to-be-disabled1 (cdr names) wrld ans)))))

(defun runes-to-be-disabled (names wrld)
  (declare (xargs :mode :program))
  (remove-duplicates-equal (runes-to-be-disabled1 names wrld '())))

(defun build-one-param-calls (fns params)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-listp params)
                              (= (len fns) (len params)))))
  (if (endp fns)
      nil
    (if (eq (car fns) 'ACL2S::ALLP)
        (build-one-param-calls (cdr fns) (cdr params))
      (cons (list (car fns) (car params))
            (build-one-param-calls (cdr fns) (cdr params))))))

(include-book "coi/symbol-fns/symbol-fns" :dir :system)

(defun numbered-vars (x k)
  (declare (xargs :guard (and (symbolp x)
                              (natp k))))
  (reverse (symbol-fns::item-to-numbered-symbol-list-rec x k)))

#|
This is true when we have defdata available. We prove this
in base.lisp

(defdata symbol-aalist (alistof symbol symbol-alist))
(thm (equal (sym-aalist1p x) (symbol-aalistp x)))
|#

#|
(i-am-here) :add enumerator macros for the alias, eg, nth-nn-rat/acc
nth-nn-rat
see (defdata foo rational)

|#

(defmacro defdata-alias (alias type &rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst))))
       (pred (let ((lst (member :pred args)))
               (and lst (cadr lst))))
       (- (cw "~%")))
    `(with-output
      ,@(and (not verbosep)
             '(:off :all :on (summary error) :summary-off (:other-than acl2::form acl2::time)))
      :gag-mode t :stack :push
      (make-event
       (b* ((pkg (current-package state))
            (M (type-metadata-table (w state)))
            (A (type-alias-table (w state)))
            (pred (if ',pred ',pred (make-predicate-symbol ',alias pkg)))
            (type (base-alias-type ',type A))
            (type-alist (acl2s::get-alist type M))
            (predicate (acl2s::get-alist :predicate type-alist))
            (def (acl2s::get-alist :def type-alist))
            (record? (and (consp def) (equal 'record (car def))))
            (base-enum (enumerator-name type A M))
            (base-enum/acc (enum/acc-name type A M))
            (alias-enum (acl2s::make-symbl `(nth- ,',alias) pkg))
            (alias-enum-acc (acl2s::make-symbl `(,alias-enum /acc) pkg))
            (x (acl2s::fix-intern$ "X" pkg))
            (seed (acl2s::fix-intern$ "SEED" pkg))
            ((unless predicate)
             (er hard 'defdata-alias
                 "~%**Unknown type**: ~x0 is not a known type name.~%" ',type))
            ((when record?)
             (er hard 'defdata-alias
                 "~%**Record type**: ~x0 is a record and records cannot be aliased.~%" ',type)))
         `(encapsulate
           ()
           (table type-alias-table
                  ',',alias
                  '((:pred . ,pred)
                    (:type . ,type)
                    (:predicate . ,predicate))
                  :put)
           (table pred-alias-table
                  ',pred
                  '((:alias . ,',alias)
                    (:type . ,type)
                    (:predicate . ,predicate))
                  :put)
           (defmacro ,pred (,x) `(,',predicate ,,x))
           (defmacro ,alias-enum (,x) `(,',base-enum ,,x))
           (defmacro ,alias-enum-acc (,x ,seed) `(,',base-enum/acc ,,x ,,seed))))))))

#|
(defmacro defdata-alias (alias type &rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst))))
       (pred (let ((lst (member :pred args)))
               (and lst (cadr lst))))
       (- (cw "~%")))
    `(make-event
      (b* ((pkg (current-package state))
           (M (type-metadata-table (w state)))
           (A (type-alias-table (w state)))
           (pred (if ',pred ',pred (make-predicate-symbol ',alias pkg)))
           (type (base-alias-type ',type A))
           (predicate (acl2s::get-alist
                       :predicate (acl2s::get-alist type M)))
           (base-enum (enumerator-name type A M))
           (base-enum/acc (enum/acc-name type A M))
           (alias-enum (acl2s::make-symbl `(nth- ,',alias) pkg))
           (alias-enum-acc (acl2s::make-symbl `(,alias-enum /acc) pkg))
           (x (acl2s::fix-intern$ "X" pkg))
           (seed (acl2s::fix-intern$ "SEED" pkg))
           ((unless predicate)
            (er hard 'defdata-alias
                "~%**Unknown type**: ~x0 is not a known type name.~%" ',type )))
        `(with-output
          ,@(and (not ,verbosep) '(:off :all :on (summary error) :summary-off (:other-than acl2::form acl2::time)))
          :gag-mode t :stack :push
          (encapsulate
           ()
           (table type-alias-table
                  ',',alias
                  '((:pred . ,pred)
                    (:type . ,type)
                    (:predicate . ,predicate))
                  :put)
           (table pred-alias-table
                  ',pred
                  '((:alias . ,',alias)
                    (:type . ,type)
                    (:predicate . ,predicate))
                  :put)
           (defmacro ,pred (,x) `(,',predicate ,,x))
           (defmacro ,alias-enum (,x) `(,',base-enum ,,x))
           (defmacro ,alias-enum-acc (,x ,seed) `(,',base-enum/acc ,,x ,,seed))))))))
|#

(defmacro predicate-name (tname &optional A M)
; if Metadata table is not provided, wrld should be in scope.
  (if (and A M)
      `(get2 (base-alias-type ,tname ,A)
             :predicate ,M)
    `(get2 (base-alias-type ,tname (type-alias-table wrld))
           :predicate (type-metadata-table wrld))))

(defmacro enumerator-name (tname &optional A M)
; if Metadata table is not provided, wrld should be in scope.
  (if (and A M)
      `(get1 :enumerator
             (get1 (base-alias-type ,tname ,A)
                   ,M))
    `(get1 :enumerator
           (get1 (base-alias-type ,tname (type-alias-table wrld))
                 (type-metadata-table wrld)))))

(defmacro enum/acc-name (tname &optional A M)
; if Metadata table is not provided, wrld should be in scope.
  (if (and A M)
      `(get1 :enum/acc
             (get1 (base-alias-type ,tname ,A)
                   ,M))
    `(get1 :enum/acc
           (get1 (base-alias-type ,tname (type-alias-table wrld))
                 (type-metadata-table wrld)))))

(defloop predicate-names-fn (tnames A M)
  (declare (xargs :guard (and (symbol-listp tnames)
                              (sym-aalist1p A)
                              (sym-aalist1p M))))
  (for ((tname in tnames)) (collect (predicate-name tname A M))))

(defmacro predicate-names (tnames &optional A M)
  (if (and A M)
      `(predicate-names-fn ,tnames ,A ,M)
    `(predicate-names-fn
      ,tnames
      (type-alias-table wrld)
      (type-metadata-table wrld))))

(defloop possible-constant-values-p (xs)
  (for ((x in xs)) (always (possible-constant-value-p x))))

(mutual-recursion
 (defun texp-constituent-types1 (texp tnames wrld include-recursive-references-p)
   (declare (xargs :verify-guards nil))
   (cond ((possible-constant-value-p texp) nil)
         ((proper-symbolp texp)
          (cond ((member texp tnames)
                 (and include-recursive-references-p (list texp)))
                ((predicate-name texp) (list texp))
                (t nil)))
         ((atom texp) nil) ;not possible
         ((not (true-listp texp)) (texp-constituent-types1 (cdr texp) tnames wrld include-recursive-references-p))
         (t (texp-constituent-types1-lst (cdr texp) tnames wrld include-recursive-references-p))))

 (defun texp-constituent-types1-lst (texps tnames wrld include-recursive-references-p)
   (if (atom texps)
       nil
     (append (texp-constituent-types1 (car texps) tnames wrld include-recursive-references-p)
             (texp-constituent-types1-lst (cdr texps) tnames wrld include-recursive-references-p))))
 )

(defmacro texp-constituent-types (texp tnames wrld &key include-recursive-references-p)
  `(texp-constituent-types1 ,texp ,tnames ,wrld ,include-recursive-references-p))

(defun is-recursive-type-exp (texp tnames wrld)
  (declare (xargs :verify-guards nil))
  (intersection-eq tnames (texp-constituent-types texp tnames wrld :include-recursive-references-p t)))

(defun recursive-type-p (type-name wrld)
  (declare (xargs :verify-guards nil))
  (b* ((table (type-metadata-table wrld))
       (type-name
        (base-alias-type type-name (type-alias-table wrld)))
       (norm-def (get2 type-name :normalized-def table))
       (clique-names (get2 type-name :clique table)))
    (is-recursive-type-exp norm-def clique-names wrld)))

(defun constituent-types1 (p wrld)
  (declare (xargs :verify-guards nil))
  (b* (((cons & A) p)
       ((acl2::assocs ndef new-types) A)
       (tnames (strip-cars new-types)))
    (texp-constituent-types ndef tnames wrld)))

(defloop constituent-types (ps wrld)
  (declare (xargs :verify-guards nil))
  (for ((p in ps)) (append (constituent-types1 p  wrld))))

(defun named-defdata-exp-p (texp)
  "is it named, i.e of form (name . typename)"
  (and (not (possible-constant-value-p texp))
       (consp texp)
       (not (true-listp texp))
       (proper-symbolp (cdr texp))))

(defun bind-names-vals1 (texp val)
  (and (named-defdata-exp-p texp)
       (list (list (car texp) val))))

(defloop bind-names-vals (texps vals)
  "let binding for each name decl texp -> corresponding val"
  (for ((texp in texps) (val in vals))
       (append (bind-names-vals1 texp val))))

(defloop replace-calls-with-names (calls texps)
  "calls and texps are 1-1.
   return calls but if the corresponding texp is named, replace the call with the name"
  (for ((texp in texps) (call in calls))
       (collect (if (named-defdata-exp-p texp)
                    (car texp)
                  call))))

(defun to-string1 (xstr alst)
  (declare (xargs :mode :program))
  (b* (((mv & str) (acl2::fmt1!-to-string xstr alst 0)))
    str))

; Matt K. mod, 10/2017: Since ev-fncall-w is called in funcall below but is now
; untouchable, a change is necessary.  Fortunately, cert.acl2 specifies :ttags
; :all, so we can introduce a trust tag to remove ev-fncall-w as an
; untouchable.  An alternate solution, not yet tried (at least by me), is to
; use ev-fncall-w! instead; but that might slow things down a lot because of
; the extra checking done.  Note that magic-ev-fncall isn't an option, because
; state isn't available in funcall-w.

(defttag :ev-fncall-w-ok)
(remove-untouchable acl2::ev-fncall-w t)
(defttag nil)
(defun funcall-w (fn args ctx w)
  (declare (xargs :mode :program))
  (b* (((mv erp result) (acl2::ev-fncall-w fn args w nil nil t nil t))
       ((when erp)
        (er hard? ctx "~s0" (to-string1 (car result) (cdr result)))))
    result))
(push-untouchable acl2::ev-fncall-w t)

;expand-lambda : pseudo-termp -> pseudo-termp (without lambdas)
(mutual-recursion
 (defun expand-lambda (term)
   (declare (xargs :verify-guards nil :guard (pseudo-termp term)))
   (cond ((acl2::variablep term) term)
         ((acl2::fquotep term) term)
         ((eq (acl2::ffn-symb term) 'acl2::hide) term)
         (t
          (let* ((expanded-args (expand-lambda-lst (fargs term)))
                 (fn (acl2::ffn-symb term)))
            (cond ((acl2::flambdap fn) ;get rid of the lambda application
                   (acl2::subcor-var (acl2::lambda-formals fn)
                                     expanded-args
                                     (expand-lambda (acl2::lambda-body fn))))
                  (t (acl2::cons-term fn expanded-args)))))))

 (defun expand-lambda-lst (term-lst)
   (declare (xargs :guard (pseudo-term-listp term-lst)))
   (cond ((endp term-lst) '())
         (t (cons (expand-lambda (car term-lst))
                  (expand-lambda-lst (cdr term-lst)))))))

(defun separate-kwd-args (args defs-ans)
  (declare (xargs :guard (true-listp defs-ans)))
  (if (atom args)
    (mv defs-ans nil)
    (if (keyword-value-listp args)
;all defs appear before keyword args
        (mv defs-ans args)
      (separate-kwd-args (cdr args)
                         (append defs-ans (list (car args)))))))

; nat * nat -> (listof nat)
(defun make-numlist-from (curr size)
;make a list of size natural numbers starting from curr
  (declare (xargs :guard (and (natp curr) (natp size))))
  (if (zp size)
      '()
    (cons curr (make-numlist-from (1+ curr) (1- size)))))

(mutual-recursion
 (defun keep-names (texp)
   (cond ((atom texp) texp)
         ((possible-constant-value-p texp) texp)
         ((not (true-listp texp)) (car texp))
         (t (cons (car texp) (keep-names-lst (cdr texp))))))

 (defun keep-names-lst (texps)
   "collect names from all named texps"
   (if (atom texps)
       nil
     (cons (keep-names (car texps))
           (keep-names-lst (cdr texps))))))

(mutual-recursion
 (defun remove-names (texp)
   (cond ((atom texp) texp)
         ((possible-constant-value-p texp) texp)
         ((not (true-listp texp)) (cdr texp))
         (t (cons (car texp) (remove-names-lst (cdr texp))))))

 (defun remove-names-lst (texps)
   "remove names from all named texps"
   (if (atom texps)
       nil
     (cons (remove-names (car texps))
           (remove-names-lst (cdr texps))))))

(defmacro commentary (yes &rest args)
  `(value-triple
    (prog2$
     (cw? ,yes ,@args)
     :invisible)))

(defloop pair-prefix (prefix xs)
  (declare (xargs :guard (true-listp xs)))
  (for ((x in xs)) (collect (cons prefix x))))

;copied from std/util/support
(defun extract-keywords
    (ctx         ; context for error messages
     legal-kwds  ; what keywords the args are allowed to contain
     args        ; args that the user supplied
     kwd-alist   ; accumulator alist of extracted keywords to values
     ok-dup-kwds ; keywords that can have duplicates
     )
  "Returns (mv kwd-alist other-args)"
  (declare (xargs :guard (and (symbol-listp legal-kwds)
                              (no-duplicatesp legal-kwds)
                              (alistp kwd-alist)
                              (symbol-listp ok-dup-kwds))))
  (b* (((when (atom args))
        (mv (revappend kwd-alist nil) args))
       (arg1 (first args))
       ((unless (keywordp arg1))
        (b* (((mv kwd-alist other-args)
              (extract-keywords
               ctx legal-kwds (cdr args) kwd-alist ok-dup-kwds)))
          (mv kwd-alist (cons arg1 other-args))))
       ((unless (member arg1 legal-kwds))
        (er hard? ctx (concatenate 'string
                            "~x0: invalid keyword ~x1."
                            (if legal-kwds
                                "  Valid keywords: ~&2."
                              "  No keywords are valid here."))
               ctx arg1 legal-kwds)
        (mv nil nil))
       ((when (atom (rest args)))
        (er hard? ctx "~x0: keyword ~x1 has no argument." ctx arg1)
        (mv nil nil))
       ((when (and (not (member-equal arg1 ok-dup-kwds))
                   (assoc arg1 kwd-alist)))
        (er hard? ctx "~x0: multiple occurrences of keyword ~x1." ctx arg1)
        (mv nil nil))
       (value (second args))
       (kwd-alist (acons arg1 value kwd-alist)))
    (extract-keywords ctx legal-kwds (cddr args) kwd-alist ok-dup-kwds)))

;; (defstub is-disjoint (* * *) => *)
;; (defstub is-subtype (* * *) => *)
;; (defstub is-alias (* * *) => *)

(defstub is-type-predicate (* *) => *)
(defstub is-a-typeName (* *) => *)
;; (defstub is-a-custom-type (* *) => *)

(defstub forbidden-names () => *)

(defun forbidden-names-builtin () '(defdata::x acl2::x acl2s::x))
(defattach forbidden-names forbidden-names-builtin)

(defun remove1-assoc-all (key alst)
  "delete from alst all entries with key"
  (declare (xargs :guard (alistp alst)))
  (if (endp alst)
      '()
    (if (equal key (caar alst))
        (remove1-assoc-all key (cdr alst))
      (cons (car alst)
            (remove1-assoc-all key (cdr alst))))))

(defun union-alist2 (al1 al2)
  "union ke-val entries of al1 with al2, with al1 entries taking preference."
  (declare (xargs :guard (and (alistp al1)
                              (alistp al2))))
  (if (endp al1)
      al2
    (cons (car al1)
          (union-alist2 (cdr al1) (remove1-assoc-all (caar al1) al2)))))

(defun alist-equiv (A1 A2)
  (declare (xargs :guard (and (alistp A1)
                              (alistp A2))))
  (if (endp A1)
      (endp A2)
    (b* ((key (caar A1)))
      (and ;(equal (get1 key A1) (get1 key A2))
       (equal (assoc-equal key A1) (assoc-equal key A2))
       (alist-equiv (remove1-assoc-all key A1) (remove1-assoc-all key A2))))))

(defloop collect-declares (xs)
  (for ((x in xs)) (append (and (consp x) (equal 'ACL2::DECLARE (car x))
                                (true-listp x) (cdr x)))))

(defun extract-guard-from-edecls (edecls)
  "edecls is list of forms which can occur inside a declare form i.e. the di in (declare d1 ... dn)"
  (declare (xargs :guard (true-listp edecls)))
  (if (endp edecls)
      t
    (if (and (consp (car edecls))
             (eq (caar edecls) 'ACL2::XARGS)
             (keyword-value-listp (cdar edecls))
             (assoc-keyword :guard (cdar edecls)))
        (or (cadr (assoc-keyword :guard (cdar edecls))) 't)
      (extract-guard-from-edecls (cdr edecls)))))

#|

PETE: seems like this is not used. If used, have to
fix s+ form so that it has access to pkg.

(defmacro acl2s::defun-attach (&rest args)
  "generate a defun with suffix -builtin and attach it to name"
  (b* ((name (car args))
       ((unless (proper-symbolp name))
        (er hard 'defun-attach "~| ~x0 should be a proper name symbol.~%" name))
       (pkg (extract-kwd-val :pkg args))
       (b-name (s+ name "-BUILTIN" :pkg pkg))
       (formals (cadr args))
       ;(formal-stars (make-list (len formals) :initial-element 'ACL2::*))
       (guard (extract-guard-from-edecls (collect-declares args))))
    `(PROGN
      (DEFUN ,b-name . ,(cdr args))
      (VERIFY-GUARDS ,b-name)
      (encapsulate
       ((,name ,formals t :guard ,guard))
       (local (defun ,name ,formals
                (declare (xargs :guard ,guard))
                (declare (ignorable . ,formals))
                (,b-name . ,formals))))
      (DEFATTACH ,name ,b-name))))

|#

(defun convert-listpairs-to-conspairs (listpairs)
  (declare (xargs :guard (acl2::symbol-doublet-listp listpairs)))
  (if (endp listpairs)
    nil
    (cons (let* ((lstpair (car listpairs))
                 (fst (car lstpair))
                 (snd (cadr lstpair)))
            (cons fst snd))
          (convert-listpairs-to-conspairs (cdr listpairs)))))

; self-explanatory
; convert ((a . b) ...) to ((a b) ...)
(defun convert-conspairs-to-listpairs (conspairs)
  (declare (xargs :guard (symbol-alistp conspairs)))
  (if (endp conspairs)
    nil
    (cons (let* ((conspair (car conspairs))
                 (fst (car conspair))
                 (snd (cdr conspair)))
            (list fst snd))
          (convert-conspairs-to-listpairs (cdr conspairs)))))

;; 2nd copy, original in builtin-combinators.lisp
(defun get-tau-int (domain rexp)
  (declare (xargs :verify-guards t))
  (let ((dom (if (eq domain 'acl2s::integer)
                 'acl2::integerp
               'acl2::rationalp)))
  (case-match rexp
    ((lo lo-rel-sym '_ hi-rel-sym hi)
     (b* ((lo-rel (eq lo-rel-sym '<))
          (hi-rel (eq hi-rel-sym '<))
          (lo (and (rationalp lo) lo))
          (hi (and (rationalp hi) hi)))
       (acl2::make-tau-interval dom lo-rel lo hi-rel hi))))))

(defloop flatten-ANDs (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (for ((term in terms)) (append (if (and (consp term) (eq (car term) 'ACL2::AND))
                                     (cdr term)
                                   (list term)))))

(mutual-recursion
;; code taken from structures.lisp in data-structures book.
 (defun get-vars1 (term ans)
   (declare (xargs :verify-guards nil
                   :guard (proper-symbol-listp ans)))
    (cond ((atom term) (if (proper-symbolp term)
                           (add-to-set-eq term ans)
                         ans))
          ((equal (car term) 'ACL2::QUOTE) ans)
          (t (get-vars1-lst (cdr term) ans))))

 (defun get-vars1-lst (terms ans)
   (declare (xargs :verify-guards nil
                   :guard (and (true-listp terms)
                               (proper-symbol-listp ans))))
   (if (endp terms)
       ans
     (get-vars1-lst (cdr terms) (get-vars1 (car terms) ans)))))

(defun get-vars (term)
  (declare (xargs :verify-guards nil))
  (get-vars1 term '()))

(defun filter-terms-with-vars (terms vars)
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-term-listp terms)
                              (proper-symbol-listp vars))))
  (if (endp terms)
      '()
    (if (subsetp-equal (get-vars (car terms)) vars)
        (cons (car terms) (filter-terms-with-vars (cdr terms) vars))
      (filter-terms-with-vars (cdr terms) vars))))

(defloop var-or-quoted-listp (xs)
  (declare (xargs :guard (true-listp xs)))
  (for ((x in xs)) (always (or (proper-symbolp x)
                               (rquotep x)))))

