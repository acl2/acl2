#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")

;;Bunch of utility functions for use by datadef and test?
;;mostly copied from data.lisp and acl2-check.lisp

(acl2::begin-book t);$ACL2s-Preamble$|#


(in-package "CGEN")

(set-verify-guards-eagerness 2)
(include-book "std/util/bstar" :dir :system)
(include-book "acl2s/utilities" :dir :system)
;(include-book "basis")

;; PETE: add the global cgen::cgen-guard-checking to control how
; guard-checking is handled.
; The default value is :none, but set it to :all to get more error reporting.
; See below.

(defmacro get-cgen-guard-checking ()
  `(@ cgen::cgen-guard-checking))

(defmacro set-cgen-guard-checking (val)
  `(make-event (er-progn (acl2::assign cgen::cgen-guard-checking, val)
                         (value '(value-triple nil)))
               :check-expansion t))

(set-cgen-guard-checking :none)
; How to set guard-checking 
; (set-cgen-guard-checking :all)


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

(defmacro   debug-flag  (vl)
  `(> ,vl 3))

(defmacro   system-debug-flag ( vl)
  `(> ,vl 4))

(defmacro   verbose-stats-flag ( vl)
  `(> ,vl 2))

(defmacro   verbose-flag ( vl)
  `(> ,vl 1))

(defmacro   inhibit-output-flag ( vl)
  `(<= ,vl 0))


(defmacro   normal-output-flag ( vl)
  `(> ,vl 0))


;TODO: hide this macro in a function and there put a guard that prop should be a ACL2 symbol.
(defmacro acl2-getprop (name prop w &key default)
 `(getprop ,name ,prop ,default 'acl2::current-acl2-world ,w))




(defun or-list (lst)
  (if (atom lst)
    lst
    (or (car lst)
        (or-list (cdr lst)))))

(defun to-symbol-in-package (sym pkg-name)
  (declare (xargs :guard (and (symbolp sym)
                              (pkgp pkg-name))))
  (acl2s::fix-intern$ (symbol-name sym) pkg-name))

(defun to-symbol-in-package-lst (sym-lst pkg)
  (declare (xargs :guard (and (symbol-listp sym-lst)
                              (pkgp pkg))))
  (if (endp sym-lst)
      nil
    (cons (to-symbol-in-package (car sym-lst) pkg)
          (to-symbol-in-package-lst (cdr sym-lst) pkg))))




;general
(defun list-up-lists (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2)
                              (= (len l1) (len l2)))))
  "same as listlis"
  (if (endp l1)
    nil
    (cons (list (car l1) (car l2))
          (list-up-lists (cdr l1) (cdr l2)))))


(verify-termination LEGAL-VARIABLE-OR-CONSTANT-NAMEP)
(verify-termination legal-constantp)
;;-- convert function lambda-keywordp from :program mode to :logic mode
(verify-termination acl2::lambda-keywordp)
(verify-guards  acl2::lambda-keywordp)
(verify-guards legal-constantp)

(defun proper-symbolp (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (or (keywordp x);a keyword
                (booleanp x);t or nil
                (legal-constantp x)))))


(defun proper-symbol-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (null xs)
    (and (proper-symbolp (car xs))
         (proper-symbol-listp (cdr xs)))))




;;--check if x if a keyword list
(defun keyword-listp (x)
  (if (consp x)
    (and (keywordp (car x))
         (keyword-listp (cdr x)))
    (null x)))




;;-- evaluates expr and returns its value if expr does not return a multi-value answer
(defun trans-eval-single-value (expr ctx state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (acl2::state-global-let*
;   ((acl2::guard-checking-on :none))
;; PETE: now controlled by the global cgen::cgen-guard-checking
   ((acl2::guard-checking-on (@ cgen-guard-checking)))
   (er-let* ((ans (trans-eval expr ctx state t)));for now aok is t
     (if (equal (car ans) '(nil))
       (value (cdr ans))
       (er soft ctx "Expected a single return value in evaluation of ~x0."
           expr)))))

(local (defthm union-true-lists

         (implies (and (true-listp l1)
                       (true-listp l2))
                  (true-listp (union-equal l1 l2)))))

(defun union-lsts (lsts)
  (declare (xargs :mode :logic
                  :guard (true-list-listp lsts)))
  (if (endp lsts)
    nil
    (union-equal (car lsts)
                 (union-lsts (cdr lsts)))))

(defun assoc-lst (keys alist)
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (endp keys)
    nil
    (cons (assoc-equal (car keys) alist)
          (assoc-lst (cdr keys) alist))))

(defun flatten (b lst&)
  (declare (xargs :guard (true-listp lst&)))
  (if (atom b)
    (cons b lst&)
    (flatten (car b) (flatten (cdr b) lst&))))

;from the members of an union expression, get the constituents
;that are non-recursive.
(defthm flatten-is-true-list1
  (implies (true-listp lst)
           (true-listp (flatten b lst)))
  :hints (("Goal" :in-theory (enable flatten))))



(defun mem-tree (x tree)
  (declare (xargs :guard (symbolp x)))
  (if (atom tree)
    (eq x tree)
    (or (mem-tree x (car tree))
        (mem-tree x (cdr tree)))))

;; (mutual-recursion
;;  (defun defbodyp (x)
;;    (or (symbolp x)
;;        (possible-constant-value-p x)
;;        (defbody-listp (cdr x))))
;;  (defun defbody-listp (xs)
;;    (if (atom xs)
;;      (equal xs nil)
;;      (and (defbodyp (car xs))
;;           (defbody-listp (cdr xs))))))

(include-book "misc/total-order" :dir :system)

(defun order-two-terms (t1 t2)
  (declare (xargs :guard t))
  (if (acl2::<< t1 t2);total order
      (mv t1 t2)
      (mv t2 t1)))

(defthm flatten-is-true-list
  (implies (true-listp lst)
           (true-listp (flatten b lst)))
  :rule-classes :type-prescription)
(in-theory (disable flatten))

(defun listof-alistp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (eq x nil))
        (t (and (alistp (car x))
                (listof-alistp (cdr x))))))

(defun true-list-symbol-alistp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (eq x nil))
        (t (and (symbol-alistp (car x))
                (true-list-symbol-alistp (cdr x))))))


;;self-explanatory
(defun symbol-doublet-list-listp (xs)
  (declare (xargs :guard t))
  (if (null xs)
    t
    (if (atom xs)
      nil
      (and (acl2::symbol-doublet-listp (car xs))
           (symbol-doublet-list-listp (cdr xs))))))

(defun symbol-alist-listp (x)
  (declare (xargs :guard T))
  (if (atom x)
    (null x)
    (and (symbol-alistp (car x))
         (symbol-alist-listp (cdr x)))))



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
  (cond ((atom x) nil)
        (t (cons (cadar x)
                 (strip-cadrs (cdr x))))))





;utility funs
;boolean-or: Expr * Expr * ... -> Bool
(defun boolean-or-macro (lst)
  (if (consp lst)
    (list 'if
          (car lst)
          't
          (boolean-or-macro (cdr lst)))
    'nil))
;boolean-or: Expr * Expr * ... -> Bool
(defmacro boolean-or (&rest args)
  (boolean-or-macro args))


;; (defun is-simple-type-hyp (term wrld)
;; ;is a simple type hypothesis, and if true returns
;; ; the type-name (not the predicate itself)
;;   (declare (xargs :verify-guards nil))
;;   (and (consp term)
;;        (eql (len term) 2)
;;        (atom (cadr term))
;;        (is-a-variablep (cadr term)) ;check wether its arg is sa variable
;;        (plausible-predicate-functionp (car term) wrld)
;;        (is-type-predicate (car term) wrld))) ;check if its a type predicate


;NEEDED BY EVERYONE:

; 12/4/2012, Matt K.: Omitting the definitions of nat-listp and
; acl2-number-listp, which are being built into ACL2.

;; (defun naturals-listp (x)
;;    (declare (xargs :guard t))
;;   (if (atom x)
;;     (null x)
;;     (and (natp (car x))
;;          (naturals-listp (cdr x)))))

; already in program mode:
(DEFUN POS-LISTP (acl2::L)
   (declare (xargs :guard t))
  (COND ((ATOM acl2::L) (EQ acl2::L NIL))
        (T (AND (POSP (CAR acl2::L))
                (POS-LISTP (CDR acl2::L))))))


;; ;is x permutation of y
;; (defun permutation (xs ys)
;;   (declare (xargs :verify-guards nil))
;;   (cond ((atom xs) (atom ys))
;;         (t (and (mem1 (car xs) ys) (permutation (cdr xs) (del (car xs) ys))))))

(defun get-value-from-keyword-value-list (key kv-lst)
  (declare (xargs :guard (keyword-value-listp kv-lst)))
  (second (assoc-keyword key kv-lst)))





;NOTE PACKAGES are very IMP while assuming that symbols are all ACL2. Like
;I just fixed a bug, where 'CONSTANT was assumed in ACL2 package, but due to
;this book being in DEFDATA PACKAGE, the equality check is against the symbol
;DEFDATA::CONSTANT which not same as ACL2::CONSTANT resulting in treating
;t and nil as variables.

;;list the free variables in a term
(mutual-recursion
;; code taken from structures.lisp in data-structures book.
 (defun get-free-vars1 (term ans)
   "A free variable is a symbol that is not a constant, i.e., it excludes T,
    NIL, and *CONST*, and keywords"
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil))
   (cond
    ((atom term) (if (proper-symbolp term)
                   (add-to-set-eq term ans)
                   ans))
    ((eq (car term) 'QUOTE) ans)
    (t (get-free-vars1-lst (cdr term) ans))))

 (defun get-free-vars1-lst (terms ans)
   (declare (xargs :guard (pseudo-term-listp terms)
                   :verify-guards nil))
   (cond
    ((endp terms) ans)
    (t (get-free-vars1-lst (cdr terms)
                           (get-free-vars1 (car terms) ans))))))

;auxiliary function for get-free-vars
(defun get-free-vars0 (form state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (if (acl2::termp form (w state))
; had a bug due to namespace change
     (value (get-free-vars1 form '()))
; translate the form into a term
     (er-let* ((term (acl2::translate form t nil t
                                'get-free-vars (w state) state)))
       (value (get-free-vars1 term '())))))

;get list of free variables in acl2 expression 'form'
(defmacro get-free-vars (form)
  `(get-free-vars0 ,form state))


(defun all-vars-lst (terms)
  "all free variables in list of terms"
  (declare (xargs :guard (pseudo-term-listp terms))) ;-> symbol-list)
  (all-vars1-lst terms '()))



;filter typ-exps which are typenames
(defun filter-alist-keys (alst wanted-keys)
  (declare (xargs :guard (and (alistp alst)
                              (true-listp wanted-keys))))
  (if (endp alst)
    nil
    (let* ((key (caar alst))
           (we-want-to-add  (member-equal key wanted-keys)))
      (if we-want-to-add
        (cons (car alst);cons the wanted entry
              (filter-alist-keys (cdr alst) wanted-keys))
        (filter-alist-keys (cdr alst) wanted-keys)))))


(defun remove-entry (key alist)
  (declare (xargs  :guard (and (alistp alist))))
  (if (endp alist)
    nil
    (if (equal key (caar alist))
      (cdr alist)
      (cons (car alist)
            (remove-entry key (cdr alist))))))

(defun remove-entry-lst (keys alist)
  (declare (xargs  :guard (and (true-listp keys)
                               (alistp alist))))
  (if (endp keys)
    alist
    (remove-entry-lst (cdr keys)
                      (remove-entry (car keys) alist))))

;get value of key in alist
(defun get-val (key alist)
  (declare (xargs  :guard (and (alistp alist))))
  (if (endp alist)
    nil
    (if (equal key (caar alist))
      (cdar alist)
      (get-val key (cdr alist)))))

;recurse on above
(defun get-val-lst (keys alist)
  (declare (xargs  :guard (and (true-listp keys)
                               (alistp alist))))
  (if (endp keys)
      nil
    (let ((found-val (get-val (car keys) alist)))
      (if found-val
        (cons found-val
              (get-val-lst (cdr keys) alist))
        (get-val-lst (cdr keys) alist)))))

;if val is different, then add it at the very end,
;do not update in place. Assumes unique entries
(defun remove-and-add-at-end-entry (key val alist)
  (declare (xargs  :guard (alistp alist)))
  (if (endp alist)
    (list (cons key val))
    (let* ((curr-entry (car alist))
           (curr-key (car curr-entry))
           (curr-val (cdr curr-entry)))
      (if (not (equal key curr-key))
        (cons curr-entry
              (remove-and-add-at-end-entry key val (cdr alist)))
        (if (equal val curr-val)
          alist;return unchanged
          (remove-and-add-at-end-entry key val (cdr alist)))))))

(defun remove-and-add-at-front-entry (key val alist)
  (declare (xargs  :guard (alistp alist)))
  (cons (cons key val)
        (remove-entry key alist)))

;put the key val entry in alist(overwrite)
;assumes unique entries
(defun put-entry (key val alist)
  (declare (xargs  :guard (alistp alist)))
  (if (endp alist)
    (list (cons key val))
    (if (equal key (caar alist))
      (cons (cons key val)
            (cdr alist))
      (cons (car alist)
            (put-entry key val (cdr alist))))))



;get key having value val in alist
(defun get-key (val alist)
  (declare (xargs  :guard (alistp alist)))
  (if (endp alist)
      nil
    (if (equal val (cdar alist))
      (caar alist)
      (get-key val (cdr alist)))))

;recurse on above, in order of vals.
(defun get-key-lst (vals alist)
  (declare (xargs  :guard (and (true-listp vals)
                               (alistp alist))))
  (if (endp vals)
    nil
    (let ((found-key (get-key (car vals) alist)))
      (if found-key
        (cons found-key
              (get-key-lst (cdr vals) alist))
        (get-key-lst (cdr vals) alist)))))

(defun get-var-from-i-or-is-lst (is var-i-alst)
  (declare (xargs  :verify-guards nil))
  (if (endp is)
    nil
    (let ((i (car is)))
      (if (atom i)
        (let ((found-key (get-key i var-i-alst)))
          (if found-key
            (cons found-key (get-var-from-i-or-is-lst (cdr is) var-i-alst))
            (get-var-from-i-or-is-lst (cdr is) var-i-alst)))
        ;else its a nat-listp
        (let ((found-keys (get-key-lst i var-i-alst)))
          (if found-keys
            (cons found-keys (get-var-from-i-or-is-lst (cdr is) var-i-alst))
            (get-var-from-i-or-is-lst (cdr is) var-i-alst)))))))


;returns list of all keys matching val
(defun get-all-keys1 (val alist ans)
  (declare (xargs  :guard (alistp alist)))
  (if (endp alist)
      ans;return answer
    (let* ((entry (car alist))
           (key (car entry))
           (value (cdr entry)))
      (if (equal val value)
        (get-all-keys1 val (cdr alist) (cons key ans));accumulate keys and recurse
      (get-all-keys1 val (cdr alist) ans)))));recurse

(defun get-all-keys (val alist)
  (declare (xargs  :guard (alistp alist)))
  (get-all-keys1 val alist nil))

;recurse on above, in order of vals.
(defun get-all-keys-lst (vals alist)
  (declare (xargs  :guard (and (true-listp vals)
                               (alistp alist))))
  (if (endp vals)
    nil
    (let ((found-keys (get-all-keys (car vals) alist)))
      (if found-keys
        (cons found-keys
              (get-all-keys-lst (cdr vals) alist))
        (get-all-keys-lst (cdr vals) alist)))))


;from Matt ;TODO get rid of this
(defun trans-eval2 (form ctx state)
  (declare (xargs :mode :program :stobjs state))
  (acl2::state-global-let*
;   ((acl2::guard-checking-on :none))
;; PETE: now controlled by the global cgen::cgen-guard-checking
   ((acl2::guard-checking-on (@ cgen-guard-checking)))
   (mv-let
    (erp trans bindings state)
    (acl2::translate1 form
                      t nil
                      t
                      'top-level (w state) state)
    (declare (ignore bindings))
    (cond
     (erp (mv t nil state))
     (t
      (let ((vars (all-vars trans)))
        (cond
         ((acl2::unknown-stobj-names vars t (w state)) ;;; known-stobjs = t
          (er soft 'top-level
              "Global variables, such as ~&0, are not allowed. See ~
               :DOC ASSIGN and :DOC @."
              (acl2::unknown-stobj-names vars t (w state)))) ;;; known-stobjs = t
         (t (acl2::ev-for-trans-eval trans nil ctx state t

; Matt K. mod: Added conservative value of new argument,
; user-stobjs-modified-warning.

                                     t)))))))))

;returns (cdr (cons translated-term value)) == value of term under bindings
(defun trans-eval-single-value-with-bindings (term bindings ctx state)
  (declare (xargs :mode :program :stobjs state))
  (acl2::state-global-let*
;   ((acl2::guard-checking-on :none))
;; PETE: now controlled by the global cgen::cgen-guard-checking
   ((acl2::guard-checking-on (@ cgen-guard-checking)))
   (er-let* ((term-val (acl2::simple-translate-and-eval term bindings nil
                                                        "" ctx (w state) state t)))
     (value (cdr term-val)))))

; this function basically creates in one go cons bindings
; for a list of variable names
(defun make-var-value-cons-bindings (var-lst ans)
  (declare (xargs :guard (and (symbol-listp var-lst)
                              (true-listp ans))))
  (if (endp var-lst)
    (cons 'list ans)
    (let ((var (car var-lst)))
      (make-var-value-cons-bindings (cdr var-lst)
                                    (append ans (list `(cons ',var ,var)))))))

; this function basically creates in one go list bindings for
; a list of variable names
(defun make-var-value-list-bindings (var-lst ans)
  (declare (xargs :guard (and (symbol-listp var-lst)
                              (true-listp ans))))
  (if (endp var-lst)
    (cons 'list ans)
    (let ((var (car var-lst)))
      (make-var-value-list-bindings
       (cdr var-lst)
       (append ans (list `(list ',var ,var)))))));changed to mimic let binding

; needed for simple-translate-and-eval only.
; Not needed now!!
(defun make-constant-value-cons-bindings (var-lst constant-val ans)
  (declare (xargs :guard (and (symbol-listp var-lst)
                              (true-listp ans))))
  (if (endp var-lst)
    (cons 'list ans)
    (let ((var (car var-lst)))
      (make-constant-value-cons-bindings
       (cdr var-lst)
       constant-val
       (append ans (list (cons var constant-val)))))))

;needed for trans-eval
(defun make-constant-value-let-bindings (var-lst constant-val ans)
  (declare (xargs :guard (and (symbol-listp var-lst)
                              (true-listp ans))))
  (if (endp var-lst)
    ans
    (let ((var (car var-lst)))
      (make-constant-value-let-bindings
       (cdr var-lst)
       constant-val
       (append ans (list (list var constant-val)))))))



;;self-explanatory
(defun convert-listpair-to-conspair-lst (listpairs)
  (declare (xargs :guard (acl2::symbol-doublet-listp listpairs)))
  (if (endp listpairs)
    nil
    (cons (let* ((lstpair (car listpairs))
                 (fst (car lstpair))
                 (snd (cadr lstpair)))
            (cons fst snd))
          (convert-listpair-to-conspair-lst (cdr listpairs)))))


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

(local
 (defthm convert-conspairs-to-listpairs-sig1
  (implies (symbol-alistp P)
           (symbol-doublet-listp (convert-conspairs-to-listpairs P)))
  :rule-classes (:rewrite :type-prescription :forward-chaining)))

(local
 (defthm symbol-doublet-listp-implication1
  (implies (and (symbol-doublet-listp A)
                (consp A))
           (and (consp (car A))
                (symbolp (caar A))
                (consp (cdr (car A)))
                (null (cddr (car A)))))
  :rule-classes (:forward-chaining)))

(defun count-occurrences (v lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
    0
    (if (equal v (car lst))
      (1+ (count-occurrences v (cdr lst)))
      (count-occurrences v (cdr lst)))))

(defun sym-eq-lst (syms1 syms2)
  (declare (xargs :guard (and (symbol-listp syms1)
                              (symbol-listp syms2))))
  "returns first symbol in syms2 which is in syms1 o.w nil"
  (if (endp syms2)
    nil
    (if (member-eq (car syms2) syms1)
      (car syms2)
      (sym-eq-lst syms1 (cdr syms2)))))

(defun insert-entry-after-key (entry k alst)
  (declare (xargs :guard (and (symbolp k)
                              (symbol-alistp alst))))
  "insert entry immediately after the pair in alst having key k"
  (if (endp alst)
   (list entry)
    (if (eq k (caar alst))
      (cons (car alst)
            (cons entry (cdr alst)))
      (cons (car alst)
           (insert-entry-after-key entry k (cdr alst))))))

(defun get-ordered-alst (keys alst ans)
  (declare (xargs :guard (and (true-listp keys) (alistp ans) (alistp alst))))
  "accumulate entries of alist in ans in the order of keys"
  (if (endp keys)
    ans
    (let ((at (assoc-equal (car keys) alst)))
      (if at
        (get-ordered-alst (cdr keys) alst (append ans (list at)))
        (get-ordered-alst (cdr keys) alst ans)))))


;filter all elements in lst that are IN in-lst
(defun filter-in (lst in-lst)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp in-lst))))
  (if (endp lst)
      nil
    (if (member-equal (car lst) in-lst)
        (cons (car lst) (filter-in (cdr lst) in-lst))
      (filter-in (cdr lst) in-lst))))
;filter all elements in lst that are NOT IN in-lst
(defun filter-not-in (lst in-lst)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp in-lst))))
  (if (endp lst)
      nil
    (if (not (member-equal (car lst) in-lst))
        (cons (car lst) (filter-in (cdr lst) in-lst))
      (filter-in (cdr lst) in-lst))))

;self-explanatory code.
;compose 2 finite functions basically
(defun compose-two-alists (a-b-alst b-c-alst)
  (declare (xargs :guard (and (alistp a-b-alst)
                              (alistp b-c-alst))))
   (if (endp a-b-alst)
    nil
    (let* ((a-b (car a-b-alst))
           (a (car a-b))
           (b (cdr a-b))
           (c (get-val b b-c-alst))
           (a-c (cons a c)))
      (cons a-c
            (compose-two-alists (cdr a-b-alst) b-c-alst)))))

;just like subst, but uses equal for comparision.
(defun subst-equal (new old tree)
  (cond ((equal tree old) new)
        ((atom tree) tree)
        (t (cons (subst-equal new old (car tree))
                 (subst-equal new old (cdr tree))))))


; Matt K. mod, 10/2017: Since ev-fncall-w is called in funcall my-ev-w but is
; now untouchable, a change is necessary.  Fortunately, cert.acl2 specifies
; :ttags :all, so we can introduce a trust tag to remove ev-fncall-w as an
; untouchable.  An alternate solution, not yet tried (at least by me), is to
; use ev-fncall-w! instead; but that might slow things down a lot because of
; the extra checking done.  Note that magic-ev-fncall isn't an option, because
; state isn't available in my-ev-w.

(defttag :ev-fncall-w-ok)
(remove-untouchable acl2::ev-fncall-w t)
(defttag nil)

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
      (b* (((mv cond-er cond) (my-ev-w (second term) alist ctx w hard-error-returns-nilp))
           ((when cond-er) (prog2$
                            (er hard ctx "Eval if condition failed~%")
                            (mv t term))))
        (if cond
            (my-ev-w (third term) alist ctx w hard-error-returns-nilp)
          (my-ev-w (fourth term) alist ctx w hard-error-returns-nilp)))
      )
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

(push-untouchable acl2::ev-fncall-w t) ; see Matt K. comment above

(defun trans-my-ev-w (form ctx w hard-error-returns-nilp)
(declare (xargs :mode :program
                :guard (and (plist-worldp w)
                            (booleanp hard-error-returns-nilp))))

  (mv-let
   (erp term x)
   (acl2::translate11 form nil nil nil nil nil nil
                ctx w (acl2::default-state-vars nil))
   (declare (ignore x))
   (if erp
       (if hard-error-returns-nilp
           (mv erp form)
         (prog2$
          (er hard ctx "~x0 could not be translated.~%" form)
          (mv erp form)))
     (my-ev-w term nil ctx w hard-error-returns-nilp))))

(defun all-vars-in-var-term-alst (alst)
  (declare (xargs :guard (alistp alst)
                  :verify-guards nil
                              ))
  ;key might be a term in case of generalization TODO.CHECK
;value is always a term, so we gets free-vars from them
  (union-eq (get-free-vars1-lst (strip-cars alst) nil)
            (get-free-vars1-lst (strip-cdrs alst) nil)))

;collect matching key-value pairs in an alist
;if var in 'vars' has a value in 'bindings', then collect it
(defun occurring-var-bindings (bindings vars)
  (declare (xargs :guard (and (true-listp vars)
                              (symbol-alistp bindings))))
  (if (endp vars)
    nil
    (let ((b (assoc-eq (car vars) bindings)))
      (if b
        (cons b (occurring-var-bindings bindings (cdr vars)))
        (occurring-var-bindings bindings (cdr vars))))))


; every cons(that is not quoted) and list in the value list
; bindings is quoted to avoid errors in evaluation
(defun quote-conses-and-symbols-in-bindings (val-bs)
;val-bs is kind of let binding
  (declare (xargs :guard (symbol-doublet-listp val-bs)))
  (if (endp val-bs)
    nil
    (b* (((list var val) (car val-bs)))
      (if (or (symbolp val)
              (and (consp val) (not (equal (car val) 'quote))))
        (cons (list var (list 'quote val))
              (quote-conses-and-symbols-in-bindings (cdr val-bs)))
        (cons (list var val)
              (quote-conses-and-symbols-in-bindings (cdr val-bs)))))))

(defun filter-symbol-keys-in-alist (alst)
  "Given an alist, it filters the entries that have
   symbols as the keys(first elem of cons)"
  (declare (xargs :guard (alistp alst)))
  (if (endp alst)
    nil
    (if (symbolp (caar alst))
      (cons (car alst) (filter-symbol-keys-in-alist (cdr alst)))
      (filter-symbol-keys-in-alist (cdr alst)))))#|ACL2s-ToDo-Line|#

(defun symbol-list-listp (v)
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (symbol-listp (car v))
         (symbol-list-listp (cdr v)))))

(defun order-var-te-alist. (A connected-vs-lst ans.)
  "helper to order-var-te-alist"
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-alistp A)
                              (symbol-list-listp connected-vs-lst)
                              (symbol-alistp ans.))))
  (if (endp connected-vs-lst)
      ans.
    (b* ((vs        (car connected-vs-lst))
         (tes       (get-val-lst vs A))
         (A-partial (pairlis$ vs tes)))
     (order-var-te-alist.  A (cdr connected-vs-lst)
                            (append ans. A-partial)))))

(defun order-var-te-alist (A connected-vs-lst)
  "order var-type-expression-dlist using connected-vertices information"
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-alistp A)
                              (symbol-list-listp connected-vs-lst))))

  (if (null connected-vs-lst)
      A
    (order-var-te-alist. A connected-vs-lst '() )))

(defun to-string (x)
  (declare (xargs :mode :program))
  (coerce (cdr (coerce (fms-to-string "~x0" (list (cons #\0 x))) 'list)) 'string))


;; (include-book "clause-processors/magic-ev" :dir :system)

;; (defthm strip-cdrs-car-len-decreases
;;   (implies (and (consp x)
;;                 (consp (car x)))
;;            (< (len (car (strip-cdrs x)))
;;               (len (car x))))
;;   :rule-classes :linear)


;; (defun map-if-filter-aux (map-fn if-fn filter-fn comb ls alist state)
;; ; map-fn is of arity (len ls)
;; ; if-fn is of arity (len ls) and returns boolean
;; ; filter-fn is a predicate
;; ; comb is one of collect, cons, append, return (similar to defloop)
;; ; ls is a list of lists
;; ; alist is a value binding for free variables
;;   (declare (xargs :stobjs (state)
;;                   :measure (len (car ls))
;;                   :verify-guards nil
;;                   :guard (and (member-eq comb '(acl2::collect cons append acl2::return))
;;                               (symbol-alistp alist)
;;                               (true-list-listp ls))))
;;   (if (or (atom ls)
;;           (atom (car ls)))
;;       nil
;;     (b* ((ctx 'map-filter-aux)
;;          (kwoted-ls (kwote-lst ls))
;;          ((mv err ans) (acl2::magic-ev `(,map-fn . ,kwoted-ls) alist state t t))
;;          ((when err) (er hard? ctx "~| Error in evaluation (magic-ev) fn:~x0, args:~x1~%" map-fn ls))
;;          ((mv err ok1p) (acl2::magic-ev `(,if-fn . ,kwoted-ls) alist state t t))
;;          ((when err) (er hard? ctx "~| Error in evaluation (magic-ev) fn:~x0, args:~x1~%" map-fn ls))
;;          ((mv err ok2p) (if (null filter-fn)
;;                            (mv nil t)
;;                          (acl2::magic-ev `(,filter-fn ',ans) alist state t t)))
;;          ((when err) (er hard? ctx "~| Error in evaluation (magic-ev) fn:~x0, arg:~x1~%" filter-fn ans)))

;;       (if (and ok1p ok2p)
;;           (case comb
;;             (acl2::collect (cons ans (map-if-filter-aux map-fn if-fn filter-fn comb (strip-cdrs ls) alist state)))
;;             (cons (cons ans (map-if-filter-aux map-fn if-fn filter-fn comb (strip-cdrs ls) alist state)))
;;             (append (append ans (map-if-filter-aux map-fn if-fn filter-fn comb (strip-cdrs ls) alist state)))
;;             (return ans)
;;             (otherwise (er hard? ctx "~| Unsupported combinator ~x0 ~%." comb)))
;;         (map-if-filter-aux map-fn if-fn filter-fn comb (strip-cdrs ls) alist state)))))

;; ; similar syntax to defloop of data-structures/utilities
;; ; but this is crippled, since macros are not allowed in when, unless and main-clause
;; (defmacro for (for-clauses main-clause &key (when 't) (unless 'nil))

;;   (b* ((iter-vars (strip-cars for-clauses))
;;        (list-vars (acl2::strip-caddrs for-clauses))
;;        (A (pairlis$ iter-vars (listlis (make-list (len for-clauses) :initial-element 'CAR) list-vars)))
;;        (kind (car main-clause))
;;        (main-expr (cadr main-clause))
;;        (map-lambda-fn `(LAMBDA ,list-vars
;;                                ;(DECLARE (IGNORABLE ,@list-vars))
;;                                ,(acl2::sublis-var A main-expr)))
;;        (if-free-vars (ALL-VARS1-LST (list when unless) '()))
;;        (- (cw "~%if-fv: ~x0" if-free-vars))
;;        (if-lambda-fn (if (null if-free-vars)
;;                        nil
;;                        `(LAMBDA ,list-vars
;; ;(DECLARE (IGNORABLE ,@list-vars))
;;                                 (IF ,when (NOT ,unless) 'NIL))))
;;        (free-vars (set-difference-eq (ALL-VARS1 main-expr '()) iter-vars))
;;        (A (pairlis$ (make-list (len free-vars) :initial-element 'CONS) (listlis (acl2::kwote-lst free-vars) free-vars)))
;;        (- (cw "~%A: ~x0" A))
;;        )
;;     `(map-if-filter-aux ',map-lambda-fn ',if-lambda-fn nil ',kind (list ,@list-vars) (list ,@A) state)))

#|
(trace$ map-if-filter-aux)

(let ((L1 '((1 a) (2 b) (45 c)))
      (L2 '(-1 -2 -3))
      (N 99))
  (for ((x in l1)
        (y in l2))
       (collect (cons (car x) (cons n y)))))
|#


;; chose 29 bits, because ACL2 uses signed 29 bits in its code!
(defun unsigned-29bits-p (x)
  (declare (xargs :guard T))
  (acl2::unsigned-byte-p 29 x))

(defun fixnump (x)
  (declare (xargs :guard T))
  (unsigned-29bits-p x))

;;; Style of accessing/changing defrec objects. The name of the object is
;;; always same as the name of the defrec, just like in stobjs. THis way we
;;; can drop in stobjs in their place!
(defmacro access (r a)
  `(acl2::access ,r ,r ,(acl2s::fix-intern-in-pkg-of-sym (symbol-name a) :key)))
(defmacro change (r a val )
  `(acl2::change ,r ,r ,(acl2s::fix-intern-in-pkg-of-sym (symbol-name a) :key) ,val))



;TODO from defdata-util. ideally just import these names
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

(defun cgen-dumb-negate-lit (term) ;hack
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (eq (car term) 'IF)
           (equal (third term) ''NIL)) ;got a not
      (second term)
    (acl2::dumb-negate-lit term)))


;; COPIED FROM acl2-sources/basis.lisp line 12607
;; because it is program mode there, and verify-termination needed more effort
;; than I could spare.
(defun cgen-dumb-negate-lit-lst (lst)
  (declare (xargs :guard (pseudo-term-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (cgen-dumb-negate-lit (car lst))
                 (cgen-dumb-negate-lit-lst (cdr lst))))))


(defun clause-mv-hyps-concl (cl)
  (declare (xargs :verify-guards nil))
  ;; (decl :sig ((clause) 
  ;;             -> (mv pseudo-term-list pseudo-term))
  ;;       :doc "return (mv hyps concl) which are proper terms given a
  ;; clause cl. Adapted from prettyify-clause2 in other-processes.lisp")
  (cond ((null cl) (mv '() ''NIL))
        ((null (cdr cl)) (mv '() (car cl)))
        ((null (cddr cl)) (mv (list (cgen-dumb-negate-lit (car cl)))
                              (cadr cl)))
        (t (mv (cgen-dumb-negate-lit-lst (butlast cl 1))
               (car (last cl))))))

(defun clausify-hyps-concl (hyps concl)
  (declare (xargs :verify-guards nil))
  ;; (decl :sig ((pseudo-term-list pseudo-term)
  ;;             -> clause)
  ;;       :doc "given hyps concl which are proper terms return equivalent
  ;; clause cl. inverse of clause-mv-hyps-concl")
  (cond ((and (endp hyps) (equal concl ''NIL)) 'NIL)
        ((endp hyps) (list concl))
        ((endp (cdr hyps)) (list (cgen-dumb-negate-lit (car hyps)) concl))
        (t (append (cgen-dumb-negate-lit-lst hyps)
                   (list concl)))))

(defun is-var-equality-hyp (term)
  (and (equal (len term) 3)
       (member-equal (car term) '(EQUAL EQ EQL = INT= STRING-EQUAL ACL2::HONS-EQUAL acl2s::==))
       (and (or (proper-symbolp (second term))
                (proper-symbolp (third term)))
            (not (equal (second term) (third term))))))
