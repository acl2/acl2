
(in-package "ACL2")

(defdoc aig
  ":doc-section aig
AIG library for ACL2.~/

An AIG (And/Inverter Graph) is a Boolean function representation that consists
of AND nodes and inversions.  We represent AIGs in ACL2 as cons trees, with the
following meanings.

T represents the constant-true function

NIL represents the constant-false function

Non-Boolean atoms represent Boolean variables (inputs)

A cons whose cdr is NIL represents the negation of its car, and

A cons whose cdr is non-NIL represents the AND of its car and cdr.

Basic functions for operating on AIGs include aig-not, aig-and, aig-or,
aig-ite, etc.  An AIG may be evaluated under an assignment to its variables
(represented as a fast alist binding those variables to Booleans) using
aig-eval.
~/~/")

;; AIGs.
;; an AIG is any of:

;; TRUE, represented as t
;; FALSE, represented as nil
;; a VARIABLE, represented as any atom other than t or nil.
;; an INV of one AIG, represented as a cons with nil cdr
;; an AND of two AIGs, represented as a cons of two AIGs.

;; (Thus every ACL2 object is an AIG.)

;; Note that these next two functions are provably equal to T.
(defn aigp (x)
  (or
   (atom x)
   (and (consp x) (null (cdr x)))
   (and (aigp (car x)) (aigp (cdr x))))
  )

(defn aig-listp (x)
  (if (consp x)
      (and
       (aigp (car x))
       (aig-listp (cdr x)))
    t))   

(defmacro aig-cases (x &key true false var inv and)
  `(let ((aig-cases-var ,x))
     (cond
      ((eq aig-cases-var t) ,true)
      ((eq aig-cases-var nil) ,false)
      ((atom aig-cases-var) ,var)
      ((eq (cdr aig-cases-var) nil) ,inv)
      (t ,and))))

(defn aig-not (x)
  (aig-cases
   x
   :true nil
   :false t
   :var (hons x nil)
   :inv (car x)
   :and (hons x nil)))

(defn aig-and (x y)
  (cond
   ((or (eq x nil) (eq y nil)) nil)
   ((eq x t) y)
   ((eq y t) x)
   ((hons-equal x y) x)
   ((and (consp y) (eq (cdr y) nil)
         (hons-equal (car y) x))
    nil)
   ((and (consp x) (eq (cdr x) nil)
         (hons-equal (car x) y))
    nil)
   (t (hons x y))))



(defstub aig-env-lookup-missing-output (name) nil)

(defun aig-env-lookup-missing-quiet (name)
  (declare (xargs :guard t) (ignore name))
  nil)


(defconst *aig-env-lookup-warn-missing-binding* t)

(defun aig-env-lookup-missing-complain (name)
  (declare (xargs :guard t))
  (and *aig-env-lookup-warn-missing-binding*
       (cw "~
WARNING: Missing variable binding ~x0 in AIG-ENV-LOOKUP; assigning T~%"
           name)))

(local (in-theory (disable (break$))))

(defun aig-env-lookup-missing-break (name)
  (declare (xargs :guard t))
  (and *aig-env-lookup-warn-missing-binding*
       (prog2$ (cw "~
WARNING: Missing variable binding ~x0 in AIG-ENV-LOOKUP; assigning T.
To avoid this break, run (AIG-ENV-LOOKUP-MISSING-ACTION action), where action
is NIL or :WARN.~%" name)
               (break$))))

(defmacro aig-env-lookup-missing-action (val)
  (case val
    ((nil) '(defattach aig-env-lookup-missing-output
              aig-env-lookup-missing-quiet))
    (:warn '(defattach aig-env-lookup-missing-output
              aig-env-lookup-missing-complain))
    (:break '(defattach aig-env-lookup-missing-output
               aig-env-lookup-missing-break))
    (t (er hard 'aig-env-lookup-missing-action
           "Expected argument NIL, :WARN, or :BREAK.~%"))))

(aig-env-lookup-missing-action :warn)


(defun aig-env-lookup (x al)
  (declare (Xargs :guard t))
  (let ((look (hons-get x al)))
    (if look
        (cdr look)
      (prog2$ (and *aig-env-lookup-warn-missing-binding*
                   (aig-env-lookup-missing-output x))
              t))))

;; AIG-EVAL: Evaluates an AIG to a Boolean, given a fast alist that maps each
;; variable to a Boolean.  (If any variable is not present in that alist, it is
;; assumed to be NIL.)
(defn aig-eval (x al)
  (aig-cases
   x
   :true t
   :false nil
   :var (and (aig-env-lookup x al) t)
   :inv (not (aig-eval (car x) al))
   :and (and (aig-eval (car x) al)
             (aig-eval (cdr x) al))))

(memoize 'aig-eval :condition '(consp x))

(defn faigp (x) (consp x))

(defn faig-listp (x)
  (if (consp x)
      (and
       (faigp (car x))
       (faig-listp (cdr x)))
    (null x))
  )
   
(in-theory (disable aig-listp faig-listp))

(defun faig-fix (x)
  (declare (xargs :guard t))
  (if (consp x) x '(t . t)))

(defun faig-fix-list (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (faig-fix (car x))
          (faig-fix-list (cdr x)))))

(defun faig-fix-alist (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (atom (car x))
        (faig-fix-alist (cdr x))
      (cons (cons (caar x) (faig-fix (cdar x)))
            (faig-fix-alist (cdr x))))))


(defun faig-eval (x env)
  (declare (Xargs :guard t))
  (if (atom x)
      '(t . t)
    (cons (aig-eval (car x) env)
          (aig-eval (cdr x) env))))

(defn faig-eval-pat (pat x al)
  (if pat
      (if (atom pat)
          (faig-eval x al)
        (cons (faig-eval-pat (car pat) (ec-call (car x)) al)
              (faig-eval-pat (cdr pat) (ec-call (cdr x)) al)))
    nil))



(defn aig-p (x)
  (aig-cases
   x
   :true t
   :false t
   :var t
   :inv (and (aig-p (car x))
             (hons-equal (aig-not (car x)) x))
   :and (and (aig-p (car x))
             (aig-p (cdr x))
             (hons-equal (aig-and (car x) (cdr x)) x))))

(memoize 'aig-p :condition '(and (consp x) (cdr x)))

(defn faig-patternp (pat x)
  (if pat
      (if (atom pat)
          (and (consp x)
               (aig-p (car x))
               (aig-p (cdr x)))
        (and (consp x)
             (faig-patternp (car pat) (car x))
             (faig-patternp (cdr pat) (cdr x))))
    t))



(defn aig-eval-pat (pat x al)
  (if pat
      (if (atom pat)
          (aig-eval x al)
        (cons (aig-eval-pat (car pat) (ec-call (car x)) al)
              (aig-eval-pat (cdr pat) (ec-call (cdr x)) al)))
    nil))

(defn faig-eval-list (x al)
  (if (atom x)
      nil
    (cons (faig-eval (car x) al)
          (faig-eval-list (cdr x) al))))

(defn aig-eval-list (x al)
  (if (atom x)
      nil
    (cons (aig-eval (car x) al)
          (aig-eval-list (cdr x) al))))

(defn aig-eval-alist (aig-al env)
  (if (atom aig-al)
      nil
    (if (consp (car aig-al))
        (cons (cons (caar aig-al) (aig-eval (cdar aig-al) env))
              (aig-eval-alist (cdr aig-al) env))
      (aig-eval-alist (cdr aig-al) env))))

(defn faig-eval-alist (faig-al env)
  (if (atom faig-al)
      nil
    (if (consp (car faig-al))
        (cons (cons (caar faig-al)
                    (faig-eval (cdar faig-al) env))
              (faig-eval-alist (cdr faig-al) env))
      (faig-eval-alist (cdr faig-al) env))))






;; AIG-NOT and AIG-AND are correct with respect to AIG-EVAL.
(defthm aig-eval-not
  (iff (aig-eval (aig-not x) al)
       (not (aig-eval x al))))

(defthm aig-eval-and
  (iff (aig-eval (aig-and x y) al)
       (and (aig-eval x al)
            (aig-eval y al))))

(in-theory (disable aig-and aig-not))



;; Derived operators OR, ITE, XOR, IFF and correctness theorems with respec to
;; AIG-EVAL
(defn aig-or (x y)
  (aig-not (aig-and (aig-not x) (aig-not y))))

(defthm aig-eval-or
  (iff (aig-eval (aig-or x y) al)
       (or (aig-eval x al)
           (aig-eval y al))))

(in-theory (disable aig-or))

(defn aig-ite (a b c)
  (cond ((hons-equal b c)
         b)
        ((eq b t)
         (aig-or a c))
        (t (aig-or (aig-and a b)
                   (aig-and (aig-not a) c)))))


(defthm aig-eval-ite
  (iff (aig-eval (aig-ite a b c) al)
       (if (aig-eval a al)
           (aig-eval b al)
         (aig-eval c al))))


(defn aig-xor (a b)
  (aig-or (aig-and a (aig-not b))
          (aig-and (aig-not a) b)))

(defn aig-iff (a b)
  (aig-or (aig-and a b)
          (aig-and (aig-not a) (aig-not b))))

(defthm aig-eval-xor
  (iff (aig-eval (aig-xor a b) al)
       (xor (aig-eval a al)
            (aig-eval b al))))

(defthm aig-eval-iff
  (iff (aig-eval (aig-iff a b) al)
       (iff (aig-eval a al)
            (aig-eval b al))))


(in-theory (disable aig-eval-xor aig-eval-iff aig-eval-ite))








;; Replaces some variables of X with other values.  If all variables in x are
;; keys in the alist and all their corresponding values are Boolean, this is
;; equivalent to aig-eval.  Otherwise, this is a function composition.
(defn aig-restrict (x al)
  (aig-cases
   x
   :true t
   :false nil
   :var (let ((a (hons-get x al)))
          (if a
              (cdr a)
            x))
   :inv (aig-not (aig-restrict (car x) al))
   :and (let ((a (aig-restrict (car x) al)))
          (and a (aig-and a (aig-restrict (cdr x) al))))))

(memoize 'aig-restrict :condition '(and (consp x) (cdr x)))

(defn aig-restrict-alist (x-alst al)
  (if (atom x-alst)
      nil
    (if (atom (car x-alst))
        (aig-restrict-alist (cdr x-alst) al)
      (cons (cons (caar x-alst)
                  (aig-restrict (cdar x-alst) al))
            (aig-restrict-alist (cdr x-alst) al)))))

(defthm alistp-of-aig-restrict-alist
  (alistp (aig-restrict-alist x-alst al)))


(defn aig-restrict-list (x al)
  (if (atom x)
      nil
    (cons (aig-restrict (car x) al)
          (aig-restrict-list (cdr x) al))))


(defn faig-restrict (x restr-al)
  (if (atom x)
      '(t . t)
    (cons (aig-restrict (car x) restr-al)
          (aig-restrict (cdr x) restr-al))))

(defn faig-restrict-pat (pat fpat al)
  (if pat
      (if (atom pat)
          (faig-restrict fpat al)
        (cons (faig-restrict-pat (car pat) (ec-call (car fpat)) al)
              (faig-restrict-pat (cdr pat) (ec-call (cdr fpat)) al)))
    nil))


(defn faig-restrict-alist (al comp-al)
  (if (atom al)
      nil
    (let ((rest (faig-restrict-alist (cdr al) comp-al)))
      (if (atom (car al))
          rest
        (cons (cons (caar al) (faig-restrict (cdar al) comp-al))
              rest)))))

(defn faig-restrict-alists (als restr-al)
  (if (atom als)
      nil
    (cons (faig-restrict-alist (car als) restr-al)
          (faig-restrict-alists (cdr als) restr-al))))






(defconst *aig-compose-warn-missing-binding* t)

(defn aig-compose (x al)
  (aig-cases
   x
   :true t
   :false nil
   :var (aig-env-lookup x al)
   :inv (aig-not (aig-compose (car x) al))
   :and (let ((a (aig-compose (car x) al)))
          (and a (aig-and a (aig-compose (cdr x) al))))))

(memoize 'aig-compose :condition '(and (consp x) (cdr x)))

(defn aig-compose-alist (x-alst al)
  (if (atom x-alst)
      nil
    (if (atom (car x-alst))
        (aig-compose-alist (cdr x-alst) al)
      (cons (cons (caar x-alst)
                  (aig-compose (cdar x-alst) al))
            (aig-compose-alist (cdr x-alst) al)))))

(defn aig-compose-list (x al)
  (if (atom x)
      nil
    (cons (aig-compose (car x) al)
          (aig-compose-list (cdr x) al))))


(defn faig-compose (x comp-al)
  (if (atom x)
      '(t . t)
    (cons (aig-compose (car x) comp-al)
          (aig-compose (cdr x) comp-al))))

(defn faig-compose-pat (pat fpat al)
  (if pat
      (if (atom pat)
          (faig-compose fpat al)
        (cons (faig-compose-pat (car pat) (ec-call (car fpat)) al)
              (faig-compose-pat (cdr pat) (ec-call (cdr fpat)) al)))
    nil))

(defn faig-compose-alist (al comp-al)
  (if (atom al)
      nil
    (let ((rest (faig-compose-alist (cdr al) comp-al)))
      (if (atom (car al))
          rest
        (cons (cons (caar al) (faig-compose (cdar al) comp-al))
              rest)))))








(defabbrev fast-alphorder (x y)
  (mbe :logic (alphorder x y)
       :exec
       (if (and (symbolp x)
                (symbolp y))
           (or (eq x y)
               (not (symbol-< y x)))
         (alphorder x y))))

(defun hons-alphorder-merge (a b)
  (declare (xargs :guard (and (atom-listp a)
                              (atom-listp b))
                  :guard-hints(("Goal" :in-theory (enable alphorder
                                                          symbol-<)))
                  :measure (+ (len a) (len b))))
  (cond ((atom a) b)
        ((atom b) a)
        ((equal (car a) (car b))
         (hons-alphorder-merge (cdr a) b))
        ((fast-alphorder (car b) (car a))
         (hons (car b) (hons-alphorder-merge a (cdr b))))
        (t (hons (car a) (hons-alphorder-merge (cdr a) b)))))

(memoize 'hons-alphorder-merge
         :condition '(or (consp a) (consp b))
         :inline nil)

(defthm atom-listp-hons-alphorder-merge
  (implies (and (atom-listp a)
                (atom-listp b))
           (atom-listp (hons-alphorder-merge a b)))
  :hints(("Goal" :in-theory (enable hons-alphorder-merge
                                    atom-listp))))

(defthm member-equal-hons-alphorder-merge
  (iff (member-equal k (hons-alphorder-merge a b))
       (or (member-equal k a)
           (member-equal k b))))



;; Collects the variable list of X.
(defun aig-vars (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (aig-cases
   x
   :true nil
   :false nil
   :var  (hons x nil)
   :inv (aig-vars (car x))
   :and (hons-alphorder-merge (aig-vars (car x))
                              (aig-vars (cdr x)))))

(defthm atom-listp-aig-vars
  (atom-listp (aig-vars x)))

(verify-guards aig-vars)

(memoize 'aig-vars :condition '(and (consp x) (cdr x)))








;; Translate Lisp-like terms into AIGs.
(mutual-recursion
 (defun logic-to-aig (tree)
   (declare (xargs :measure (acl2-count tree)
                   :guard t))
   (if (atom tree)
       tree
     (case (car tree)
       ((and or xor iff) (logic-to-aig-list (car tree) (cdr tree)))
       (nand (aig-not (logic-to-aig-list 'and (cdr tree))))
       (nor (aig-not (logic-to-aig-list 'or (cdr tree))))
       (implies (and (eql (len tree) 3)
                     (aig-or (aig-not (logic-to-aig (cadr tree)))
                             (logic-to-aig (caddr tree)))))
       (if (and (eql (len tree) 4)
                (aig-ite (logic-to-aig (cadr tree))
                         (logic-to-aig (caddr tree))
                         (logic-to-aig (cadddr tree)))))
       (not (and (eql (len tree) 2)
                 (aig-not (logic-to-aig (cadr tree))))))))
 (defun logic-to-aig-list (op trees)
   (declare (xargs :measure (acl2-count trees)
                   :guard t))
   (if (atom trees)
       (case op
         (xor nil)
         (iff t)
         (and t)
         (or nil))
     (let ((first (logic-to-aig (car trees)))
           (rest (logic-to-aig-list op (cdr trees))))
       (case op
         (xor (aig-xor first rest))
         (iff (aig-iff first rest))
         (and (aig-and first rest))
         (or (aig-or first rest)))))))

(memoize 'logic-to-aig :condition '(consp tree))



;---- some macros for aig-or/aig-and/... 
;do we want to rebalance it (make it less deep and smaller)?
; would rebalancing have any impact on zz-sat performance?
(defn aig-and-fn (lst)
  (if (consp lst)
      (if (consp (cdr lst))
          (list
           'aig-and
           (car lst)
           (aig-and-fn (cdr lst)))
        (car lst))
    t)
  )

(defmacro aig-and-macro (&rest args) (aig-and-fn args))

(defn aig-or-fn (lst)
  (if (consp lst)
      (if (consp (cdr lst))
          (list
           'aig-or
           (car lst)
           (aig-or-fn (cdr lst)))
        (car lst))
    nil)
  )

(defmacro aig-or-macro (&rest args) (aig-or-fn args))

(defn one-hot-fn (lst)
  (if (consp lst)
      (if (consp (cdr lst))
          `(aig-or
            (aig-and 
             ,(car lst) 
             (aig-not ,(aig-or-fn (cdr lst))))
            (aig-and
             (aig-not ,(car lst))
             ,(one-hot-fn (cdr lst))))
        (car lst))
    nil
    )
  )

(defmacro one-hot (&rest args) (one-hot-fn args))
  




(defn aig-implies (x y)
  ;; [Jared]: moved here from e4/recent.lisp, we probably want the usual
  ;; theorems about this, etc.
  (aig-not (aig-and x (aig-not y))))




(defn aig-and-list (x)
  (if (atom x)
      t
    (aig-and (car x) (aig-and-list (cdr x)))))

(defn aig-or-list (x)
  (if (atom x)
      nil
    (aig-or (car x) (aig-or-list (cdr x)))))

(defn aig-and-lists (a b)
  (if (or (atom a) (atom b))
      nil
    (cons (aig-and (car a) (car b))
          (aig-and-lists (cdr a) (cdr b)))))

(defn aig-or-lists (a b)
  (if (or (atom a) (atom b))
      nil
    (cons (aig-or (car a) (car b))
          (aig-or-lists (cdr a) (cdr b)))))

(defn aig-iff-lists (a b)
  (if (or (atom a) (atom b))
      nil
    (cons (aig-iff (car a) (car b))
          (aig-iff-lists (cdr a) (cdr b)))))

(defn aig-xor-lists (a b)
  (if (or (atom a) (atom b))
      nil
    (cons (aig-xor (car a) (car b))
          (aig-xor-lists (cdr a) (cdr b)))))

(defn aig-implies-lists (a b)
  (if (or (atom a) (atom b))
      nil
    (cons (aig-implies (car a) (car b))
          (aig-implies-lists (cdr a) (cdr b)))))

(defn aig-not-list (x)
  (if (atom x)
      nil
    (cons (aig-not (car X))
          (aig-not-list (cdr x)))))
