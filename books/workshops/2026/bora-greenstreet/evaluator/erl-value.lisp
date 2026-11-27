; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "erl-ast")
(include-book "std/omaps/top" :dir :system)
(include-book "kestrel/fty/defsubtype" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

(set-induction-depth-limit 1)

; Erlang Values and Exceptions -------------------------------------------------

(set-well-founded-relation l<)

; Representation of the Erlang values returned by the evaluator.
; Remarks:
; - Strings are represented as list of integers
; - Pairs are not supported
; - Named funs are not supported
(fty::deftypes erl-val
  
  ; Erlang Values
  (fty::deftagsum erl-val
    ; Erlang return values
    (:integer ((val integerp)))
    (:atom ((val symbolp)))
    (:cons ((lst erl-vlst-p)))
    (:tuple ((lst erl-vlst-p)))
    (:fun ((arity natp)
           (cls erl-clause-list-p)
           (bind bind-p)
           (module symbolp)))
    (:excpt ((err-class erl-val-p) (err-reason erl-val-p) (err-stack erl-vlst-p)))
    ; For now, PIDs are represented as natural numbers
    (:pid ((id natp)))

    ; Internal return values
    (:none ())
    (:reject ((err stringp)))
    (:flimit ())

    ; Return when the process enters a receive
    ; klst must always be an erl-klst. This property
    ; is proven later.
    (:receive ((klst true-listp)))

    ; Return when a process fails to receive a message.
    (:blocked ())

    ; Return when a process requests to spawn another.
    (:spawn ((module symbolp) (fn symbolp) (args erl-vlst-p)))

    :measure (list (acl2-count x) 1))

  ; List of Erlang Values
  (fty::deflist erl-vlst
    :elt-type erl-val-p
    :true-listp t
    :measure (list (acl2-count x) 0))

  ; Reprsentation of Erlang bindings. Maps each variable to a value.
  (fty::defomap bind
    :key-type symbol
    :val-type erl-val
    :measure (list (acl2-count x) 0)))

; Erlang Message  --------------------------------------------------------------

; Process Identifier: PIDs are unique among processors that are alive on
; connected nodes. PID's of terminated processes can be reused.
; - For simplicity, PID's are represented as natural numbers for now.
(fty::defsubtype pid
  :supertype erl-val-p
  :restriction 
    (lambda (x) (equal (erl-val-kind x) :pid))
  :fix-value (make-erl-val-pid :id 0))

(defrule erl-val-kind-of-pid-p
  (implies (pid-p v) (equal (erl-val-kind v) :pid))
  :enable pid-p)

(fty::deflist pid-lst
  :elt-type pid
  :true-listp t)

(defrule erl-vlst-p-of-pid-lst
  (implies (pid-lst-p lst) (erl-vlst-p lst))
  :enable (pid-lst-p erl-vlst-p))

(fty::defset pid-set
  :elt-type pid
  :elementp-of-nil nil)

(defrule nil-not-in-pid-set
  (implies (pid-set-p pids) (not (set::in nil pids)))
  :use ((:instance pid-p-when-in-pid-set-p-binds-free-x (a nil) (x pids)))
  :disable pid-p-when-in-pid-set-p-binds-free-x)

; Map from PID to messages sent
(fty::defomap outbox
  :key-type pid-p
  :val-type erl-vlst-p)

; Utility Functions/Types ------------------------------------------------------

; Erlang boolean
(fty::defsubtype erl-boolean
  :supertype erl-val-p
  :restriction 
    (lambda (x) 
      (and (equal (erl-val-kind x) :atom)
           (or (equal (erl-val-atom->val x) 'true)
              (equal (erl-val-atom->val x) 'false))))
  :fix-value (make-erl-val-atom :val 'false))

; Erlang anonymous function
(fty::defsubtype erl-fun
  :supertype erl-val-p
  :restriction 
    (lambda (x)
      (and (equal (erl-val-kind x) :fun)))
  :fix-value 
    (make-erl-val-fun 
      :arity 0 
      :cls '((:none)) 
      :bind nil 
      :module 'local))

(defrule erl-val-when-erl-fun
  (implies
    (and (erl-val-p fun) (equal (erl-val-kind fun) :fun))
    (erl-fun-p fun))
  :enable erl-fun-p)

; Helper for implementing list substraction.
(define remove-first-of-each ((x erl-vlst-p) (lst erl-vlst-p))
  :returns (vlst erl-vlst-p)
  :measure (erl-vlst-count x)
  (b* ((x (erl-vlst-fix x))
       (lst (erl-vlst-fix lst)))      
      (if (endp x)
          lst
          (remove-first-of-each (cdr x) (remove1 (car x) lst :test 'equal)))))

; Turns a list of integers to a list of Erlang integers.
(define ints-to-erl-ints ((x integer-listp))
  :returns (vlst erl-vlst-p)
  :measure (len x)
  (b* ((x (integer-list-fix x))
       ((if (null x)) nil))
      (cons (make-erl-val-integer :val (car x))
            (ints-to-erl-ints (cdr x)))))

; Turns a string into the correponding Erlang integer list.
(define string=>erl-cons ((x stringp))
  :returns (v erl-val-p)
  (b* ((x (string x))
       (lst (string=>nats x))
       (erl-lst (ints-to-erl-ints lst)))
      (make-erl-val-cons :lst erl-lst))
  ///
    (more-returns
      (v (equal (erl-val-kind v) :cons)
      :name erl-val-kind-of-string=>erl-cons)))

; Obtain the arity of a clause-list. Return nil if all clauses do not
; have the same arity, or if x is nil. The intended use for this function
; is to find the arity of a function, given its clauses.
(define erl-clause-list->arity ((x erl-clause-list-p))
  :measure (len x)
  (b* ((x (erl-clause-list-fix x))
       ((if (null x)) nil)
       (arity (len (node-clause->cases (car x))))
       ((if (null (cdr x))) arity)
       (rest (erl-clause-list->arity (cdr x)))
       ((if (null rest)) nil)
       ((unless (equal rest arity)) nil))
      arity))

; Theorems ---------------------------------------------------------------------

; ; If a vlst has len > 2, its cdr is not nil.
; (defrule consp-of-cdr-of-erl-vlst
;   (implies (and (erl-vlst-p x) (> (len x) 1))
;            (consp (cdr x))))

; ; Appending two vlst will produce a vlst
; (defrule append-of-erl-vlst
;   (implies (and (erl-vlst-p vlst1) (erl-vlst-p vlst2))
;            (erl-vlst-p (append vlst1 vlst2))))

; ; nth of an erl-vlst is an erl-val
; (defrule nth-of-erl-vlst
;   (implies 
;     (and (erl-vlst-p vlst) 
;          (integerp n)
;          (>= n 0)
;          (< n (len vlst)))
;     (erl-val-p (nth n vlst))))

; ; A cons pair of two erl-vals is not an erl-val.
; ; This can be useful in a few places.
; (defrule cons-of-erl-val-p
;   (implies (erl-val-p v)
;            (not (erl-val-p (cons v x))))
;   :expand ((erl-val-p v) (erl-val-p (cons v x))))


; Utility Theorems/Functions ---------------------------------------------------

; These might be unnecessary after including the omap book.
; (defrule bind-update-lookup
;   (equal (omap::lookup s (omap::update s x m)) x)
;   :enable omap::lookup)

; (defrule bind-update-update-lookup
;   (implies
;     (not (equal s1 s2))
;     (equal (omap::lookup s2 (omap::update s1 x1 (omap::update s2 x2 m))) x2))
;   :enable omap::lookup)

; ; This is useful for theorems that reason about the value of an erl-val-integer. 
; (encapsulate nil
;   (local (include-book "std/lists/len" :dir :system))
;   (defrule erl-val-integer-of-car-and-cdr
;     (implies (and (erl-val-p x)
;                   (equal (erl-val-kind x) :integer)
;                   (equal (erl-val-integer->val x) v))
;              (equal x `(:integer ,v)))
;     :enable (erl-val-kind erl-val-integer->val erl-val-p)
;     :expand (true-listp (cdr x))
;     :rule-classes :forward-chaining))

; ; Predicate for a list of well-formed values.
; (define wf-vlst-p ((vlst erl-vlst-p))
;   :enabled t
;   :measure (len (erl-vlst-fix vlst))
;   (b* ((vlst (erl-vlst-fix vlst))
;        ((if (null vlst)) t))
;       (and (null (member (erl-val-kind (car vlst))
;                          '(:flimit :excpt :reject :blocked :receive)))
;            (wf-vlst-p (cdr vlst))))
  
;   ///
;     (defcong erl-vlst-equiv equal (wf-vlst-p vlst) 1
;       :hints (("Goal" :expand (wf-vlst-p vlst-equiv))))
    
;     (defrule non-receive-of-car-of-wf-vlst-p
;       (implies
;         (wf-vlst-p lst)
;         (not (equal (erl-val-kind (car lst)) :receive)))))