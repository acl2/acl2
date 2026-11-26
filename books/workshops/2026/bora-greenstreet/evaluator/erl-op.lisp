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
(include-book "erl-value")

(include-book "misc/total-order" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

; Arithemtic Erlang Operations -------------------------------------------------

; Remarks:
; - Floating point operations are not currently supported, so '/' is not implemented.
; - bitwise operations are not yet supported.
; - The '!' (send) operation is handled by the evaluator.

; Apply Erlang unary +.
; - Returns the badarith exception if the argument is not an integer.
(define erl-plus ((val erl-val-p))
  :returns (v erl-val-p)
  (b* ((val (erl-val-fix val))
       ((unless (equal (erl-val-kind val) :integer))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarith))))
      val)
  ///
    (defcong erl-val-equiv equal (erl-plus x) 1))

; Apply Erlang unary -.
; - Returns the badarith exception if the argument is not an integer.
(define erl-minus ((val erl-val-p))
  :returns (v erl-val-p)
  (b* ((val (erl-val-fix val))
       ((unless (equal (erl-val-kind val) :integer))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarith))))
      (make-erl-val-integer :val (* -1 (erl-val-integer->val val))))
  ///
    (defcong erl-val-equiv equal (erl-minus x) 1))

; Apply Erlang addition.
; - Returns the badarith exception if arguments are not integers.
(define erl-add ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (and (equal (erl-val-kind left) :integer)
                     (equal (erl-val-kind right) :integer)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarith))))
      (make-erl-val-integer :val (+ (erl-val-integer->val left)
                                    (erl-val-integer->val right))))
    ///
      (defcong erl-val-equiv equal (erl-add x y) 1)
      (defcong erl-val-equiv equal (erl-add x y) 2))

; Apply Erlang substraction.
; - Returns the badarith exception if arguments are not integers.
(define erl-sub ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (and (equal (erl-val-kind left) :integer) 
                     (equal (erl-val-kind right) :integer)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarith))))
      (make-erl-val-integer :val (- (erl-val-integer->val left)
                                    (erl-val-integer->val right))))
  ///
    (defcong erl-val-equiv equal (erl-sub x y) 1)
    (defcong erl-val-equiv equal (erl-sub x y) 2))

; Apply Erlang multiplication.
; - Returns the badarith exception if arguments are not integers.
(define erl-mul ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (and (equal (erl-val-kind left) :integer) 
                     (equal (erl-val-kind right) :integer)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarith))))
      (make-erl-val-integer :val (* (erl-val-integer->val left)
                                    (erl-val-integer->val right))))
    ///
      (defcong erl-val-equiv equal (erl-mul x y) 1)
      (defcong erl-val-equiv equal (erl-mul x y) 2))

; Apply Erlang integer division (div).
; - The result is rounded down to the largest integer less than the result.
; - Returns badarith if arguments are not integers or if there is division by 0.
(define erl-div ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless 
          (and (equal (erl-val-kind left) :integer) 
               (equal (erl-val-kind right) :integer)
               (not (equal (erl-val-integer->val right) 0))))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarith)))
       (left-val (erl-val-integer->val left))
       (right-val (erl-val-integer->val right)))
      (make-erl-val-integer :val (floor left-val right-val)))
  
  ///
    (defcong erl-val-equiv equal (erl-div x y) 1)
    (defcong erl-val-equiv equal (erl-div x y) 2))

; Apply Erlang integer remainder (rem).
; - Returns badarith if arguments are not integers or if there is division by 0.
(define erl-rem ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless 
          (and (equal (erl-val-kind left) :integer) 
               (equal (erl-val-kind right) :integer)
               (not (equal (erl-val-integer->val right) 0))))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarith)))
       (left-val (erl-val-integer->val left))
       (right-val (erl-val-integer->val right)))
      (make-erl-val-integer :val (rem left-val right-val)))
  ///
    (defcong erl-val-equiv equal (erl-rem x y) 1)
    (defcong erl-val-equiv equal (erl-rem x y) 2))

; Given an arithmetic binop, apply the corresponding Erlang operation.
(define apply-erl-arithm-binop ((op arithm-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (arithm-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((unless 
          (and (equal (erl-val-kind left) :integer) 
               (equal (erl-val-kind right) :integer)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarith))))
      (case op
        (+ (erl-add left right))
        (- (erl-sub left right))
        (* (erl-mul left right))
        (div (erl-div left right))
        (rem (erl-rem left right))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defcong arithm-binop-equiv equal (apply-erl-arithm-binop op x y) 1)
      (defcong erl-val-equiv equal (apply-erl-arithm-binop op x y) 2)
      (defcong erl-val-equiv equal (apply-erl-arithm-binop op x y) 3))

; Erlang Boolean Operations ----------------------------------------------------

; Apply Erlang 'not' on the given booelan.
; - Returns badarg if the argument is not a boolean.
(define erl-not ((val erl-val-p))
  :returns (v erl-val-p)
  (b* ((val (erl-val-fix val))
       ((unless (erl-boolean-p val))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarg))))
      (if (equal (erl-val-atom->val val) 'true)
          (make-erl-val-atom :val 'false)
          (make-erl-val-atom :val 'true)))
  :guard-hints (("Goal" :in-theory (enable erl-boolean-p)))
  
  ///
    (defcong erl-val-equiv equal (erl-not x) 1))

; Apply Erlang 'and' on the given booleans.
; - Returns badarg if arguments are not booleans.
(define erl-and ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (and (erl-boolean-p left) 
                     (erl-boolean-p right)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarg))))
      (if (and (equal (erl-val-atom->val left) 'true)
              (equal (erl-val-atom->val right) 'true))
          (make-erl-val-atom :val 'false)
          (make-erl-val-atom :val 'true)))
  :guard-hints (("Goal" :in-theory (enable erl-boolean-p)))
  
  ///
    (defcong erl-val-equiv equal (erl-and a b) 1)
    (defcong erl-val-equiv equal (erl-and a b) 2))

; Apply Erlang 'or' on the given booleans.
; - Returns badarg if arguments are not booleans.
(define erl-or ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (and (erl-boolean-p left) 
                     (erl-boolean-p right)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarg))))
      (if (or (equal (erl-val-atom->val left) 'true)
              (equal (erl-val-atom->val right) 'true))
          (make-erl-val-atom :val 'false)
          (make-erl-val-atom :val 'true)))
  :guard-hints (("Goal" :in-theory (enable erl-boolean-p)))
  
  ///
    (defcong erl-val-equiv equal (erl-or a b) 1)
    (defcong erl-val-equiv equal (erl-or a b) 2))

; Apply Erlang 'xor' on the given booleans.
; - Returns badarg if arguments are not booleans.
(define erl-xor ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless (and (erl-boolean-p left) 
                     (erl-boolean-p right)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarg))))
      (if (xor (equal (erl-val-atom->val left) 'true)
               (equal (erl-val-atom->val right) 'true))
          (make-erl-val-atom :val 'false)
          (make-erl-val-atom :val 'true)))
  :guard-hints (("Goal" :in-theory (enable erl-boolean-p)))
  
  ///
    (defcong erl-val-equiv equal (erl-xor a b) 1)
    (defcong erl-val-equiv equal (erl-xor a b) 2))

; Given a boolean binop, apply the corresponding Erlang operation.
(define apply-erl-bool-binop ((op bool-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (bool-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((unless 
          (and (erl-boolean-p left) (erl-boolean-p right)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarg))))
      (case op
        ('and (erl-and left right))
        ('or (erl-or left right))
        ('xor (erl-xor left right))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defcong bool-binop-equiv equal (apply-erl-bool-binop op x y) 1)
      (defcong erl-val-equiv equal (apply-erl-bool-binop op x y) 2)
      (defcong erl-val-equiv equal (apply-erl-bool-binop op x y) 3))

; Erlang Comparison Operators --------------------------------------------------

; Remarks:
; - Strings are represented as lists of integers. This is compatible with the
;   Erlang rules for equivalence. For example, "A" =:= [65] evaluates to true.
; - 0 and -0 are not considered equivalent by =:= in Erlang. This is currently
;   not supported.

; Helper for anonymous function comparison.
; The Erlang refernce manual gives an order for how functions can be compared
; with other terms. However, the manual does not specify how funs are compared
; with other funs. Experimentation shows that there is an ordering for funs --
; for example, funs in the same module are compared by mathcing their clauses,
; including line numbers, but this evaluator will leave fun comparison as undefined
; behavior in accordance with the Erlang manual.  
(encapsulate
  ; compare anonymous Erlang functions
  (((erl-fun-compare * *) => * 
      :formals (f1 f2) :guard (and (erl-fun-p f1) (erl-fun-p f2))))

  ; Witness function
  (local (define erl-fun-compare ((f1 erl-fun-p) (f2 erl-fun-p))
    :enabled t
    (b* ((f1 (erl-fun-fix f1))
         (f2 (erl-fun-fix f2))
         ((if (<< f2 f1)) 1)
         ((if (<< f1 f2)) -1))
        0)))

  ; Constarints
  (defthm erl-fun-compare-is-integer (integerp (erl-fun-compare f1 f2)))
  (defthm erl-fun-compare-is-irreflexive (equal (erl-fun-compare f f) 0))
  (defthm erl-fun-compare-is-transitive 
    (implies (and (equal (erl-fun-compare f1 f2) -1)
                  (equal (erl-fun-compare f2 f3) -1))
             (equal (erl-fun-compare f1 f3) -1)))
  (defthm erl-fun-compare-is-asymmteric
    (implies (equal (erl-fun-compare f1 f2) 1)
             (equal (erl-fun-compare f2 f1) -1)))
  (defthm erl-fun-compare-trichotomy
    (or (equal (erl-fun-compare f1 f2) 1)
        (equal (erl-fun-compare f1 f2) 0)
        (equal (erl-fun-compare f1 f2) -1)))
  
  (defcong erl-fun-equiv equal (erl-fun-compare f g) 1)
  (defcong erl-fun-equiv equal (erl-fun-compare f g) 2))

; ACL2 total ordering is used for the execution of erl-fun-compare.
(define total-order-fun-compare ((f1 erl-fun-p) (f2 erl-fun-p))
  (b* ((f1 (erl-fun-fix f1))
       (f2 (erl-fun-fix f2))
       ((if (<< f2 f1)) 1)
       ((if (<< f1 f2)) -1))
      0)
  ///
  (defattach (erl-fun-compare total-order-fun-compare)))

; Helper to compare Erlang atoms (which must first be converted to integer lists). 
; - Return 0 if they are equal
; - Return 1 if left is greater than right
; - Return -1 if left is smaller than right
(define erl-compare-atom-string ((l integer-listp) (r integer-listp))
  :returns (i integerp)
  :measure (len (integer-list-fix l))
  (b* ((l (integer-list-fix l))
       (r (integer-list-fix r)))
      (cond 
        ((and (null l) (null r)) 0)
        ((null l) -1)
        ((null r) 1)
        ((> (car l) (car r)) 1)
        ((< (car l) (car r)) -1)
        (t (erl-compare-atom-string (cdr l) (cdr r))))))

; Compare Erlang terms
; - Return 0 if they are equal
; - Return 1 if left is greater than right
; - Return -1 if left is smaller than right
; - If an arg is not a valid Erlang value, return 3.
;
; The arguments can be of different data types. The following order is defined
; in the Erlang reference manual:
; number < atom < reference < fun < port < pid < tuple < map < nil < list < bit string
;
; Remark: 
; fun comparisons, though not documented in the Erlang manual, are allowed in Erlang.
; Since this is not a very practical feature of Erlang, it will not be supported for now. 
;
(defines erl-comparison
  :flag-local nil
  (define erl-compare ((left erl-val-p) (right erl-val-p))
    :returns (i integerp) 
    :measure (erl-val-count left)
    (b* ((left (erl-val-fix left))
         (right (erl-val-fix right)))
        (fty::multicase ((erl-val-case left) (erl-val-case right))
          ((:flimit &) 3)
          ((& :flimit) 3)
          ((:reject &) 3)
          ((& :reject) 3)
          ((:none &) 3)
          ((& :none) 3)
          ((:excpt &) 3)
          ((& :excpt) 3)
          ((:receive &) 3)
          ((& :receive) 3)
          ((:blocked &) 3)
          ((& :blocked) 3)
          ((:integer :integer) 
           (let ((lv (erl-val-integer->val left))
                 (rv (erl-val-integer->val right)))
            (cond ((> lv rv) 1)
                  ((= lv rv) 0)
                  ((< lv rv) -1))))
          ((:integer &) -1)
          ((:atom :atom) 
           (b* ((lv (erl-val-atom->val left))
                 (rv (erl-val-atom->val right))
                 (l (string=>nats (symbol-name lv)))
                 (r (string=>nats (symbol-name rv))))
                 (erl-compare-atom-string l r)))
          ((:atom :integer) 1)
          ((:atom &) -1)
          ((:fun :fun) (erl-fun-compare left right))
          ((:fun :integer) 1)
          ((:fun :atom) 1)
          ((:fun &) -1)
          ((:tuple :tuple)
           (let ((llst (erl-val-tuple->lst left))
                 (rlst (erl-val-tuple->lst right))) 
             (cond 
               ((> (len llst) (len rlst)) 1)
               ((> (len rlst) (len llst)) -1)
               (t (erl-compare-by-elements llst rlst)))))
          ((:tuple :integer) 1)
          ((:tuple :atom) 1)
          ((:tuple :fun) 1)
          ((:tuple &) -1)
          ((:cons :cons) 
           (let ((llst (erl-val-cons->lst left))
                 (rlst (erl-val-cons->lst right)))
            (erl-compare-by-elements llst rlst)))
          ((:cons :integer) 1)
          ((:cons :atom) 1)
          ((:cons :fun) 1)
          ((:cons :tuple) 1)
          ((:cons &) -1)
          (:otherwise 3))))

  (define erl-compare-by-elements ((left erl-vlst-p) (right erl-vlst-p))
    :returns (i integerp)
    :measure (erl-vlst-count left)
    (b* ((left (erl-vlst-fix left))
         (right (erl-vlst-fix right)))
        (cond 
          ((and (null left) (null right)) 0)
          ((null left) -1)
          ((null right) 1)
          (t (let ((curr (erl-compare (car left) (car right))))
                  (cond 
                    ((equal curr 1) 1)
                    ((equal curr -1) -1)
                    ((equal curr 0) (erl-compare-by-elements (cdr left) (cdr right)))
                    (t curr))))))))

(defcong erl-val-equiv equal (erl-compare a b) 1
  :hints (("Goal" :expand ((erl-compare a b) (erl-compare a-equiv b)))))
(defcong erl-val-equiv equal (erl-compare a b) 2
  :hints (("Goal" :expand ((erl-compare a b) (erl-compare a b-equiv)))))

; Given a comparison binop, apply the corresponding Erlang operation.
(define apply-erl-comp-binop ((op comp-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (comp-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       (comp (erl-compare left right))
       ((if (equal comp 3)) (make-erl-val-reject :err "erl-compare called with inavlid term.")))
      (case op
        (== 
          (if (equal comp 0)
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (/= 
          (if (not (equal comp 0))
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (=< 
          (if (or (equal comp 0) (equal comp -1))
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (< 
          (if (equal comp -1)
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (>=
          (if (or (equal comp 0) (equal comp 1))
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (>
          (if (equal comp 1)
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (=.=
          (if (equal left right)
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (=/=
          (if (not (equal left right))
              (make-erl-val-atom :val 'true)
              (make-erl-val-atom :val 'false)))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defcong comp-binop-equiv equal (apply-erl-comp-binop op x y) 1)
      (defcong erl-val-equiv equal (apply-erl-comp-binop op x y) 2)
      (defcong erl-val-equiv equal (apply-erl-comp-binop op x y) 3))

; Apply Erlang List Operations -------------------------------------------------

; Apply Erlang list concatenation (++).
; Since pairs are not supported currently, the arguments must be lists.
; - Returns badarg if the arguments are not lists.
(define erl-concat ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless 
          (and (equal (erl-val-kind left) :cons) 
               (equal (erl-val-kind right) :cons)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarg)))
       (left-lst (erl-val-cons->lst left))
       (right-lst (erl-val-cons->lst right)))
      (make-erl-val-cons :lst (append left-lst right-lst)))
  
  ///
    (defcong erl-val-equiv equal (erl-concat l1 l2) 1)
    (defcong erl-val-equiv equal (erl-concat l1 l2) 2))

; Apply Erlang list substraction (--).
; Since pairs are not supported currently, the arguments must be lists.
; - Returns badarg if the arguments are not lists.
(define erl-substract ((left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((left (erl-val-fix left)) 
       (right (erl-val-fix right))
       ((unless 
          (and (equal (erl-val-kind left) :cons) 
               (equal (erl-val-kind right) :cons)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarg)))
       (left-lst (erl-val-cons->lst left))
       (right-lst (erl-val-cons->lst right)))
      (make-erl-val-cons :lst (remove-first-of-each right-lst left-lst)))
  ///
    (defcong erl-val-equiv equal (erl-substract l1 l2) 1)
    (defcong erl-val-equiv equal (erl-substract l1 l2) 2))

; Given a list-op, apply the corresponding Erlang operation.
(define apply-erl-list-op ((op list-op-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (list-op-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right))
       ((unless 
          (and (equal (erl-val-kind left) :cons)
               (equal (erl-val-kind right) :cons)))
        (make-erl-val-excpt
          :err-class (make-erl-val-atom :val 'error)
          :err-reason (make-erl-val-atom :val 'badarg))))
      (case op
        (++ (erl-concat left right))
        (-- (erl-substract left right))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defcong list-op-equiv equal (apply-erl-list-op op x y) 1)
      (defcong erl-val-equiv equal (apply-erl-list-op op x y) 2)
      (defcong erl-val-equiv equal (apply-erl-list-op op x y) 3))

; Apply Erlang Binary Operations -----------------------------------------------

; Given a binop, apply the corresponding Erlang operation.
(define apply-erl-binop ((op erl-binop-p) (left erl-val-p) (right erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (erl-binop-fix op))
       (left (erl-val-fix left))
       (right (erl-val-fix right)))
      (cond
        ((arithm-binop-p op) (apply-erl-arithm-binop op left right))
        ((bool-binop-p op) (apply-erl-bool-binop op left right))
        ((comp-binop-p op) (apply-erl-comp-binop op left right))
        ((list-op-p op) (apply-erl-list-op op left right))
        (t (make-erl-val-reject :err "bad op"))))
    ///
      (defcong erl-binop-equiv equal (apply-erl-binop op x y) 1)
      (defcong erl-val-equiv equal (apply-erl-binop op x y) 2)
      (defcong erl-val-equiv equal (apply-erl-binop op x y) 3))

; Apply Erlang Unary Operations ------------------------------------------------

; Given an unop, apply the corresponding Erlang operation.
(define apply-erl-unop ((op erl-unop-p) (val erl-val-p))
  :returns (v erl-val-p)
  (b* ((op (erl-unop-fix op))
       (val (erl-val-fix val)))
      (case op
        (+ (erl-plus val))
        (- (erl-minus val))
        (not (erl-not val))
        (otherwise (make-erl-val-reject :err "bad op"))))
    ///
      (defcong erl-unop-equiv equal (apply-erl-unop op x) 1)
      (defcong erl-val-equiv equal (apply-erl-unop op x) 2))