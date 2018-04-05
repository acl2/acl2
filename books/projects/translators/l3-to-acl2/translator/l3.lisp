; L3 prelude

(in-package "ACL2")

(defconst *case-match+-var* 'case-match+-var)

(defun case-match+-1 (x)
  (cond ((endp x) nil)
        (t (cons (append (butlast (car x) 1)
                         `((check-vars-not-free (,*case-match+-var*)
                                                ,(car (last (car x))))))
                 (case-match+-1 (cdr x))))))

(defmacro case-match+ (var &rest clauses)
  (declare (xargs :guard (alistp clauses)))
  (cond ((symbolp var)
         `(case-match ,var
            ,@clauses))
        (t `(let ((,*case-match+-var* ,var))
              (case-match ,*case-match+-var*
                ,@(pairlis$ (strip-cars clauses)
                            (case-match+-1 (strip-cdrs clauses))))))))

(defun make-type (sym)
  (declare (xargs :guard t))
  (cond ((not (symbolp sym))
         (er hard? 'make-type
             "Non-symbol argument to make-type: ~x0"
             sym))
        (t (case sym
             (bty 'booleanp)
             (nty 'natp)
             (ity 'integerp)
             (qty 'st$p)
             (sty 'stringp)
             (uty 'null)
             (vty 'boolean-listp)
             (otherwise
              (intern-in-package-of-symbol
               (concatenate 'string "TYPE-" (symbol-name sym))
               sym))))))

(defthm true-listp-make-var-lst1
  (equal (true-listp (make-var-lst1 root sym n acc))
         (true-listp acc)))

(mutual-recursion

(defun type-expr-lst (vars lst)
  (declare (xargs :guard (and (true-listp vars)
                              (true-listp lst))
                  :measure (* 2 (acl2-count lst))))
  (cond ((endp lst) nil)
        (t (cons (type-expr (car vars) (car lst))
                 (type-expr-lst (cdr vars) (cdr lst))))))

(defun type-expr (name spec)

; E.g., (type-expr name (funct shiftt conditiont regt regt regt)) says that
; name is a 6-tuple of elements having the indicated types.

  (declare (xargs :guard t
                  :measure (1+ (* 2 (acl2-count spec)))))
  (cond ((null spec) ; or, spec is [] in input file
         `(null ,name))
        ((symbolp spec)
         `(,(make-type spec) ,name))
        ((true-listp spec)
         (case-match spec
           (('unsigned-byte n)
            `(unsigned-byte-p ,n ,name))
           (& (let ((vars (make-var-lst 'x (length spec))))
                `(slet ,vars
                       ,name
                       (and ,@(type-expr-lst vars spec))
                       nil ; hardp
                       nil ; default
                       )))))
        (t (er hard? 'type-expr
               "Illegal type spec for ~x0: ~x1"
               name spec))))
)

(defun construct-disjunct (clause)

; Clause is from a construct form, e.g.,
;   reservedinstr
; or:
;   (in (funct shiftt conditiont
;              (unsigned-byte 7)
;              (unsigned-byte 7)
;              (unsigned-byte 7)))

  (declare (xargs :guard t))
  (cond ((symbolp clause)
         `(eq x ',clause))
        ((and (consp clause)
              (symbolp (car clause))
              (consp (cdr clause))
              (true-listp (cadr clause))
              (null (cddr clause)))
         (let* ((type-expr (type-expr '(cadr x) (cadr clause)))
                (type-expr-conjuncts (cond ((and (consp type-expr)
                                                 (eq (car type-expr) 'and))
                                            (cdr type-expr))
                                           (t (list type-expr)))))
           `(and (consp x)
                 (eq (car x) ',(car clause))
                 (consp (cdr x))
                 (null (cddr x))
                 ,@type-expr-conjuncts)))
        (t (er hard? 'construct-disjunct
               "Illegal CONSTRUCT clause: ~x0"
               clause))))

(defun construct-disjuncts (clauses)
  (declare (xargs :guard (true-listp clauses)))
  (cond ((endp clauses) nil)
        (t (cons (construct-disjunct (car clauses))
                 (construct-disjuncts (cdr clauses))))))

(defun make-cast-to-nat (sym)
  (declare (type symbol sym))
  (intern-in-package-of-symbol
   (concatenate 'string "CAST-" (symbol-name sym) "-TO-NAT")
   sym))

(defun make-cast-from-nat (sym)
  (declare (type symbol sym))
  (intern-in-package-of-symbol
   (concatenate 'string "CAST-" (symbol-name sym) "-FROM-NAT")
   sym))

(defun construct-casters (type clauses)
  (cond ((symbol-listp clauses)
         `((defun ,(make-cast-to-nat type) (x)
             (declare (xargs :guard t :mode :logic))
             (let ((lst (member-eq x ',clauses)))
               (- ,(len clauses)
                  (len lst))))
           (defun ,(make-cast-from-nat type) (n)
             (declare (xargs :guard (natp n) :mode :logic))
             (nth n ',clauses))))
        (t nil)))

(defmacro cast-unsigned-byte (n x)
  (declare (xargs :guard (natp n)))
  `(logand ,(1- (expt 2 n)) ,x))

(defmacro cast (from-to x)
  (case-match from-to
    ((('unsigned-byte from) ('unsigned-byte to))
     (cond ((or (not (natp from))
                (not (natp to)))
            (er hard 'cast
                "Illegal cast from-to (expected natural numbers):~|~x0"
                from-to))
           ((<= from to)
            x)
           (t `(cast-unsigned-byte ,to ,x))))
    ((('unsigned-byte &) to)
     `(,(make-cast-from-nat to) ,x))
    ((from ('unsigned-byte &))
     `(,(make-cast-to-nat from) ,x))
    (& (er hard 'cast
           "Illegal cast from-to:~|~x0"
           from-to))))

(defmacro arb-qty ()
  'st$)

(defun make-arb (sym)
  (declare (type symbol sym))
  (intern-in-package-of-symbol
   (concatenate 'string "ARB-" (symbol-name sym))
   sym))

(mutual-recursion

(defun construct-arb-cdr (x)
  (declare (xargs :guard t
                  :measure (1+ (* 2 (acl2-count x)))))
  (cond ((null x) nil)
        ((symbolp x)
         `(,(make-arb x)))
        ((not (true-listp x))
         (er hard? 'construct-arb-cdr
             "Illegal piece of construct def: ~x0"
             x))
        (t (case-match x
             (('unsigned-byte n)
              `(arb-unsigned-byte ,n))
             (& (cons 'list
                      (construct-arb-cdr-lst x)))))))

(defun construct-arb-cdr-lst (x)
  (declare (xargs :guard (true-listp x)
                  :measure (* 2 (acl2-count x))))
  (cond ((endp x) nil)
        (t (cons (construct-arb-cdr (car x))
                 (construct-arb-cdr-lst (cdr x))))))
)

(defun construct-arb-def (type type-name clause)
  (declare (xargs :guard (symbolp type)))
  (let* ((arb-name (make-arb type))
         (thm-name (intern-in-package-of-symbol
                    (concatenate 'string
                                 (symbol-name arb-name)
                                 "-IS-"
                                 (symbol-name type))
                    type)))
    `(encapsulate
      (((,arb-name) => *))
      (logic)
      (set-ignore-ok t)
      (local (defun ,arb-name ()
               ,(cond ((atom clause)
                       (kwote clause))
                      ((and (symbolp (car clause))
                            (true-listp (cdr clause)))
                       `(cons ',(car clause)
                              ,(construct-arb-cdr (cdr clause))))
                      (t (er hard? 'construct-arb-def
                             "Illegal construct clause for type ~x0:~|~x1"
                             type clause)))))
      (defthm ,thm-name
        (,type-name (,arb-name))))))

(defun type-list-name (type-name)
  (declare (type symbol type-name))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name type-name) "-LIST")
   type-name))

(defmacro construct (type clauses)
  (declare (xargs :guard (symbolp type)))
  (let* ((type-name (make-type type))
         (type-def `(defun ,type-name (x)
                      (declare (xargs :guard t :mode :logic))
                      (or ,@(construct-disjuncts clauses))))
         (arb-def (construct-arb-def type type-name (car clauses)))
         (cast-defs (construct-casters type clauses))
         (type-list-name (type-list-name type-name)))
    `(progn ,@cast-defs
            ,type-def
            ,arb-def
            (defun ,type-list-name (x)
              (declare (xargs :guard t :mode :logic))
              (cond ((atom x) (null x))
                    (t (and (,type-name (car x))
                            (,type-list-name (cdr x)))))))))

; Matt K., 8/8/2015: Commenting out the definitions of TRUE and FALSE, which
; are now defined as functions in std/basic/defs.lisp.

; (defmacro true ()
;   t)
;
; (defmacro false ()
;   nil)

(verify-termination doublet-listp)
(verify-guards doublet-listp)

#||
   [raise'exception_def]  Definition

      |-  e.
           raise'exception e =
           ( state.
              (ARB,
               if state.exception = NoException then
                 state with exception := e
               else state))
||#

(encapsulate
 (((arb-unsigned-byte *) => *))
 (logic)
 (local (defun arb-unsigned-byte (n) (declare (ignore n)) 0))
 (defthm unsigned-byte-p-arb-unsigned-byte
   (implies (force (natp n))
            (unsigned-byte-p n (arb-unsigned-byte n)))))

(defthm natp-arb-unsigned-byte
  (implies (natp n)
           (natp (arb-unsigned-byte n)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable unsigned-byte-p-arb-unsigned-byte)
           :use unsigned-byte-p-arb-unsigned-byte)))

(defthm natp-expt
  (implies (and (natp b)
                (natp e))
           (natp (expt b e)))
  :rule-classes :type-prescription)

(defthm arb32-upper-bound
  (implies (natp n)
           (<= (arb-unsigned-byte n) (1- (expt 2 n))))
  :rule-classes ((:linear :trigger-terms ((arb-unsigned-byte n))))
  :hints (("Goal" :in-theory (disable unsigned-byte-p-arb-unsigned-byte)
           :use unsigned-byte-p-arb-unsigned-byte)))

(defmacro raise-exception (e val st)
  (declare (xargs :guard (symbolp st)))
  `(let ((,st (if (eq (exception ,st) 'NoException)
                  (update-exception ,e ,st)
                ,st)))
     (mv ,val ,st)))

; Start development of defun-struct, which is like defun except that a formal
; may be "structured":
;   (f1 f2 f3 ... fk)
; where each fi is either a symbol or a pair (sym guard).
; Each such is replaced by SFORMAL1, SFORMAL2, etc.

(defthm character-listp-explode-nonnegative-integer
  (implies
   (character-listp ans)
   (character-listp (explode-nonnegative-integer n print-base ans))))

(defun new-formal (i)
  (declare (xargs :guard (natp i)))
  (intern (concatenate 'string
                       "SFORMAL"
                       (coerce (explode-atom i 10) 'string))
          "ACL2"))

(defun destructure-formals-1 (sformal x orig)
  (declare (xargs :guard t))
  (cond ((atom x)
         (prog2$ (or (null x)
                     (er hard? 'destructure-formals-1
                         "Illegal structured formal, ~x0"
                         orig))
                 (mv nil nil)))
        (t (mv-let
            (cdr-bindings cdr-guards)
            (destructure-formals-1 sformal (cdr x) orig)
            (let* ((name (if (atom (car x))
                             (car x)
                           (caar x)))
                   (bindings
                    (cons (list name (list 'car sformal))
                          (cond ((null (cdr x))
                                 cdr-bindings)
                                (t (cons (list sformal (list 'cdr sformal))
                                         cdr-bindings))))))
              (prog2$
               (or (symbolp name)
                   (er hard? 'destructure-formals-1
                       "Illegal structured formal, ~x0"
                       orig))
               (cond ((atom (car x))
                      (mv bindings cdr-guards))
                     ((and (true-listp (car x))
                           (eql (length (car x)) 2))
                      (mv bindings (cons (cadr (car x)) cdr-guards)))
                     (t (mv (er hard? 'destructure-formals-1
                                "Illegal structured formal, ~x0"
                                orig)
                            nil)))))))))

(defthm true-listp-car-destructure-formals-1
  (true-listp (car (destructure-formals-1 sformal x orig))))

(defthm true-listp-nth-1-destructure-formals-1
  (true-listp (mv-nth 1 (destructure-formals-1 sformal x orig))))

(defun destructure-formals (formals i)
  (declare (xargs :guard (and (true-listp formals)
                              (natp i))))
  (cond ((endp formals)
         (mv nil nil nil nil nil))
        (t
         (mv-let
          (cdr-bindings cdr-names cdr-formals cdr-len-guards cdr-guards)
          (destructure-formals (cdr formals) (1+ i))
          (cond
           ((symbolp (car formals))
            (mv cdr-bindings
                cdr-names
                (cons (car formals) cdr-formals)
                cdr-len-guards
                cdr-guards))
           ((and (consp (car formals))
                 (symbolp (caar formals))
                 (consp (cdar formals))
                 (null (cddar formals)))
            (mv cdr-bindings
                cdr-names
                (cons (caar formals) cdr-formals)
                cdr-len-guards
                (cons (cadar formals)
                      cdr-guards)))
           (t
            (let ((new-formal (new-formal i)))
              (mv-let (new-bindings new-guards)
                      (destructure-formals-1 new-formal
                                             (car formals)
                                             (car formals))
                      (mv (append new-bindings cdr-bindings)
                          (cons new-formal cdr-names)
                          (cons new-formal cdr-formals)
                          (if (consp (car formals))
                              (cons `(eql (len ,new-formal)
                                          ,(len (car formals)))
                                    cdr-len-guards)
                            cdr-len-guards)
                          (append new-guards cdr-guards))))))))))

(defmacro defun-struct (name formals &rest rest)
  (declare (xargs :guard (true-listp formals)))
  (mv-let
   (measure rest)
   (cond ((eq (car rest) :measure)
          (mv (cadr rest) (cddr rest)))
         (t (mv nil rest)))
   (mv-let
    (bindings new-names new-formals len-guards guards)
    (destructure-formals formals 1)
    (let* ((ign-decl `(declare (ignorable
                                ,@(set-difference-eq (strip-cars bindings)
                                                     new-names))))
           (guard0 (if guards
                      `(let* ,bindings
                         ,ign-decl
                         (check-vars-not-free ,new-names
                                              (and ,@guards)))
                    t)))
      `(defun ,name ,new-formals
         (declare (xargs :guard
                         ,(if len-guards
                              (if (eq guard0 t)
                                  len-guards
                                `(and ,@len-guards
                                      ,guard0))
                            guard0)
                         ,@(and measure
                                `(:measure
                                  (let* ,bindings
                                    ,ign-decl
                                    (check-vars-not-free ,new-names
                                                         ,measure))))))
         ,@(butlast rest 1)
         (let* ,bindings
           ,ign-decl
           (check-vars-not-free ,new-names
                                ,(car (last rest)))))))))

(include-book "arithmetic-5/top" :dir :system)

(defmacro n+ (n x y)
  (declare (xargs :guard (natp n)))
  `(cast-unsigned-byte ,n (+ ,x ,y)))

(defmacro n- (n x y)
  (declare (xargs :guard (natp n)))
  `(cast-unsigned-byte ,n (- ,x ,y)))

; The following has lemmas like SIGNED-BYTE-P-LOGOPS and
; UNSIGNED-BYTE-P-LOGXOR.
(include-book "ihs/logops-lemmas" :dir :system)

(in-theory (disable signed-byte-p))

(defun bl-fn (n x)
  (declare (xargs :guard (and (natp n)
                              (symbolp x))))
  (cond ((zp n) nil)
        (t (let ((n (1- n)))
             (cons `(logbitp ,n ,x)
                   (bl-fn n x))))))

(defmacro bl (n x)
  (declare (xargs :guard (and (natp n)
                              (symbolp x))))
  (cons 'mv (bl-fn n x)))

; Here is a definition of bits adapted from books/rtl/rel8/lib/bits.lisp.  If
; we want to get serious about reasoning for this project, we should
; investigate more carefully which libraries to use.

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (if (< i j)
      0
    (logand (ash x (- j)) (1- (ash 1 (1+ (- i j)))))))

; Anthony will supply HOL4 imports, and then I can (hopefully!) find
; corresponding ACL2 libraries.

; Theory management:
(in-theory (disable ash-to-floor
                    unsigned-byte-p
                    logand-with-mask
                    logand-constant-mask
                    logbitp))

(defthm unsigned-byte-p-bits
  (implies (and (natp i)
                (natp j)
                (< j i)
                (equal k (1+ (- i j))))
           (unsigned-byte-p k (bits x i j)))
  :hints (("Goal" :in-theory (e/d (bits ash unsigned-byte-p)))))

(defthm natp-bits
  (natp (bits x i j))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (enable unsigned-byte-p bits ash))))

; !! Consider making more efficient by adding guard that args are of expected
; maximum bit width and then using mbe to avoid the call of BITS in the body.
(defund binary-cat (x m y n)
; Loosely based on rtl/rel8/lib/bits.lisp, but uses logior instead of +.
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (logior (ash (bits x (1- m) 0) n)
              (bits y (1- n) 0))
    0))

; From rtl/rel8/lib/bits.lisp:

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))

(defthm unsigned-byte-p-cat
   (implies (and (natp n1)
                 (natp n2)
                 (equal k (+ n1 n2)))
            (unsigned-byte-p k (cat x n1 y n2)))
   :hints (("Goal" :in-theory (enable unsigned-byte-p binary-cat bits ash))))

(defun unit-value ()

; Warning: If this is replaced with something other than nil, then

  (declare (xargs :guard t))
  nil)

(defmacro tuple (&rest args)
  (cons 'list args))

(defun slet-ignores (x)
  (declare (xargs :guard t))
  (cond ((null x) nil)
        ((symbolp x) (list x))
        ((atom x) nil)
        ((eq (car x) 'quote) nil)
        (t (union-eq (slet-ignores (car x))
                     (slet-ignores (cdr x))))))

(defmacro slet (str val expr &optional (hardp 't) (default '0))

; Structured let, for example:
; (slet (func shift skip w a b) args expr)

  `(case-match+ ,val
     (,str
      (declare (ignorable ,@(slet-ignores str)))
      ,expr)
     (& ,(cond (hardp `(prog2$ (er hard! 'slet
                                   "Ill-formed: ~x0"
                                   '(slet ,str ,val ,expr))
                               ,default))
               (t default)))))

; The following was needed in order to admit encode in tiny.lisp.
(defthm equal-len-0
  (equal (equal (len x) 0)
         (not (consp x))))

; The following was useful for admitting dfn-loadconstant.
(encapsulate
 ()

 (local (scatter-exponents))

 (defthm unsigned-byte-p-monotone
   (implies (and (unsigned-byte-p k x)
                 (natp k)
                 (integerp n)
                 (<= k n))
            (unsigned-byte-p n x))
   :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

(defun arb-uty ()
  (declare (xargs :guard t))
  (unit-value))

(defun arb-list-fn (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons `(arb ,(car lst))
                 (arb-list-fn (cdr lst))))))

(defmacro arb (type)
  (case-match type
    (('unsigned-byte n)
     `(arb-unsigned-byte ,n))
    ('qty ''st$)
    ((& . &)
     (let ((lst (arb-list-fn type)))
       (cond ((member-equal 'qty type)
              (cons 'mv lst))
             (t (cons 'tuple lst)))))
    (& (cond ((symbolp type)
              `(,(make-arb type)))
             (t (er hard 'arb
                    "Illegal argument to arb:~|~x0"
                    type))))))

(defmacro call-constructor (typ sym x)
  (declare (ignore typ))
  `(list ',sym ,x))

(defmacro mv-let-ignorable (&rest rst)
  (declare (xargs :guard ; from mv-let
                  (and (>= (length rst) 3)
                       (true-listp (car rst))
                       (>= (length (car rst)) 2))))
  `(mv-let ,(car rst)
           ,(cadr rst)
           (declare (ignorable ,@(car rst)))
           ,@(cddr rst)))

(defun stobj-mapper-name (updater rec-p)
  (declare (xargs :guard (symbolp updater)))
  (intern-in-package-of-symbol
   (cond (rec-p
          (concatenate 'string "MAP-" (symbol-name updater)
                       "-REC"))
         (t
          (concatenate 'string "MAP-" (symbol-name updater))))
   updater))

(defun defstobj-mappers-1 (field-name n type-spec st-name renaming-alist)
  (declare (xargs :guard (and (symbolp field-name)
                              (posp n)
                              (symbolp st-name))
                  :mode ; because of defstobj-fnname
                  :program))
  (let* ((init (if (eq st-name 'init)
                   'init-val
                 'init))
         (k (if (eq st-name 'k)
                'i
              'k))
         (updater (defstobj-fnname field-name :updater :array renaming-alist))
         (mapper (stobj-mapper-name updater nil))
         (mapper-rec (stobj-mapper-name updater t)))
    `((defun ,mapper-rec (,k ,init ,st-name)
        (declare (xargs :stobjs ,st-name)
                 (type ,type-spec ,init)
                 (type (integer 0 ,n) ,k))
        (cond ((zp ,k) ,st-name)
              (t (let* ((,k (1- ,k))
                        (,st-name (,updater ,k ,init ,st-name)))
                   (,mapper-rec ,k ,init ,st-name)))))
      (defun ,mapper (,init ,st-name)
        (declare (xargs :stobjs ,st-name)
                 (type ,type-spec ,init))
        (,mapper-rec ,n ,init ,st-name)))))

(defun defstobj-mappers (x st-name renaming-alist)

; X is the cdr of a defstobj form, and thus is a list consisting of field
; specifications followed, optionally, by a keyword-value-listp.

; Note that we do not support renaming of stobj updaters.  That could be added
; if necessary.

  (declare (xargs :guard (and (true-listp x)
                              (symbolp st-name))
                  :mode ; because of defstobj-mappers-1
                  :program))
  (cond ((endp x) nil)
        ((keywordp (car x)) nil)
        ((atom (car x))
         (defstobj-mappers (cdr x) st-name renaming-alist))
        ((keyword-value-listp (cdr (car x)))
         (cond
          ((not (symbolp (car (car x))))
           (er hard? 'defstobj-mappers
               "Found non-symbolp CAR of stobj field ~x0"
               (car x)))
          (t (let ((tp (cadr (assoc-keyword :type (cdr (car x))))))
               (case-match tp
                 (('array type-spec (n))
                  (cond ((posp n)
                         (append (defstobj-mappers-1 (car (car x)) n type-spec
                                   st-name renaming-alist)
                                 (defstobj-mappers (cdr x) st-name
                                   renaming-alist)))
                        (t (er hard? 'defstobj-mappers
                               "Found non-posp array dimension in stobj ~
                                field:~|~x0"
                               (car x)))))
                 (& (defstobj-mappers (cdr x) st-name renaming-alist)))))))
        (t (defstobj-mappers (cdr x) st-name renaming-alist))))

(defmacro defstobj+ (&rest args)
  (let ((renaming-alist (cadr (member-eq :renaming args))))
    `(progn (defstobj ,@args)
            ,@(defstobj-mappers (cdr args) (car args) renaming-alist))))
