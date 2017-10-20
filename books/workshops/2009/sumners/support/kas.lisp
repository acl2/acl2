#| KAS - Kernel Architecture Simplifier |#

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| Some logical functions needed to define KAS operation                      |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

(defun symbol-appendp (x) (or (symbolp x) (stringp x) (natp x)))

(defun dec-to-string (d)
  (case d (0 "0") (1 "1") (2 "2") (3 "3") (4 "4") (5 "5") (6 "6") (7 "7") (8 "8") (t "9")))

(defun nat-to-string (n)
  (string-append (if (zp (floor n 10)) "" (nat-to-string (floor n 10)))
		 (dec-to-string (mod n 10))))

(defun symbol-append-string (x)
  (cond ((symbolp x) (symbol-name x))
	((stringp x) x)
	(t (nat-to-string x))))

(defun symbol-binary-append (x y)
  (declare (xargs :guard (and (symbol-appendp x) (symbol-appendp y))))
  ;; (intern-in-package-of-symbol (string-append (symbol-name x) (symbol-name y)) x))
  (intern (string-append (symbol-append-string x) (symbol-append-string y)) "ACL2"))

(defmacro symbol-append (symb1 symb2 &rest symbs)
  `(symbol-binary-append ,symb1 ,(if (endp symbs) symb2 `(symbol-append ,symb2 ,@symbs))))

(defun make-hyps-and-args-list (n)
  (if (zp n) () (cons (symbol-append 'x n) (make-hyps-and-args-list (1- n)))))

(defun make-hyps-and-fn (n)
  `(defun ,(symbol-append 'hyps-and- n) ,(make-hyps-and-args-list n)
     (and ,(symbol-append 'x n)
          ,(cons (symbol-append 'hyps-and- (1- n))
                 (make-hyps-and-args-list (1- n))))))

(defun make-hyps-and-fns (n r)
  (if (zp n) r (make-hyps-and-fns (1- n) (cons (make-hyps-and-fn n) r))))

(logic)

(defun siv (x) (declare (ignore x)) t)
(defthm siv-rewrite (equal (siv x) t))
(in-theory (disable siv (siv)))
(defun fak (x) x)
(defun fail (x) x)
(defmacro sieve (x) `(siv (quote ,x)))
(defun hyps-and-0 () ())
(defmacro make-hyps-and-functions (n)
  (declare (xargs :guard (natp n)))
  (cons 'progn (make-hyps-and-fns n ())))
(make-hyps-and-functions 63) ; greater value can cause CCL compiler warnings

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| ACL2 interface macros and functions                                        |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

(defmacro kern-comp ()
  ; '(value t)
  ; '(comp-gcl t)
  ; '(comp t)
  ; '(comp-gcl :raw)
  '(comp :raw)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| definition of stobj+ macros                                                |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We define a bunch of macros for defining functions which use stobj+'s.
; Basically, these macros lift the main program from overnotating several
; common structures encountered in programming with stobjs.

(defmacro kern-fixnum-size () 61)
(defmacro my-fixnum (x) `(the (signed-byte ,(kern-fixnum-size)) ,x))

(defun gen-stobj+-renaming (flds stb)
  (if (endp flds) ()
    (let ((name (caar flds))
          (type (cadar flds)))
      (append (if (member-eq type '(:fixnum :object))
                  (list (list name
                              (symbol-append 'get- name))
                        (list (symbol-append 'update- name)
                              (symbol-append 'set- name))
                        (list (symbol-append name 'p)
                              (symbol-append stb '- name 'p)))
                (list (list (symbol-append name 'i)
                            (symbol-append 'get- name))
                      (list (symbol-append 'update- name 'i)
                            (symbol-append 'set- name))
                      (list (symbol-append name 'p)
                            (symbol-append stb '- name 'p))
                      (list (symbol-append 'resize- name)
                            (symbol-append stb '-resize- name))
                      (list (symbol-append name '-length)
                            (symbol-append 'length- name))))
              (gen-stobj+-renaming (cdr flds) stb)))))

(defun process-stobj+-fields (flds)
  (if (endp flds) ()
    (cons (cons (caar flds)
		(case (cadar flds)
		  (:fixnum       `(:type (signed-byte ,(kern-fixnum-size))
				   :initially 0))
		  (:fixnum-array `(:type (array (signed-byte ,(kern-fixnum-size)) (0))
				   :initially 0
				   :resizable t))
		  (:object       `(:type T
				   :initially nil))
		  (:object-array `(:type (array T (0))
				   :initially nil
				   :resizable t))
		  (otherwise     (er hard 'process-stobj+-fields
				     "ill-formed stobj+ definition"))))
          (process-stobj+-fields (cdr flds)))))

(defun stobj+-resize-funcs (flds stb)
  (cond ((endp flds) ())
        ((member-eq (cadar flds) '(:fixnum :object))
         (stobj+-resize-funcs (cdr flds) stb))
        (t
         (cons `(defun ,(symbol-append 'resize- (caar flds))
                  (size ,stb)
                  (declare (xargs :stobjs ,stb))
                  (if (eql size (,(symbol-append 'length- (caar flds)) ,stb))
                      ,stb
                    (prog2$ (and (,(symbol-append 'get- stb '-resize-array-display)
                                  ,stb)
                                 (cw "~x0:~x1~%"
                                     (quote ,(symbol-append 'resize- (caar flds)))
                                     size))
                      (,(symbol-append stb '-resize- (caar flds)) size ,stb))))
               (stobj+-resize-funcs (cdr flds) stb)))))

(defun stobj+-clear-arr-funcs (flds stb)
  (cond ((endp flds) ())
        ((member-eq (cadar flds) '(:fixnum :object))
         (stobj+-clear-arr-funcs (cdr flds) stb))
        (t
         (let ((clear-arr-fn (symbol-append `clear-arr- (caar flds)))
               (set-arr-fn (symbol-append 'set- (caar flds)))
               (clear-obj (if (eq (cadar flds) :fixnum-array) 0 nil)))
           (cons `(defun ,clear-arr-fn (N ,stb)
                    (declare (xargs :stobjs ,stb)
                             (type (signed-byte ,(kern-fixnum-size)) N))
                    (if (=^ N 0) ,stb
                      (let ((N (1-^ N)))
                        (declare (type (signed-byte ,(kern-fixnum-size)) N))
                        (let ((,stb (,set-arr-fn N ,clear-obj ,stb)))
                          (,clear-arr-fn N ,stb)))))
                 (stobj+-clear-arr-funcs (cdr flds) stb))))))

(defun stobj+-clear-func (flds stb)
  (if (endp flds) ()
    (cons (list stb
                (case (cadar flds)
                      (:fixnum (list (symbol-append 'set- (caar flds)) 0 stb))
                      (:object (list (symbol-append 'set- (caar flds)) nil stb))
                      (t (list (symbol-append 'clear-arr- (caar flds))
                               (list (symbol-append 'length- (caar flds)) stb)
                               stb))))
          (stobj+-clear-func (cdr flds) stb))))

(defun built-in-stobj+-fields (stobj-name)
  (list (list (symbol-append stobj-name '-resize-array-display) :object)))

(defmacro define-stobj+ (stobj-name &rest fields)
  (let ((fields (append fields (built-in-stobj+-fields stobj-name))))
    (cons 'progn
          (append (list `(defstobj ,stobj-name
                           ,@(process-stobj+-fields fields)
                           :inline t
                           :renaming ,(gen-stobj+-renaming fields stobj-name)))
                  (stobj+-resize-funcs fields stobj-name)
                  (stobj+-clear-arr-funcs fields stobj-name)
                  (list `(defun ,(symbol-append 'clear- stobj-name)
                           (,stobj-name)
                           (declare (xargs :stobjs ,stobj-name))
                           (let* ,(stobj+-clear-func fields stobj-name)
                             ,stobj-name)))))))

;; now we define some macros for defining record-arrays. These are records stored consecutively
;; in possibly different arrays which are declared with special types.

(defun stobj+-record-fields-fn (stb fields array object type ctr)
  (if (endp fields) ()
    (let ((field (first fields)))
      (list* `(defmacro ,(symbol-append object (intern "." "ACL2") field)
                (,object)
                ,(let ((form `(list ',(symbol-append 'get- array)
                                    ,(if (eql ctr 0)
                                         `(list ',(symbol-append array '-arr-ndx) ,object)
                                       `(list '+^
                                              (list ',(symbol-append array '-arr-ndx) ,object)
                                              ,ctr))
                                    ',stb)))
                   (if (eq type :fixnum)
                       `(list 'my-fixnum ,form)
                     form)))
             `(defmacro ,(symbol-append object '.set- field)
                (,object ,field)
                (list ',(symbol-append 'set- array)
                      ,(if (eql ctr 0)
                           `(list ',(symbol-append array '-arr-ndx) ,object)
                         `(list '+^
                                (list ',(symbol-append array '-arr-ndx) ,object)
                                ,ctr))
                      ,(if (eq type :fixnum)
                           `(list 'my-fixnum ,field)
                         field)
                      ',stb))
             (stobj+-record-fields-fn stb (rest fields) array object type (1+ ctr))))))

(defun stobj+-record-fields (fields stb object)
  (if (endp fields) ()
    (let* ((fld (first fields))
           (array (second fld))
           (rcd-size (len (third fld))))
      (cons `(defmacro ,(symbol-append (second fld) '-arr-ndx)
               (,object)
               ,(if (>= rcd-size 2)
                    `(list '*^ (list 'my-fixnum ,object) ,rcd-size)
                  `(list 'my-fixnum ,object)))
            (append (stobj+-record-fields-fn stb (third fld) array object (first fld) 0)
                    (stobj+-record-fields (rest fields) stb object))))))

(defun resize-rcd-arr-calls (fields stb)
  (if (endp fields) ()
    (let ((array (second (first fields)))
          (rcd-size (length (third (first fields)))))
      (cons (list stb (list (symbol-append 'resize- array)
                            `(*^ (+^ ptr extra 1) ,rcd-size)
                            stb))
            (resize-rcd-arr-calls (rest fields) stb)))))

(defun merge-fields-into-list (fields)
  (if (endp fields) ()
    (append (third (first fields))
            (merge-fields-into-list (rest fields)))))

(defun merge-fields-into-object-arr (fields)
  (let ((obj-arr (second (assoc :object fields))))
    (if obj-arr
        (list (list :object obj-arr (merge-fields-into-list fields)))
      fields)))

(defmacro define-stobj+-record-array (stb object merge-into-obj-arr &rest fields)
  (let ((fields (if merge-into-obj-arr
                    (merge-fields-into-object-arr fields)
                  fields)))
    (let ((array (second (first fields)))
          (rcd-size (len (third (first fields)))))
      (list* 'progn
             `(defabbrev ,(symbol-append 'num-of- object)
                ()
                (let ((size (,(symbol-append 'length- array) ,stb)))
                  (declare (type (signed-byte ,(kern-fixnum-size)) size))
                  (floor^ size ,rcd-size)))
             `(defabbrev ,(symbol-append 'ensure- object)
                (ptr extra)
                (declare (type (signed-byte ,(kern-fixnum-size)) ptr extra))
                (let ((size (,(symbol-append 'length- array) ,stb)))
                  (declare (type (signed-byte ,(kern-fixnum-size)) size))
                  (if (<^ (*^ (1+^ ptr) ,rcd-size) size)
                      ,stb
                    (let* ,(resize-rcd-arr-calls fields stb)
                      ,stb))))
             `(defabbrev ,(symbol-append 'restrict- object)
                (ptr)
                (declare (type (signed-byte ,(kern-fixnum-size)) ptr))
                (let ((size (,(symbol-append 'length- array) ,stb)))
                  (if (=^ (*^ (1+^ ptr) ,rcd-size) size)
                      ,stb
                    (let ((extra 0))
                      (let* ,(resize-rcd-arr-calls fields stb)
                        ,stb)))))
             (stobj+-record-fields fields stb object)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| utility functions and macros                                               |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun kern-monitor-comp   () nil)   ; enable/disable monitor code at compile-time
(defun kern-monitor-run    () nil)   ; enable/disable monitor code at run-time
(defun kern-assert-comp    () t)     ; enable/disable assert code at compile-time
(defun kern-merge-arrays   () nil)   ; should be NIL for GCL, T for Franz

; enables for various inline checks for compiled code

(defun kern-enable-check-<^s () nil)
(defun kern-enable-check-fixns () nil)
(defun kern-enable-temp-recording () t)

; kern-display is a simple macro which is used to add some display code
; kern-monitor actually performs a test to see if it should display or not and
; can be disabled at compile

(defmacro kern-display (&rest x)
  (declare (xargs :guard (>= (len x) 1)))
  `(prog2$ (cw ,@(butlast x 1)) ,(car (last x))))

(defmacro kern-monitor (&rest x)
  (declare (xargs :guard (>= (len x) 2)))
  (if (kern-monitor-comp)
      `(prog2$ (and (kern-monitor-run)
                    ,(car x)
                    (cw ,@(butlast (cdr x) 1)))
               ,(car (last x)))
    (car (last x))))

; kern-assert is used to declare an assertion which is checked before
; evaluating the body term provided.

(defmacro kern-force-assert (mbt body)
  (let ((r (if (atom mbt) (list mbt) mbt)))
    `(prog2$ (and (not (eq ,mbt t))
                  (er hard (quote (assert ,@r))
                      "assert non-T value: ~x0"
                      ,mbt))
       ,body)))

(defmacro kern-assert (mbt body)
  (if (kern-assert-comp)
      `(kern-force-assert ,mbt ,body)
    body))

; The macro define-stobj+-record-array is defined in stobjp.lisp. This is
; simply a wrapper macro.

(defmacro define-kern-record-array (record &rest fields)
  `(define-stobj+-record-array ls$ ,record
     ,(kern-merge-arrays)
     ,@fields))

(defmacro define-user-record-array (record &rest fields)
  `(define-stobj+-record-array us$ ,record
     ,(kern-merge-arrays)
     ,@fields))

; We often wish to pass back multiple values such that the first is a fixnum.
; This declares that the first value in the mv is a fixnum which keeps it from
; being boxed (mainly of use in GCL).

(defmacro mv^ (x &rest rest)
  `(mv (my-fixnum ,x) ,@rest))

; We now define the letk which is our general purpose let-form which
; automatically includes the necessary fixnum declarations, introduces mv-lets
; when appropriate, and handles propogation of errors (when appropriate). We
; use a variable and function name scheme to allow the letk macro determine the
; "type" of the variable and function calls. Basically in any letk binding, the
; first return value is always a fixnum unless it is a stobj (which is either
; 'state or ends in the character #\$). For functions, if a function ends in a
; #\! character then it may return an "error" which will need to be propagated.
; The letk macro is essentially written for the kernel functions in this file
; and really should not be used in any other context. If a more generic let
; form could be conceived which achieved the uses here, then please make the
; suggestion to the ACL2 maintainers.

(defun is-letk-stobj-var (x)
  (and (symbolp x)
       (not (keywordp x))
       (or (eq x 'state)
           (let ((s (symbol-name x)))
             (eql (char s (1- (length s))) #\$)))))

(defun is-letk-object-var (x)
  (and (symbolp x)
       (not (keywordp x))
       (let ((s (symbol-name x)))
         (eql (char s (1- (length s))) #\.))))

(defun is-letk-fixnum-var (x)
  (and (symbolp x)
       (not (or (booleanp x)
                (keywordp x)
                (is-letk-stobj-var x)
                (is-letk-object-var x)))))

(defun drop-list-last (x)
  (if (endp (rest x)) ()
    (cons (first x)
          (drop-list-last (rest x)))))

(defun legal-var-listp (x)
  (or (null x)
      (and (consp x)
           (or (symbolp (car x))
               (and (consp (car x))
                    (null (cdar x))
                    (symbolp (caar x))))
           (legal-var-listp (cdr x)))))

(defun letk-binding-entryp (x)
  (and (true-listp x)
       (>= (len x) 2)
       (legal-var-listp (drop-list-last x))
       (or (atom (car (last x)))
           (symbolp (caar (last x))))))

(defun letk-bindingp (x)
  (or (null x)
      (and (consp x)
           (letk-binding-entryp (first x))
           (letk-bindingp (rest x)))))

(defmacro letk (bind rslt)
  (declare (xargs :guard (letk-bindingp bind)))
  (if (endp bind) rslt
    (let ((b (first bind)))
      (if (= (len b) 2)
          (let* ((lhs (first b))
                 (is-fixn (is-letk-fixnum-var lhs))
                 (rhs (if (and is-fixn (kern-enable-check-fixns))
                          `(the (signed-byte ,(kern-fixnum-size)) ,(second b))
                        (second b))))
            `(let ((,lhs ,rhs))
               ,@(and is-fixn
                      `((declare (type (signed-byte ,(kern-fixnum-size)) ,lhs))))
               (letk (,@(rest bind)) ,rslt)))
        (let* ((lhs (drop-list-last b))
               (rhs (car (last b)))
               (is-fixn (is-letk-fixnum-var (first lhs))))
          `(mv-let ,lhs ,rhs
             ,@(and is-fixn
                    `((declare (type (signed-byte ,(kern-fixnum-size)) ,(first lhs)))))
             ,(let ((body `(letk (,@(rest bind)) ,rslt)))
                (if (and is-fixn (kern-enable-check-fixns))
                    `(let ((,(first lhs) (the (signed-byte ,(kern-fixnum-size)) ,(first lhs))))
                       (declare (type (signed-byte ,(kern-fixnum-size)) ,(first lhs)))
                       ,body)
                  body))))))))

(defun defunk-fixnum-vars (vars)
  (cond ((endp vars) ())
        ((is-letk-fixnum-var (first vars))
         (cons (first vars)
               (defunk-fixnum-vars (rest vars))))
        (t (defunk-fixnum-vars (rest vars)))))

(defun defunk-type-declare (vars)
  (let ((vars (defunk-fixnum-vars vars)))
    (and vars `((declare (type (signed-byte ,(kern-fixnum-size)) ,@vars))))))

(defun defunk-stobj-vars (vars)
  (cond ((endp vars) ())
        ((is-letk-stobj-var (first vars))
         (cons (first vars)
               (defunk-stobj-vars (rest vars))))
        (t (defunk-stobj-vars (rest vars)))))

(defun defunk-stobj-declare (vars)
  (let ((vars (defunk-stobj-vars vars)))
    (and vars `((declare (xargs :stobjs ,vars))))))

(defconst *defunk-sig-vars*
  '(a b c d e f g h i j k l m n o p q r s t u v w x y z))

(defun defunk-create-sig (args vars)
  (cond ((endp args) ())
        ((is-letk-stobj-var (first args))
         (cons (first args)
               (defunk-create-sig (rest args) vars)))
        ((endp vars)
         (er hard 'defunk-create-sig
             "ran out of var.s"))
        (t
         (cons (first vars)
               (defunk-create-sig (rest args) (rest vars))))))

(mutual-recursion
(defun defunk-mv-sig (term)
  (and (consp term)
       (case (first term)
             (mv^  (defunk-create-sig (rest term) *defunk-sig-vars*))
             (if   (or (defunk-mv-sig (third term)) (defunk-mv-sig (fourth term))))
             (letk (defunk-mv-sig (third term)))
             (cond (defunk-cond-sig (rest term)))
             (case (defunk-cond-sig (rest (rest term))))
             ((kern-assert kern-error prog2$) (defunk-mv-sig (third term))))))

(defun defunk-cond-sig (conds)
  (and (consp conds)
       (or (defunk-mv-sig (second (first conds)))
           (defunk-cond-sig (rest conds)))))
)

(defconst *kern-fixnum-ops*
  '(+^ -^ *^ floor^ logand^ my-fixnum lognot^
    logior^ logxor^ mod^ expt^ max^ min^ ash^
    abs^ er0 1+^ 1-^ mask^ dctx-0 kern-make-opcd))

(mutual-recursion
(defun defunk-fixnum-body (term)
  (cond
   ((is-letk-fixnum-var term) t)
   ((atom term) nil)
   (t (case (first term)
            (if (or (defunk-fixnum-body (third term))
                    (defunk-fixnum-body (fourth term))))
            (letk (defunk-fixnum-body (third term)))
            (cond (defunk-cond-fixnum (rest term)))
            (case (defunk-cond-fixnum (rest (rest term))))
            ((kern-assert kern-error prog2$)
             (defunk-fixnum-body (fourth term)))
            (t (member-eq (first term) *kern-fixnum-ops*))))))

(defun defunk-cond-fixnum (conds)
  (and (consp conds)
       (or (defunk-fixnum-body (second (first conds)))
           (defunk-cond-fixnum (rest conds)))))
)

(defun defunk-tag-body (body)
  (if (defunk-fixnum-body body) `(my-fixnum ,body)
    (let ((sig (defunk-mv-sig body)))
      (if sig `(the-mv ,sig (signed-byte ,(kern-fixnum-size)) ,body)
        body))))

(defun defunk-make-binds (vars)
  (if (endp vars) ()
    (cons (list (first vars) (first vars))
          (defunk-make-binds (rest vars)))))

(defconst *defunk-body-primitives*
  '(+   *   1+   =  1-   -   /=  <=  <  >  >=
    +^  *^  1+^  =^ 1-^  -^  /=^ <=^ <^ >^ >=^
    mod mod^ floor floor^ expt expt^
    min min^ max max^
    logand logand^ logior logior^
    lognot lognot^ logxor logxor^
    ash ash^
    mask^ mv mv^ my-fixnum
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
    acons assoc assoc-eq assoc-equal
    strip-cars strip-cdrs
    numerator denominator realpart imagpart
    char-code char code-char
    symbol-name symbol-package-name
    intern intern-in-package-of-symbol
    symbol-append bozo
    equal eql eq
    member-eq member member-equal
    ))

(defconst *defunk-body-prefixes*
  '(get- set- length- resize- ensure- num-of- restrict-
    candidate. undo. qobj. rule. oper. node. opcd. memo. loop.))

(defun str-has-prefix (x y i)
  (or (>= i (length y))
      (and (< i (length x))
           (eql (char x i) (char y i))
           (str-has-prefix x y (1+ i)))))

(defun symb-has-prefix (x y)
  (str-has-prefix (symbol-name x)
                  (symbol-name y)
                  0))

(defun symb-prefixes (x lst)
  (and (not (endp lst))
       (or (symb-has-prefix x (first lst))
           (symb-prefixes x (rest lst)))))

(defun is-kern-primitive (op)
  (or (member-eq op *defunk-body-primitives*)
      (symb-prefixes op *defunk-body-prefixes*)))

(defun map-kern-op (op)
  (if (is-kern-primitive op) op (symbol-append 'kern- op)))

(mutual-recursion
(defun add-kern-to-calls (term)
  (cond ((atom term) term)
        ((eq (first term) 'quote) term)
        ((eq (first term) 'cond)
         (cons 'cond
               (add-kern-to-conds (rest term))))
        ((eq (first term) 'case)
         (list* 'case
                (add-kern-to-calls (second term))
                (add-kern-to-binds (rest (rest term)))))
        ((eq (first term) 'letk)
         (list 'letk
               (add-kern-to-binds (second term))
               (add-kern-to-calls (third term))))
        (t
         (cons (map-kern-op (first term))
               (add-kern-to-args (rest term))))))

(defun add-kern-to-args (args)
  (if (endp args) ()
    (cons (add-kern-to-calls (first args))
          (add-kern-to-args (rest args)))))

(defun add-kern-to-binds (binds)
  (if (endp binds) ()
    (cons (append (butlast (first binds) 1)
                  (add-kern-to-args (last (first binds))))
          (add-kern-to-binds (rest binds)))))

(defun add-kern-to-conds (conds)
  (if (endp conds) ()
    (cons (add-kern-to-args (first conds))
          (add-kern-to-conds (rest conds)))))
)

(defun mk-defunk (name vars inlined decls body)
  (kern-assert (and (symbolp name)
                    (symbol-listp vars))
   (let* ((name (map-kern-op name))
          (body (add-kern-to-calls body))
          (body (if (kern-enable-check-fixns)
                    `(letk ,(defunk-make-binds (defunk-fixnum-vars vars))
                       ,body)
                  body)))
     (if inlined
         `(defabbrev ,name ,vars ,@decls
            ,@(defunk-type-declare vars)
            ,(defunk-tag-body body))
       `(defun ,name ,vars ,@decls
          ,@(defunk-type-declare vars)
          ,@(defunk-stobj-declare vars)
          ,(defunk-tag-body body))))))

(defun parse-defunk-args (args)
  (let* ((inlined (and (consp args)
                       (eq (first args) :inline)))
         (args (if inlined (rest args) args)))
    (mv inlined (butlast args 1) (car (last args)))))

(defmacro defunk (name vars &rest args)
  (if (endp args)
      (let ((body (add-kern-to-calls vars)))
        (list 'defmacro (symbol-append 'kern- name) ()
              (list 'let (list (list 'x body)) (list 'list ''quote 'x))))
    (mv-let (inlined decls body) (parse-defunk-args args)
      (mk-defunk name vars inlined decls body))))

(defun split-defunks (fns)
  (if (endp fns) (mv () ())
    (let ((fn (first fns)))
      (kern-assert (and (true-listp fn)
                        (> (length fn) 3)
                        (eq (first fn) 'defunk))
       (mv-let (inlined decls body)
           (parse-defunk-args (rest (rest (rest fn))))
         (let ((fn (mk-defunk (second fn) (third fn)
                              inlined decls body)))
           (mv-let (abbrevs funcs)
               (split-defunks (rest fns))
             (if (and (consp fn) (eq (first fn) 'defabbrev))
                 (mv (cons fn abbrevs) funcs)
               (mv abbrevs (cons fn funcs))))))))))

(defmacro mutual-recursionk (&rest fns)
  (mv-let (abbrevs funcs) (split-defunks fns)
    (cons 'progn (append abbrevs (list (cons 'mutual-recursion funcs))))))

;; a node which has been "promoted" or is persistent will have a pointer value
;; greater than 0.

;; we exclude 0 = (node-btm) as a special node
(defunk promoted (x) :inline (>^ x 0))
(defunk temp-node (x) :inline (<^ x 0))

(defunk node< (x y) :inline
  (assert (and (promoted x)
               (promoted y))
   (<^ x y)))

(defmacro kern-check-<^ (x y ctx)
  (if (kern-enable-check-<^s)
      `(my-fixnum
        (if (<^ ,x ,y) ,x
          (er0 hard ,ctx "expected decreasing ~x0 < ~x1" ,x ,y)))
    x))

; We now defined several macros which are "fixnum" verions of existing
; functions and primitives.

(defmacro -^ (x &rest y)
  (if (consp y)          `(my-fixnum (-      (my-fixnum ,x) (my-fixnum ,(first y))))
                         `(my-fixnum (-      (my-fixnum ,x)))))
(defmacro +^ (x &rest y)
  (if (endp y)           `(my-fixnum ,x)
                         `(my-fixnum (+      (my-fixnum ,x) (+^ ,(first y) ,@(rest y))))))
(defmacro *^ (x &rest y)
  (if (endp y)           `(my-fixnum ,x)
                         `(my-fixnum (*      (my-fixnum ,x) (*^ ,(first y) ,@(rest y))))))
(defmacro 1+^ (x)        `(my-fixnum (1+     (my-fixnum ,x))))
(defmacro 1-^ (x)        `(my-fixnum (1-     (my-fixnum ,x))))
(defmacro ash^ (x y)     `(my-fixnum (ash    (my-fixnum ,x) (my-fixnum ,y))))
(defmacro =^ (x y)                  `(eql    (my-fixnum ,x) (my-fixnum ,y)))
(defmacro <^ (x y)                  `(<      (my-fixnum ,x) (my-fixnum ,y)))
(defmacro mod^ (x y)     `(my-fixnum (mod    (my-fixnum ,x) (my-fixnum ,y))))
(defmacro floor^ (x y)   `(my-fixnum (floor  (my-fixnum ,x) (my-fixnum ,y))))
(defmacro expt^ (x y)    `(my-fixnum (expt   (my-fixnum ,x) (my-fixnum ,y))))
(defmacro lognot^ (x)    `(my-fixnum (lognot (my-fixnum ,x))))
(defmacro logand^ (x &rest y)
  `(my-fixnum ,(if (endp y) x `(logand (my-fixnum ,x) (logand^ ,(first y) ,@(rest y))))))
(defmacro logior^ (x &rest y)
  `(my-fixnum ,(if (endp y) x `(logior (my-fixnum ,x) (logior^ ,(first y) ,@(rest y))))))
(defmacro logxor^ (x &rest y)
  `(my-fixnum ,(if (endp y) x `(logxor (my-fixnum ,x) (logxor^ ,(first y) ,@(rest y))))))

(defmacro mask^ (x y)    `(my-fixnum (logand ,x ,y)))

(defmacro /=^ (x y)      `(not (=^ ,x ,y)))
(defmacro <=^ (x y)      `(<= (my-fixnum ,x) (my-fixnum ,y)))
(defmacro >^ (x y)       `(<^ ,y ,x))
(defmacro >=^ (x y)      `(<=^ ,y ,x))

(defmacro max^ (x &rest r)
  (if (endp r) x
    `(letk ((x ,x)
            (m (max^ ,@r)))
       (if (>^ x m) x m))))

(defmacro min^ (x &rest r)
  (if (endp r) x
    `(letk ((x ,x)
            (m (min^ ,@r)))
       (if (<^ x m) x m))))

(defmacro er0 (&rest args) `(prog2$ (er ,@args) 0))

; The following macro is simply a wrapper for getprop. The
; variable wrld is captured from the current context and is
; expected to be the current ACL2 world.

(defmacro kern-getprop (name prop)
  `(getprop ,name ,prop nil 'current-acl2-world wrld))

; (defunk zp (x)             :inline (or (not (integerp x)) (<=^ x 0)))
(defunk zp (x)             :inline (<=^ x 0))
(defunk absf (x)           :inline (if (<^ x 0) (-^ x) x))
(defunk is-boolean (x.)    :inline (or (eq x. t) (eq x. nil)))
(defunk is-natrual (x.)    :inline (and (integerp x.) (>= x. 0)))
(defunk is-trace-mark (x.) :inline (or (is-boolean x.) (eq x. :all)))

(defunk spcs (n) (if (zp n) "" (string-append " " (spcs (1- n)))))

(defunk max-fixnum   (1- (expt 2 60)))
(defunk min-fixnum   (- (expt 2 60)))
(defunk maximum-array-size (max-fixnum))

(defunk fixnump (x) :inline
  (and (integerp x)
       (>= x (min-fixnum))
       (<= x (max-fixnum))))

(kern-comp)  ;; compile to get macros compiled

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| ls$ stobj, structures, and access functions                                |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We now define the stobj used in the kernel functions.  The stobj is called
; ls$ which stands for "logic state stobj".

(define-stobj+ ls$
  (node-stor        :fixnum-array)
  (node-hash        :fixnum-array)
  (alloc-nodes      :fixnum)
  (num-of-nodes     :fixnum)
  (quote-stor       :object-array)
  (quote-hash       :fixnum-array)
  (next-quote       :fixnum)
  (node-step        :fixnum)
  (node-limit       :fixnum)
  (hash-mask        :fixnum)
  (trans-stor       :fixnum-array)
  (trans-hash       :fixnum-array)
  (alloc-trans      :fixnum)
  (num-trans-nodes  :fixnum)
  (memo-stor        :fixnum-array)
  (loop-stack       :fixnum-array)
  (loop-stk-top     :fixnum)
  (op-obj-stor      :object-array)
  (op-fix-stor      :fixnum-array)
  (next-op-ndx      :fixnum)
  (op-hash          :fixnum-array)
  (undo-stk         :fixnum-array)
  (undo-chains      :fixnum-array)
  (undo-top         :fixnum)
  (undo-free-list   :fixnum)
  (rule-fix-stor    :fixnum-array)
  (rule-obj-stor    :object-array)
  (next-rule-ndx    :fixnum)
  (curr-ctx-stk     :fixnum-array)
  (curr-ctx-top     :fixnum)
  (current-world    :object)
  (current-ens      :object)
  (var-chg-stk      :fixnum)
  (current-age      :fixnum)
  (bchain-limit     :fixnum)
  (next-extend-age  :fixnum)
  (current-dctx     :fixnum)
  (warned-ctx-depth :object)
  (current-clock    :fixnum)
  (output-verbose   :object)
  (kern-size-param  :object)
  (flip-t-fns       :object)
  (flip-nil-fns     :object)
  (allow-context-reduction :object)
  (initial-rule-trace-descriptor :object)
  (initial-node-prune-depth :object)
  (rew-call-depth   :fixnum)  ;; only used for debugging
)

(define-kern-record-array memo
  (:fixnum memo-stor (opcd rslt dcv arg0 arg1 arg2)))

(define-kern-record-array undo
  (:fixnum undo-stk (node rep dcv chain)))

(define-kern-record-array qobj
  (:object quote-stor (obj uniq-chain)))

(define-kern-record-array oper
  (:object op-obj-stor (name is-var is-if is-equal non-nil rules boolp assume-tbr assume-fbr))
  (:fixnum op-fix-stor (next-stk bound narg uniq-chain num-nodes num-trans exec)))

(define-kern-record-array rule
  (:object rule-obj-stor (rune sieves enabled traced))
  (:fixnum rule-fix-stor (ctr tryctr lhs rhs op hyps)))

(define-kern-record-array loop
  (:fixnum loop-stack (rule node)))

; We may use more than one memo slot if the num. args for the fn is greater
; than 3. In order to facilitate this definition, we include the following
; definition of arg access/update functions

(defunk opcd-memo-mrkr -1)
(defunk max-memo-narg   9)
(defunk num-1memo-args  3)

(defunk memo.arg (x i) :inline
  (assert (<^ i (max-memo-narg))
   (case i
     (0 (memo.arg0 x))
     (1 (memo.arg1 x))
     (2 (memo.arg2 x))
     (3 (memo.rslt (1+^ x)))
     (4 (memo.dcv  (1+^ x)))
     (5 (memo.arg0 (1+^ x)))
     (6 (memo.arg1 (1+^ x)))
     (t (memo.arg2 (1+^ x))))))

(defunk memo.set-arg (x i v) :inline
  (assert (<^ i (max-memo-narg))
   (case i
     (0 (memo.set-arg0 x v))
     (1 (memo.set-arg1 x v))
     (2 (memo.set-arg2 x v))
     (3 (memo.set-rslt (1+^ x) v))
     (4 (memo.set-dcv  (1+^ x) v))
     (5 (memo.set-arg0 (1+^ x) v))
     (6 (memo.set-arg1 (1+^ x) v))
     (t (memo.set-arg2 (1+^ x) v)))))

; We include a "wrapper" for oper.uniq which checks if the uniq-ptr retrieved
; is strictly less than o. This should be an invariant of the construction of
; nodes, but we add this "wrapper" to help in admitting various functions which
; traverse nodes. BOZO -- need to check if this affects performance appreciably
; and note here whether or not it does.

(defunk oper.uniq (o) :inline
  (letk ((uniq (oper.uniq-chain o)))
    (check-<^ uniq o 'oper.uniq)))

(defunk oper.set-uniq (o uniq) :inline
  (oper.set-uniq-chain o uniq))

; We include a "wrapper" for qobj.uniq which checks if the uniq-ptr retrieved
; is strictly less than q. This should be an invariant of the construction of
; nodes, but we add this "wrapper" to help in admitting various functions which
; traverse nodes. BOZO -- need to check if this affects performance appreciably
; and note here whether or not it does.

(defunk qobj.uniq (q) :inline
  (letk ((uniq (qobj.uniq-chain q)))
    (check-<^ uniq q 'qobj.uniq)))

(defunk qobj.set-uniq (q uniq) :inline
  (qobj.set-uniq-chain q uniq))


;; A node consists of the following fields (each encoded in a fixnum) at an
;; offset from a base address for the node:
;;
;;  offset  0:  <vcnt[14],fcnt[14]>,<in-ctx>,<user-mark>,<op[18],equal[1],if[1],var[1],narg[9]>  <-- count[28],user-mark[1],in-ctx[1],opcd[30]
;;  offset -1:  rep[60]/age[60]
;;  offset -2:  dcv[60]
;;  offset -3:  uniq[60]
;;  offset -4:  arg1[60]
;;  offset -5:  ...

(defunk avg-num-args     3)
(defunk base-node-alloc  4)
(defunk base-trans-alloc 1)

(defunk var-mask     (ash 1 10))
(defunk non-var-mask (lognot (var-mask)))
(defunk if-mask      (ash (var-mask) 1))
(defunk equal-mask   (ash (if-mask) 1))
(defunk opndx-shft   (ash (equal-mask) 1))
(defunk narg-mask    (1- (var-mask)))
(defunk opcd-mask    (1- (ash 1 30)))
(defunk in-ctx-mask  (ash 1 31))
(defunk in-ctx-flip  (lognot (in-ctx-mask)))
(defunk user-mark-mask  (ash 1 32))
(defunk user-mark-flip  (lognot (user-mark-mask)))

(defunk size-shft     (ash 1 32))
(defunk non-size-mask (1- (size-shft)))
(defunk size-mask     (lognot (non-size-mask)))
(defunk vcnt-shft     (ash 1 14))
(defunk fcnt-mask     (1- (vcnt-shft)))

(defunk max-num-args  (narg-mask))
(defunk max-num-fns   (- (ash 1 18) 2))
(defunk max-size-valu (1- (ash 1 28)))
(defunk size-btm      (max-size-valu))
(defunk max-fcnt-valu (fcnt-mask))
(defunk max-vcnt-valu (1- (ash 1 14)))


(defunk opcd.is-var (o)   :inline (=^ (logand^ o (var-mask))   (var-mask)))
(defunk opcd.is-if (o)    :inline (=^ (logand^ o (if-mask))    (if-mask)))
(defunk opcd.is-equal (o) :inline (=^ (logand^ o (equal-mask)) (equal-mask)))
(defunk opcd.narg (o)     :inline (logand^ o (narg-mask)))
(defunk opcd.index (o)    :inline (floor^ o (opndx-shft)))

(defunk make-opcd (narg var. is-if. is-eq. ndx) :inline
  (logior^ (*^ ndx (opndx-shft))
	   (if is-eq. (equal-mask) 0)
	   (if is-if. (if-mask) 0)
	   (if var. (var-mask) 0)
	   narg))

(defunk get-size-fcnt  (size)      :inline (logand^ size (fcnt-mask)))
(defunk get-size-vcnt  (size)      :inline (floor^ size (vcnt-shft)))
(defunk make-node-size (vcnt fcnt) :inline (logior^ (*^ vcnt (vcnt-shft)) fcnt))

(defunk node.set-opcd (n szop) :inline  (if (promoted n) (set-node-stor n szop ls$) (set-trans-stor (-^ n) szop ls$)))
(defunk node.opcd (n) :inline (logand^ (if (promoted n) (my-fixnum (get-node-stor n ls$)) (my-fixnum (get-trans-stor (-^ n) ls$))) (opcd-mask)))
(defunk node.size (n) :inline (floor^  (if (promoted n) (my-fixnum (get-node-stor n ls$)) (my-fixnum (get-trans-stor (-^ n) ls$))) (size-shft)))

(defunk node.in-ctx (n) :inline
  (assert (promoted n) (=^ (logand^ (get-node-stor n ls$) (in-ctx-mask)) (in-ctx-mask))))
(defunk node.set-in-ctx (n in-ctx.) :inline
  (assert (promoted n) (set-node-stor n (if in-ctx. (logior^ (get-node-stor n ls$) (in-ctx-mask))
					  (logand^ (get-node-stor n ls$) (in-ctx-flip))) ls$)))

(defunk node.user-mark (n) :inline
  (=^ (logand^ (get-node-stor n ls$) (user-mark-mask)) (user-mark-mask)))
(defunk node.set-user-mark (n user-mark.) :inline
  (set-node-stor n (if user-mark. (logior^ (get-node-stor n ls$) (user-mark-mask))
		     (logand^ (get-node-stor n ls$) (user-mark-flip))) ls$))

(defunk node.rep (n)         :inline (if (promoted n) (my-fixnum (get-node-stor (1-^ n) ls$)) (node-btm)))
(defunk node.set-rep (n rep) :inline (assert (promoted n) (set-node-stor (1-^ n) rep ls$)))

(defunk node.dcv (n)         :inline (assert (promoted n) (get-node-stor (-^ n 2) ls$)))
(defunk node.set-dcv (n dcv) :inline (assert (promoted n) (set-node-stor (-^ n 2) dcv ls$)))

; We include a "wrapper" for node.uniq which checks if the uniq-ptr retrieved
; is strictly less than the node id n passed in. This should be an invariant of
; the construction of nodes, but we add this "wrapper" to help in admitting
; various functions which traverse nodes. BOZO -- need to check if this affects
; performance appreciably and note here whether or not it does.

(defunk node.uniq (n)          :inline (assert (promoted n) (letk ((uniq (get-node-stor (-^ n 3) ls$))) (check-<^ uniq n 'node.uniq))))
(defunk node.set-uniq (n uniq) :inline (assert (promoted n) (set-node-stor (-^ n 3) uniq ls$)))


; Some special node ids. (node-btm) is a special node which denotes "no
; value". NOTE -- it is important that 0 is not a legal node value (for
; multiple reasons). So, actual node ids should always begin with node id 1.

(defunk node-btm 0)
(defunk args-btm 0)
(defunk opcd-btm 0)
(defunk qobj-btm 0)
(defunk loop-btm 0)

(defunk dctx-0    0)
(defunk dctx-btm  -1)
(defunk dcv-empty 0)
(defunk dcv-btm   -1)

; NOTE -- While the preceding constants may look "symbolic", it is important
; that these constants keep the value for which they are declared.

(defunk opcd-quote (make-opcd 1 nil nil nil 1))
(defunk opcd-if    (make-opcd 3 nil t   nil 2))
(defunk opcd-equal (make-opcd 2 nil nil t   3))
(defunk opcd-cons  (make-opcd 2 nil nil nil 4))
(defunk opcd-hide  (make-opcd 1 nil nil nil 5))
(defunk opcd-fail  (make-opcd 1 nil nil nil 6))

(defunk node-nil (1+ (base-node-alloc)))
(defunk node-t   (+ (node-nil) (base-node-alloc) 1))

; We include a "wrapper" for node.arg which checks if the arg retrieved is
; strictly less than the node id n passed in. This should be an invariant of
; the construction of nodes, but we add this "wrapper" to help in admitting
; various functions which traverse nodes. BOZO -- need to check if this affects
; performance appreciably and note here whether or not it does.

(defunk node.arg (n i) :inline
  (letk ((promoted. (promoted n))
         (alloc (if promoted. (base-node-alloc) (base-trans-alloc)))
         (n+ (if promoted. n (-^ n)))
         (ptr (-^ n+ (+^ alloc i)))
         (arg (if promoted.
                  (get-node-stor ptr ls$)
                (get-trans-stor ptr ls$))))
    (assert (or (temp-node n)
                (=^ (node.opcd n) (opcd-quote))
                (node< arg n)
                (list n i arg
                      (oper.name (opcd.index (node.opcd n)))
                      (opcd.narg (node.opcd n))
		      (opcd.is-var (node.opcd n))))
     arg)))

(defunk node.set-arg (n i arg) :inline
  (letk ((promoted. (promoted n))
         (alloc (if promoted. (base-node-alloc) (base-trans-alloc)))
         (n+ (if promoted. n (-^ n)))
         (ptr (-^ n+ (+^ alloc i))))
    (assert (or (temp-node n)
                (=^ (node.opcd n) (opcd-quote))
                (node< arg n)
                (list n i arg
                      (oper.name (opcd.index (node.opcd n)))
                      (opcd.narg (node.opcd n))
                      (node-to-term arg)))
     (if promoted.
         (set-node-stor ptr arg ls$)
       (set-trans-stor ptr arg ls$)))))

;; The function node-to-term is used to generate final results and to provide
;; feedback in debugging. We generate an "illegal term" for (node-btm), but we
;; want these to show up in the case this function is being used for
;; debugging. We filter these "illegal terms" out when doing final result
;; printing. This function may also be too "expensive" since it does not
;; memoize the term structure created, but in this case, the user is in trouble
;; already since the term which results will either be viewed by the user or
;; used subsequently by ACL2 and as such, the ability to memoize common
;; subterms would be irrelevant (although we could return a lambda expression
;; and perhaps this is the more appropriate path to take).

(mutual-recursionk
(defunk node-to-term1 (node ls$)
  (if (=^ node (node-btm)) :btm
    (letk ((opcd (node.opcd node))
           (op   (opcd.index opcd)))
      (cond ((opcd.is-var opcd)
             (oper.name op))
            ((=^ opcd (opcd-quote))
             (list 'quote (qobj.obj (node.arg node 0))))
            (t
             (cons (oper.name op)
                   (args-to-terms (opcd.narg opcd) 0 node ls$)))))))

(defunk args-to-terms (n i node ls$)
  (if (zp n) ()
    (cons (node-to-term1 (node.arg node i) ls$)
          (args-to-terms (1-^ n) (1+^ i) node ls$))))
)

(defunk node-to-term (node) :inline (node-to-term1 node ls$))

(defunk funcall (op. args.) :inline
  (ev-fncall-w op. args. (get-current-world ls$)
               nil    ; user-stobj-alist (guess from Matt K. after v4-3)
               nil    ; safe-mode
               t      ; gc-off
               nil    ; hard-error-returns-nilp
               nil))  ; aok

(defmacro kern-error (err-string node rslt)
  `(prog2$ (kern-print-stats ls$)
           (prog2$ (cw "       Final Term on Error: ~| ~p0 ~|~|" (kern-prune-node-term ,node))
                   (prog2$ (er hard 'kernel-simplify ,err-string)
                           ,rslt))))

(kern-comp) ;; compile to get macros compiled


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| functions defining a stats printing function                               |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defunk merge-histograms (x. y.)
  (cond ((endp x.) y.)
        ((endp y.) x.)
        ((< (cadar x.) (cadar y.))
         (cons (car x.)
               (merge-histograms (cdr x.) y.)))
        (t (cons (car y.)
                 (merge-histograms x. (cdr y.))))))

(defunk split-histogram (x. y. n)
  (if (or (endp x.) (zp n)) (mv x. y.)
    (split-histogram (cdr x.) (cons (car x.) y.) (1-^ n))))

(defunk sort-histogram (x.)
  (if (endp (cdr x.)) x.
    (letk ((y. z. (split-histogram x. () (floor^ (length x.) 2))))
      (merge-histograms (sort-histogram y.)
                        (sort-histogram z.)))))

(defunk get-rule-histogram (n r. ls$)
  (if (zp n) r.
    (letk ((n (1-^ n))
           (r. (if (>^ (rule.ctr n) 0)
                   (cons (list (rule.rune n)
                               (rule.ctr n))
                         r.)
                 r.)))
      (get-rule-histogram n r. ls$))))

(defunk compute-rule-histogram () :inline
  (sort-histogram (get-rule-histogram (num-of-rule) () ls$)))

(defunk get-rule-try-histogram (n r. ls$)
  (if (zp n) r.
    (letk ((n (1-^ n))
           (r. (if (>^ (rule.tryctr n) 0)
                   (cons (list (rule.rune n)
                               (rule.tryctr n))
                         r.)
                 r.)))
      (get-rule-try-histogram n r. ls$))))

(defunk compute-rule-try-histogram () :inline
  (sort-histogram (get-rule-try-histogram (num-of-rule) () ls$)))

(defunk get-node-histogram (n r. ls$)
  (if (zp n) r.
    (letk ((n (1-^ n))
           (r. (if (>^ (oper.num-nodes n) 0)
                   (cons (list (if (eq (oper.name n) 'quote)
                                   :quote
                                 (oper.name n))
                               (oper.num-nodes n))
                         r.)
                 r.)))
      (get-node-histogram n r. ls$))))

(defunk compute-node-histogram () :inline
  (sort-histogram (get-node-histogram (num-of-oper) () ls$)))

(defunk get-trans-histogram (n r. ls$)
  (if (zp n) r.
    (letk ((n (1-^ n))
           (r. (if (>^ (oper.num-trans n) 0)
                   (cons (list (if (eq (oper.name n) 'quote)
                                   :quote
                                 (oper.name n))
                               (oper.num-trans n))
                         r.)
                 r.)))
      (get-trans-histogram n r. ls$))))

(defunk compute-trans-histogram () :inline
  (sort-histogram (get-trans-histogram (num-of-oper) () ls$)))

(defunk histogram-to-ttree (histogram. ttree.)
  (if (endp histogram.) ttree.
    (histogram-to-ttree (cdr histogram.)
                        (push-lemma (caar histogram.) ttree.))))

(defunk print-loop-stack (n l r. ls$)
  (if (or (zp n) (zp l)) r.
    (print-loop-stack (1-^ n) (1-^ l)
                      (cons (rule.rune (loop.rule l)) r.)
                      ls$)))

(defunk compute-rule-stack () :inline
  (print-loop-stack 100 (1-^ (get-loop-stk-top ls$)) () ls$))

(mutual-recursionk
(defunk prune-print-term1 (x. n)
  (cond ((atom x.) x.)
        ((eq (first x.) 'quote) x.)
        ((zp n) "...")
        (t (cons (first x.)
                 (prune-print-args (rest x.) (1-^ n))))))

(defunk prune-print-args (a. n)
  (if (endp a.) ()
    (cons (prune-print-term1 (first a.) n)
          (prune-print-args (rest a.) n))))
)

(defunk fixfix (n)
  (if (and (integerp n) (>= n 0) (< n (max-fixnum))) n 0))

(defunk prune-node-term (x) :inline
  (prune-print-term1 (node-to-term x) (fixfix (get-initial-node-prune-depth ls$))))

(defunk print-suffix-stack (n l r. ls$)
  (if (or (zp n) (zp l)) r.
    (print-suffix-stack (1-^ n) (1-^ l)
                        (cons (list (rule.rune (loop.rule l))
                                    (prune-node-term (loop.node l)))
                              r.)
                        ls$)))

(defunk compute-suffix-stack () :inline
  (print-suffix-stack 10 (1-^ (get-loop-stk-top ls$)) () ls$))

(defunk print-stats (ls$)
  (letk ((rule-hist.  (compute-rule-histogram))
	 (try-hist.   (compute-rule-try-histogram))
         (node-hist.  (compute-node-histogram))
         (trans-hist. (compute-trans-histogram))
         (ttree.      (histogram-to-ttree rule-hist. ()))
         (rule-stk.   (compute-rule-stack))
         (stk-terms.  (compute-suffix-stack))
         (num-promo   (get-num-of-nodes ls$))
         (num-trans   (get-num-trans-nodes ls$))
         (num-nodes   (+^ num-promo num-trans)))
    (or (not (get-output-verbose ls$))
        (cw "--- KAS Num. Nodes: ~p0 ~|"                    num-nodes)
        (cw "        Num. Promoted Nodes: ~p0 ~|"           num-promo)
        (cw "        Num. Current Temp. Nodes: ~p0 ~|"      num-trans)
        (cw "        Applied Rule Histogram: ~| ~p0 ~|~%"   rule-hist.)
	(cw "        Attempted Rule Histogram: ~| ~p0 ~|~%" try-hist.)
        (cw "        Promoted Node Histogram: ~| ~p0 ~|~%"  node-hist.)
        (cw "        Temporary Node Histogram: ~| ~p0 ~|~%" trans-hist.)
        (and rule-stk.
             (cw "        Pending Rule Stack (top 100): ~| ~p0 ~|~%"  rule-stk.))
        (and stk-terms.
             (cw "        Rule Stack With Terms (top 10): ~| ~p0 ~|~%" stk-terms.))
        ttree.)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| functions defining various hash codes used in the kernel                   |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following macro defines the bound on the node indexes which are used
; throughout the kernel code to efficiently encode terms. This bound is
; necessary due to the requirements of the subsequent hashing function for
; newly created nodes.

(defunk hash-index-string (index mask string. acc)
  (if (zp index) acc
    (letk ((index (1-^ index))
           (acc (logand^ mask (+^ acc (char-code (char string. index))))))
      (hash-index-string index mask string. acc))))

(defunk hash-index-evg (evg. hash-mask)
  (mask^ hash-mask
   (cond
    ((integerp evg.)
     evg.)
    ((rationalp evg.)
     (+ (numerator evg.)
        (* 17 (denominator evg.))))
    ((acl2-numberp evg.)
     (+^ (hash-index-evg (realpart evg.) hash-mask)
	 (hash-index-evg (imagpart evg.) hash-mask)))
    ((characterp evg.)
     (+^ (floor^ hash-mask 4) (char-code evg.)))
    ((symbolp evg.)
     (*^ 19 (hash-index-evg (symbol-name evg.) hash-mask)))
    ((stringp evg.)
     (hash-index-string (length evg.) hash-mask evg. (floor^ hash-mask 2)))
    (t
     (assert (consp evg.)
             (+^ (hash-index-evg (car evg.) hash-mask)
		 (*^ 2 (hash-index-evg (cdr evg.) hash-mask))))))))

;; modify the following number to adjust the various params used in allocating
;; the kernel simplifier data structures.

(defunk static-param (expt 2 12))
(defunk op-hash-tbl-size (floor (static-param) 8))
(defunk op-hash-tbl-mask (1- (op-hash-tbl-size)))

(defunk fn-hash-code (name.) :inline
  (letk ((str. (symbol-name name.)))
    (hash-index-string (length str.) (op-hash-tbl-mask) str. 0)))

(defunk mult-kern-mask (1- (expt 2 28)))
(defunk add-kern-mask  (1- (expt 2 58)))
(defunk add-kern-mod   1021) ;; greatest prime < 1024

(defunk hash-step (arg mask acc) :inline
  (logand^ (+^ (logand^ (*^ (logand^ acc (mult-kern-mask))
			    (logand^ arg (mult-kern-mask)))
			(add-kern-mask))
	       (logand^ arg (add-kern-mask))
	       (mod^ acc (add-kern-mod)))
	   mask))

(defunk hash-args (n i acc mask x ls$)
  (if (zp n) acc
    (hash-args (1-^ n) (1+^ i)
               (hash-step (node.arg x i) mask acc)
               mask x ls$)))

(defunk hash-arg-list (args. acc mask ls$)
  (if (endp args.) acc
    (hash-arg-list (rest args.)
                   (hash-step (first args.) mask acc)
                   mask ls$)))

(defunk hash-node (node) :inline
  (letk ((opcd (node.opcd node))
         (narg (opcd.narg opcd))
         (mask (get-hash-mask ls$)))
    (hash-step opcd mask (hash-args narg 0 1 mask node ls$))))

(defunk hash-signature (sig.) :inline
  (letk ((opcd (first sig.))
         (args. (rest sig.))
         (mask (get-hash-mask ls$)))
    (hash-step opcd mask (hash-arg-list args. 1 mask ls$))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| auxiliary functions supporting main kernel loop and user fn updates        |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defunk lookup-opcd (op name. var. ls$)
  (cond ((zp op)
         (opcd-btm))
        ((and (equal name. (oper.name op))
              (eq var. (oper.is-var op)))
         (make-opcd (oper.narg op)
                    var.
                    (oper.is-if op)
                    (oper.is-equal op)
                    op))
        (t (lookup-opcd (oper.uniq op) name. var. ls$))))

(defunk find-fn-opcd (name.) :inline
  (letk ((op (get-op-hash (fn-hash-code name.) ls$)))
    (lookup-opcd op name. nil ls$)))

(defunk find-var-opcd (name.) :inline
  (letk ((op (get-op-hash (fn-hash-code name.) ls$)))
    (lookup-opcd op name. t ls$)))

(defunk oper-stor-incr (floor (static-param) 8))
(defunk rule-stor-incr (floor (static-param) 8))

(defunk alloc-rule-ndx (ls$)
  (letk ((ndx (get-next-rule-ndx ls$))
         (ls$ (ensure-rule ndx (rule-stor-incr)))
         (ls$ (set-next-rule-ndx (1+^ ndx) ls$)))
    (mv^ ndx ls$)))

(defunk arg-list= (n i x args. ls$)
  (cond ((zp n) (endp args.))
        ((endp args.) nil)
        ((/=^ (node.arg x i) (first args.)) nil)
        (t (arg-list= (1-^ n) (1+^ i) x (rest args.) ls$))))

(defunk args= (n i x y ls$)
  (cond ((zp n) t)
        ((/=^ (node.arg x i) (node.arg y i)) nil)
        (t (args= (1-^ n) (1+^ i) x y ls$))))

(defunk node= (x y) :inline
  (or (=^ x y)
      (and (not (and (promoted x) (promoted y)))
           (node=fn x y 0 0 nil ls$))))

(defunk node=fn (x y n i args-p. ls$)
  (if args-p.
      (or (zp n)
          (and (node= (node.arg x i) (node.arg y i))
               (node=fn x y (1-^ n) (1+^ i) t ls$)))
    (assert (and (/=^ x (node-btm))
                 (/=^ y (node-btm)))
     (letk ((opcd-x (node.opcd x))
            (opcd-y (node.opcd y)))
       (and (=^ opcd-x opcd-y)
            (letk ((narg (opcd.narg opcd-x)))
              (node=fn x y narg 0 t ls$)))))))

(defunk find-uniq-sig (node opcd args. ls$)
  (cond ((zp node) (node-btm))
        ((and (=^ (node.opcd node) opcd)
              (arg-list= (opcd.narg opcd) 0 node args. ls$))
         node)
        (t (find-uniq-sig (node.uniq node) opcd args. ls$))))

(defunk find-uniq-node (node opcd x ls$)
  (cond ((zp node) (node-btm))
        ((and (=^ (node.opcd node) opcd)
              (args= (opcd.narg opcd) 0 node x ls$))
         node)
        (t (find-uniq-node (node.uniq node) opcd x ls$))))

(defunk copy-new-args (n y i x ls$)
  (if (zp n) ls$
    (letk ((ls$ (node.set-arg x i (node.arg y i))))
      (copy-new-args (1-^ n) y (1+^ i) x ls$))))

(defunk add-size (x y) :inline
  (if (or (=^ x (size-btm))
          (=^ y (size-btm)))
      (size-btm)
    (letk ((fcnt (+^ (get-size-fcnt x)
		     (get-size-fcnt y)))
           (vcnt (+^ (get-size-vcnt x)
		     (get-size-vcnt y))))
      (if (not (and (<^ fcnt (max-fcnt-valu))
                    (<^ vcnt (max-vcnt-valu))))
          (size-btm)
        (make-node-size vcnt fcnt)))))

(defunk compute-args-size (i n x rslt ls$)
  (if (zp n) rslt
    (compute-args-size (1+^ i) (1-^ n) x
                       (add-size (node.size (node.arg x i)) rslt)
                       ls$)))

(defunk compute-node-size (size opcd narg x) :inline
  (cond ((/=^ size (size-btm))  size)
        ((=^ opcd (opcd-quote)) (make-node-size 0 1))
        ((opcd.is-var opcd)     (make-node-size 1 0))
        ((=^ narg 0)            (make-node-size 0 1))
        (t      (compute-args-size 0 narg x 0 ls$))))

(defunk all-args-prom (x n i ls$)
  (or (zp n)
      (and (promoted (node.arg x i))
           (all-args-prom x (1-^ n) (1+^ i) ls$))))

(defunk args-promoted (x) :inline
  (all-args-prom x (opcd.narg (node.opcd x)) 0 ls$))

(defmacro kern-record-temp-alloc ()
  (if (kern-enable-temp-recording)
      '(if promote. ls$
         (letk ((ndx (opcd.index opcd))
                (num-trans (oper.num-trans ndx))
                (ls$ (oper.set-num-trans ndx (1+^ num-trans))))
           ls$))
    'ls$))

(defunk allocate-node (opcd size promote. ls$)
  (letk ((temp. (not promote.))
         (narg (opcd.narg opcd))
         (num-of-nodes (if temp. (get-num-trans-nodes ls$) (get-num-of-nodes ls$)))
         (alloc-nodes (if temp. (get-alloc-trans ls$) (get-alloc-nodes ls$)))
         (node-step (get-node-step ls$))
         (base-alloc (if temp. (base-trans-alloc) (base-node-alloc)))
         (min-alloc (+^ alloc-nodes narg base-alloc))
         (length (if temp. (length-trans-stor ls$) (length-node-stor ls$)))
         (ls$ (if (>=^ min-alloc length)
                  (letk ((new-length (+^ min-alloc
					 (*^ node-step
					     (+^ (avg-num-args)
						 (if temp. (base-trans-alloc)
						   (base-node-alloc)))))))
                    (if temp. (resize-trans-stor new-length ls$)
                      (resize-node-stor new-length ls$)))
                ls$))
         (node (1-^ min-alloc))
         (ls$ (if temp.
                  (letk ((ls$ (set-alloc-trans min-alloc ls$))
                         (ls$ (set-num-trans-nodes (1+^ num-of-nodes) ls$)))
                    ls$)
                (letk ((ls$ (set-alloc-nodes min-alloc ls$))
                       (ls$ (set-num-of-nodes (1+^ num-of-nodes) ls$)))
                  ls$)))
         (node (if temp. (-^ node) node))
         (ls$ (node.set-opcd node (logand^ (logand^ (logior^ opcd (*^ size (size-shft)))
						    (in-ctx-flip)) ; clear the in-ctx bit on allocation
					   (user-mark-flip))))  ; clear the user-mark bit on allocation
         (ls$ (record-temp-alloc)))
    (mv^ node ls$)))

(defunk complete-promoted-init (new chain hash opcd ls$)
  (letk ((ls$ (node.set-uniq new chain))
         (ls$ (node.set-rep new (node-btm)))
         (ls$ (node.set-dcv new (dcv-empty)))
         (ls$ (set-node-hash hash new ls$))
         (ndx (opcd.index opcd))
         (num-nodes (oper.num-nodes ndx))
         (ls$ (oper.set-num-nodes ndx (1+^ num-nodes))))
    (mv^ new ls$)))

(defunk make-arg-list (n i x ls$)
  (if (zp n) ()
    (cons (node.arg x i)
          (make-arg-list (1-^ n) (1+^ i) x ls$))))

(defunk signature-to-node (sig. ls$)
  (find-uniq-sig (get-node-hash (hash-signature sig.) ls$)
                 (first sig.) (rest sig.) ls$))

(defunk node-to-signature (node ls$)
  (letk ((opcd (node.opcd node))
         (narg (opcd.narg opcd)))
    (cons opcd (make-arg-list narg 0 node ls$))))

(defunk install-node (x promote. ls$)
  (if (eq promote. (promoted x))
      (mv^ x ls$)
    (letk ((temp. (not promote.))
           (opcd  (node.opcd x))
           (size  (node.size x))
           (narg  (opcd.narg opcd))
           (size  (compute-node-size size opcd narg x))
           (hash  (if temp. 0 (hash-node x)))
           (chain (if temp. 0 (get-node-hash hash ls$)))
           (node  (if temp. (node-btm) (find-uniq-node chain opcd x ls$))))
      (assert (not (and temp. (opcd.is-var opcd)))
       (assert (or temp. (=^ opcd (opcd-quote)) (args-promoted x))
        (if (/=^ node (node-btm))
            (mv^ node ls$)
          (letk ((new ls$ (allocate-node opcd size promote. ls$))
                 (ls$ (copy-new-args narg x 0 new ls$)))
            (if temp. (mv^ new ls$)
              (complete-promoted-init new chain hash opcd ls$)))))))))

(defunk install-node-memo (opcd x hash ls$)
  (assert (args-promoted x)
   (letk ((narg (opcd.narg opcd))
          (size (node.size x))
          (size (compute-node-size size opcd narg x))
          (chain (get-node-hash hash ls$))
          (new ls$ (allocate-node opcd size t ls$))
          (ls$ (copy-new-args narg x 0 new ls$))
          (x ls$ (complete-promoted-init new chain hash opcd ls$)))
     (mv^ x ls$))))

(defunk quote-obj-incr  (floor (static-param) 4))
(defunk quote-hash-size (* (quote-obj-incr) 2))
(defunk quote-hash-mask (1- (quote-hash-size)))

(defunk find-quote-obj (ptr obj. ls$)
  (cond ((zp ptr) (qobj-btm))
        ((equal (qobj.obj ptr) obj.) ptr)
        (t (find-quote-obj (qobj.uniq ptr) obj. ls$))))

(defunk make-quote (obj. ls$)
  (letk ((hash (hash-index-evg obj. (quote-hash-mask)))
         (chain (get-quote-hash hash ls$))
         (qobj (find-quote-obj chain obj. ls$)))
    (if (/=^ qobj (qobj-btm))
        (mv^ qobj ls$)
      (letk ((x (get-next-quote ls$))
             (ls$ (ensure-qobj x (quote-obj-incr)))
             (ls$ (qobj.set-obj x obj.))
             (ls$ (qobj.set-uniq x chain))
             (ls$ (set-quote-hash hash x ls$))
             (ls$ (set-next-quote (1+^ x) ls$)))
        (mv^ x ls$)))))

(defunk create-quote (obj.) :inline
  (letk ((v ls$ (make-quote obj. ls$))
         (x ls$ (allocate-node (opcd-quote) (size-btm) nil ls$))
         (ls$ (node.set-arg x 0 v)))
    (install-node x t ls$)))

(defunk install-quote (obj. ls$)
  (cond ((eq obj. t)   (mv^ (node-t) ls$))
        ((eq obj. nil) (mv^ (node-nil) ls$))
        (t (create-quote obj.))))

(defunk install-var-oper (name. ls$)
  (letk ((hash (fn-hash-code name.))
         (chain (get-op-hash hash ls$))
         (opcd (lookup-opcd chain name. t ls$))
         (ndx (if (/=^ opcd (opcd-btm))
                  (opcd.index opcd)
                (get-next-op-ndx ls$)))
         (ls$ (if (/=^ opcd (opcd-btm))
                  ls$
                (letk ((ls$ (ensure-oper ndx (oper-stor-incr)))
                       (ls$ (oper.set-uniq ndx chain))
                       (ls$ (set-op-hash hash ndx ls$))
                       (ls$ (set-next-op-ndx (1+^ ndx) ls$))
                       (ls$ (oper.set-next-stk ndx (opcd-btm)))
                       (ls$ (oper.set-bound ndx (node-btm))))
                  ls$)))
         (ls$ (oper.set-name ndx name.))
         (ls$ (oper.set-is-var ndx t))
         (ls$ (oper.set-rules ndx ()))
         (ls$ (oper.set-narg ndx 0))
         (ls$ (oper.set-num-nodes ndx 0))
         (ls$ (oper.set-num-trans ndx 0))
         (ls$ (oper.set-exec ndx (node-btm)))
         (ls$ (oper.set-boolp ndx nil))
         (ls$ (oper.set-assume-tbr ndx nil))
         (ls$ (oper.set-assume-fbr ndx nil))
         (ls$ (oper.set-is-if ndx nil))
         (ls$ (oper.set-is-equal ndx nil))
         (ls$ (oper.set-non-nil ndx nil)))
    (mv^ ndx ls$)))

(defunk get-var-opcode (name. ls$)
  (letk ((opcd (find-var-opcd name.)))
    (if (/=^ opcd (opcd-btm))
        (mv^ opcd ls$)
      (letk ((op ls$ (install-var-oper name. ls$)))
        (mv^ (make-opcd 0 t nil nil op) ls$)))))

(defunk install-var (name. ls$)
  (letk ((opcd ls$ (get-var-opcode name. ls$))
         (x ls$ (allocate-node opcd (size-btm) nil ls$))
         (x ls$ (install-node x t ls$)))
    (mv^ x ls$)))

(mutual-recursionk
(defunk term-to-node (term. ls$)
  (cond
   ((atom term.)
    (assert (symbolp term.)
     (install-var term. ls$)))
   ((eq (first term.) 'quote)
    (install-quote (second term.) ls$))
   ((and (consp (first term.))
         (eq (first (first term.)) 'lambda))
    (mv^ (er0 hard 'term-to-node
              "should not encounter lambdas in mapping term to node")
         ls$))
   (t
    (letk ((opcd (find-fn-opcd (first term.)))
           (narg (opcd.narg opcd)))
      (if (or (=^ opcd (opcd-btm))
              (/=^ narg (length (rest term.))))
          (mv^ (er0 hard 'term-to-node
                    "could not locate appropriate opcode for term ~x0 ~x1"
                    (first term.) opcd)
               ls$)
        (letk ((x ls$ (allocate-node opcd (size-btm) nil ls$))
               (ls$ (rest-to-args (rest term.) 0 x ls$)))
          (install-node x t ls$)))))))

(defunk rest-to-args (args. i x ls$)
  (if (endp args.) ls$
    (letk ((arg ls$ (term-to-node (first args.) ls$))
           (ls$ (node.set-arg x i arg)))
      (rest-to-args (rest args.) (1+^ i) x ls$))))
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| functions implementing undo-stk and depth ctx (dctx)                       |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defunk undo-btm                 0)
(defunk undo-stk-increment   12286)
(defunk undo-chains-increment 1048)

(defunk dctx-max-rep (- (fixnum-size) 2))
(defunk dcv-max-rep (1- (ash 1 (1+ (dctx-max-rep)))))

(defunk alloc-undo-ptr (ls$)
  (letk ((free (get-undo-free-list ls$)))
    (if (/=^ free (undo-btm))
        (letk ((ls$ (set-undo-free-list (undo.chain free) ls$)))
          (mv^ free ls$))
      (letk ((top (get-undo-top ls$))
             (ls$ (ensure-undo top (undo-stk-increment)))
             (ls$ (set-undo-top (1+^ top) ls$)))
        (mv^ top ls$)))))

(defunk memo-args= (x m n i ls$)
  (or (zp n)
      (and (=^ (node.arg x i) (memo.arg m i))
           (memo-args= x m (1-^ n) (1+^ i) ls$))))

(defunk find-max-dctx (dcv dcx)
  (cond ((zp dcx) (dctx-0))
        ((/=^ (logand^ (ash^ 1 dcx) dcv) 0) dcx)
        (t (find-max-dctx dcv (1-^ dcx)))))

(defunk max-in-dcv (dcv) :inline
  (if (=^ dcv (dcv-empty)) (dctx-0) (find-max-dctx dcv (dctx-max-rep))))

(defunk create-new-undo (x dcv old-r old-d ls$)
  (if (=^ dcv (dcv-empty)) ls$
    (letk ((dcx (max-in-dcv dcv))
           (chain (get-undo-chains dcx ls$))
           (uptr ls$ (alloc-undo-ptr ls$))
           (ls$ (undo.set-node uptr x))
           (ls$ (undo.set-rep uptr old-r))
           (ls$ (undo.set-dcv uptr old-d))
           (ls$ (undo.set-chain uptr chain))
           (ls$ (set-undo-chains dcx uptr ls$)))
      ls$)))

(defunk create-update-rep (node new-r dcv ls$)
  (if (>=^ dcv (dcv-max-rep)) ls$
    (letk ((old-r (node.rep node))
           (old-d (node.dcv node))
           (ls$ (create-new-undo node dcv old-r old-d ls$))
           (ls$ (node.set-rep node new-r))
           (ls$ (node.set-dcv node dcv)))
      ls$)))

;; The following is the ratio from entries in the unique node hash-table and
;; the memo-table. Since we reuse the hashing function, we have to divide down
;; the hash address in order to get the memo table address.

(defunk hash-memo-divisor 4)

(defunk check-memos (x ls$)
  (if (promoted x)
      (mv^ x ls$)
    (letk ((opcd (node.opcd x))
           (narg (opcd.narg opcd)))
      (if (or (>^ narg (max-memo-narg))
              (not (args-promoted x)))
          (mv^ x ls$)
        (letk ((h (hash-node x))
               (node (find-uniq-node (get-node-hash h ls$) opcd x ls$)))
          (if (/=^ node (node-btm))
              (mv^ node ls$)
            (letk ((m (floor^ h (hash-memo-divisor)))
                   (m-opcd (memo.opcd m))
                   (match. (and (=^ opcd m-opcd)
                                (or (<=^ narg (num-1memo-args))
                                    (=^ (memo.opcd (1+^ m))
                                        (opcd-memo-mrkr)))
                                (memo-args= x m narg 0 ls$))))
              (if (not match.)
                  (mv^ x ls$)
                (letk ((node ls$ (install-node-memo opcd x h ls$))
                       (ls$ (if (/=^ (node.rep node) (node-btm)) ls$
                              (create-update-rep node (memo.rslt m) (memo.dcv m) ls$))))
                  (mv^ node ls$))))))))))

(defunk memo-copy-args (m x n i ls$)
  (if (zp n) ls$
    (letk ((ls$ (memo.set-arg m i (node.arg x i))))
      (memo-copy-args m x (1-^ n) (1+^ i) ls$))))

(defunk create-memo-if-needed (x rep dcv ls$)
  (assert (and (temp-node x) (>^ rep 0))
   (letk ((opcd (node.opcd x))
          (narg (opcd.narg opcd)))
     (if (or (>^ narg (max-memo-narg))
             (not (args-promoted x))
             (>=^ dcv (dcv-max-rep)))
         ls$
       (letk ((m (floor^ (hash-node x) (hash-memo-divisor)))
              (ls$ (memo.set-opcd m opcd))
              (ls$ (memo.set-rslt m rep))
              (ls$ (memo.set-dcv  m dcv))
              (ls$ (memo-copy-args m x narg 0 ls$))
              (ls$ (if (<=^ narg (num-1memo-args)) ls$
                     (memo.set-opcd (1+^ m) (opcd-memo-mrkr))))
              (ls$ (create-new-undo (-^ m) dcv (node-btm) (dcv-btm) ls$)))
         ls$)))))

(defunk update-rep (node rep dcv id ls$)
  (declare (ignore id))
  (assert (or (and (>=^ dcv (dcv-btm))
                   (/=^ node (node-btm))
                   (/=^ (node.opcd node) (opcd-quote)))
              (list dcv node rep (node.opcd node)))
   (cond ((=^ rep (node-btm))
          (assert (promoted node)
           (node.set-rep node (node-btm))))
         ((temp-node node)
          (create-memo-if-needed node rep dcv ls$))
         ((=^ rep node) ls$)
         ((=^ dcv (dcv-btm))
          (letk ((ls$ (node.set-rep node rep))
                 (ls$ (node.set-dcv node (dcv-empty))))
            ls$))
         ((=^ (node.rep node) rep) ls$)
         (t (create-update-rep node rep dcv ls$)))))

(defunk pop-undo-stk-fn (uptr depth ls$)
  (cond ((zp depth)
         (prog2$ (er0 hard 'pop-undo-stk-fn
                      "An internal error in the KAS algorithm has been detected. ~
                       Please notify current maintainer of KAS")
           ls$))
        ((zp uptr) ls$)
        (t
         (letk ((node (undo.node uptr))
                (chain (undo.chain uptr))
                (ls$ (cond ((=^ node (node-btm))
			    (letk ((dcv (undo.dcv uptr)))
			      (if (=^ dcv (dcv-btm))
				  (node.set-in-ctx (undo.rep uptr) nil)
				(set-curr-ctx-stk dcv (undo.rep uptr) ls$))))
                           ((promoted node)
                            (letk ((ls$ (node.set-rep node (undo.rep uptr)))
                                   (ls$ (node.set-dcv node (undo.dcv uptr))))
                              ls$))
                           (t (memo.set-opcd (-^ node) (opcd-btm))))) ;; clear the memo
                (free (get-undo-free-list ls$))
                (ls$ (undo.set-chain uptr free))
                (ls$ (set-undo-free-list uptr ls$)))
           (pop-undo-stk-fn chain (1-^ depth) ls$)))))

(defunk pop-undo-stk (dcx) :inline
  (letk ((undo (get-undo-chains dcx ls$))
         (ls$ (set-undo-chains dcx (undo-btm) ls$))
         (ls$ (pop-undo-stk-fn undo (1+^ (get-undo-top ls$)) ls$)))
    ls$))

(defunk create-new-dctx (ls$)
  (letk ((dcx (get-current-dctx ls$))
         (dcx (1+^ dcx))
         (ls$ (if (<=^ (ash^ 1 dcx) (dcv-max-rep)) ls$
                (prog2$ (and (not (get-warned-ctx-depth ls$))
                             (cw "NOTE: context depth exceeded maximum ctx. limit. performance will be hindered."))
                        (set-warned-ctx-depth t ls$))))
         (ls$ (if (<^ dcx (length-undo-chains ls$))
                  ls$
                (resize-undo-chains
                 (+^ dcx (undo-chains-increment)) ls$)))
         (ls$ (set-undo-chains dcx (node-btm) ls$))
         (ls$ (set-current-dctx dcx ls$)))
    (mv^ dcx ls$)))

(defunk restore-previous-state (dcx- dcx+ age ls$)
  (letk ((ls$ (pop-undo-stk dcx+))
         (ls$ (set-current-dctx dcx- ls$))
         (ls$ (set-current-age age ls$)))
    ls$))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| heuristic for generating case splits implemented as a sieve                |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defunk non-nilp (x) :inline
  (or (=^ x (node-t))
      (letk ((opcd (node.opcd x)))
        (or (and (/=^ x (node-nil))
                 (=^ opcd (opcd-quote)))
            (oper.non-nil (opcd.index opcd))))))

(defunk is-boolp (x) :inline
  (or (=^ x (node-t))
      (=^ x (node-nil))
      (oper.boolp (opcd.index (node.opcd x)))))

;; The following is the user stobj which can be used to store whatever
;; data the user wants to maintain during the simplification process.
(define-stobj+ us$
  (dynamic-user-state-obj :object)
  (candidate-stor         :fixnum-array)
  (candidate-hash         :fixnum-array)
  (candidate-mask         :fixnum)
  (candidate-step         :fixnum)
  (next-candidate         :fixnum)
  (candidate-stk          :fixnum-array)
  (candidate-top          :fixnum)
  (opcd-bv                :fixnum)
)

(define-user-record-array candidate
  (:fixnum candidate-stor (node weight tst chain)))

(defunk candidate-tbl-init  (sp) (floor (expt 2 sp) 64))
(defunk candidate-tbl-step  (sp) (candidate-tbl-init sp))
(defunk candidate-hash-size (sp) (* (candidate-tbl-init sp) 2))
(defunk candidate-hash-mask (sp) (- (candidate-hash-size sp) 1))

(defunk init-candidate-hash (n us$)
  (if (zp n) us$
    (letk ((n (1-^ n))
           (us$ (set-candidate-hash n (node-btm) us$)))
      (init-candidate-hash n us$))))

(defunk user-init (ls$ us$)
  (letk ((sp (get-kern-size-param ls$))
         (us$ (set-opcd-bv (opcd-btm) us$))
         (us$ (set-dynamic-user-state-obj nil us$))
         (us$ (resize-candidate-hash (candidate-hash-size sp) us$))
         (us$ (init-candidate-hash (candidate-hash-size sp) us$))
         (us$ (set-candidate-mask (candidate-hash-mask sp) us$))
         (us$ (ensure-candidate (candidate-tbl-init sp) 0))
         (us$ (set-candidate-step (candidate-tbl-step sp) us$))
         (us$ (set-next-candidate (1+^ (node-btm)) us$))
         (us$ (resize-candidate-stk (candidate-hash-size sp) us$))
         (us$ (set-candidate-top 0 us$)))
    us$))

; We implement a heuristic for introducing case-splits. The basic idea is to
; case-split on the most frequently referenced term which appears in the test
; of an if (or is equated in the test of an if).
;
; 1. Introduce entry for each candidate node
; 2. Weighted count of all references to candidate nodes
; 3. determination of heaviest candidate in weighting
;    -- and clear the hash-table at the same time.

(defunk hash-candidate (node) :inline
  (logand^ node (get-candidate-mask us$)))

(defunk find-candidate-in-chain (cand node us$)
  (cond ((zp cand) (node-btm))
        ((=^ (candidate.node cand) node) cand)
        (t (find-candidate-in-chain (candidate.chain cand) node us$))))

(defunk add-candidate-node (node tst us$)
  (letk ((hash (hash-candidate node))
         (chain (get-candidate-hash hash us$))
         (cand (find-candidate-in-chain chain node us$)))
    (if (/=^ cand (node-btm)) us$
      (letk ((cand (get-next-candidate us$))
             (us$ (ensure-candidate cand (get-candidate-step us$)))
             (us$ (candidate.set-node   cand node))
             (us$ (candidate.set-weight cand 0))
             (us$ (candidate.set-tst    cand tst))
             (us$ (candidate.set-chain  cand chain))
             (us$ (set-candidate-hash hash cand us$))
             (us$ (set-next-candidate (1+^ cand) us$)))
        (if (/=^ chain (node-btm)) us$
          (letk ((top (get-candidate-top us$))
                 (us$ (set-candidate-stk top hash us$))
                 (us$ (set-candidate-top (1+^ top) us$)))
            us$))))))

(mutual-recursionk
(defunk if-subterm (x ls$)
  (letk ((opcd (node.opcd x)))
    (cond
     ((=^ opcd (opcd-quote)) nil)
     ((opcd.is-var opcd) nil)
     ((opcd.is-if opcd) t)
     (t (if-subterm-args (opcd.narg opcd) 0 x ls$)))))

(defunk if-subterm-args (n i x ls$)
  (and (not (zp n))
       (or (if-subterm (node.arg x i) ls$)
           (if-subterm-args (1-^ n) (1+^ i) x ls$))))
)

(defunk add-candidate-nodes (opcd x ls$ us$)
  (if (not (opcd.is-if opcd)) us$
    (letk ((tst (node.arg x 0)))
      (if (or (not (is-boolp tst)) (if-subterm tst ls$)) us$
        (letk ((us$ (add-candidate-node tst tst us$)))
          (if (/=^ (node.opcd tst) (opcd-equal)) us$
            (add-candidate-node (node.arg tst 0) tst us$)))))))

(mutual-recursionk
(defunk add-candidates-for-node (x ls$ us$)
  (letk ((opcd (node.opcd x)))
    (if (or (=^ opcd (opcd-quote)) (opcd.is-var opcd)) us$
      (letk ((us$ (add-candidate-nodes opcd x ls$ us$)))
        (add-candidates-for-args (opcd.narg opcd) 0 x ls$ us$)))))

(defunk add-candidates-for-args (n i x ls$ us$)
  (if (zp n) us$
    (letk ((us$ (add-candidates-for-node (node.arg x i) ls$ us$)))
      (add-candidates-for-args (1-^ n) (1+^ i) x ls$ us$))))
)

(defunk case-split-candidates (x ls$ us$)
  (letk ((opcd (node.opcd x)))
    (cond
     ((or (=^ opcd (opcd-quote))
          (opcd.is-var opcd))
      us$)
     ((and (opcd.is-if opcd)
           (not (if-subterm (node.arg x 0) ls$)))
      (letk ((us$ (case-split-candidates (node.arg x 1) ls$ us$)))
        (case-split-candidates (node.arg x 2) ls$ us$)))
     ((=^ (opcd.narg opcd) 1)
      (case-split-candidates (node.arg x 0) ls$ us$))
     (t
      (add-candidates-for-node x ls$ us$)))))


;; An upper bound on the weight for any candidate. We use this as
;; a cap on nodes which may get too much weight due to reconvergent
;; nodes (in those cases, we are probably already in trouble), and
;; we need a mechanism to ensure that we maintain fixnums.
(defunk max-candidate-weight (expt 2 20))

(defunk adjust-candidate-weight (x weight us$)
  (letk ((hash (hash-candidate x))
         (chain (get-candidate-hash hash us$))
         (cand (find-candidate-in-chain chain x us$)))
    (if (=^ cand (node-btm)) us$
      (letk ((curr (candidate.weight cand))
             (new (if (and (<^ curr (max-candidate-weight))
                           (<^ weight (max-candidate-weight))
                           (<^ (+^ curr weight) (max-candidate-weight)))
                      (+^ curr weight)
                    (max-candidate-weight)))
             (us$ (candidate.set-weight cand new)))
        us$))))

(defunk decrement-weight (weight decr) :inline
  (if (>^ weight decr) (-^ weight decr) 1))

(mutual-recursionk
(defunk weigh-case-splits (x weight ls$ us$)
  (letk ((opcd (node.opcd x)))
    (cond
     ((or (=^ opcd (opcd-quote))
          (opcd.is-var opcd))
      us$)
     ((opcd.is-if opcd)
      (letk ((br-w (decrement-weight weight 2))
             (us$ (weigh-case-splits (node.arg x 1) br-w ls$ us$))
             (us$ (weigh-case-splits (node.arg x 2) br-w ls$ us$)))
        (weigh-case-splits (node.arg x 0) (decrement-weight weight 1) ls$ us$)))
     (t
      (letk ((us$ (adjust-candidate-weight x weight us$)))
        (weigh-case-split-args (opcd.narg opcd) 0 x weight ls$ us$))))))

(defunk weigh-case-split-args (n i x w ls$ us$)
  (if (zp n) us$
    (letk ((us$ (weigh-case-splits (node.arg x i) w ls$ us$)))
      (weigh-case-split-args (1-^ n) (1+^ i) x w ls$ us$))))
)

(defunk find-better-candidate (cand max us$)
  (cond ((zp cand) max)
        ((=^ max (node-btm)) cand)
        ((>^ (candidate.weight cand) (candidate.weight max))
         (find-better-candidate (candidate.chain cand) cand us$))
        (t (find-better-candidate (candidate.chain cand) max us$))))

(defunk find-and-clear-split (ptr max us$)
  (if (zp ptr) (mv^ max us$)
    (letk ((ptr (1-^ ptr))
           (hash (get-candidate-stk ptr us$))
           (cand (get-candidate-hash hash us$))
           (max (find-better-candidate cand max us$))
           (us$ (set-candidate-hash hash (node-btm) us$)))
      (find-and-clear-split ptr max us$))))

(defunk determine-case-split (us$)
  (letk ((top (get-candidate-top us$))
         (cand us$ (find-and-clear-split top (node-btm) us$)))
    (if (=^ cand (node-btm))
        (mv^ (node-btm) us$)
      (letk ((split (candidate.tst cand))
             (us$ (set-candidate-top 0 us$))
             (us$ (set-next-candidate (1+^ (node-btm)) us$)))
        (mv^ split us$)))))

(defunk valid-case-split (x) :inline
  (and (/=^ x (node-btm))
       (promoted x)
       (letk ((opcd (node.opcd x)))
         (and (/=^ opcd (opcd-quote))
              (not (opcd.is-var opcd))))))

;; initial weight which is distributed differently through if args
;; and added to the weights accumulating in the candidate table.
(defunk initial-case-split-weight 32)

(defunk generate-case-split (sieve. x ls$ us$)
  (letk ((n (second sieve.))
         (opcd (node.opcd n)))
    (if (not (opcd.is-var opcd))
        (mv () us$)
      (letk ((var (opcd.index opcd))
             (us$ (case-split-candidates x ls$ us$))
             (us$ (weigh-case-splits x (initial-case-split-weight) ls$ us$))
             (split us$ (determine-case-split us$)))
        (mv (and (valid-case-split split)
                 (list (list :set-var-bound var
                             (node-to-signature split ls$))))
            us$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| user function stobj (us$) and user function call                           |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The user-fn responds with an answer and a list of "update"s to the kernel
; logic state stobj ls$. The reason we use this interface is to restrict (in a
; clear logical sense) what "effects" the user-fn can have on ls$ (which stores
; all of the information relevant to the soundness of the kernel
; simplifier). The following updates are currently supported/allowed:
;
; (:set-var-bound     <var>  <node>)        <var>   is nfix index, <node> is nfix index
; (:set-rule-sieves   <rule> <sieves>)
; (:set-rule-enabled  <rule> <flag>)        <rule>  is nfix index, <flag> is boolean
; (:set-rule-always   <rule> <flag>)        <rule>  is nfix index, <flag> is boolean
; (:set-rule-ctr      <rule> <ctr>)
; (:set-node-step     <step>)               <step>  is nfix
; (:set-node-limit    <limit>)              <limit> is nfix
; (:change-rule-order <rule> <pos>)         <rule>  is nfix index, <pos>  is natural
; (:set-rule-traced   <rule> <mark>)
; (:set-user-mark     <node> <mark>)
;
;;;; nfix is a natural fixnum
;
; The function process-update does not place any assumptions on the
; update structure from the user-fn, so some checks are required.

(defunk first-oper-ndx 1)
(defunk first-rule-ndx 1)

(defunk drop-rule (rules. ndx)
  (cond ((endp rules.) ())
        ((=^ (car rules.) ndx) (cdr rules.))
        (t (cons (car rules.)
                 (drop-rule (cdr rules.) ndx)))))

(defunk place-rule (rules. ndx pos)
  (if (or (zp pos) (endp rules.))
      (cons ndx rules.)
    (cons (car rules.)
          (place-rule (cdr rules.) ndx (1-^ pos)))))

(defunk move-rule (rules. ndx pos)
  (place-rule (drop-rule rules. ndx) ndx pos))

(defunk is-legal-rule (rule. ls$)
  (and (fixnump rule.)
       (>=^ rule. (first-rule-ndx))
       (<^ rule. (get-next-rule-ndx ls$))))

(defunk is-legal-oper (op. ls$)
  (and (fixnump op.)
       (>=^ op. (first-oper-ndx))
       (<^ op. (get-next-op-ndx ls$))))

(defunk is-legal-sig-args (sig.)
  (or (null sig.)
      (and (consp sig.)
           (fixnump (first sig.))
           (is-legal-sig-args (rest sig.)))))

(defunk is-legal-sig (sig.)
  (and (consp sig.)
       (fixnump (first sig.))
       (is-legal-sig-args (rest sig.))))

(defunk legal-sieves (sieves.)
  (or (null sieves.)
      (and (consp sieves.)
           (consp (first sieves.))
           (keywordp (first (first sieves.)))
           (true-listp (rest (first sieves.)))
           (legal-sieves (rest sieves.)))))

(defunk install-arg-as-node (arg. ls$)
  (if (termp arg. (get-current-world ls$))
      (term-to-node arg. ls$)
    (term-to-node (list 'quote arg.) ls$)))

(defunk install-sieve-args (args. ls$)
  (if (endp args.)
      (mv () ls$)
    (letk ((node ls$ (install-arg-as-node (first args.) ls$))
           (rst. ls$ (install-sieve-args (rest args.) ls$)))
      (mv (cons node rst.) ls$))))

(defunk install-sieves (sieves. ls$)
  (if (endp sieves.)
      (mv () ls$)
    (letk ((args. ls$ (install-sieve-args (rest (first sieves.)) ls$))
           (rst. ls$ (install-sieves (rest sieves.) ls$)))
      (mv (acons (first (first sieves.)) args. rst.) ls$))))

(defunk er-process-update-arg (msg.) :inline
  (er hard 'process-update
      "ill-formed user-fn update. message: ~x0 update: ~x1"
      msg. upd.))

(defunk er-process-update (msg.) :inline
  (prog2$ (er-process-update-arg msg.) ls$))

(defunk pu-bool (x.) :inline
  (if (is-boolean x.) x. (er-process-update-arg "expected boolean value")))

(defunk pu-nat (x. lo. hi.) :inline
  (if (and (fixnump x.)
           (or (null lo.) (>= x. lo.))
           (or (null hi.) (<= x. hi.)))
      x.
    (er-process-update-arg "expected natural number")))

(defunk find-rule-id (rules. rune. ls$)
  (cond ((endp rules.) nil)
        ((equal (rule.rune (first rules.)) rune.)
         (first rules.))
        (t (find-rule-id (rest rules.) rune. ls$))))

(defunk pu-rule (x.) :inline
  (if (is-legal-rule x. ls$) x.
    (if (atom x.)
        (er-process-update-arg "expected legal rule or rune")
      (letk ((op. (car x.))
             (rune. (cdr x.))
             (opcd (find-fn-opcd op.)))
        (if (=^ opcd (opcd-btm))
            (er-process-update-arg "could not find rune base op.")
          (letk ((rule. (find-rule-id (oper.rules op.) rune. ls$)))
            (if (not rule.)
                (er-process-update-arg "could not find rule for rune")
              rule.)))))))

(defunk pu-free-var (x.) :inline
  (if (not (is-legal-oper x. ls$))
      (er-process-update-arg "expected legal free var. name")
    (if (/=^ (oper.bound x.) (node-btm))
        (er-process-update-arg "expected free var. to be unbound")
      x.)))

(defunk pu-signature-node (x.) :inline
  (if (not (is-legal-sig x.))
      (er-process-update-arg "expected legal node signature")
    (letk ((n. (signature-to-node x. ls$)))
      (if (= n. (node-btm))
          (er-process-update-arg "expected signature to define existing promoted node")
        n.))))

(defunk pu-sieves (x.) :inline
  (if (legal-sieves x.) x.
    (er-process-update-arg "expected well-formed list of sieves")))

(defunk pu-trace-mark (x.) :inline
  (if (is-trace-mark x.) x.
    (er-process-update-arg "expected t/nil, :all, or symbol-list for trace mark")))

(defunk set-var-bound (var node) :inline
  (letk ((ls$ (oper.set-bound var node))
         (ls$ (oper.set-next-stk var (get-var-chg-stk ls$)))
         (ls$ (set-var-chg-stk var ls$)))
    ls$))

(defunk process-update (upd. ls$)
  (if (not (true-listp upd.))
      (er-process-update "expected update to be a true list")
    (letk ((cmd. (first upd.))
           (a1. (second upd.))
           (a2. (third upd.)))
      (case cmd.
            (:set-var-bound
             (set-var-bound (pu-free-var a1.) (pu-signature-node a2.)))
            (:set-rule-sieves
             (letk ((sieves. ls$ (install-sieves (pu-sieves a2.) ls$)))
               (rule.set-sieves (pu-rule a1.) sieves.)))
            (:set-rule-enabled
             (rule.set-enabled (pu-rule a1.) (pu-bool a2.)))
            (:set-rule-ctr
             (rule.set-ctr (pu-rule a1.) (pu-nat a2. 0 nil)))
            (:set-node-step
             (set-node-step (pu-nat a1. 1 (maximum-array-size)) ls$))
            (:set-node-limit
             (set-node-limit (pu-nat a1. 1 (maximum-array-size)) ls$))
            (:change-rule-order
             (letk ((rule (pu-rule a1.))
                    (op (rule.op rule))
                    (pos. (pu-nat a2. 0 nil)))
               (oper.set-rules op (move-rule (oper.rules op) rule pos.))))
            (:set-rule-traced
             (rule.set-traced (pu-rule a1.) (pu-trace-mark a2.)))
	    (:set-user-mark
	     (node.set-user-mark (pu-signature-node a1.) (pu-bool a2.)))
            (t (er-process-update "illegal command encountered in update"))))))

(defunk process-updates (updates. ls$)
  (if (atom updates.) ls$
    (letk ((ls$ (process-update (first updates.) ls$)))
      (process-updates (rest updates.) ls$))))

(defunk maximum-p-fn-count (1- (expt 2 19)))

(mutual-recursionk
(defunk node-aux-cnt (x typ. ls$)
  (letk ((opcd (node.opcd x)))
    (cond ((=^ opcd (opcd-quote))
           (if (not (eq typ. :quote-fns)) 0
             (mask^ (fn-count-evg (qobj.obj (node.arg x 0)))
                    (maximum-p-fn-count))))
          ((opcd.is-var opcd) (if (eq typ. :vars) 1 0))
          (t (+^ (if (eq typ. :fns) 1 0)
		 (args-aux-cnt x (opcd.narg opcd) 0 typ. 0 ls$))))))

(defunk args-aux-cnt (x n i typ. r ls$)
  (if (zp n) r
    (letk ((r (+^ r (node-aux-cnt (node.arg x i) typ. ls$))))
      (args-aux-cnt x (1-^ n) (1+^ i) typ. r ls$))))
)

(defunk node-var-cnt (x) :inline
  (node-aux-cnt x :vars ls$))

(defunk node-fn-cnt (x) :inline
  (node-aux-cnt x :fns ls$))

(defunk node-q-fn-cnt (x) :inline
  (node-aux-cnt x :quote-fns ls$))

(mutual-recursionk
(defunk lex-order (x y ls$)
  (letk ((opcd-x (node.opcd x))
         (opcd-y (node.opcd y)))
    (or (<^ opcd-x opcd-y)
        (and (=^ opcd-x opcd-y)
             (if (=^ opcd-x (opcd-quote))
                 (letk ((x-o. (qobj.obj (node.arg x 0)))
                        (y-o. (qobj.obj (node.arg y 0))))
                   (and (not (equal x-o. y-o.))
                        (lexorder x-o. y-o.)))
               (args-order (opcd.narg opcd-x) 0 x y ls$))))))

(defunk args-order (n i x y ls$)
  (cond ((zp n) nil)
        ((lex-order (node.arg x i) (node.arg y i) ls$) t)
        ((not (node= (node.arg x i) (node.arg y i))) nil)
        (t (args-order (1-^ n) (1+^ i) x y ls$))))
)

(defunk term-order (x y ls$)
  (and (/=^ x (node-btm))
       (/=^ y (node-btm))
       (letk ((x-size (node.size x))
              (y-size (node.size y)))
         (if (and (/=^ x-size (size-btm))
                  (/=^ y-size (size-btm))
                  (/=^ x-size y-size))
             (<^ x-size y-size)
           (letk ((x-cnt (node-var-cnt x))
                  (y-cnt (node-var-cnt y)))
             (or (<^ x-cnt y-cnt)
                 (and (=^ x-cnt y-cnt)
                      (letk ((x-cnt (node-fn-cnt x))
                             (y-cnt (node-fn-cnt y)))
                        (or (<^ x-cnt y-cnt)
                            (and (=^ x-cnt y-cnt)
                                 (letk ((x-cnt (node-q-fn-cnt x))
                                        (y-cnt (node-q-fn-cnt y)))
                                   (or (<^ x-cnt y-cnt)
                                       (and (=^ x-cnt y-cnt)
                                            (lex-order x y ls$))))))))))))))

(defunk bdd< (x y op-bv) :inline
  (and (/=^ x (node-btm))
       (/=^ y (node-btm))
       (letk ((op-x (node.opcd x)))
         (and (=^ op-x op-bv)
              (letk ((op-y (node.opcd y)))
                (cond ((=^ op-y op-bv)
                       (node< x y))
                      ((opcd.is-if op-y)
                       (letk ((y (node.arg y 0))
                              (op-y (node.opcd y)))
                         (and (=^ op-y op-bv)
                              (node< x y))))
                      (t t)))))))

(defunk bdd-order-p (x y ls$ us$)
  (letk ((op-bv1 (get-opcd-bv us$))
         (op-bv2 (if (=^ op-bv1 (opcd-btm)) (find-fn-opcd 'bv) op-bv1)))
    (if (=^ op-bv2 (opcd-btm))
        (mv (er hard 'bdd-order-p "could not locate opcd for operator bv") us$)
      (letk ((us$ (if (=^ op-bv1 (opcd-btm)) (set-opcd-bv op-bv2 us$) us$)))
        (mv (bdd< x y op-bv2) us$)))))

(defunk bound-node (x) :inline
  (letk ((opcd (node.opcd x)))
    (if (opcd.is-var opcd)
        (oper.bound (opcd.index opcd))
      (node-btm))))

(defunk create-sieve-arg (x ls$)
  (letk ((rep (node.rep x))
         (bound (bound-node x)))
    (cond ((/=^ bound (node-btm)) (node-to-term bound))
          ((>^ rep 0)             (node-to-term rep))
          (t                      (node-to-term x)))))

(defunk create-sieve-args (args. ls$)
  (if (endp args.) ()
    (cons (create-sieve-arg (first args.) ls$)
          (create-sieve-args (rest args.) ls$))))

(defunk process-fast-sieve (sieve.) :inline
  (case (first sieve.)
        (:quotep (=^ (node.opcd (bound-node (second sieve.)))
                     (opcd-quote)))
        (:non-nilp (non-nilp (bound-node (second sieve.))))
        (:boolp (is-boolp (bound-node (second sieve.))))
        (:termordp (term-order (bound-node (second sieve.))
                               (bound-node (third sieve.))
                               ls$))
        (:nodeordp (node< (bound-node (second sieve.))
			  (bound-node (third sieve.))))
        (t :no-rslt)))

(defunk process-slow-sieve (sieve. x ls$ us$)
  (case (first sieve.)
        (:bddordp (bdd-order-p (bound-node (second sieve.))
                               (bound-node (third sieve.))
                               ls$ us$))
        (:case-split (generate-case-split sieve. x ls$ us$))
        (t (mv () us$))))

; Matt K. mod, 10/2017: Since ev-fncall-w is called in funcall below but is now
; untouchable, a change is necessary.  (Note that funcall is a macro that
; generates a call of ev-fncall-w, which is why a change wasn't necessary
; earlier.)  Fortunately, kas.acl2 specifies :ttags :all, so we can introduce a
; trust tag to remove ev-fncall-w as an untouchable.  An alternate solution,
; not yet tried (at least by me), is to use ev-fncall-w! instead; but that
; might slow things down a lot because of the extra checking done.  Note that
; magic-ev-fncall isn't an option, because state isn't available in funcall
; (though we could consider adding it).

(defttag :ev-fncall-w-ok)
(remove-untouchable ev-fncall-w t)
(defttag nil)

(defunk process-user-sieve (sieve. r ls$ us$)
  (if (not (eq (first sieve.) :funcall))
      (mv nil () us$)
    (letk ((rune. (rule.rune r))
	   (args. (create-sieve-args (rest sieve.) ls$)))
      (if (not (and (consp (first args.))
		    (eq (first (first args.)) 'quote)
		    (symbolp (second (first args.)))))
	  (mv (er hard 'process-sieve
		  "In applying ~x0: first argument to :funcall sieve should be quoted name of function: ~x1"
		  rune. (first args.))
	      () us$)
	(letk ((op. (second (first args.)))
	       (args. (rest args.))
	       (st. (get-dynamic-user-state-obj us$))
	       (wrld. (get-current-world ls$))
	       (erp. val. (funcall op. (list args. st. wrld.))))
          (cond (erp.
		 (mv (er hard 'process-sieve
			 "In applying ~x0: encountered error in evaluating sieve: ~x1"
			 rune. sieve.)
		     () us$))
		((is-boolean val.)
		 (mv val. () us$))
		((and (consp val.)
		      (true-listp val.)
		      (= (length val.) 3))
		 (letk ((us$ (set-dynamic-user-state-obj (third val.) us$)))
		       (mv (first val.) (second val.) us$)))
		(t
		 (mv (er hard 'process-sieve
			 "In applying ~x0: expected result from ~x1 must either be boolean or a triple"
			 rune. op.)
		     () us$))))))))

(defunk process-sieve (sieve. x r ls$ us$)
  (letk ((rslt. (process-fast-sieve sieve.)))
    (if (is-boolean rslt.) (mv rslt. () us$)
      (letk ((upds. us$ (process-slow-sieve sieve. x ls$ us$)))
        (if upds. (mv t (and (consp upds.) upds.) us$)
          (process-user-sieve sieve. r ls$ us$))))))

(defunk process-each-sieve (sieves. x r ls$ us$)
  (if (endp sieves.)
      (mv t ls$ us$)
    (letk ((ok. upds. us$ (process-sieve (first sieves.) x r ls$ us$))
           (ls$ (process-updates upds. ls$)))
      (if (not ok.)
          (mv nil ls$ us$)
        (process-each-sieve (rest sieves.) x r ls$ us$)))))

(defunk process-sieves (x r) :inline
  (process-each-sieve (rule.sieves r) x r ls$ us$))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| kernel unification and rewrite rule application functions                  |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defunk pop-var-chg-stk-fn (stk ls$)
  (if (=^ stk (opcd-btm))
      (set-var-chg-stk (opcd-btm) ls$)
    (letk ((nxt (oper.next-stk stk))
           (ls$ (oper.set-bound stk (node-btm))))
      (pop-var-chg-stk-fn nxt ls$))))

(defunk pop-var-chg-stk () :inline
  (letk ((stk (get-var-chg-stk ls$)))
    (if (=^ stk (opcd-btm)) ls$
      (pop-var-chg-stk-fn stk ls$))))

(defunk trace-rule-app (traced. rune. x) :inline
  (if (not traced.) ls$
    (prog2$ (cw ">>>~p0~%" rune.)
      (if (eq traced. t) ls$
        (prog2$ (cw "~p0~%" (prune-node-term x)) ls$)))))

(mutual-recursionk
(defunk subst-node (y ls$)
  (assert (/=^ y (node-btm))
   (letk ((opcd-y (node.opcd y)))
     (cond
      ((=^ opcd-y (opcd-quote))
       (mv^ y ls$))
      ((opcd.is-var opcd-y)
       (letk ((node (oper.bound (opcd.index opcd-y)))
              (node (if (=^ node (node-btm)) y node)))
         (assert (or (promoted node)
                     (list y node (node-to-term y) (node-to-term node)))
           (mv^ node ls$))))
      (t
       (letk ((x ls$ (allocate-node opcd-y (size-btm) nil ls$))
              (ls$ (subst-args (opcd.narg opcd-y) y 0 x ls$)))
         (mv^ x ls$)))))))

(defunk subst-args (narg y i x ls$)
  (if (zp narg) ls$
    (letk ((a ls$ (subst-node (node.arg y i) ls$))
           (ls$ (node.set-arg x i a)))
      (subst-args (1-^ narg) y (1+^ i) x ls$))))
)

(defunk 1way-unify-var (x opcd-y ls$)
  (letk ((op-y (opcd.index opcd-y))
         (bound (oper.bound op-y)))
    (if (=^ bound (node-btm))
        (letk ((ls$ (set-var-bound op-y x))) (mv t ls$))
      (mv (node= bound x) ls$))))

(defunk 1way-unify-obj (x. opcd-y y ls$)
  (cond
   ((=^ opcd-y (opcd-cons))
    (if (atom x.) (mv nil ls$)
      (letk ((y0 (node.arg y 0))
             (y1 (node.arg y 1))
             (op0 (node.opcd y0))
             (op1 (node.opcd y1))
             (match. ls$ (1way-unify-obj (car x.) op0 y0 ls$)))
        (if (not match.) (mv nil ls$)
          (1way-unify-obj (cdr x.) op1 y1 ls$)))))
   ((opcd.is-var opcd-y)
    (letk ((x ls$ (create-quote x.)))
      (1way-unify-var x opcd-y ls$)))
   (t (mv nil ls$))))

; The following function performs one-way unification of x with y (i.e. match x
; with y where all variables in x are treated as ground).

(defunk 1way-unify (x y n i args-p. ls$)
  (if args-p.
      (if (zp n) (mv t ls$)
        (letk ((match. ls$ (1way-unify (node.arg x i)
                                       (node.arg y i)
                                       0 0 nil ls$)))
          (if (not match.) (mv nil ls$)
            (1way-unify x y (1-^ n) (1+^ i) t ls$))))
    (assert (and (/=^ x (node-btm)) (/=^ y (node-btm)))
     (letk ((opcd-y (node.opcd y))
            (opcd-x (node.opcd x)))
       (cond
        ((opcd.is-var opcd-y)
         (1way-unify-var x opcd-y ls$))
        ((=^ opcd-y (opcd-quote))
         (mv (=^ x y) ls$))
        ((=^ opcd-x (opcd-quote))
         (1way-unify-obj (qobj.obj (node.arg x 0)) opcd-y y ls$))
        ((/=^ opcd-x opcd-y)
         (mv nil ls$))
        (t
         (1way-unify x y (opcd.narg opcd-x) 0 t ls$)))))))

(defunk unify-args (x y narg) :inline
  (1way-unify x y narg 0 t ls$))

(defunk maximum-rule-ctr (- (expt 2 28) 2))

(defunk incr-rule-ctr (r) :inline
  (letk ((ctr (rule.ctr r))
         (ctr (if (<^ ctr (maximum-rule-ctr)) (1+^ ctr) ctr)))
    (rule.set-ctr r ctr)))

(defunk incr-rule-tryctr (r) :inline
  (letk ((ctr (rule.tryctr r))
         (ctr (if (<^ ctr (maximum-rule-ctr)) (1+^ ctr) ctr)))
    (rule.set-tryctr r ctr)))

(defunk loop-stk-incr () (floor (static-param) 8))

(defunk push-loop-stack (r x ls$)
  (letk ((l (get-loop-stk-top ls$))
         (ls$ (ensure-loop l (loop-stk-incr)))
         (ls$ (loop.set-rule l r))
         (ls$ (loop.set-node l x))
         (ls$ (set-loop-stk-top (1+^ l) ls$)))
    ls$))

(defunk oper-rule-match (x r ls$ us$)
  (if (not (rule.enabled r))
      (mv nil ls$ us$)
    (letk ((match. ls$ us$ (process-sieves x r)))
      (if (not match.)
          (mv nil ls$ us$)
        (letk ((ls$ (incr-rule-ctr r)))
          (mv t ls$ us$))))))

(defunk rule-matches (x r narg ls$ us$)
  (letk ((ls$ (incr-rule-tryctr r))
	 (match. ls$ (unify-args x (rule.lhs r) narg)))
    (if (not match.)
        (mv nil ls$ us$)
      (letk ((match. ls$ us$ (process-sieves x r)))
        (if (not match.)
            (mv nil ls$ us$)
          (letk ((ls$ (incr-rule-ctr r)))
            (mv t ls$ us$)))))))

(defunk args-are-quotes (n i x ls$)
  (or (zp n)
      (and (=^ (node.opcd (node.arg x i)) (opcd-quote))
           (args-are-quotes (1-^ n) (1+^ i) x ls$))))

(defunk args-quote-objs (n i x ls$)
  (if (zp n) ()
    (cons (qobj.obj (node.arg (node.arg x i) 0))
          (args-quote-objs (1-^ n) (1+^ i) x ls$))))

(defunk apply-exec (op x ls$)
  (letk ((args. (args-quote-objs (oper.narg op) 0 x ls$))
         (erp. val. (funcall (oper.name op) args.)))
    (if erp. (mv^ x ls$)
      (letk ((ls$ (incr-rule-ctr (oper.exec op)))
             (y ls$ (install-quote val. ls$)))
        (mv^ y ls$)))))

; ; Matt K. mod, 10/2017: Undo the removal of ev-fncall-w as an untouchable,
; performed earlier above.
(push-untouchable ev-fncall-w t)

(defunk exec-counterpart (opcd x ls$ us$)
  (letk ((op (opcd.index opcd))
         (narg (opcd.narg opcd))
         (exec (oper.exec op)))
    (if (not (args-are-quotes narg 0 x ls$))
        (mv^ x (dcv-empty) nil ls$ us$)
      (letk ((go. ls$ us$ (oper-rule-match x exec ls$ us$)))
        (if (not go.)
            (mv^ x (dcv-empty) nil ls$ us$)
          (letk ((rslt ls$ (apply-exec op x ls$)))
            (mv^ rslt (dcv-empty) nil ls$ us$)))))))

(defunk node/= (x y) :inline
  (and (/=^ x y)
       (or (and (=^ (node.opcd x) (opcd-quote))
                (=^ (node.opcd y) (opcd-quote)))
           (and (=^ x (node-nil)) (non-nilp y))
           (and (=^ y (node-nil)) (non-nilp x)))))

(defunk built-in-rewrites (opcd x) :inline
  (cond ((opcd.is-equal opcd)
         (letk ((lhs (node.arg x 0))
                (rhs (node.arg x 1)))
           (cond ((node= lhs rhs) (node-t))
                 ((node/= lhs rhs) (node-nil))
                 (t x))))
        ((opcd.is-if opcd)
         (letk ((tst (node.arg x 0))
		(tbr (node.arg x 1))
		(fbr (node.arg x 2)))
           (cond ((=^ tst (node-nil)) fbr)
                 ((non-nilp tst) tbr)
		 ((node= tbr fbr) tbr)
                 (t x))))
        (t x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| main kernel rewrite loop functions (rewrite-node is entry point)           |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defunk depth-exceeded () :inline
  (zp (get-current-clock ls$)))

(defunk space-exceeded () :inline
  (>^ (+^ (get-num-trans-nodes ls$) (get-num-of-nodes ls$))
      (get-node-limit ls$)))

; compute-if-direction can return one of the following:
;  nil      -- if-test has rewritten to nil, only rewrite false branch
;  t        -- if-test has rewritten to non-nil, only rewrite true branch
; :both     -- assume context on both branches
; :only-t   -- assume context only on true branch
; :only-nil -- assume context only on false branch
; :neither  -- do not assume context on either branch

(defunk compute-if-direction (tst+) :inline
  (cond ((=^ tst+ (node-nil)) nil)
        ((non-nilp tst+) t)
        (t (letk ((op (opcd.index (node.opcd tst+))))
             (if (oper.assume-tbr op)
                 (if (oper.assume-fbr op) :both :only-t)
               (if (oper.assume-fbr op) :only-nil :neither))))))

(defunk drop-dctx-dcv (dcx dcv) :inline
  (if (>=^ dcx (dctx-max-rep)) dcv (logand^ dcv (lognot^ (ash^ 1 dcx)))))

(mutual-recursionk
(defunk promote-node (x ls$)
  (if (promoted x) (mv^ x ls$)
    (letk ((ls$ (promote-args (opcd.narg (node.opcd x)) 0 x ls$)))
      (install-node x t ls$))))

(defunk promote-args (n i x ls$)
  (if (zp n) ls$
    (letk ((a ls$ (promote-node (node.arg x i) ls$))
           (ls$ (node.set-arg x i a)))
      (promote-args (1-^ n) (1+^ i) x ls$))))
)

(defunk well-formed-context-equation (tst) :inline
  (and (opcd.is-equal (node.opcd tst))
       (not (=^ (node.opcd (node.arg tst 0)) (opcd-quote)))))

(defunk create-equal-tst-for-case (tst cas. ls$)
  (letk ((opcd (node.opcd tst)))
    (assert (/=^ opcd (opcd-quote))
      (if (and cas. (or (opcd.is-equal opcd)
                        (not (oper.boolp (opcd.index opcd)))))
          (mv^ tst ls$)
        (letk ((x ls$ (allocate-node (opcd-equal) (size-btm) nil ls$))
               (ls$ (node.set-arg x 0 tst))
               (rhs (if cas. (node-t) (node-nil)))
               (ls$ (node.set-arg x 1 rhs)))
          (promote-node x ls$))))))

(defunk push-new-context (tst ls$)
  (letk ((top (get-curr-ctx-top ls$)))
    (if (>=^ top (length-curr-ctx-stk ls$))
        (error "Maximum number of context stack nodes exceeded. ~
                The user may wish to adjust the maximum node bound for KAS."
               tst (mv^ top ls$))
      (letk ((ls$ (set-curr-ctx-stk top tst ls$))
	     (ls$ (set-curr-ctx-top (1+^ top) ls$)))
	(mv^ top ls$)))))

(defunk pop-new-context (ls$)
  (set-curr-ctx-top (1-^ (get-curr-ctx-top ls$)) ls$))

(mutual-recursionk
(defunk is-subterm (x y ls$)
  (or (node= x y)
      (letk ((opcd (node.opcd y)))
	(and (/=^ opcd (opcd-quote))
	     (not (opcd.is-var opcd))
	     (is-subterm-args x y (opcd.narg opcd) 0 ls$)))))

(defunk is-subterm-args (x y n i ls$)
  (and (not (zp n))
       (or (is-subterm x (node.arg y i) ls$)
	   (is-subterm-args x y (1-^ n) (1+^ i) ls$))))
)

(mutual-recursionk
(defunk mark-node-in-ctx (x dcv ls$)
  (letk ((opcd (node.opcd x)))
    (if (=^ opcd (opcd-quote)) ls$
      (letk ((ls$ (if (node.in-ctx x) ls$
                    (letk ((ls$ (create-new-undo (node-btm) dcv x (dcv-btm) ls$))
                           (ls$ (node.set-in-ctx x t)))
                      ls$))))
        (mark-args-in-ctx (opcd.narg opcd) 0 x dcv ls$)))))

(defunk mark-args-in-ctx (n i x dcv ls$)
  (if (zp n) ls$
    (letk ((ls$ (mark-node-in-ctx (node.arg x i) dcv ls$)))
      (mark-args-in-ctx (1-^ n) (1+^ i) x dcv ls$))))
)

(defunk mark-subnodes-in-ctx (x dcv ls$)
  (letk ((opcd (node.opcd x)))
    (if (=^ opcd (opcd-quote)) ls$
      (mark-args-in-ctx (opcd.narg opcd) 0 x dcv ls$))))

(mutual-recursionk
(defunk rewrite-hyps-args (n i h dcv ls$ us$)
  (if (zp n) (mv t dcv ls$ us$)
    (letk ((a dcv+ ls$ us$ (rewrite-node (node.arg h i) ls$ us$)))
      (if (not (non-nilp a)) (mv nil (dcv-empty) ls$ us$)
        (rewrite-hyps-args (1-^ n) (1+^ i) h (logior^ dcv dcv+) ls$ us$)))))

(defunk rewrite-hyps (h ls$ us$)
  (if (=^ h (node-t)) (mv t (dcv-empty) ls$ us$)
    (letk ((bc (get-bchain-limit ls$)))
      (if (zp bc) (mv nil (dcv-empty) ls$ us$)
        (letk ((ls$ (set-bchain-limit (1-^ bc) ls$))
               (op (node.opcd h))
               (pass. dcv ls$ us$ (rewrite-hyps-args (opcd.narg op) 0 h (dcv-empty) ls$ us$))
               (ls$ (set-bchain-limit bc ls$)))
          (mv pass. dcv ls$ us$))))))

(defunk apply-rule (r x narg ls$ us$)
  (if (not (rule.enabled r))
      (mv^ x (dcv-empty) nil ls$ us$)
    (letk ((match. ls$ us$ (rule-matches x r narg ls$ us$)))
      (if (not match.)
          (letk ((ls$ (pop-var-chg-stk)))
            (mv^ x (dcv-empty) nil ls$ us$))
        (letk ((ls$ (push-loop-stack r x ls$))
               (h+ ls$ (subst-node (rule.hyps r) ls$))
               (y ls$ (subst-node (rule.rhs r) ls$))
               (ls$ (pop-var-chg-stk))
               (pass. dcv ls$ us$ (rewrite-hyps h+ ls$ us$)))
          (if (not pass.)
              (mv^ x (dcv-empty) t ls$ us$)
            (letk ((ls$ (trace-rule-app (rule.traced r) (rule.rune r) x)))
              (mv^ y dcv nil ls$ us$))))))))

(defunk apply-rules (rules. x narg cond-failed. ls$ us$)
  (if (endp rules.)
      (mv^ x (dcv-empty) cond-failed. ls$ us$)
    (letk ((y dcv c-f. ls$ us$ (apply-rule (first rules.) x narg ls$ us$))
           (cond-failed. (or c-f. cond-failed.)))
      (if (/=^ y x)
          (mv^ y dcv cond-failed. ls$ us$)
        (apply-rules (rest rules.) x narg cond-failed. ls$ us$)))))

(defunk apply-rewrite (opcd x) :inline
  (apply-rules (oper.rules (opcd.index opcd)) x (opcd.narg opcd) nil ls$ us$))

(defunk rewrite-step (opcd x ls$ us$)
  (letk ((y (built-in-rewrites opcd x)))
    (if (/=^ y x) (mv^ y (dcv-empty) nil ls$ us$)
      (letk ((y dcv c-f. ls$ us$ (apply-rewrite opcd x)))
        (if (/=^ y x) (mv^ y dcv c-f. ls$ us$)
          (exec-counterpart opcd x ls$ us$))))))

(defunk decr-and-rewrite (x ls$ us$)
  (letk ((clk (get-current-clock ls$))
         (ls$ (set-current-clock (1-^ clk) ls$))
         (x+ dcv ls$ us$ (rewrite-node x ls$ us$))
         (ls$ (set-current-clock clk ls$)))
    (mv^ x+ dcv ls$ us$)))

(defunk extend-context (tst dcv ndx ls$ us$)
  (if (not (well-formed-context-equation tst))
      (mv t ls$ us$)
    (letk ((nxt (get-next-extend-age ls$))
           (ls$ (set-current-age nxt ls$))
           (ls$ (set-next-extend-age (1+^ nxt) ls$))
           (lhs (node.arg tst 0))
           (rhs (node.arg tst 1))
           (ls$ (update-rep lhs rhs dcv 1 ls$)))
      (if (not (get-allow-context-reduction ls$)) (mv t ls$ us$)
        (letk ((ls$ (mark-subnodes-in-ctx lhs dcv ls$))
               (ls$ (mark-node-in-ctx rhs dcv ls$)))
          (if (not (node.in-ctx lhs)) (mv t ls$ us$)
	    (rewrite-context (get-curr-ctx-top ls$) lhs ndx ls$ us$)))))))

(defunk rewrite-context (i lhs ndx ls$ us$)
  (if (=^ i 0) (mv t ls$ us$)
    (letk ((i (1-^ i)))
      (if (=^ i ndx) (rewrite-context i lhs ndx ls$ us$)
	(letk ((top (get-curr-ctx-stk i ls$)))
          (if (not (and (well-formed-context-equation top)
			(is-subterm lhs top ls$)))
	      (rewrite-context i lhs ndx ls$ us$)
	    (letk ((top-lhs (node.arg top 0))
		   (tmp (node.rep top-lhs))
		   (ls$ (node.set-rep top-lhs (node-btm)))
		   (top+ dcv ls$ us$ (decr-and-rewrite top ls$ us$))
		   (ls$ (node.set-rep top-lhs tmp)))
              (cond ((=^ top+ (node-nil))
		     (mv nil ls$ us$))
		    ((node= top+ top)
		     (rewrite-context i lhs ndx ls$ us$))
		    (t
		     (letk ((ls$ (set-curr-ctx-stk i top+ ls$))
			    (ls$ (create-new-undo (node-btm) dcv top i ls$))
			    (vald. ls$ us$ (extend-context top+ dcv i ls$ us$)))
                       (if (not vald.) (mv nil ls$ us$)
			 (rewrite-context i lhs ndx ls$ us$))))))))))))

(defunk rewrite-case (cas. brn tst+ dir. ls$ us$)
  (cond
   ((and (not (eq dir. cas.))
         (is-boolean dir.))
    (mv^ brn (dcv-empty) ls$ us$))  ; DO NOT REWRITE branch
   ((or (eq dir. cas.)
        (eq dir. :neither)
        (if cas. (eq dir. :only-nil) (eq dir. :only-t)))
    (rewrite-node brn ls$ us$))     ; REWRITE branch with no test assumption
   (t
    (letk ((dcx- (get-current-dctx ls$))
           (age (get-current-age ls$))
           (dcx+ ls$ (create-new-dctx ls$))
           (tst= ls$ (create-equal-tst-for-case tst+ cas. ls$))
           (ndx ls$ (push-new-context tst= ls$))
           (vald. ls$ us$ (extend-context tst= (ash^ 1 dcx+) ndx ls$ us$)))
      (if (not vald.)
          (letk ((ls$ (pop-new-context ls$))
		 (ls$ (restore-previous-state dcx- dcx+ age ls$)))
            (mv^ (node-btm) (dcv-empty) ls$ us$))
        (letk ((node dcv ls$ us$ (rewrite-node brn ls$ us$))
               (ls$ (pop-new-context ls$))
               (ls$ (restore-previous-state dcx- dcx+ age ls$))
               (dcv (drop-dctx-dcv dcx+ dcv)))
          (assert (<=^ (max-in-dcv dcv) dcx-)
            (mv^ node dcv ls$ us$))))))))

(defunk rewrite-args-if (x ls$ us$)
  (letk ((tst (node.arg x 0))
         (tbr (node.arg x 1))
         (fbr (node.arg x 2))
         (tst+ tst-dcv ls$ us$ (rewrite-node tst ls$ us$))
         (dir. (compute-if-direction tst+))
         (tbr+ tbr-dcv ls$ us$ (rewrite-case t tbr tst+ dir. ls$ us$))
         (fbr+ fbr-dcv ls$ us$ (rewrite-case nil fbr tst+ dir. ls$ us$))
	 (no-tbr. (=^ tbr+ (node-btm)))
	 (no-fbr. (=^ fbr+ (node-btm)))
	 (tst+ (if no-tbr. (node-nil) (if no-fbr. (node-t) tst+)))
	 (tbr+ (if no-tbr. tbr tbr+))
	 (fbr+ (if no-fbr. fbr fbr+))
         (ls$ (node.set-arg x 0 tst+))
         (ls$ (node.set-arg x 1 tbr+))
         (ls$ (node.set-arg x 2 fbr+))
         (chgd. (or (/=^ tst+ tst) (/=^ tbr+ tbr) (/=^ fbr+ fbr))))
    (mv chgd. (logior^ tst-dcv tbr-dcv fbr-dcv) ls$ us$)))

(defunk rewrite-args-op (n i x chgd. dcv ls$ us$)
  (if (zp n) (mv chgd. dcv ls$ us$)
    (letk ((a (node.arg x i))
           (a+ dcv+ ls$ us$ (rewrite-node a ls$ us$))
           (ls$ (node.set-arg x i a+))
           (chgd. (or (/=^ a+ a) chgd.))
           (dcv (logior^ dcv dcv+)))
      (rewrite-args-op (1-^ n) (1+^ i) x chgd. dcv ls$ us$))))

(defunk rewrite-args-hide () :inline
  (mv nil (dcv-empty) ls$ us$))

(defunk rewrite-args (opcd x ls$ us$)
  (assert (temp-node x)
   (cond ((opcd.is-if opcd)     (rewrite-args-if x ls$ us$))
         ((=^ opcd (opcd-hide)) (rewrite-args-hide))
         (t                     (rewrite-args-op (opcd.narg opcd) 0 x nil (dcv-empty) ls$ us$)))))

(defunk rewrite-node+ (x- opcd rep age ls$ us$)
  (if (>^ rep 0)
      (assert (and (promoted x-) (/=^ x- rep))
       (letk ((x+ dcv ls$ us$ (decr-and-rewrite rep ls$ us$))
              (dcv (logior^ (node.dcv x-) dcv))
              (ls$ (update-rep x- x+ dcv 2 ls$)))
         (mv^ x+ dcv ls$ us$)))
    ;; /\ If we have a rep node, then rewrite the rep node and return the result, otherwise....
    (letk ((x ls$ (install-node x- nil ls$))
           (chgd. dcv1 ls$ us$ (rewrite-args opcd x ls$ us$)))
      (if (and (/=^ rep (node-btm)) (not chgd.))
          (assert (and (promoted x-) (/=^ x- rep))
           (letk ((ls$ (update-rep x- (-^ age) (dcv-btm) 3 ls$)))
             (mv^ x- (dcv-empty) ls$ us$)))
        ;; /\ Rewrite the args and if the args have not changed and we were not marked to rewrite, then return original, otherwise...
        (letk ((x+ dcv2 cond-failed. ls$ us$ (rewrite-step opcd x ls$ us$)))
          (if (/=^ x+ x)
              (letk ((x+ dcv3 ls$ us$ (decr-and-rewrite x+ ls$ us$))
                     (dcv (logior^ dcv1 dcv2 dcv3))
		     (ls$ (update-rep x- x+ dcv 4 ls$))
                     (ls$ (update-rep x x+ dcv 5 ls$)))
                (mv^ x+ dcv ls$ us$))
            ;; /\ Apply rewrite rules and return rewrite of result if a rule fired, otherwise...
            (letk ((x ls$ (promote-node x ls$))
                   (rep (node.rep x)))
              (if (>^ rep 0)
                  (assert (/=^ x rep)
                   (letk ((x+ dcv2 ls$ us$ (decr-and-rewrite rep ls$ us$))
                          (dcv (logior^ dcv1 dcv2 (node.dcv x)))
                          (ls$ (update-rep x- x+ dcv 6 ls$))
                          (ls$ (update-rep x x+ dcv 7 ls$)))
                     (mv^ x+ dcv ls$ us$)))
                ;; /\ promote the node (it is in normal form) and then see if the node has a rep node which can then rewrite and return the result, otherwise...
                ;; \/ look to see if we had a conditional rule fail due to hypothesis and mark rep accordingly and return promoted node.
                (letk ((ls$ (update-rep x- x dcv1 8 ls$))
                       (x-rep (if cond-failed. (node-btm) (-^ age)))
                       (ls$ (update-rep x x-rep (dcv-btm) 9 ls$)))
                  (mv^ x dcv1 ls$ us$))))))))))

(defunk rewrite-node (x ls$ us$)
  (letk ((x ls$ (check-memos x ls$))
         (opcd (node.opcd x))
         (rep (node.rep x))
         (age (get-current-age ls$)))
    (cond
     ((depth-exceeded)
      (error "Maximum number of iterations in term rewriting was reached. ~
              The user may wish to adjust the rewrite depth for KAS."
             x (mv^ x (dcv-empty) ls$ us$)))
     ((space-exceeded)
      (error "Maximum number of allocated nodes was reached during KAS rewriting. ~
              The user may wish to adjust the maximum node bound for KAS."
             x (mv^ x (dcv-empty) ls$ us$)))
     ((or (=^ opcd (opcd-quote))  ;; quoted objects are always in normal-form
	  (and (opcd.is-var opcd) ;; var.s which are not equated, are in normal-form
	       (not (>^ rep 0)))
          (>=^ (-^ rep) age))      ;; node tagged in normal-form in current ctx
      (assert (promoted x)
       (mv^ x (dcv-empty) ls$ us$)))
     (t
      (assert (/=^ rep x) ;; this isn't critical, but we don't expect this to happen
       (letk ((save-depth (get-rew-call-depth  ls$))
              (save-alloc (get-alloc-trans     ls$))
              (save-num   (get-num-trans-nodes ls$))
              (save-ltop  (get-loop-stk-top    ls$))
              (ls$ (set-rew-call-depth (1+^ save-depth) ls$))
              (x+ dcv ls$ us$ (rewrite-node+ x opcd rep age ls$ us$))
              (ls$ (set-num-trans-nodes save-num   ls$))
              (ls$ (set-alloc-trans     save-alloc ls$))
              (ls$ (set-rew-call-depth  save-depth ls$))
              (ls$ (set-loop-stk-top    save-ltop  ls$)))
         (assert (promoted x+)
          (assert (=^ (get-current-age ls$) age)
           (mv x+ dcv ls$ us$)))))))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| stobj initialization and wrapper call for rewrite-node                     |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defabbrev rlrcd.sieves    (rule) (first rule))
(defabbrev rlrcd.lhs       (rule) (second rule))
(defabbrev rlrcd.rhs       (rule) (third rule))
(defabbrev rlrcd.rune      (rule) (fourth rule))
(defabbrev rlrcd.enabled   (rule) (fifth rule))
(defabbrev rlrcd.traced    (rule) (sixth rule))
(defabbrev rlrcd.hyps      (rule) (seventh rule))

(defabbrev make-rlrcd (sieves lhs rhs rune enabled traced hyps)
  (list sieves lhs rhs rune enabled traced hyps))

(defabbrev oprcd.name            (opr) (first (first opr)))
(defabbrev oprcd.is-var          (opr) (second (first opr)))
(defabbrev oprcd.rules           (opr) (third (first opr)))
(defabbrev oprcd.narg            (opr) (fourth (first opr)))
(defabbrev oprcd.boolp           (opr) (first (second opr)))
(defabbrev oprcd.is-if           (opr) (second (second opr)))
(defabbrev oprcd.is-equal        (opr) (third (second opr)))
(defabbrev oprcd.non-nil         (opr) (fourth (second opr)))
(defabbrev oprcd.exec-enabled    (opr) (fifth (second opr)))

(defun make-oprcd (name is-var rules narg
                   boolp is-if is-equal non-nil
                   exec-enabled)
  (list (list name is-var rules narg)
        (list boolp is-if is-equal non-nil
              exec-enabled)))

(defun kern-chk-rule-traced (rune typ name descr)
  (if (atom descr) descr
    (let ((elem (first descr)))
      (cond ((atom elem) elem)
            ((or (equal rune (first elem))
                 (and (member-eq typ '(:rewrite :definition))
                      (equal name (first elem))))
             (second elem))
            (t (kern-chk-rule-traced rune typ name (rest descr)))))))

(defun kern-is-rule-traced (rune ls$)
  (declare (xargs :stobjs ls$))
  (kern-assert
   (and (consp rune) (eql (len rune) 2))
   (let ((traced
          (kern-chk-rule-traced rune (first rune) (second rune)
                                (get-initial-rule-trace-descriptor ls$))))
     (if (kern-is-trace-mark traced) traced
       (er hard 'kern-is-rule-traced "illegal trace mark: ~x0" traced)))))

(defmacro defunf (fn args body)
  `(defun ,fn ,args
     (declare (xargs :stobjs ls$)
              (type (signed-byte ,(kern-fixnum-size)) ,(first args)))
     ,body))

(defunf kern-install-auto-rule (ndx opr typ ls$)
  (let* ((rune (list typ (oprcd.name opr)))
         (enabled (case typ
                    (:executable-counterpart (oprcd.exec-enabled opr))))
         (traced (kern-is-rule-traced rune ls$)))
    (letk ((r ls$ (kern-alloc-rule-ndx ls$))
           (ls$ (case typ
                  (:executable-counterpart (oper.set-exec ndx r))
                  (t ls$)))
           (ls$ (rule.set-op       r ndx))
           (ls$ (rule.set-sieves   r ()))
           (ls$ (rule.set-rune     r rune))
           (ls$ (rule.set-lhs      r (kern-node-btm)))
           (ls$ (rule.set-rhs      r (kern-node-btm)))
           (ls$ (rule.set-hyps     r (kern-node-btm)))
           (ls$ (rule.set-ctr      r 0))
	   (ls$ (rule.set-tryctr   r 0))
           (ls$ (rule.set-enabled  r enabled))
           (ls$ (rule.set-traced   r traced)))
      ls$)))

(defunf kern-install-oper-type (ndx opr typ ls$)
  (let* ((rune (case typ
                     (:boolp (oprcd.boolp opr))
                     (:is-if (oprcd.is-if opr))
                     (:is-equal (oprcd.is-equal opr))
                     (:non-nil (oprcd.non-nil opr))
                     (t (er hard 'kern-install-oper-type "illegal typ"))))
         (flag (if rune t nil))
         (ls$ (case typ
                    (:boolp (oper.set-boolp ndx flag))
                    (:is-if (oper.set-is-if ndx flag))
                    (:is-equal (oper.set-is-equal ndx flag))
                    (:non-nil (oper.set-non-nil ndx flag))
                    (t ls$)))
         (ls$ (if (not (eq typ :boolp)) ls$
                (letk ((ls$ (oper.set-assume-tbr ndx flag))
                       (ls$ (oper.set-assume-fbr ndx flag)))
                  ls$)))
         (ls$ (if (consp rune)
                  (letk ((r ls$ (kern-alloc-rule-ndx ls$))
                         (ls$ (rule.set-op       r ndx))
                         (ls$ (rule.set-sieves   r ()))
                         (ls$ (rule.set-rune     r rune))
                         (ls$ (rule.set-lhs      r (kern-node-btm)))
                         (ls$ (rule.set-rhs      r (kern-node-btm)))
                         (ls$ (rule.set-hyps     r (kern-node-btm)))
                         (ls$ (rule.set-ctr      r 1)))
                    ls$)
                ls$)))
    ls$))

(defun kern-install-oper-base (name is-var opr ls$)
  (declare (xargs :stobjs ls$))
  (letk ((hash (kern-fn-hash-code name))
         (chain (get-op-hash hash ls$))
         (opcd (kern-lookup-opcd chain name is-var ls$))
         (ndx (if (/=^ opcd (kern-opcd-btm))
                  (opcd.index opcd)
                (get-next-op-ndx ls$)))
         (ls$ (if (/=^ opcd (kern-opcd-btm))
                  ls$
                (letk ((ls$ (ensure-oper ndx (kern-oper-stor-incr)))
                       (ls$ (oper.set-uniq ndx chain))
                       (ls$ (set-op-hash hash ndx ls$))
                       (ls$ (set-next-op-ndx (1+^ ndx) ls$)))
                  ls$)))
         (ls$ (oper.set-name ndx name))
         (ls$ (oper.set-is-var ndx is-var))
         (ls$ (oper.set-rules ndx ()))
         (ls$ (oper.set-num-nodes ndx 0))
         (ls$ (oper.set-num-trans ndx 0))
         (ls$ (oper.set-narg ndx (oprcd.narg opr)))
         (ls$ (oper.set-next-stk ndx (kern-opcd-btm)))
         (ls$ (oper.set-bound ndx (kern-node-btm)))
         (ls$ (oper.set-assume-tbr ndx nil))
         (ls$ (oper.set-assume-fbr ndx nil))
         (ls$ (if (eq name 'quote) ls$
                (kern-install-auto-rule ndx opr :executable-counterpart ls$)))
         (ls$ (kern-install-oper-type ndx opr :boolp ls$))
         (ls$ (kern-install-oper-type ndx opr :is-if ls$))
         (ls$ (kern-install-oper-type ndx opr :is-equal ls$))
         (ls$ (kern-install-oper-type ndx opr :non-nil ls$))
         (ls$ (if (member name (get-flip-t-fns ls$))
                  (oper.set-assume-tbr ndx (not (oper.assume-tbr ndx)))
                ls$))
         (ls$ (if (member name (get-flip-nil-fns ls$))
                  (oper.set-assume-fbr ndx (not (oper.assume-fbr ndx)))
                ls$)))
    ls$))

(defun kern-create-alist (vars vals)
  (if (endp vars) ()
    (acons (first vars) (first vals)
           (kern-create-alist (rest vars) (rest vals)))))

(mutual-recursion
(defun kern-expand-lambdas-fn (term alist)
  (cond ((atom term)
         (if (assoc term alist)
             (cdr (assoc term alist))
           term))
        ((eq (first term) 'quote)
         term)
        ((atom (first term))
         (cons (first term)
               (kern-expand-lambdas-args (rest term) alist)))
        (t
         (kern-expand-lambdas-fn
          (third (first term))
          (kern-create-alist
           (second (first term))
           (kern-expand-lambdas-args (rest term) alist))))))

(defun kern-expand-lambdas-args (args alist)
  (if (endp args) ()
    (cons (kern-expand-lambdas-fn (first args) alist)
          (kern-expand-lambdas-args (rest args) alist))))
)

(defabbrev kern-expand-lambdas (term)
  (kern-expand-lambdas-fn term ()))

(defun kern-expand-lambda-terms (terms)
  (if (endp terms) ()
    (cons (kern-expand-lambdas (first terms))
          (kern-expand-lambda-terms (rest terms)))))

(defun kern-install-rules (rlrcds op ls$)
  (declare (xargs :stobjs ls$))
  (if (endp rlrcds)
      (oper.set-rules op ())
    (letk ((r. (first rlrcds))
           (lhs. (kern-expand-lambdas (rlrcd.lhs r.)))
           (rhs. (kern-expand-lambdas (rlrcd.rhs r.)))
           (hyps. (kern-expand-lambdas (rlrcd.hyps r.)))
           (sieves. ls$ (kern-install-sieves (rlrcd.sieves r.) ls$))
           (ndx ls$ (kern-alloc-rule-ndx ls$))
           (lhs ls$ (kern-term-to-node lhs. ls$))
           (rhs ls$ (kern-term-to-node rhs. ls$))
           (hyps ls$ (kern-term-to-node hyps. ls$))
           (ls$ (rule.set-rune      ndx (rlrcd.rune r.)))
           (ls$ (rule.set-sieves    ndx sieves.))
           (ls$ (rule.set-ctr       ndx 0))
           (ls$ (rule.set-lhs       ndx lhs))
           (ls$ (rule.set-rhs       ndx rhs))
           (ls$ (rule.set-hyps      ndx hyps))
           (ls$ (rule.set-op        ndx op))
           (ls$ (rule.set-enabled   ndx (rlrcd.enabled r.)))
           (ls$ (rule.set-traced    ndx (rlrcd.traced r.)))
           (ls$ (kern-install-rules (rest rlrcds) op ls$)))
      (oper.set-rules op (cons ndx (oper.rules op))))))

(defun kern-install-base-opers (oprcds ls$)
  (declare (xargs :stobjs ls$))
  (if (endp oprcds) ls$
    (letk ((ls$ (kern-install-oper-base (oprcd.name (first oprcds))
                                        (oprcd.is-var (first oprcds))
                                        (first oprcds) ls$)))
      (kern-install-base-opers (rest oprcds) ls$))))

(defun kern-install-rlrcds (oprcds ls$)
  (declare (xargs :stobjs ls$))
  (if (endp oprcds) ls$
    (letk ((opcd (kern-find-fn-opcd (oprcd.name (first oprcds))))
           (ndx (kern-assert (/=^ opcd (kern-opcd-btm))
                             (opcd.index opcd)))
           (ls$ (kern-install-rules (oprcd.rules (first oprcds)) ndx ls$)))
      (kern-install-rlrcds (rest oprcds) ls$))))

(defun kern-install-oprcds (oprcds ls$)
  (declare (xargs :stobjs ls$))
  (letk ((ls$ (kern-install-base-opers oprcds ls$)))
    (kern-install-rlrcds oprcds ls$)))

(defun kern-remove-equal-list (e x)
  (cond ((endp x) ())
        ((equal e (first x))
         (kern-remove-equal-list e (rest x)))
        (t (cons (first x)
                 (kern-remove-equal-list e (rest x))))))

(mutual-recursion
(defun kern-unfak-term (term)
  (cond ((atom term) term)
        ((eq (first term) 'quote) term)
        ((eq (first term) 'fak)
         (kern-unfak-term (second term)))
        (t (cons (first term)
                 (kern-unfak-terms (rest term))))))

(defun kern-unfak-terms (args)
  (if (endp args) ()
    (cons (kern-unfak-term (first args))
          (kern-unfak-terms (rest args)))))
)

(defun kern-translate-hyps (hyps)
  (cons (symbol-append 'hyps-and- (length hyps)) hyps))

(defun kern-prune-sieves (hyps)
  (cond ((endp hyps) ())
	((and (consp (first hyps))
	      (eq (caar hyps) 'siv))
	 (kern-prune-sieves (rest hyps)))
	(t (cons (first hyps) (kern-prune-sieves (rest hyps))))))

(defun kern-extract-sieves (hyps)
  (cond ((endp hyps) ())
	((and (consp (first hyps))
	      (eq (caar hyps) 'siv))
	 (cons (if (quotep (cadar hyps)) (cadr (cadar hyps)) (cadar hyps))
	       (kern-extract-sieves (rest hyps))))
	(t (kern-extract-sieves (rest hyps)))))

(defun kern-find-new-rules (lemmas recp ens all-fns rules new-fns ls$)
  (declare (xargs :stobjs ls$))
  (if (endp lemmas)
      (mv new-fns (reverse rules))
    (let* ((lemma (first lemmas))
           (rhs (kern-unfak-term (access rewrite-rule lemma :rhs)))
           (lhs (kern-unfak-term (access rewrite-rule lemma :lhs)))
           (rune (access rewrite-rule lemma :rune))
           (subclass (access rewrite-rule lemma :subclass))
           (hyps (and (not (eq subclass 'abbreviation))
                      (kern-unfak-terms (access rewrite-rule lemma :hyps))))
           (heuristic-info (access rewrite-rule lemma :heuristic-info)))
      (if (and (eq (access rewrite-rule lemma :equiv) 'equal)
               (member-eq subclass '(definition abbreviation backchain))
               (implies (eq subclass 'backchain) (null heuristic-info)))
          (let* ((enabled   (enabled-numep (access rewrite-rule lemma :nume) ens))
                 (traced    (kern-is-rule-traced rune ls$))
                 (is-def    (eq subclass 'definition))
                 (enabled   (and enabled (not (and is-def recp))))
		 (sieves    (kern-extract-sieves hyps))
		 (hyps      (kern-prune-sieves hyps))
                 (hyps      (kern-translate-hyps hyps))
                 (new-rule  (make-rlrcd sieves lhs rhs rune enabled traced hyps))
                 (rule-fns  (union-eq (all-fnnames lhs) (union-eq (all-fnnames rhs) (all-fnnames hyps)))))
            (kern-find-new-rules (rest lemmas) recp ens all-fns (cons new-rule rules)
                                 (union-eq (set-difference-eq rule-fns all-fns) new-fns) ls$))
        (kern-find-new-rules (rest lemmas) recp ens all-fns rules new-fns ls$)))))

(defun kern-filter-fak-thms (lemmas fn)
  (cond ((endp lemmas) ())
        ((eq (first (access rewrite-rule (first lemmas) :lhs)) fn)
         (cons (first lemmas)
               (kern-filter-fak-thms (rest lemmas) fn)))
        (t (kern-filter-fak-thms (rest lemmas) fn))))

(defun kern-rules-alist-fn (fns all-fns rules-alist fak-thms ens wrld ls$)
  (declare (xargs :stobjs ls$))
  (if (endp fns)
      (reverse rules-alist)
    (let ((fn (first fns)))
      (mv-let (new-fns rules)
          (kern-find-new-rules (append (kern-getprop fn 'lemmas)
                                       (kern-filter-fak-thms fak-thms fn))
                               (kern-getprop fn 'recursivep)
                               ens (cons fn all-fns) () () ls$)
        (kern-rules-alist-fn (append (rest fns) new-fns)
                             (append new-fns all-fns)
                             (cons (cons fn rules) rules-alist)
                             fak-thms ens wrld ls$)))))

(defun kern-trans-fak-thms (lemmas)
  (if (endp lemmas) ()
    (let* ((lemma (first lemmas))
           (lhs (kern-unfak-term (access rewrite-rule lemma :lhs)))
           (equiv (access rewrite-rule lemma :equiv)))
      (if (not (and (eq equiv 'equal)
                    (consp lhs)
                    (not (quotep lhs))))
          (kern-trans-fak-thms (rest lemmas))
        (cons (make rewrite-rule
                    :rune (access rewrite-rule lemma :rune)
                    :nume (access rewrite-rule lemma :nume)
                    :hyps (access rewrite-rule lemma :hyps)
                    :equiv 'equal
                    :lhs lhs
                    :rhs (access rewrite-rule lemma :rhs)
                    :subclass (access rewrite-rule lemma :subclass)
                    :heuristic-info (access rewrite-rule lemma :heuristic-info)
                    :backchain-limit-lst (access rewrite-rule lemma :backchain-limit-lst)
                    :match-free (access rewrite-rule lemma :match-free))
              (kern-trans-fak-thms (rest lemmas)))))))

(defun kern-rules-alist (fns ens wrld ls$)
  (declare (xargs :stobjs ls$))
  (kern-rules-alist-fn fns fns () (kern-trans-fak-thms (kern-getprop 'fak 'lemmas)) ens wrld ls$))

(defun kern-find-nume (pairs rune)
  (cond ((endp pairs) nil)
        ((equal rune (cdar pairs))
         (caar pairs))
        (t (kern-find-nume (cdr pairs) rune))))

(defun kern-type-pre-subsetp (tp ens ts)
  (and (enabled-numep (access type-prescription tp :nume) ens)
       (ts-subsetp (access type-prescription tp :basic-ts) ts)
       (null (access type-prescription tp :hyps))
       (null (access type-prescription tp :vars))))

;; NOTE: In the following function, we have decided to ignore the enabled
;; status of the definition rule we use to determine the match. The problem is
;; that the user may want a function to be matched to equal or if, but disable
;; the definition rule. One level of indirection in the function definition
;; will fail this check and allow the user to define functions which are equal,
;; if, but are not understood by the simplifier as such.
;;
;;   (enabled-numep (access rewrite-rule lemma :nume) ens)

(defun kern-match-defn-body (lemma ens lhs fn num-formals)
  (declare (ignore ens))
  (and (equal (length lhs) (1+ num-formals))
       (member (access rewrite-rule lemma :subclass)
               '(abbreviation definition))
       (null (access rewrite-rule lemma :hyps))
       (let ((rune (access rewrite-rule lemma :rune)))
         (and (consp rune) (eq (first rune) :definition)))
       (eq (access rewrite-rule lemma :equiv) 'equal)
       (equal (access rewrite-rule lemma :lhs) lhs)
       (equal (access rewrite-rule lemma :rhs)
              (cons fn (rest lhs)))))

(defun kern-find-boolp (lst ens)
  (if (endp lst) nil
    (let ((tp (first lst)))
      (if (kern-type-pre-subsetp tp ens *ts-boolean*)
          (access type-prescription tp :rune)
        (kern-find-boolp (rest lst) ens)))))

(defun kern-find-non-nil (lst ens)
  (if (endp lst) nil
    (let ((tp (first lst)))
      (if (kern-type-pre-subsetp tp ens *ts-non-nil*)
          (access type-prescription tp :rune)
        (kern-find-non-nil (rest lst) ens)))))

(defun kern-find-is-if (lst ens lhs)
  (if (endp lst) nil
    (let ((r (first lst)))
      (if (kern-match-defn-body r ens lhs 'if 3)
          (access rewrite-rule r :rune)
        (kern-find-is-if (rest lst) ens lhs)))))

(defun kern-find-is-equal (lst ens lhs)
  (if (endp lst) nil
    (let ((r (first lst)))
      (if (kern-match-defn-body r ens lhs 'equal 2)
          (access rewrite-rule r :rune)
        (kern-find-is-equal (rest lst) ens lhs)))))

(defun kern-create-oprcds (alist ens wrld)
  (if (endp alist) ()
    (let* ((fn (caar alist))
           (rules (cdar alist))
           (exec (list :executale-counterpart fn))
           (formals (kern-getprop fn 'formals))
           (lhs (cons fn formals))
           (nume (kern-find-nume (kern-getprop fn 'runic-mapping-pairs) exec))
           (enabled-exec (if nume (enabled-numep nume ens) t))
           (num-formals (if (eq fn 'quote) 1 (length formals)))
           (type-pres (kern-getprop fn 'type-prescriptions))
           (lemmas (kern-getprop fn 'lemmas))
           (boolp    (or (eq fn 'equal) (kern-find-boolp type-pres ens)))
           (non-nil  (or (eq fn 'cons)  (kern-find-non-nil type-pres ens)))
           (is-if    (or (eq fn 'if)    (kern-find-is-if lemmas ens lhs)))
           (is-equal (or (eq fn 'equal) (kern-find-is-equal lemmas ens lhs)))
           (exec-enabled (if enabled-exec t nil)))
      (cons (make-oprcd fn nil rules num-formals
                        boolp is-if is-equal non-nil exec-enabled)
            (kern-create-oprcds (cdr alist) ens wrld)))))

(defunf kern-init-node-hash (n ls$)
  (if (kern-zp n) ls$
    (letk ((n (1-^ n))
           (ls$ (set-node-hash n (kern-node-btm) ls$)))
      (kern-init-node-hash n ls$))))

(defunf kern-init-quote-hash (n ls$)
  (if (kern-zp n) ls$
    (letk ((n (1-^ n))
           (ls$ (set-quote-hash n (kern-node-btm) ls$)))
      (kern-init-quote-hash n ls$))))

(defunf kern-init-op-hash (n ls$)
  (if (kern-zp n) ls$
    (letk ((n (1-^ n))
           (ls$ (set-op-hash n (kern-opcd-btm) ls$)))
      (kern-init-op-hash n ls$))))

(defunf kern-init-memo-tbl (m ls$)
  (if (kern-zp m) ls$
    (letk ((m (1-^ m))
           (ls$ (memo.set-opcd m (kern-opcd-btm))))
      (kern-init-memo-tbl m ls$))))

(defun kern-install-and-check-quotes (alst ls$)
  (declare (xargs :stobjs ls$))
  (if (endp alst) ls$
    (letk ((node ls$ (kern-create-quote (caar alst))))
      (kern-force-assert (equal node (cdar alst))
       (kern-install-and-check-quotes (cdr alst) ls$)))))

(defun kern-base-quote-alist ()
  (list (cons nil (kern-node-nil))
        (cons t   (kern-node-t))))

(defun kern-install-base-quotes (ls$)
  (declare (xargs :stobjs ls$))
  (kern-install-and-check-quotes (kern-base-quote-alist) ls$))

(defun kern-find-max-narg1 (oprcds max)
  (cond ((endp oprcds)
         (or max (er hard 'kern-logic-init "illegal empty list of oprcds")))
        ((or (null max)
             (> (oprcd.narg (first oprcds))
                (oprcd.narg max)))
         (kern-find-max-narg1 (rest oprcds) (first oprcds)))
        (t (kern-find-max-narg1 (rest oprcds) max))))

(defun kern-find-max-narg (oprcds)
  (kern-find-max-narg1 oprcds nil))

(defun kern-check-opcode-alist (alst ls$)
  (declare (xargs :stobjs ls$))
  (if (endp alst) ls$
    (letk ((opcd (kern-find-fn-opcd (caar alst))))
      (if (not (equal opcd (cdar alst)))
          (prog2$ (er hard 'kern-check-opcode-alist
                      "built-in opcd failure: ~x0"
                      (list opcd (caar alst) (cdar alst)))
            ls$)
       (kern-check-opcode-alist (cdr alst) ls$)))))

(defun kern-initial-fns () '(quote if equal cons hide fail))

(defun kern-base-opcd-alist ()
  (list (cons 'quote (kern-opcd-quote))
        (cons 'if    (kern-opcd-if))
        (cons 'equal (kern-opcd-equal))
        (cons 'cons  (kern-opcd-cons))
        (cons 'hide  (kern-opcd-hide))
        (cons 'fail  (kern-opcd-fail))))

(defun kern-check-base-opcodes (ls$)
  (declare (xargs :stobjs ls$))
  (kern-check-opcode-alist (kern-base-opcd-alist) ls$))

(defunf kern-clear-node-counts (n ls$)
  (if (kern-zp n) ls$
    (letk ((n (1-^ n))
           (ls$ (oper.set-num-nodes n 0))
           (ls$ (oper.set-num-trans n 0)))
      (kern-clear-node-counts n ls$))))

(defun user-node-limit (sp) (expt 2 sp))
(defun user-node-alloc (sp) (floor (user-node-limit sp) 8))
(defun user-node-step (sp) (user-node-alloc sp))
(defun qobj-tbl-initial (sp) (floor (user-node-alloc sp) 4))
(defun oper-tbl-initial (sp) (floor (user-node-alloc sp) 8))
(defun rule-tbl-initial (sp) (* 2 (oper-tbl-initial sp)))
(defun undo-stk-initial (sp) (* 2 (oper-tbl-initial sp)))
(defun node-hash-size (sp) (* (user-node-alloc sp) 2))
(defun node-hash-mask (sp) (1- (node-hash-size sp)))
;; The 1+ in the next definition is needed because an entry may take two slots
;; and we need an extra slot for padding the last entry in the memo-table.
(defun node-memo-size (sp) (1+ (floor (node-hash-size sp)
                                      (kern-hash-memo-divisor))))
(defun node-memo-hash (sp) (- (node-memo-size sp) 2))
(defun start-clock-value (sp) (floor (user-node-alloc sp) 2))
(defun node-trans-size (sp) (* (floor (user-node-alloc sp) 2)
                               (+ (kern-base-trans-alloc)
                                  (kern-avg-num-args))))
(defun node-stor-size (sp) (* (user-node-alloc sp)
                              (+ (kern-base-node-alloc)
                                 (kern-avg-num-args))))
(defun initial-loop-size (sp) (floor (user-node-alloc sp) 8))
(defun curr-ctx-stk-size (sp) (* sp sp 10))
(defun first-quote-ndx () (1+ (kern-qobj-btm)))
(defun first-oper-ndx () (1+ (kern-opcd-btm)))
(defun first-node-ndx () (1+ (kern-node-btm)))
(defun first-trans-ndx () (1+ (kern-node-btm)))

(defun kern-logic-init (term wrld ens ls$)
  (declare (xargs :stobjs ls$))
  (let* ((fns (all-fnnames term))
         (fns (set-difference-eq fns (kern-initial-fns)))
         (fns (append (kern-initial-fns) fns))
         (alist (kern-rules-alist fns ens wrld ls$))
         (oprcds (kern-create-oprcds alist ens wrld)))
    (cond ((>= (length oprcds) (kern-max-num-fns))
           (prog2$ (er0 hard 'kern-logic-init
                        "The kernel simplifier has a hard limit of ~x0 for the number of ~
                         functions which can be installed for a given term. The number of ~
                         functions required for this call is ~x1 which exceeds th limit."
                        (kern-max-num-fns)
                        (length oprcds))
             ls$))
          ((>= (oprcd.narg (kern-find-max-narg oprcds)) (kern-max-num-args))
           (prog2$ (er0 hard 'kern-logic-init
                        "The kernel simplifier has a hard limit of ~x0 for the number of ~
                         arguments for any given function. The number of arguments for the ~
                         function ~x1 is ~x2 which exceeds the limit."
                        (kern-max-num-args)
                        (oprcd.name (kern-find-max-narg oprcds))
                        (oprcd.narg (kern-find-max-narg oprcds)))
             ls$))
          (t
           (letk ((sp (get-kern-size-param ls$))
                  (ls$ (resize-node-stor (node-stor-size sp) ls$))
                  (ls$ (resize-node-hash (node-hash-size sp) ls$))
                  (ls$ (kern-init-node-hash (node-hash-size sp) ls$))
                  (ls$ (set-alloc-nodes (first-node-ndx) ls$))
                  (ls$ (set-num-of-nodes 0 ls$))
                  (ls$ (ensure-qobj (qobj-tbl-initial sp) 0))
                  (ls$ (resize-quote-hash (kern-quote-hash-size) ls$))
                  (ls$ (kern-init-quote-hash (kern-quote-hash-size) ls$))
                  (ls$ (set-next-quote (first-quote-ndx) ls$))
                  (ls$ (set-node-step (user-node-step sp) ls$))
                  (ls$ (set-node-limit (user-node-limit sp) ls$))
                  (ls$ (set-hash-mask (node-hash-mask sp) ls$))
                  (ls$ (resize-trans-stor (node-trans-size sp) ls$))
                  (ls$ (set-alloc-trans (first-trans-ndx) ls$))
                  (ls$ (set-num-trans-nodes 0 ls$))
                  (ls$ (ensure-memo (node-memo-size sp) 0))
                  (ls$ (kern-init-memo-tbl (node-memo-size sp) ls$))
                  (ls$ (ensure-loop (initial-loop-size sp) 0))
                  (ls$ (set-loop-stk-top (1+ (kern-loop-btm)) ls$))
                  (ls$ (ensure-oper (oper-tbl-initial sp) 0))
                  (ls$ (set-next-op-ndx (first-oper-ndx) ls$))
                  (ls$ (resize-op-hash (kern-op-hash-tbl-size) ls$))
                  (ls$ (kern-init-op-hash (kern-op-hash-tbl-size) ls$))
                  (ls$ (ensure-undo (undo-stk-initial sp) 0))
                  (ls$ (set-undo-top 1 ls$))
                  (ls$ (set-undo-free-list (kern-undo-btm) ls$))
                  (ls$ (ensure-rule (rule-tbl-initial sp) 0))
                  (ls$ (set-next-rule-ndx (kern-first-rule-ndx) ls$))
                  (ls$ (set-current-world wrld ls$))
                  (ls$ (set-current-ens ens ls$))
                  (ls$ (set-var-chg-stk (kern-node-btm) ls$))
                  (ls$ (set-current-age 1 ls$))
                  (ls$ (set-bchain-limit 2 ls$))
                  (ls$ (set-next-extend-age 2 ls$))
                  (ls$ (set-current-dctx (kern-dctx-0) ls$))
                  (ls$ (set-current-clock (start-clock-value sp) ls$))
                  (ls$ (set-warned-ctx-depth nil ls$))
                  (ls$ (kern-install-base-quotes ls$))
                  (ls$ (kern-install-oprcds oprcds ls$))
                  (ls$ (kern-check-base-opcodes ls$))
                  (ls$ (set-rew-call-depth 0 ls$))
                  (ls$ (set-curr-ctx-top 0 ls$))
                  (ls$ (resize-curr-ctx-stk (curr-ctx-stk-size sp) ls$))
                  (ls$ (kern-clear-node-counts (num-of-oper) ls$)))
             ls$)))))

(mutual-recursionk
(defunk has-fail-subterm (x ls$)
  (letk ((opcd (node.opcd x)))
    (or (=^ opcd (opcd-fail))
	(and (/=^ opcd (opcd-quote))
	     (not (opcd.is-var opcd))
	     (args-has-fail-subterm x (opcd.narg opcd) 0 ls$)))))

(defunk args-has-fail-subterm (x n i ls$)
  (and (not (zp n))
       (or (has-fail-subterm (node.arg x i) ls$)
	   (args-has-fail-subterm x (1-^ n) (1+^ i) ls$))))
)

(defun kern-create-result (node term ls$ state)
  (declare (xargs :stobjs (ls$ state)))
  (if (=^ node (kern-node-btm))
      (let ((state (fms "An internal error in kernel-simplify: returned (node-btm). ~
                         Please notify current maintainer of kern-simp."
                        () (standard-co state) state nil)))
        (mv t term () state))
    (let ((ttree (kern-print-stats ls$)))
      (if (kern-has-fail-subterm node ls$)
	  (mv nil term ttree state)
	(mv nil (kern-node-to-term node) ttree state)))))

(defun kern-simplify-term (term wrld ens ls$ us$)
  (declare (xargs :stobjs (ls$ us$)))
  (letk ((term. (kern-unfak-term term))
         (ls$ (kern-logic-init term. wrld ens ls$))
         (us$ (kern-user-init ls$ us$))
         (node ls$ (kern-term-to-node term. ls$))
         (node+ dcv ls$ us$ (kern-rewrite-node node ls$ us$)))
        (kern-force-assert (or (=^ dcv (kern-dcv-empty)) (list dcv))
                           (mv node+ ls$ us$))))

(defun parse-kernel-simplify-hint (hint)
  (if (and (consp hint)
           (eq (first hint) 'k-s-hint)
           (quote-listp (rest hint)))
      (mv (second (second hint))
          (second (third hint))
          (second (fourth hint))
          (second (fifth hint))
          (second (sixth hint))
	  (second (seventh hint))
	  (second (eighth hint))
	  (second (ninth hint)))
    (mv nil nil nil nil nil nil 4 t)))

(defun min-size-param () 13) ;; this one ensures lower-bound for several parameters
(defun max-size-param () 36) ;; this one is limited by the number of bits in a node

(defun kern-init-top-params (hint ls$)
  (declare (xargs :stobjs ls$))
  (mv-let (size-param quiet alloc-display flip-t flip-nil rule-trace prune-depth context-reduce)
      (parse-kernel-simplify-hint hint)
    (let* ((size-param (min (max (nfix size-param) (min-size-param)) (max-size-param)))
           (ls$ (set-kern-size-param size-param ls$))
           (ls$ (set-output-verbose (not quiet) ls$))
           (ls$ (set-ls$-resize-array-display alloc-display ls$))
	   (ls$ (set-initial-rule-trace-descriptor rule-trace ls$))
	   (ls$ (set-initial-node-prune-depth prune-depth ls$))
	   (ls$ (set-allow-context-reduction context-reduce ls$))
           (ls$ (set-flip-t-fns (and (true-listp flip-t) flip-t) ls$))
           (ls$ (set-flip-nil-fns (and (true-listp flip-nil) flip-nil) ls$)))
      ls$)))

(defun kern-clause-to-term (cl)
  (cond ((endp cl) *T*)
        ((endp (rest cl)) (first cl))
        (t (list 'if (first cl) *T* (kern-clause-to-term (rest cl))))))

(defun kern-simplify-main (cl hint ls$ us$ state)
  (declare (xargs :stobjs (ls$ us$ state)))
  (let* ((ls$ (kern-init-top-params hint ls$))
         (cl (kern-expand-lambda-terms cl))
         (term (kern-clause-to-term cl)))
    (mv-let (node ls$ us$)
        (kern-simplify-term term (w state) (ens state) ls$ us$)
      (mv-let (erp term ttree state)
          (kern-create-result node term ls$ state)
        (mv erp term ttree state ls$ us$)))))

(defun kernel-simplify (cl hint state)
  (declare (xargs :stobjs state))
  (with-local-stobj ls$
    (mv-let (erp term ttree state ls$)
	(with-local-stobj us$
	  (mv-let (erp term ttree state ls$ us$)
	      (kern-simplify-main cl hint ls$ us$ state)
	    (mv erp term ttree state ls$)))
      (declare (ignore ttree))
      (let ((cl-list (list (list term))))
	(mv erp cl-list state)))))

(kern-comp)

(logic)

;; the "hint" for the kernel-simplify processor is expected to be a call of the following
;; function where the arguments to the call should be quoted constants which are used to
;; provide optional parameters to simplifier:

(defun k-s-hint (size-param quiet alloc-display flip-t flip-nil rule-trace prune-depth context-reduce)
  (list 'k-s-hint
	(list 'quote size-param)
	(list 'quote quiet)
	(list 'quote alloc-display)
        (list 'quote flip-t)
        (list 'quote flip-nil)
	(list 'quote rule-trace)
	(list 'quote prune-depth)
	(list 'quote context-reduce)))

(defmacro defthmk-generic (name form &rest aux)
  `(defthm ,name ,form
     :hints (("Goal"
	      :do-not-induct t
	      :do-not '(preprocess simplify eliminate-destructors fertilize generalize eliminate-irrelevance)
	      :clause-processor (:function kernel-simplify :hint (k-s-hint 20 nil nil nil nil nil 4 nil))))
     ,@aux))

(define-trusted-clause-processor kernel-simplify nil :ttag kernel-simplify-ttag)

