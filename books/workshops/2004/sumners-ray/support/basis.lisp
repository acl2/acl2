(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;; definitions and rules for time operators ;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Even though the invariant prover proves invariants by an induction over time
;; (where time is understood to be natural number), we prefer to use our own
;; operators t+, t-, t0, and tzp to define the behavior of the time
;; parameter. This avoids issues which may arise with the aliasing of ACL2
;; arithmetic and allows us to define time in a manner which avoids the need to
;; introduce natp hypothesis.

(encapsulate
 (((t- *) => *)
  ((t0) => *)
  ((tzp *) => *)
  ((tmsr *) => *))

(local (defun tzp (n) (or (atom n) (car n))))
(local (defun t- (n) (if (tzp n) n (cdr n))))
(local (defun t0 () nil))
(local (defun tmsr (n) (if (tzp n) 0 (1+ (tmsr (cdr n))))))

(defthm tzp-t0redux  (equal (tzp (t0)) t))
(defthm tmsr-ordinal (o-p (tmsr n)))
(defthm tzp-tmsr-o<  (implies (not (tzp n)) (o< (tmsr (t- n)) (tmsr n))))

;; The following definition and theorems are not exported because we do not
;; want any user functions which are defined in terms of t+, so it is built in
;; directly in the rewriter. We prove these theorems here to demonstrate that
;; the built-in rules in the rewriter are valid.

(local (defun t+ (n) (cons nil n)))

;; The following theorem is included to demonstrate that every object in the
;; ACL2 universe is either tzp or equal to (t+ n) for some n. This also means
;; that if a theorem is proven for (t0) and (t+ n) for every n, then it is true
;; for all n since the only property that we export about (t0) is (tzp (t0)).

(local (defthm time-totality (implies (not (tzp n)) (equal (t+ (t- n)) n))))
(local (defthm tzp-t+redux   (equal (tzp (t+ n)) nil)))
(local (defthm t--t+-redux   (equal (t- (t+ n)) n))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; auxiliary helper functions ;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro char-in-range (c x y)
  `(let ((a (char-code ,c)))
     (and (>= a (char-code ,x))
          (<= a (char-code ,y)))))

(defun str-to-number1 (str i n acc)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) acc)
        ((char-in-range (char str i) #\0 #\9)
         (str-to-number1 str (1+ i) (1- n)
                         (+ (* acc 10)
                            (- (char-code (char str i))
                               (char-code #\0)))))
        (t (er hard 'str-to-number
               "ill-formed token encountered: ~x0"
               str))))

(defun str-to-number (str)
  (str-to-number1 str 0 (length str) 0))

(defun digit-to-str (dig)
  (string (code-char (+ dig (char-code #\0)))))

(defun number-to-str1 (num d)
  (declare (xargs :measure (nfix d)))
  (cond ((zp d)
         (er hard 'number-2-str
             "attempt to print too large natural: ~x0" num))
        ((not (and (integerp num) (>= num 0)))
         (er hard 'number-2-str
             "attempt to print non-natural: ~x0" num))
        ((< num 10) (digit-to-str num))
        (t (string-append (number-to-str1 (floor num 10) (1- d))
                          (digit-to-str (mod num 10))))))

(defun number-to-str (num)
  (number-to-str1 num 1000000))

(defun pos-of-char1 (ch str i n)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) nil)
        ((>= i (length str)) nil)
        ((eql (char str i) ch) i)

        (t (pos-of-char1 ch str (1+ i) (1- n)))))

(defun pos-of-char (ch str)
  (pos-of-char1 ch str 0 (length str)))

(defun to-string (obj)
  (cond ((stringp obj)    obj)
        ((characterp obj) (string obj))
        ((symbolp obj)    (string-downcase (symbol-name obj)))
        ((natp obj)       (number-to-str obj))
        (t (er hard 'to-string
               "don't know how to convert to string: ~x0" obj))))

(defun snap-objs (objs)
  (if (endp objs) ""
    (string-append (to-string (first objs))
                   (snap-objs (rest objs)))))

(defmacro snap (&rest objs)
  `(snap-objs (list ,@objs)))

(defmacro snap-sym (&rest objs)
  `(intern (string-upcase (snap ,@objs)) "ACL2"))

(defmacro snap-key (&rest objs)
  `(intern (string-upcase (snap ,@objs)) "KEYWORD"))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;; macro for generating if-lifting rules ;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun replace-arg (call arg term)
  (cond ((endp call)
         (er hard 'replace-arg "did not find arg"))
        ((eq arg (first call))
         (cons term (rest call)))
        (t
         (cons (first call)
               (replace-arg (rest call) arg term)))))

(defun if-lift-call (arg call)
  `(defthm ,(snap-sym 'if-lift- (first call) '- arg)
     (equal ,(replace-arg call arg '(if tst tbr fbr))
            (if tst ,(replace-arg call arg 'tbr) ,(replace-arg call arg 'fbr)))))

(defun if-lifts-call (args call)
  (if (endp args) ()
    (cons (if-lift-call (first args) call)
          (if-lifts-call (rest args) call))))

(defun if-lifts-calls (calls)
  (if (endp calls) ()
    (append (if-lifts-call (rest (first calls)) (first calls))
            (if-lifts-calls (rest calls)))))

(defmacro if-lift-rules (&rest calls)
  (cons 'progn (if-lifts-calls calls)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;; macro for generating abstraction rules ;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun abs-termp (x)
  (and (consp x)
       (not (quotep x))
       (pseudo-termp x)))

(defun abs-term-listp (x)
  (or (null x)
      (and (consp x)
           (abs-termp (first x))
           (abs-term-listp (rest x)))))

(defun make-abs-thm (trm n)
  `(defthm ,(snap-sym 'abstract- (first trm) '- n)
     (equal ,trm (hide ,trm))
     :hints (("Goal" :expand (hide ,trm)))))

(defun make-abs-thms (trms n)
  (if (endp trms) ()
    (cons (make-abs-thm (first trms) n)
          (make-abs-thms (rest trms) (1+ n)))))

(defmacro abstract-terms (&rest trms)
  (declare (xargs :guard (abs-term-listp trms)))
  `(progn ,@(make-abs-thms trms 0)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;; macro for generating finite case-splits ;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun finite-case-term (tgt cases)
  (if (endp cases) tgt
    (let ((c (first cases)))
      `(if (equal ,tgt ,c) ,c ,(finite-case-term tgt (rest cases))))))

(defmacro finite-cases (name class target cases)
  (declare (xargs :guard (and (symbolp name)
                              (member class '(:state :input))
                              (consp target)
                              (symbol-listp target)
                              (true-listp cases))))
  (let ((op! (snap-sym (first target) '!)))
    `(encapsulate
      ()
      (defun ,op! ,(rest target) ,target)
      (defthm ,(snap-sym name '-finite-cases)
        (implies (syntaxp (equal n (quote ,(if (eq class :input) '(t+ n) 'n))))
                 (equal ,target ,(finite-case-term (cons op! (rest target)) cases))))
      ,@(and (eq class :state)
             `((defthm ,(snap-sym name '-unwrap-cases)
                 (implies (syntaxp (or (equal n '(t0)) (equal n '(t+ n))))
                          (equal ,(cons op! (rest target)) ,target)))))
      (in-theory (disable ,op!)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; basic rules for equal and if ;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We use if* here to avoid ACL2 restriction on if lhs rewrite rules. The
;; invariant prover will read any lhs if* rules as if rules and so the user is
;; encouraged to make use of this bypass around ACL2 when they wish to have
;; rules which have 'if as the outermost lhs operator.

(defthm if-if-lift-rule
  (equal (if* (if x y z) a b)
         (if x (if y a b) (if z a b))))

(defthm equal-if-lift-lhs
  (equal (equal (if x y z) a)
         (if x (equal y a) (equal z a))))

(defthm equal-if-lift-rhs
  (equal (equal a (if x y z))
         (if x (equal a y) (equal a z))))

(defthm equal-orient-rule
  (implies (syntaxp (term-order x y))
           (equal (equal x y) (equal y x)))
  ;; I have to add the following to keep ACL2 from adding
  ;; a loop stopper by default :(
  :rule-classes ((:rewrite :loop-stopper ())))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;; define-system macro ;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun reg-declp (reg)
  (and (true-listp reg)
       (equal (length reg) 4)
       (symbolp (first reg))
       (symbol-listp (second reg))))

(defun reg-declsp (regs)
  (or (null regs)
      (and (consp regs)
           (reg-declp (first regs))
           (reg-declsp (rest regs)))))

(defun reg-fn (reg)
  (list `(defun ,(first reg) ,(second reg)
           (declare (xargs :measure (tmsr n)))
           (if (tzp n) ,(third reg) (let ((n- (t- n))) ,(fourth reg))))))

(defun reg-thm (reg)
  (list `(if-lift-rules (,(first reg) ,@(second reg)))
        `(defthm ,(snap-sym (first reg) '-tzp)
           (implies (tzp n)
                    (equal (,(first reg) ,@(second reg))
                           ,(third reg))))
        `(defthm ,(snap-sym (first reg) '-t+)
           (implies (not (tzp n))
                    (equal (,(first reg) ,@(second reg))
                           (let ((n- (t- n))) ,(fourth reg)))))))

(defun reg-fns (regs)
  (if (endp regs) ()
    (append (reg-fn (first regs))
            (reg-fns (rest regs)))))

(defun reg-thms (regs)
  (if (endp regs) ()
    (append (reg-thm (first regs))
            (reg-thms (rest regs)))))

(defmacro define-system (name &rest regs)
  (declare (xargs :guard (and (symbolp name) (reg-declsp regs)))
           (ignore name))
  (list* 'progn
         (cons 'mutual-recursion (reg-fns regs))
         (reg-thms regs)))
