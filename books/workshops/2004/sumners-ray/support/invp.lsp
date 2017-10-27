#| (ld "invp.lisp") |#

(in-package "ACL2")

#|

  invp.lisp
  ~~~~~~~~~

CODE SECTIONS
-------------

1. include the basis book which defines numerous operators
2. definition and initialization of ic$ stobj
3. inside-out conditional term rewriter
4. extended rewriting and propagating rep-step
5. invariant checker implementation
6. top-level algorithm and interface
7. some simple test examples


TODO LIST
---------

1. Add translation of model to Verilog and interface to VIS model checker.

2. Add deep if-lifting to rewrite-step

3. Add some tagging of terms to declare the term to be in normal-form to
   avoid rewriting terms which are in normal-form.


NOTES/ISSUES
------------

1. Why do we need to set the translate-flg in the calls of simplify-term??

2. Need to write-up arguments for the correctness of all of the reductions
   supported in this tool.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| <SECTION>   1. include the basis book which defines numerous operators |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "basis")

(defun zip-fms (chars lst)
  (cond ((endp lst) ())
        ((endp chars)
         (er hard 'zip-fms "too many args to detail!"))
        (t (acons (car chars) (car lst)
                  (zip-fms (cdr chars) (cdr lst))))))

(defconst *fms-chars*
  '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))

(program)

(defun detail-fn (fmt-str lst chan state)
  (declare (xargs :stobjs state))
  (if (not chan) state
    (fms fmt-str (zip-fms *fms-chars* lst) chan state nil)))

(defmacro detail (&rest r)
  `(let ((state (detail-fn ,(first r)
                           ,(cons 'list (rest (butlast r 1)))
                           (detail-channel ic$) state)))
     ,(car (last r))))

(defmacro report (&rest r)
  `(prog2$ (cw ,@(butlast r 1))
           (detail ,(string-append "REPORT:" (first r))
                   ,@(rest r))))

(defmacro bozo (&rest r)
  `(prog2$ (cw ,@(butlast r 1))
           ,(car (last r))))

(defmacro seq (&rest bind)
  (cond ((endp bind)
         (er hard 'seq
             "no body/result expression in seq form"))
        ((endp (cdr bind))
         (car bind))
        ((atom (caar bind))
         `(let ((,(caar bind) ,(cadar bind)))
            (seq ,@(cdr bind))))
        (t
         `(mv-let ,(caar bind) ,(cadar bind)
            (seq ,@(cdr bind))))))

(defmacro die (&rest r)
  `(prog2$ (er hard ,@(butlast r 1))
           ,(car (last r))))

(logic)

(defabbrev bnil () 0)
(defabbrev bnth (i x) (logbitp i x))

(defun blist-length (x)
  (cond ((atom x)
         (er hard 'blist-length "ill-formed"))
        ((eq (first x) 'bnil) 0)
        ((eq (first x) 'bcons)
         (1+ (blist-length (third x))))
        (t (er hard 'blist-length "ill-formed"))))

(defmacro bcons (b x)
  (let ((size (1+ (blist-length x))))
    `(the (unsigned-byte ,size)
       (let ((b ,b)
             (x (the (unsigned-byte ,size) (* ,x 2))))
         (declare (type (unsigned-byte ,size) x))
         (if b (the (unsigned-byte ,size) (1+ x)) x)))))

(local ; ACL2 primitive
 (defmacro 1+f (x)
   `(the-fixnum (1+ (the-fixnum ,x)))))

(local ; ACL2 primitive
 (defmacro 1-f (x)
   `(the-fixnum (1- (the-fixnum ,x)))))

(defmacro modf (x y)
  `(the-fixnum (mod (the-fixnum ,x) (the-fixnum ,y))))

(defmacro fzp (x)
  `(let ((x ,x))
     (declare (type (signed-byte 29) x))
     (or (not (integerp x))
         (<= x 0))))

(in-theory (disable ash logbitp))

;; We need to get some properties of the functions we deal with from the
;; current ACL2 world. We define the macro fn-prop below for that purpose.
(defabbrev fn-prop (fn prop)
  (getprop fn prop nil 'current-acl2-world (w state)))

;; and more precisely, we will have the unnormalized-body and the formals.
(defabbrev get-formals (fn)
  (fn-prop fn 'formals))

(defabbrev get-body (fn)
  (fn-prop fn 'unnormalized-body))

(defabbrev get-normal-body (fn)
  (fn-prop fn 'body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| <SECTION>   2. definition and initialization of ic$ stobj              |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

;; we now define a stobj which we use to hold much of the state which
;; we use as a holding area for various parameters and variables which
;; are updated throughout the invariant proof
(defstobj ic$
  (reduce-contexts  :type T)
  (jump-bound       :type T)
  (check-bound      :type T)
  (refine-bound     :type T)
  (inputs-bound     :type T)
  (fast-search      :type T)
  (detail-channel   :type T)
  (always-check     :type T)
  (disable-exec     :type T)
  (num-rep-bits     :type T)
  (inv-check-result :type T)
  ;; the following are merely in the stobj instead of being parameters to dfs
  (search-bound :type (signed-byte 29)
                :initially 0)
  (num-states   :type (signed-byte 29)
                :initially 0)
  (num-inputs   :type (signed-byte 29)
                :initially 0)
  (input-vec    :type (array T (0))
                :resizable T)
  (inv-bit      :type T)
  (st-hashtbl   :type (array T (0))
                :resizable T))

(defun is-prime-number (x y)
  (cond ((or (zp x) (= x 1)) t)
        ((eql (mod y x) 0) nil)
        (t (is-prime-number (1- x) y))))

(defun prev-prime-number (x)
  (cond ((zp x) 1)
        ((is-prime-number x x) x)
        (t (prev-prime-number (1- x)))))

(defun clear-ic$-for-inv-check (ic$)
  (declare (xargs :stobjs ic$))
  (seq
   (ic$ (resize-st-hashtbl 0 ic$)) ;; this will clear the st-hashtbl
   (ic$ (resize-st-hashtbl (prev-prime-number (check-bound ic$)) ic$))
   (ic$ (update-inv-check-result nil ic$))
   ic$))

;; we initialize the inv-checker stobj ic$ for the book-keeping we need.
(defun initialize-ic$ (jump-bound
                       check-bound
                       refine-bound
                       inputs-bound
                       fast-search
                       detail-file
                       always-check
                       disable-exec
                       reduce-contexts
                       ic$
                       state)
  (declare (xargs :stobjs (ic$ state)))
  (seq
   (ic$ (update-jump-bound      jump-bound      ic$))
   (ic$ (update-check-bound     check-bound     ic$))
   (ic$ (update-refine-bound    refine-bound    ic$))
   (ic$ (update-inputs-bound    inputs-bound    ic$))
   (ic$ (update-fast-search     fast-search     ic$))
   (ic$ (update-always-check    always-check    ic$))
   (ic$ (update-disable-exec    disable-exec    ic$))
   (ic$ (update-reduce-contexts reduce-contexts ic$))
   (ic$ (clear-ic$-for-inv-check ic$))
   ((channel state)
    (if detail-file
        (open-output-channel detail-file :character state)
      (mv nil state)))
   (ic$ (update-detail-channel channel ic$))
   (mv ic$ state)))

(defun cleanup-ic$ (ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (seq
   (state (close-output-channel (detail-channel ic$) state))
   (mv ic$ state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| <SECTION>   3. iterative inside-out conditional term rewriter          |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

(defabbrev equiv-ops (a b)
  (let ((op-a (if (atom a) a (car a)))
        (op-b (if (atom b) b (car b))))
    (and (not (eq op-a 'lambda))
         (eq op-a op-b))))

(defabbrev hidep (x)
  (and (consp x) (eq (first x) 'hide)))

(defun equiv-terms1 (x y is-lst)
  (cond ((and is-lst (endp x)) (endp y))
        (is-lst (and (equiv-terms1 (first x) (first y) nil)
                     (equiv-terms1 (rest x) (rest y) t)))
        ((hidep x) (equiv-terms1 (second x) y nil))
        ((hidep y) (equiv-terms1 x (second y) nil))
        ((atom x) (eq x y))
        ((atom y) nil)
        (t (and (equiv-ops (first x) (first y))
                (equiv-terms1 (rest x) (rest y) t)))))

(defabbrev equiv-terms (x y) (equiv-terms1 x y nil))

(defun bind-args* (vars args rslt)
  (if (endp vars) rslt
    (bind-args* (rest vars) (rest args)
                (cons (cons (first vars)
                            (first args))
                      rslt))))

(defabbrev bind-args (vars args)
  (bind-args* vars args ()))

(defun subst-term* (trm alst is-lst in-synp ctx)
  (cond
   ((and is-lst (endp trm)) ())
   (is-lst (cons (subst-term* (first trm) alst nil in-synp ctx)
                 (subst-term* (rest trm) alst t in-synp ctx)))
   ((atom trm)
    (let* ((mtch (assoc-eq trm alst))
           (val (if mtch (cdr mtch) trm)))
      (if (not in-synp) val
        (list 'quote (if (and (not mtch) (eq trm 'ctx)) ctx val)))))
   (t
    (let ((op (first trm)))
      (cond
       ((eq op 'quote) trm)
       ((eq op 'synp) (subst-term* (second (fourth trm)) alst nil t ctx))
       (t (cons (if (atom op) (list op) op)
                (subst-term* (rest trm) alst t in-synp ctx))))))))

(defabbrev subst-term-ctx (trm alst ctx)
  (subst-term* trm alst nil nil ctx))

(defabbrev subst-term (trm alst)
  (subst-term* trm alst nil nil nil))

(defabbrev st-phase   (st) (car st))
(defabbrev st-wrld    (st) (cadr st))
(defabbrev st-ens     (st) (caddr st))
(defabbrev st-rew-ctx (st) (cadddr st))
(defabbrev st-depth   (st) (cddddr st))

(defun make-init-st (wrld ens rew-ctx depth)
  (list* nil wrld ens rew-ctx depth))

(defabbrev in-hyps (st)
  (if (st-phase st) st (cons t (cdr st))))

(defabbrev match-ctx-elem (trm ctx iff)
  (cond
   ((and iff (equiv-terms trm ctx)) ''t)
   ((let ((op (first ctx)))
      (or (eq op 'equal)
          (and (eq op 'iff) iff)))
    (and (equiv-terms trm (second ctx))
         (third ctx)))))

(defun match-in-ctx* (trm ctx iff)
  (and (not (endp ctx))
       (or (match-ctx-elem trm (first ctx) iff)
           (match-in-ctx* trm (rest ctx) iff))))

(defun match-in-ctx (trm ctx iff)
  (if (quotep trm) nil (match-in-ctx* trm ctx iff)))

(defmacro gprop (name prop)
  `(getprop ,name ,prop nil 'current-acl2-world wrld))

(defun quoted-args (args)
  (or (endp args)
      (and (quotep (first args))
           (quoted-args (rest args)))))

(defun fncall-args (args)
  (if (endp args) ()
    (cons (second (first args))
          (fncall-args (rest args)))))

(defun merge-alsts (new alst)
  (if (endp new) alst
    (merge-alsts (cdr new)
                 (let ((mtch (assoc-eq (caar new) alst)))
                   (if mtch alst (cons (car new) alst))))))

(defun find-nume (pairs rune)
  (cond ((endp pairs) nil)
        ((equal rune (cdar pairs))
         (caar pairs))
        (t (find-nume (cdr pairs) rune))))

(defun rewrt-built-in (op args)
  (cond
   ((eq op 'if)
    (let ((tst (first args))
          (tbr (second args))
          (fbr (third args)))
      (cond
       ((quotep tst) (if (second tst) tbr fbr))
       ((equal tbr fbr) tbr))))
   ((eq op 'equal)
    (let ((lhs (first args))
          (rhs (second args)))
      (cond
       ((equal lhs rhs) ''t)
       ((and (quotep lhs) (quotep rhs)) ''nil))))
   (t
    (let ((n (first args)))
      (cond
       ((and (consp n) (eq (first n) 't+))
        (cond ((eq op 'tzp) ''nil)
              ((eq op 't-) (second n)))))))))

(defun all-vars-bound* (trm alst is-lst)
  (cond
   ((and is-lst (endp trm)) t)
   (is-lst (and (all-vars-bound* (first trm) alst nil)
                (all-vars-bound* (rest trm) alst t)))
   ((atom trm) (assoc-eq trm alst))
   ((eq (first trm) 'quote) t)
   (t (all-vars-bound* (rest trm) alst t))))

(defabbrev all-vars-bound (trm alst)
  (all-vars-bound* trm alst nil))

(defun subtermp1 (x y is-lst)
  (cond ((and is-lst (endp y)) nil)
        (is-lst (or (subtermp1 x (first y) nil)
                    (subtermp1 x (rest y) t)))
        ((equiv-terms x y) t)
        ((atom y) nil)
        ((eq (first y) 'quote) nil)
        (t (subtermp1 x (rest y) t))))

(defun subtermp (x y) (subtermp1 x y nil))

(defun subterm-ctx (lhs ctx)
  (and (not (endp ctx))
       (or (subtermp lhs (first ctx))
           (subterm-ctx lhs (rest ctx)))))

(defabbrev func-symb (term)
  (let ((op (car term))) (if (atom op) op (car op))))

(mutual-recursion
(defun unify-1way1 (pat term alist)
  (cond
   ((variablep pat)
    (let ((pair (assoc-eq pat alist)))
      (cond (pair (cond ((equiv-terms (cdr pair) term)
                         (mv t alist))
                        (t (mv nil alist))))
            (t (mv t (cons (cons pat term) alist))))))
   ((fquotep pat)
    (cond ((equal pat term) (mv t alist))
          (t (mv nil alist))))
   ((variablep term) (mv nil alist))
   ((fquotep term)
    (let ((func-symb (func-symb pat)))
      (cond
       ((acl2-numberp (cadr term))
        (case func-symb
          (binary-+
           (cond
            ((quotep (fargn pat 1))
             (unify-1way1 (fargn pat 2) (kwote (- (cadr term) (fix (cadr (fargn pat 1))))) alist))
            ((quotep (fargn pat 2))
             (unify-1way1 (fargn pat 1) (kwote (- (cadr term) (fix (cadr (fargn pat 2))))) alist))
            (t (mv nil alist))))
          (binary-*
           (cond
            ((and (quotep (fargn pat 1))
                  (integerp (cadr (fargn pat 1)))
                  (> (abs (cadr (fargn pat 1))) 1))
             (unify-1way1 (fargn pat 2) (kwote (/ (cadr term) (cadr (fargn pat 1)))) alist))
            ((and (quotep (fargn pat 2))
                  (integerp (cadr (fargn pat 2)))
                  (> (abs (cadr (fargn pat 2))) 1))
             (unify-1way1 (fargn pat 1) (kwote (/ (cadr term) (cadr (fargn pat 2)))) alist))
            (t (mv nil alist))))
          (unary--
           (cond
            ((>= (+ (realpart (cadr term)) (imagpart (cadr term))) 0)
             (mv nil alist))
            (t (unify-1way1 (fargn pat 1) (kwote (- (cadr term))) alist))))
          (unary-/
           (cond
            ((or (>= (* (cadr term) (conjugate (cadr term))) 1) (eql 0 (cadr term)))
             (mv nil alist))
            (t (unify-1way1 (fargn pat 1) (kwote (/ (cadr term))) alist))))
          (otherwise (mv nil alist))))
      ((symbolp (cadr term))
       (cond
        ((eq func-symb 'intern-in-package-of-symbol)
         (let ((pkg (symbol-package-name (cadr term)))
               (name (symbol-name (cadr term))))
           (mv-let (ans alist1)
               (unify-1way1 (fargn pat 1) (kwote name) alist)
             (if ans
                 (if (and (nvariablep (fargn pat 2))
                          (fquotep (fargn pat 2)))
                     (if (not (symbolp (cadr (fargn pat 2))))
                         (mv (if (equal term *nil*) ans nil) alist)
                       (if (equal pkg (symbol-package-name (cadr (fargn pat 2))))
                           (mv ans alist1)
                         (mv nil alist)))
                   (mv-let (ans alist2)
                       (unify-1way1 (fargn pat 2) term alist1)
                     (if ans (mv ans alist2) (mv nil alist))))
               (mv nil alist)))))
         (t (mv nil alist))))
      ((stringp (cadr term))
       (cond
        ((and (eq func-symb 'coerce) (equal (fargn pat 2) ''string))
         (unify-1way1 (fargn pat 1) (kwote (coerce (cadr term) 'list)) alist))
        (t (mv nil alist))))
      ((consp (cadr term))
       (cond
        ((eq func-symb 'cons)
         (mv-let (ans alist1)
             (unify-1way1 (fargn pat 1) (kwote (car (cadr term))) alist)
           (if ans
               (mv-let (ans alist2)
                   (unify-1way1 (fargn pat 2) (kwote (cdr (cadr term))) alist1)
                 (if ans (mv ans alist2) (mv nil alist)))
             (mv nil alist))))
        (t (mv nil alist))))
      (t (mv nil alist)))))
   (t
    (let ((pat-fn (func-symb pat))
          (term-fn (func-symb term)))
      (cond
       ((or (not (eq pat-fn term-fn)) (eq pat-fn 'lambda))
        (mv nil alist))
       ((eq pat-fn 'equal)
        (unify-1way1-equal (fargn pat 1) (fargn pat 2)
                           (fargn term 1) (fargn term 2)
                           alist))
       (t (mv-let (ans alist1)
              (unify-1way1-lst (fargs pat) (fargs term) alist)
            (if ans (mv ans alist1) (mv nil alist)))))))))

(defun unify-1way1-lst (pl tl alist)
  (if (endp pl) (mv t alist)
    (mv-let (ans alist)
        (unify-1way1 (car pl) (car tl) alist)
      (if (not ans) (mv nil alist)
        (unify-1way1-lst (cdr pl) (cdr tl) alist)))))

(defun unify-1way1-equal1 (pat1 pat2 term1 term2 alist)
  (mv-let (ans alist1)
      (unify-1way1 pat1 term1 alist)
    (if (not ans) (mv nil alist)
      (mv-let (ans alist2)
          (unify-1way1 pat2 term2 alist1)
        (if ans (mv ans alist2) (mv nil alist))))))

(defun unify-1way1-equal (pat1 pat2 term1 term2 alist)
  (mv-let (ans alist)
      (unify-1way1-equal1 pat1 pat2 term1 term2 alist)
    (if ans (mv ans alist)
      (unify-1way1-equal1 pat2 pat1 term1 term2 alist))))
)

(defun unify-1way (pat term) (unify-1way1 pat term nil))

(defun ctx-lhs (trm)
  (if (and (consp trm) (member-eq (first trm) '(equal iff))) (second trm) trm))

(defabbrev already-reduced (op op! go)
  (or (eq op! 'quote)
      (eq op! 'hide)
      (and (eq op op!) (not go))))

(mutual-recursion
(defun prune-trm1 (trm)
  (if (atom trm) trm
    (let* ((op (first trm))
           (op! (if (atom op) op (first op))))
      (cond ((eq op op!) trm)
            ((eq op! 'quote) (cons 'quote (rest trm)))
            (t (cons op! (prune-args (rest trm))))))))

(defun prune-args (args)
  (if (endp args) ()
    (cons (prune-trm1 (first args))
          (prune-args (rest args)))))
)

(defabbrev prune-trm (op op! trm)
  (cond ((eq op op!) trm)
        ((eq op! 'hide) (prune-trm1 trm))
        (t (cons op! (rest trm)))))

(mutual-recursion
(defun rewrt-hyp (hyp alst dp ctx st)
  (if (not (all-vars-bound hyp alst)) :fail
    (let ((rew (rewrt-trm (subst-term-ctx hyp alst ctx)
                          nil (1- dp) ctx t (in-hyps st))))
      (if (and (consp hyp) (eq (first hyp) 'synp))
          (cond
           ((not (quotep rew))
            (er hard 'rewrt-hyp "illegal synp rewrite"))
           ((eq (second rew) t) alst)
           ((consp (second rew)) (merge-alsts rew alst))
           (t :fail))
        (if (equal rew ''t) alst :fail)))))

(defun rewrt-hyps (hyps alst dp ctx st)
  (if (endp hyps) alst
    (let ((alst (rewrt-hyp (first hyps) alst dp ctx st)))
      (if (eq alst :fail) alst
        (rewrt-hyps (rest hyps) alst dp ctx st)))))

(defun rewrt-rule (r recp ens trm dp ctx iff st)
  (let ((subc  (access rewrite-rule r :subclass))
        (lhs   (access rewrite-rule r :lhs))
        (rhs   (access rewrite-rule r :rhs))
        (hyps  (access rewrite-rule r :hyps))
        (equiv (access rewrite-rule r :equiv))
        (hinfo (access rewrite-rule r :heuristic-info))
        (nume  (access rewrite-rule r :nume)))
    (and (not (and recp (eq subc 'definition)))
         (member-eq subc '(definition abbreviation backchain))
         (enabled-numep nume ens)
         (consp lhs)
         (implies (eq subc 'backchain) (null hinfo))
         (or (eq equiv 'equal) (and iff (eq equiv 'iff)))
         (consp trm)
         (implies (eq (car trm) 'if*) (not (eq subc 'definition)))
         (mv-let (mtch alst) (unify-1way lhs trm)
           (and mtch
                (let ((alst (if (st-phase st) (if hyps :fail alst)
                              (rewrt-hyps hyps alst dp ctx st))))
                  (and (not (eq alst :fail))
                       (subst-term rhs alst))))))))

(defun rewrt-rules (lemmas recp ens trm dp ctx iff st)
  (and (not (endp lemmas))
       (or (rewrt-rule (first lemmas) recp ens trm dp ctx iff st)
           (rewrt-rules (rest lemmas) recp ens trm dp ctx iff st))))

(defun rewrt-step (trm dp ctx iff st)
  (let* ((wrld (st-wrld st))
         (ens (st-ens st))
         (op (first trm))
         (args (rest trm))
         (op* (if (eq op 'if) 'if* op))
         (op-ok (not (eq op 't+)))
         (lemmas (and op-ok (gprop op* 'lemmas)))
         (recp (and op-ok (gprop op* 'recursivep)))
         (trm* (if (eq op 'if) (cons 'if* args) trm)))
    (or (rewrt-built-in op args)
        (rewrt-rules lemmas recp ens trm* dp ctx iff st)
        (and op-ok (quoted-args args)
             (or (eq (gprop op 'symbol-class) :program) ;; could only occur in synp
                 (let ((nume (find-nume (gprop op 'runic-mapping-pairs)
                                        (list :executable-counterpart op))))
                   (and nume (enabled-numep nume ens))))
             (mv-let (erp val)
; Matt K. mod, 10/2017: Replaced call of ev-fncall-w, now untouchable, by call
; of ev-fncall-w!.
                 (ev-fncall-w! op (fncall-args args) wrld nil nil t nil nil)
               (and (not erp) (list 'quote val))))
        trm)))

(defun redux-ctx (lst ctx go dp st)
  (cond
   ((eq ctx :fail) :fail)
   ((eq lst :fail) :fail)
   ((endp lst) ctx)
   (t
    (let* ((trm (rewrt-trm (first lst) go dp ctx t st))
           (ctx+ (if (quotep trm) (if (second trm) ctx :fail) (cons trm ctx))))
      (redux-ctx (rest lst) ctx+ go dp st)))))

(defun rewrt-ctx (ctx go dp st)
  (let ((ctx+ (redux-ctx (redux-ctx ctx () go dp st) () go dp st)))
    (if (or (eq ctx+ :fail) (equal ctx ctx+)) ctx (rewrt-ctx ctx+ go (1- dp) st))))

(defun extend-ctx (trm ctx go dp st)
  (cond
   ((quotep trm)
    (if (second trm) () :fail))
   ((not (st-rew-ctx st))
    (cons trm ctx))
   ((subterm-ctx (ctx-lhs trm) ctx)
    (rewrt-ctx (cons trm ctx) go dp st))
   (t (cons trm ctx))))

(defun rewrt-if-args (args go dp ctx iff st)
  (let* ((tst (rewrt-trm (first args) go dp ctx t st))
         (tbr (second args))
         (fbr (third args))
         (t-ctx (extend-ctx tst ctx go dp st)))
    (cond
     ((eq t-ctx :fail)
      (list ''nil tbr (rewrt-trm fbr go dp ctx iff st)))
     ((endp t-ctx)
      (list ''t (rewrt-trm tbr go dp ctx iff st) fbr))
     (t
      (let ((f-ctx (extend-ctx (list 'equal tst ''nil) ctx go dp st)))
        (cond
         ((eq f-ctx :fail)
          (list ''t (rewrt-trm tbr go dp ctx iff st) fbr))
         ((endp f-ctx)
          (list ''nil tbr (rewrt-trm fbr go dp ctx iff st)))
         (t
          (list tst
                (rewrt-trm tbr t dp t-ctx iff st)
                (rewrt-trm fbr t dp f-ctx iff st)))))))))

(defun rewrt-args* (args go dp ctx st)
  (if (endp args) ()
    (cons (rewrt-trm (first args) go dp ctx nil st)
          (rewrt-args* (rest args) go dp ctx st))))

(defun rewrt-args (args op go dp ctx iff st)
  (if (eq op 'if)
      (rewrt-if-args args go dp ctx iff st)
    (rewrt-args* args go dp ctx st)))

(defun rewrt-trm (trm go dp ctx iff st)
  (if (zp dp) (list 'hide trm)
    (let ((mtch (match-in-ctx trm ctx iff)))
      (cond
       (mtch (rewrt-trm mtch go (1- dp) ctx iff st))
       ((atom trm) trm)
       (t
        (let* ((op (first trm))
               (op! (if (atom op) op (car op))))
          (if (already-reduced op op! go) (prune-trm op op! trm)
            (let ((args (rewrt-args (rest trm) op! go dp ctx iff st)))
              (if (eq op! 'lambda)
                  (let ((trm+ (subst-term (third op) (bind-args (second op) args))))
                    (rewrt-trm trm+ go dp ctx iff st))
                (let ((trm+ (rewrt-step (cons op! args) (1- dp) ctx iff st)))
                  (rewrt-trm trm+ nil (1- dp) ctx iff st)))))))))))
)

(defconst *rewrt-trm-depth* 100)

(defun rewrt-term (trm ctx iff rew-ctx state)
  (declare (xargs :stobjs state))
  (let ((st (make-init-st (w state) (ens state) rew-ctx *rewrt-trm-depth*)))
    (rewrt-trm trm t (st-depth st) ctx iff st)))

(defabbrev rewrt-pure   (trm)         (rewrt-term trm ()  nil t       state))
(defabbrev rewrt-rep    (trm rew-ctx) (rewrt-term trm ()  t   rew-ctx state))
(defabbrev rewrt-in-ctx (trm ctx)     (rewrt-term trm ctx t   nil     state))

(mutual-recursion
(defun term-contains-force (trm)
  (and (consp trm)
       (or (eq (first trm) 'force)
           (args-contain-force (rest trm)))))

(defun args-contain-force (args)
  (and (not (endp args))
       (or (term-contains-force (first args))
           (args-contain-force (rest args)))))
)

(mutual-recursion
(defun strip-forces-term (trm hyps)
  (if (atom trm) (mv trm hyps)
    (case (first trm)
          ((quote hide) (mv trm hyps))
          (force (mv ''t (cons trm hyps)))
          (t (mv-let (args hyps)
                 (strip-forces-args (rest trm) hyps)
               (mv (cons (first trm) args) hyps))))))

(defun strip-forces-args (args hyps)
  (if (endp args) (mv () hyps)
    (mv-let (fst hyps)
        (strip-forces-term (first args) hyps)
      (mv-let (rst hyps)
          (strip-forces-args (rest args) hyps)
        (mv (cons fst rst) hyps)))))
)

(defun rewrt-rep-loop* (term hyps ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (let ((nterm (rewrt-rep term (reduce-contexts ic$))))
    (if (not (term-contains-force nterm)) (mv nterm hyps)
      (mv-let (nterm nhyps) (strip-forces-term nterm ())
        (rewrt-rep-loop* nterm (append nhyps hyps) ic$ state)))))

(defabbrev rewrt-rep-loop (term)
  (rewrt-rep-loop* term () ic$ state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| <SECTION>   4. extended rewriting and propagating rep-step             |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rewrite-rep-step (rep ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (mv-let (term hyps) (rewrt-rep-loop `((lambda (n) ,rep) (t+ n)))
    (detail "assuming rep hyps: ~p0 ~%" hyps (mv term hyps ic$ state))))

(mutual-recursion
(defun is-rep-term (term)
  (if (atom term) (eq term 'n)
    (let ((op (first term)))
      (or (eq op 'quote)
          (and (not (eq op 't+))
               (not (eq op 'hide))
               (are-rep-args (rest term)))))))

(defun are-rep-args (args)
  (or (endp args)
      (and (is-rep-term (first args))
           (are-rep-args (rest args)))))
)

(defmacro union-terms (x &rest y)
  (if (endp y) x `(union-equal ,x (union-terms ,(car y) ,@(cdr y)))))

(defun extract-rep-subterms (term)
  (cond ((atom term) ())
        ((eq (first term) 'quote) ())
        ((eq (first term) 'if)
         (union-terms (extract-rep-subterms (second term))
                      (extract-rep-subterms (third term))
                      (extract-rep-subterms (fourth term))))
        ((is-rep-term term) (list term))
        (t ())))

(defun extract-non-rep-subterms (term)
  (cond ((atom term) (list term))
        ((eq (first term) 'quote) ())
        ((eq (first term) 'if)
         (union-terms (extract-non-rep-subterms (second term))
                      (extract-non-rep-subterms (third term))
                      (extract-non-rep-subterms (fourth term))))
        ((is-rep-term term) ())
        (t (list term))))

(defun compute-rep-prime (reps step-alist ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (if (endp reps)
      (mv nil nil step-alist nil ic$ state)
    (seq
     (current-rep (first reps))
     ((term fst-hyps ic$ state)
      (rewrite-rep-step current-rep ic$ state))
     ((rst-reps rst-hyps step-alist rst-ins ic$ state)
      (compute-rep-prime (rest reps) step-alist ic$ state))
     (fst-reps (extract-rep-subterms term))
     (reps (union-equal fst-reps rst-reps))
     (hyps (union-equal fst-hyps rst-hyps))
     (fst-ins (extract-non-rep-subterms term))
     (ins (union-equal fst-ins rst-ins))
     (step-alist (acons current-rep term step-alist))
     (mv reps hyps step-alist ins ic$ state))))

(defun compute-step-prime (reps step-alist ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (if (endp reps)
      (mv (list 'bnil) ic$ state)
    (seq
     ((rest-step ic$ state)
      (compute-step-prime (rest reps) step-alist ic$ state))
     (first-step
      (cdr (assoc-equal (first reps) step-alist)))
     (mv (list 'bcons first-step rest-step) ic$ state))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| <SECTION>   5. invariant checker implementation                        |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun clear-st-hashtbl (ndx ic$)
  (declare (xargs :stobjs ic$))
  (if (zp ndx) ic$
    (let* ((ndx (1- ndx))
           (ic$ (update-st-hashtbli ndx nil ic$)))
      (clear-st-hashtbl ndx ic$))))

(defun clear-seen-states (ic$)
  (declare (xargs :stobjs ic$))
  (clear-st-hashtbl (st-hashtbl-length ic$) ic$))

(defconst *hex-digits*
  '("0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "A" "B" "C" "D" "E" "F"))

(defun st-str (n st)
  (if (zp n) ""
    (string-append (st-str (- n 1) (floor st 16))
                   (nth (mod st 16) *hex-digits*))))

(defmacro the-max-fix-st () (expt 2 28))

(defmacro with-st-hash (st rslt)
  `(let ((hash (let ((st ,st)
                     (len (the-fixnum (st-hashtbl-length ic$))))
                 (declare (type (signed-byte 29) len))
                 (the-fixnum (if (< st (the-max-fix-st))
                                 (the-fixnum (mod (the-fixnum st) len))
                               (the-fixnum (mod st len)))))))
     (declare (type (signed-byte 29) hash))
     ,rslt))

(defun legal-bnth (term)
  (and (consp term)
       (eq (first term) 'bnth)
       (integerp (second term))
       (>= (second term) 0)
       (member (third term) '(s i))))

(defun legal-singl (term)
  (or (legal-bnth term)
      (and (consp term)
           (case (first term)
             (quote t)
             (if (and (legal-bnth (second term))
                      (legal-singl (third term))
                      (legal-singl (fourth term))))))))

(defun legal-step (term)
  (and (consp term)
       (case (first term)
         (bcons (and (legal-singl (second term))
                     (legal-step (third term))))
         (bnil t))))

(defmacro state-report-interval () 1000)

(defun check-and-add-seen-state (st ic$)
  (declare (xargs :stobjs ic$))
  (with-st-hash
   st
   (let* ((entry (st-hashtbli hash ic$))
          (seen (cond ((eq entry nil) nil)
                      ((eq entry t) t)
                      ((consp entry) (member st entry))
                      (t (eql st entry)))))
     (if seen
         (mv t ic$)
       (let ((num-states (num-states ic$)))
         (declare (type (signed-byte 29) num-states))
         (prog2$
          (and (eql (modf num-states (state-report-interval)) 0)
               (> num-states 0)
               (cw "num. abstract states visited: ~x0 ~%" num-states))
          (let* ((ic$ (update-num-states (1+f num-states) ic$))
                 (ic$ (update-search-bound (1-f (search-bound ic$)) ic$))
                 (entry (cond ((eq entry nil) st)
                              ((fast-search ic$) t)
                              ((consp entry) (cons st entry))
                              (t (list st entry))))
                 (ic$ (update-st-hashtbli hash entry ic$)))
            (mv nil ic$))))))))

(defun mk-not-term (x)
  (cond ((atom x) (list 'not x))
        ((not (eq (first x) 'equal)) (list 'not x))
        ((equal (second x) ''nil) (third x))
        ((equal (third x) ''nil) (second x))
        (t (list 'not x))))

(defun map-rep-vector (mask reps st)
  (if (endp mask) ()
    (let ((n (first mask)))
      (cons (if (bnth n st) (nth n reps) (mk-not-term (nth n reps)))
            (map-rep-vector (rest mask) reps st)))))

(defun mk-and-term (lst)
  (cond ((endp lst) t)
        ((endp (rest lst)) (first lst))
        (t (cons 'and lst))))

(defun map-counter-example (reps inputs path mask)
  (if (endp path) ()
    (cons (list (mk-and-term (map-rep-vector (caar mask) reps (caar path)))
                (mk-and-term (map-rep-vector (cdar mask) inputs (cdar path))))
          (map-counter-example reps inputs (rest path) (rest mask)))))

(defun get-mask-terms (step tgt n)
  (if (atom step)
      (er hard 'get-mask-terms "illegal step")
    (case (first step)
      (bnil ())
      (bcons
       (if (member n tgt)
           (cons (second step)
                 (get-mask-terms (third step) tgt (1+ n)))
         (get-mask-terms (third step) tgt (1+ n))))
      (t (er hard 'get-mask-terms "illegal step")))))

(defun compute-ev (trm st in)
  (if (atom trm)
      (er hard 'compute-ev "illegal term")
    (case (first trm)
      (quote (second trm))
      (bnth (bnth (second trm)
                  (if (eq (third trm) 's) st in)))
      (if (if (compute-ev (second trm) st in)
              (compute-ev (third trm) st in)
            (compute-ev (fourth trm) st in)))
      (t (er hard 'compute-ev "illegal trm")))))

(defun compute-mask (term st in)
  (if (atom term)
      (er hard 'compute-mask "illegal term")
    (case (first term)
      (quote ())
      (bnth (list term))
      (if (let* ((tst (second term))
                 (tbr (third term))
                 (fbr (fourth term))
                 (tst-v (compute-ev tst st in))
                 (br (if tst-v tbr fbr))
                 (rst (compute-mask br st in)))
            (if (or (quotep tst)
                    (iff (compute-ev tbr st in)
                         (compute-ev fbr st in)))
                rst
              (cons tst rst))))
      (t (er hard 'compute-mask "illegal term")))))

(defun add-mask-bits (mask var rslt)
  (if (endp mask) rslt
    (add-mask-bits (rest mask) var
                   (if (eq var (third (first mask)))
                       (add-to-set-eql (second (first mask)) rslt)
                     rslt))))

(defun compute-masks (trms st in smsk imsk)
  (if (endp trms) (mv smsk imsk)
    (let ((mask (compute-mask (first trms) st in)))
      (compute-masks (rest trms) st in
                     (add-mask-bits mask 's smsk)
                     (add-mask-bits mask 'i imsk)))))

(defun compute-step-masks (step tgt st in)
  (compute-masks (get-mask-terms step tgt 0) st in () ()))

(defun compute-example-mask (path step tgt)
  (if (endp path) ()
    (seq
     ((st-mask in-mask)
      (compute-step-masks step tgt (caar path) (cdar path)))
     (acons st-mask in-mask
            (compute-example-mask (cdr path) step st-mask)))))

(defun transform-rslt-path (path)
  (if (endp (cdr path)) ()
    (seq
     (in (caar path))
     (st (cdadr path))
     (acons st in (transform-rslt-path (cdr path))))))

(defun load-input-vec (input-set ndx ic$)
  (declare (xargs :stobjs ic$))
  (if (endp input-set) ic$
    (let ((ic$ (update-input-veci ndx (first input-set) ic$)))
      (load-input-vec (rest input-set) (1+ ndx) ic$))))

(defun ivarp (x)
  (and (consp x)
       (eq (first x) 'if)
       (natp (second x))
       (eq (third x) t)
       (eq (fourth x) nil)))

(defun input-set-template (term)
  (if (atom term)
      (er hard 'input-set-template "illegal atom term")
    (case (first term)
      (quote (if (second term) t nil))
      (bcons (list 'or
                   (input-set-template (second term))
                   (input-set-template (third term))))
      (bnil :x)
      (bnth (let ((ndx (second term))
                  (var (third term)))
              (cond ((not (and (natp ndx)
                               (member var '(s i))))
                     (er hard 'input-set-template "illegal bnth term"))
                    ((eq var 'i) (list 'if ndx t nil))
                    (t :x))))
      (if (let* ((tst (input-set-template (second term)))
                 (tbr (input-set-template (third term)))
                 (fbr (input-set-template (fourth term)))
                 (tst (if (ivarp tst) (second tst) tst)))
            (cond ((natp tst) (list 'if tst tbr fbr))
                  ((eq tst t) tbr)
                  ((eq tst nil) fbr)
                  ((eq tst :x) (list 'or tbr fbr))
                  (t (er hard 'input-set-template "illegal if term")))))
      (t (er hard 'input-set-template "illegal op term")))))

(defun fully-defined (tmpl)
  (cond ((eq tmpl :x) nil)
        ((atom tmpl) t)
        ((eq (first tmpl) 'or)
         (and (fully-defined (second tmpl))
              (fully-defined (third tmpl))))
        (t
         (and (fully-defined (third tmpl))
              (fully-defined (fourth tmpl))))))

(defun reduce-template (tmpl var valu)
  (cond ((eql tmpl var) valu)
        ((atom tmpl) tmpl)
        ((eq (first tmpl) 'or)
         (let ((a (reduce-template (second tmpl) var valu))
               (b (reduce-template (third tmpl) var valu)))
           (cond ((equal a b) a)
                 ((and (atom a) (atom b)) :x)
                 (t (list 'or a b)))))
        (t
         (let ((tst (reduce-template (second tmpl) var valu)))
           (cond ((eq tst t)
                  (reduce-template (third tmpl) var valu))
                 ((eq tst nil)
                  (reduce-template (fourth tmpl) var valu))
                 (t
                  (let ((tbr (reduce-template (third tmpl) var valu))
                        (fbr (reduce-template (fourth tmpl) var valu)))
                    (cond ((and (equal tbr fbr) (fully-defined tbr)) tbr)
                          ((not (eq tst :x)) (list 'if tst tbr fbr))
                          ((and (atom tbr) (atom fbr)) :x)
                          (t (list 'or tbr fbr))))))))))

(defun first-tmpl-var (tmpl)
  (cond ((natp tmpl) tmpl)
        ((atom tmpl) nil)
        (t
         (or (first-tmpl-var (second tmpl))
             (first-tmpl-var (third tmpl))
             (and (eq (first tmpl) 'if)
                  (first-tmpl-var (fourth tmpl)))))))

(defabbrev set-bnth (i v x)
  (if v (logior x (ash 1 i)) (logand x (lognot (ash 1 i)))))

(defun add-input-set (tmpl in rslt)
  (if (atom tmpl) (cons in rslt)
    (let ((var (first-tmpl-var tmpl)))
      (add-input-set (reduce-template tmpl var t)
                     (set-bnth var t in)
                     (add-input-set (reduce-template tmpl var nil)
                                    (set-bnth var nil in)
                                    rslt)))))

(defun compute-input-set (step-term)
  (add-input-set (input-set-template step-term) 0 ()))

(defun construct-input-vec (step-term inputs state ic$)
  (declare (xargs :stobjs (state ic$)))
  (seq
   (input-set (compute-input-set step-term))
   (num-inputs (length input-set))
   (ic$ (update-num-inputs num-inputs ic$))
   (ic$ (resize-input-vec num-inputs ic$))
   (ic$ (load-input-vec input-set 0 ic$))
   (report "number of input bits: ~p0  number of inputs: ~p1 ~%"
           (length inputs) num-inputs
           (detail "inputs: ~p0 ~%" inputs
                   (mv ic$ state)))))

(defun format-counter-example1 (path n)
  (if (endp path) ()
    (cons (list :step n
                :state (first (first path))
                :input (second (first path)))
          (format-counter-example1 (rest path) (1+ n)))))

(defun format-counter-example (path)
  (format-counter-example1 (reverse path) 1))

(defconst *invariant-checker-functions-and-compile* (quote (
(defun visit-next-states (st in acc ic$)
  (declare (xargs :stobjs ic$
                  :mode :program)
           (type (signed-byte 29) in))
  (if (fzp in)
      (mv acc ic$)
    (let ((in (1-f in)))
      (declare (type (signed-byte 29) in))
      (seq
        (next-in (input-veci in ic$))
        (next-st (step-prime st next-in))
        ((seen ic$) (check-and-add-seen-state next-st ic$))
        (acc (if seen acc (cons (cons next-in next-st) acc)))
        (visit-next-states st in acc ic$)))))

(defun bfs (visiting alst next-wave path ic$)
  (declare (xargs :stobjs ic$
                  :mode :program))
  (cond
   ((endp visiting)
    (cond
     ((not (endp alst))
      (bfs (cdar alst) (cdr alst) next-wave (caar alst) ic$))
     ((endp next-wave)
      (mv :passed ic$))
     (t
      (bfs () next-wave () path ic$))))
   ((fzp (search-bound ic$))
    (mv :bound-fail ic$))
   (t
    (seq
      (pair (car visiting))
      (st (cdr pair))
      (path+ (cons pair path))
      (if (not (bnth (inv-bit ic$) st))
          (mv path+ ic$)
        (seq
          ((next ic$) (visit-next-states st (num-inputs ic$) () ic$))
          (next-wave (cons (cons path+ next) next-wave))
          (bfs (cdr visiting) alst next-wave path ic$)))))))

(defun invariant-checker (reps inputs inv-term step-term ic$ state)
  (declare (xargs :stobjs (ic$ state)
                  :mode :program))
  (if (not (legal-step step-term))
      (detail "illegal step term: ~p0 ~%" step-term
        (seq
          (ic$ (update-inv-check-result :bad-step ic$))
          (mv ic$ state)))
    (seq
      (term (rewrt-pure '(rep-prime (t0))))
      (if (not (quotep term))
          (detail "init term rewrote to: ~p0 ~%" term
            (seq
              (ic$ (update-inv-check-result :bad-init ic$))
              (mv ic$ state)))
        (seq
          (init-abs (second term))
          ((ic$ state)
           (construct-input-vec step-term inputs state ic$))
          (ic$ (clear-seen-states ic$))
          (ic$ (update-inv-bit (position-equal inv-term reps) ic$))
          (ic$ (update-search-bound (check-bound ic$) ic$))
          (ic$ (update-num-states 0 ic$))
          (ic$ (update-num-rep-bits (length reps) ic$))
          ((rslt ic$)
           (if (inv-bit ic$)
               (bfs (list (cons 0 init-abs)) () () () ic$)
             (die :model-check-inv
                  "unexpectedly did not find inv-term in list of reps"
                  (mv nil ic$))))
          (rslt (if (atom rslt) rslt
                  (seq
                    (rslt (transform-rslt-path rslt))
                    (tgt (list (inv-bit ic$)))
                    (mask (compute-example-mask rslt step-term tgt))
                    (rslt (map-counter-example reps inputs rslt mask))
                    rslt)))
          (ic$ (update-inv-check-result rslt ic$))
          (mv ic$ state))))))

(comp (quote (step-prime visit-next-states bfs invariant-checker)))
)))

(defun bogus-function-denoting-invariant-checker-side-effect (ic$)
  (declare (xargs :stobjs ic$))
  ic$)

(defun check-invariant (step-body rep-body reps inputs inv ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (mv-let (erp val state)
    (ld (append (list (list 'defun 'step-prime (list 's 'i)
                            '(declare (xargs :mode :program))
                            step-body)
                      (list 'defun 'rep-prime (list 'n)
                            '(declare (xargs :mode :logic))
                            rep-body))
                (and (disable-exec ic$)
                     (list (list 'in-theory (list 'disable (list 'rep-prime)))))
                *invariant-checker-functions-and-compile*
                (list (list 'invariant-checker
                            (list 'quote reps)
                            (list 'quote inputs)
                            (list 'quote inv)
                            (list 'quote step-body)
                            'ic$ 'state)
                      (list 'ubt! (list 'quote 'step-prime))))
        :ld-user-stobjs-modified-warning

; Matt K. mod: ACL2 now requires keyword :ld-user-stobjs-modified-warning in
; code.  If this macro is only to be evaluated at the top level, that keyword
; isn't needed.  But I'm including it, with value :same to preserve existing
; behavior, just in case someone uses it in code.  Perhaps more thought should
; be given to whether or not we want a warning here when a user stobj is
; modified.

        :same)
    (let ((ic$ (bogus-function-denoting-invariant-checker-side-effect ic$)))
      (if erp (die :check-invariant
                   "Unexpected error ~p0" val
                   (mv nil ic$ state))
        (mv (inv-check-result ic$) ic$ state)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| <SECTION>   6. top-level algorithm and interface                       |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun build-rep-body (reps)
  (if (endp reps)
      (list 'bnil)
    (list 'bcons (first reps)
          (build-rep-body (rest reps)))))

(defun snoc (e x)
  (if (endp x) (list e)
    (cons (first x) (snoc e (rest x)))))

(defun match-rep-or-input (term reps inputs)
  (let ((pos (position-equal term reps)))
    (if pos
        (mv (list 'bnth pos 's) inputs)
      (let ((pos (position-equal term inputs)))
        (if pos
            (mv (list 'bnth pos 'i) inputs)
          (mv (list 'bnth (length inputs) 'i)
              (snoc term inputs)))))))

(defun final-step-redux (term)
  (cond ((or (atom term)
             (not (eq (car term) 'if)))
         term)
        ((quotep (second term))
         (if (second (second term))
             (third term)
           (fourth term)))
        ((equal (third term) (fourth term))
         (third term))
        ((and (equal (third term) ''t)
              (equal (fourth term) ''nil))
         (second term))
        ((and (equal (third term) ''t)
              (term-order (fourth term) (second term)))
         (list 'if (fourth term) ''t (second term)))
        ((and (equal (fourth term) ''nil)
              (term-order (third term) (second term)))
         (list 'if (third term) (second term) ''nil))
        (t term)))

(defconst *step-prime-ops*
  '(bcons bnil if))

(mutual-recursion
(defun build-step-body (term reps inputs ic$)
  (declare (xargs :stobjs ic$))
  (cond ((atom term)
         (match-rep-or-input term reps inputs))
        ((eq (car term) 'quote)
         (mv (if (cadr term) ''t ''nil) inputs))
        ((member (car term) *step-prime-ops*)
         (mv-let (args inputs)
             (build-step-args (rest term) reps inputs ic$)
           (mv (final-step-redux (cons (car term) args)) inputs)))
        (t
         (match-rep-or-input term reps inputs))))

(defun build-step-args (args reps inputs ic$)
  (declare (xargs :stobjs ic$))
  (if (endp args)
      (mv () inputs)
    (mv-let (fst inputs)
        (build-step-body (first args) reps inputs ic$)
      (mv-let (rst inputs)
          (build-step-args (rest args) reps inputs ic$)
        (mv (cons fst rst) inputs)))))
)

(defun compute-reps (bound new reps hyps step-alist ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (cond
   ((endp new)
    (report "converged on reps! ~%"
            (mv t reps hyps step-alist ic$ state)))
   ((zp bound)
    (report "exceeded refine bound! ~%"
            (mv nil reps hyps step-alist ic$ state)))
   (t
    (seq
     ((new-new new-hyps step-alist new-ins ic$ state)
      (compute-rep-prime new step-alist ic$ state))
     (bound (- bound (len new)))
     (reps (union-equal new reps))
     (new (set-difference-equal new-new reps))
     (hyps (union-equal new-hyps hyps))
     (detail "new reps: ~p0 ~%" new
             (detail "new ins: ~p0 ~%" new-ins
                     (compute-reps bound new reps hyps step-alist ic$ state)))))))

(defun get-prods (term)
  (cond ((eq term t) ())
        ((and (consp term) (eq (first term) 'and))
         (rest term))
        (t (list term))))

(defun drop-nots (terms)
  (cond ((endp terms) ())
        ((and (consp (first terms))
              (eq (first (first terms)) 'not))
         (cons (second (first terms))
               (drop-nots (rest terms))))
        (t
         (cons (first terms)
               (drop-nots (rest terms))))))

(defun new-reps-in (prods)
  (cond ((endp prods) ())
        ((is-rep-term (first prods)) (list (first prods)))
        (t (new-reps-in (rest prods)))))

(defun find-new-reps (path)
  (and (consp path)
       (or (new-reps-in (drop-nots (get-prods (second (first path)))))
           (find-new-reps (rest path)))))

(defun check-abstraction (reps step-alist inv ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (detail "check-reps: ~p0 ~%" reps
          (seq
           ((step-term ic$ state)
            (compute-step-prime reps step-alist ic$ state))
           ((step-body inputs)
            (build-step-body step-term reps () ic$))
           (rep-body (build-rep-body reps))
           (ic$ (clear-ic$-for-inv-check ic$))
           ((result ic$ state)
            (detail "step-term: ~p0 ~%" step-term
                    (check-invariant step-body rep-body reps inputs inv ic$ state)))
           (detail "number of abstract states visited: ~p0~%" (num-states ic$)
                   (cond
                    ((eq result :passed)
                     (mv t () ic$ state))
                    ((eq result :bound-fail)
                     (report "exceeded bound on number of states!~%"
                             (mv nil () ic$ state)))
                    ((eq result :bad-init)
                     (report "could not rewrite (rep-prime (t0)) to constant!~%"
                             (mv nil () ic$ state)))
                    (t
                     (report "failed-inv-check!~%"
                             (detail "failed-path:~p0~%" (format-counter-example result)
                                     (mv nil (find-new-reps result) ic$ state)))))))))

(defun prove-inv-single (bound inv-term new-reps curr-reps curr-hyps curr-step ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (seq
   ((ok reps hyps step-alist ic$ state)
    (compute-reps (refine-bound ic$) new-reps curr-reps
                  curr-hyps curr-step ic$ state))
   (if (or ok (always-check ic$))
       (seq
        ((ok new-reps ic$ state)
         (check-abstraction reps step-alist inv-term ic$ state))
        (cond
         (ok                              (mv t hyps ic$ state))
         ((or (endp new-reps) (zp bound)) (mv nil hyps ic$ state))
         (t (prove-inv-single (1- bound) inv-term new-reps
                              reps hyps step-alist ic$ state))))
     (mv nil hyps ic$ state))))

(defun prove-inv-loop (to-prove proven proofs-bound ic$ state)
  (declare (xargs :stobjs (ic$ state)))
  (cond
   ((endp to-prove)
    (mv t ic$ state))
   ((member-equal (first to-prove) proven)
    (prove-inv-loop (rest to-prove) proven proofs-bound ic$ state))
   ((zp proofs-bound)
    (report "exceeded bound on number of proofs!~%"
            (mv nil ic$ state)))
   (t
    (seq
     ((ok hyps ic$ state)
      (prove-inv-single (jump-bound ic$) (first to-prove) (list (first to-prove))
                        () () () ic$ state))
     (if (not ok)
         (mv nil ic$ state)
       (prove-inv-loop (append hyps (rest to-prove))
                       (cons (first to-prove) proven)
                       (1- proofs-bound) ic$ state))))))

(defun definv-fn (inv-name
                  inv-form
                  jump-bound
                  check-bound
                  refine-bound
                  proofs-bound
                  inputs-bound
                  fast-search
                  detail-file
                  always-check
                  disable-exec
                  reduce-contexts
                  expected-result
                  ic$
                  state)
  (declare (xargs :stobjs (ic$ state)))
  (seq
   ((erp inv-term bindings state)
    (translate1 inv-form :stobjs-out '((:stobjs-out . :stobjs-out))
                t 'top-level (w state) state))
   (state
    (if (or erp

; Change by Matt K., 10/17/2013: When testing a tentative fix for a soundness
; bug, I found a guard violation below because EQ was being called instead of
; EQUAL; so I changed EQ to EQUAL.  (Implementation details: That bug involved
; doing extra guard-checking for certain :program mode functions in order to
; avoid violating stobj recognizers.  In this case definv-fn was marked as such
; a function because it depended on ld-fn, which had been marked as such a
; function because it took state.  The ultimate fix didn't give this special
; treatment for state, so the change from EQ to EQUAL below is no longer
; necessary.  But it seems that since the call of EQ was ill-guarded, it is
; still good to fix.)

            (not (equal bindings bindings)))
        (die :illegal-term
             "Error in macro-expansion: ~p0" inv-form
             state)
      state))
   ((ic$ state)
    (initialize-ic$ jump-bound
                    check-bound
                    refine-bound
                    inputs-bound
                    fast-search
                    detail-file
                    always-check
                    disable-exec
                    reduce-contexts
                    ic$
                    state))
   (state
    (detail "**************** begin ~s0 **************** ~%" detail-file
            state))
   ((ok ic$ state)
    (prove-inv-loop (list inv-term) () proofs-bound ic$ state))
   (result (if ok :qed :failed))
   (state
    (report "~x0~%" (list result inv-name result)
            (detail "**************** end ~s0 **************** ~%~%" detail-file
                    state)))
   ((ic$ state)
    (cleanup-ic$ ic$ state))
   (state
    (if (implies expected-result (equal result expected-result))
        state
      (die :unexpected-result-for-inv-proof
           "encountered unexpected result for invariant proof~%"
           state)))
   (mv state ic$)))

(defmacro definv (inv-name
                  inv-term
                  &key
                  (file '"invp.rpt")
                  (jump-bound '1)
                  (check-bound '4000)
                  (refine-bound '8)
                  (proofs-bound '10)
                  (inputs-bound '1000)
                  (fast-search 'nil)
                  (disable-exec 't)
                  (always-check 'nil)
                  (reduce-contexts 'nil)
                  (expected-result 'nil))
  (declare (xargs :guard (and (symbolp inv-name)
                              (integerp check-bound)
                              (>= check-bound 0)
                              (integerp inputs-bound)
                              (>= inputs-bound 0)
                              (integerp refine-bound)
                              (>= refine-bound 0)
                              (integerp proofs-bound)
                              (>= proofs-bound 0)
                              (or (stringp file) (not file))
                              (booleanp fast-search)
                              (booleanp always-check)
                              (booleanp disable-exec)
                              (booleanp reduce-contexts)
                              (member-eq expected-result '(:qed :failed nil)))))
  `(definv-fn
     (quote ,inv-name)
     (quote ,inv-term)
     (quote ,jump-bound)
     (quote ,check-bound)
     (quote ,refine-bound)
     (quote ,proofs-bound)
     (quote ,inputs-bound)
     (quote ,fast-search)
     (quote ,file)
     (quote ,always-check)
     (quote ,disable-exec)
     (quote ,reduce-contexts)
     (quote ,expected-result)
     ic$
     state))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#| <SECTION>   7. various test examples                                   |#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; compile the invariant prover:
(comp t)

(set-ignore-ok t)
(set-irrelevant-formals-ok t)
(set-match-free-error nil)

(logic)

;; Simple Example: A simple pair of integers
;; -----------------------------------------

(progn
(defun next (s i)
  (cons (if (car i) (if (cdr s) 1 (ifix (cdr i))) (cdr s))
        (if (cdr i) (ifix (car i)) (cdr s))))

(defun init ()
  (cons 1 2))

(in-theory (disable natp))

;; environment input function
(encapsulate (((i *) => *)) (local (defun i (n) n)))

(defun x (n)
  (declare (xargs :measure (tmsr n)))
  (if (tzp n) (init) (next (x (t- n)) (i n))))

(in-theory (disable (x)))

(if-lift-rules
 (integerp x)
 (natp x)
 (equal x y)
 (car x)
 (cdr x))

(defthm x-of-t+
  (implies (not (tzp n))
           (equal (x n) (next (x (t- n)) (i n))))
  :hints (("Goal" :in-theory (disable next))))

(defthm x-of-t0
  (equal (x (t0)) (init)))
)

(definv simple-pass-inv
  (integerp (car (x n)))
  :file "simp1.rpt"
  :expected-result :qed)

(definv simple-fail-inv
  (natp (car (x n)))
  :file "simp2.rpt"
  :expected-result :failed)

(u)

;; Another Simple Example: A mutual exclusion model
;; -------------------------------------------------

(include-book "crit")

(definv crit-inv
  (ok n)
  :file "crit.rpt"
  :expected-result :qed)

(u)

;; A slightly more complex example: A MESI cache model
;; -------------------------------------------------

(include-book "mesi")

(definv mesi-inv
  (ok n)
  :file "mesi.rpt"
  :expected-result :qed)

(u)

;; go ahead and write to success.txt in order to signal that we have succeeded
;; in proving all of the example invariants:

(defun mark-successful-run (state)
  (declare (xargs :stobjs state
                  :mode :program))
  (mv-let (channel state)
    (open-output-channel "success.txt" :character state)
    (let ((state (fms "invariant prover successfully completed proofs!!" () channel state nil)))
      (let ((state (close-output-channel channel state)))
        state))))

(mark-successful-run state)
