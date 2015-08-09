(in-package "ACL2")

(include-book "kas" :ttags :all)

#| Section 1. -- BDD rules |#

;; these rules are defined before the other if-rewriting rules since they
;; should be applied after if's are lifted and have settled.

;; bv is used in the BDD reordering to denote boolean variables.
(defun bv (x) (if x t nil))
(in-theory (disable bv))

(defun bpos (x) (if x x t))

(defthm bpos-of-bv
  (equal (bpos (bv x)) t))

(defthm bdd-if-lift-test
  (equal (fak (if (if x y z) m n))
         (if x (if y m n) (if z m n))))

(defthm bdd-reorder-then
  (implies (sieve (:bddordp a x))
	   (equal (fak (if x (if a b c) y))
		  (if a (if x b y) (if x c y)))))

(defthm bdd-reorder-then2
  (implies (sieve (:bddordp a x))
	   (equal (fak (if x a y))
		  (if a (if x (bpos a) y) (if x nil y)))))

(defthm bdd-reorder-else
  (implies (and (sieve (:bddordp a x))
		(sieve (:bddordp a y)))
	   (equal (fak (if x y (if a b c)))
		  (if a (if x y b) (if x y c)))))

(defthm bdd-reorder-else2
  (implies (and (sieve (:bddordp a x))
		(sieve (:bddordp a y)))
	   (equal (fak (if x y a))
		  (if a (if x y (bpos a)) (if x y nil)))))

(in-theory (disable bpos))

(defthm bdd-reduce-then
  (equal (fak (if x (if x b c) y))
         (if x b y)))

(defthm bdd-reduce-else
  (equal (fak (if x y (if x b c)))
         (if x y c)))

(defthm bdd-reduce-then2
  (equal (fak (if (bv x) (bv x) y))
         (if (bv x) t y)))

(defthm bdd-reduce-else2
  (equal (fak (if x y x))
         (if x y nil)))

(defthm bv-equal-t-reduce
  (equal (equal (bv x) t) (bv x)))

(defthm bv-equal-nil-reduce
  (equal (equal (bv x) nil) (if (bv x) nil t)))

(defthm bv-if-t-nil-reduce
  (equal (fak (if (bv x) t nil)) (bv x)))

(defmacro bvlst (&rest r)
  (if (endp r) () `(cons (bv ,(first r)) (bvlst ,@(rest r)))))

(defmacro bdd-on ()
  '(in-theory (enable bdd-if-lift-test
		      bdd-reorder-then
		      bdd-reorder-else
		      bdd-reorder-then2
		      bdd-reorder-else2
		      bdd-reduce-then
		      bdd-reduce-else
		      bdd-reduce-then2
		      bdd-reduce-else2)))

(defmacro bdd-off ()
  '(in-theory (disable bdd-if-lift-test
		       bdd-reorder-then
		       bdd-reorder-else
		       bdd-reorder-then2
		       bdd-reorder-else2
		       bdd-reduce-then
		       bdd-reduce-else
		       bdd-reduce-then2
		       bdd-reduce-else2)))

(bdd-off)


#| Section 2. -- if lifting rules |#

(program)

(defun replace-var (lhs var term)
  (cond ((endp lhs) ())
        ((eq (first lhs) var)
         (cons term (rest lhs)))
        (t
         (cons (first lhs)
               (replace-var (rest lhs) var term)))))

(defun if-lift-thms (args op lhs)
  (if (endp args) ()
    (cons `(defthm ,(symbol-append op '-if-lift- (first args))
             (equal ,(cons op (replace-var lhs (first args) '(if t1 t2 t3)))
                    (if t1 ,(cons op (replace-var lhs (first args) 't2))
                      ,(cons op (replace-var lhs (first args) 't3)))))
          (if-lift-thms (rest args) op lhs))))

(defun gen-if-lifts (terms)
  (if (endp terms) ()
    (append (if-lift-thms (cdar terms) (caar terms) (cdar terms))
            (gen-if-lifts (cdr terms)))))

(defun if-lift-thm-args (args op)
  (if (endp args) ()
    (cons (symbol-append op '-if-lift- (first args))
          (if-lift-thm-args (rest args) op))))

(defun if-lift-thm-names (terms)
  (if (endp terms) ()
    (append (if-lift-thm-args (cdar terms) (caar terms))
            (if-lift-thm-names (cdr terms)))))

(logic)

(defconst *single-const-vars*
  '(a b c d e f g h i j k l m n o p q r s t u v w x y z))

(defun rule-macro-termsp (x)
  (or (null x)
      (and (consp x)
           (symbol-listp (first x))
           (consp (first x))
           (not (set-difference-eq (rest (first x)) *single-const-vars*))
           (rule-macro-termsp (rest x)))))

(defmacro if-lifts (name &rest terms)
  (declare (xargs :guard (and (symbolp name)
                              (rule-macro-termsp terms))))
  (list* 'encapsulate ()
         `(defmacro ,(symbol-append name '-on) ()
            (quote (in-theory (enable ,@(if-lift-thm-names terms)))))
         `(defmacro ,(symbol-append name '-off) ()
            (quote (in-theory (disable ,@(if-lift-thm-names terms)))))
         (gen-if-lifts terms)))

(if-lifts base-if-lifts
          (car x)
          (cdr x)
          (cons x y)
          (consp x)
          (integerp x)
          (equal x y)
          (< x y)
          (bv x)
          (binary-append x y)
          (binary-+ x y)
          (unary-- x)
          (binary-* x y)
          (unary-/ x))

(defthm if-if-lift
  (equal (fak (if (if x y z) a b))
         (if x (if y a b) (if z a b))))

(defthm if-same-then-else
  (equal (fak (if x y y)) y))

;; we disable if-lifting by default
(in-theory (disable if-if-lift))
(base-if-lifts-off)

(defun prv (x) x)
(defun prv2 (x) x)
(defun prv3 (x) x)

(defthm prv-evaporates
  (equal (prv x) x))

(defthm prv-force-case-split
  (implies (sieve (:case-split y))
	   (equal (prv x) (prv2 (if y (prv3 x) (hide x)))))
  :hints (("Goal" :expand (hide x))))

(defthm prv2-then-fail-drop
  (equal (prv2 (if x y z))
         (if x y z)))

(defthm prv2-then-pass-shift
  (equal (prv2 (if x t (hide z)))
         (if x t (prv z)))
  :hints (("Goal" :expand (hide z))))

(defthm prv2-if-gen-prv
  (equal (prv2 (if x (prv3 y) z))
         (prv2 (if x (prv y) z))))

(defthm prv3-drop-if-t
  (equal (prv3 t) t))

(in-theory (disable prv prv2 prv3))


#| Section 3. -- simple typing rules |#

(program)

(defun gen-type-rule (term typ)
  `(defthm ,(symbol-append (first term) '- typ)
     ,(case typ
            (boolean (list 'booleanp term))
            (non-nil term))
     :rule-classes :type-prescription))

(defun gen-type-rules (terms typ)
  (if (endp terms) ()
    (cons (gen-type-rule (first terms) typ)
          (gen-type-rules (rest terms) typ))))

(logic)

(defmacro booleans (&rest terms)
  (declare (xargs :guard (rule-macro-termsp terms)))
  (list* 'encapsulate () (gen-type-rules terms 'boolean)))

(defmacro non-nils (&rest terms)
  (declare (xargs :guard (rule-macro-termsp terms)))
  (list* 'encapsulate () (gen-type-rules terms 'non-nil)))

(booleans (consp x)
          (integerp x)
          (symbolp x)
          (stringp x)
          (characterp x)
          (acl2-numberp x)
          (rationalp x)
          (booleanp x)
          (not x)
          (iff x y)
          (implies x y)
          (equal x y)
          (< x y))

(non-nils (+ x y)
          (* x y)
          (- x)
          (/ x)
          (cons x y)
          (acons a x y)
          (ifix x)
          (fix x)
          (nfix x)
          (len x)
          (acl2-count x)
          (char-code x)
          (code-char x))




#| Section 4. -- several basic "type" facts which s! does not know |#

(defthm consp-of-cons    (equal (consp (cons x y)) t))
(defthm integerp-of-cons (equal (integerp (cons x y)) nil))
(defthm symbolp-of-cons  (equal (symbolp (cons x y)) nil))

(defthm car-of-cons (equal (car (cons x y)) x))
(defthm cdr-of-cons (equal (cdr (cons x y)) y))

(defthm acl2-numberp-of-fix (equal (acl2-numberp (fix x)) t))
(defthm integerp-of-ifix (equal (integerp (ifix x)) t))
(defthm integerp-of-nfix (equal (integerp (nfix x)) t))
(defthm integerp-of-len (equal (integerp (len x)) t))
(defthm integerp-of-acl2-count (equal (integerp (acl2-count x)) t))

(defthm >=0-of-nfix (equal (< (nfix x) 0) nil))
(defthm >=0-of-len  (equal (< (len x) 0) nil))
(defthm >=0-of-acl2-count (equal (< (acl2-count x) 0) nil))


#| Section 5. -- some rules for reducing car/cons/cdr/equal |#

(defthm equal-cons-redux-1
  (equal (equal (cons x y) a)
         (and (consp a)
              (equal (car a) x)
              (equal (cdr a) y))))

(defthm equal-cons-redux-2
  (equal (equal a (cons x y))
         (and (consp a)
              (equal (car a) x)
              (equal (cdr a) y))))


#| Section 6. -- conditional rewrite rule hypothesis operators |#

(defun c-a (x y) (if x y nil))
(defun c-h (x y) (c-a x y))

(defthm c-a-t-1
  (equal (c-a t (hide t)) t)
  :hints (("Goal" :expand (hide t))))

(defthm c-a-t-2
  (equal (c-a t (hide (c-h x y)))
         (c-a x (hide y)))
  :hints (("Goal" :expand (hide (c-h x y)))
          ("Goal'" :expand (hide y))))

(defthm c-a-nil
  (equal (c-a nil x) nil))

(in-theory (disable c-a c-h))


#| Section 7. -- macros which change some parameters of the simplifier |#

(defmacro set-rule-trace (d)
  `(progn (redef!) (defun initial-rule-trace-descriptor () ,d) (logic)))

(defmacro set-prune-depth (d)
  `(progn (redef!) (defun kern-initial-node-prune-depth () ,d) (logic)))


#| Section 9. -- theorems about gfl and rfl |#

(defun gfl (x) x)
(defun rfl (x y) (declare (ignore x)) y)

(defun report-cw-false (args obj wrld)
  (declare (ignore obj wrld))
  (prog2$ (and (not (equal (first args) (list 'quote nil)))
	       (cw "~x0~%" (list 'not (first args))))
	  t))

(defun report-cw-true (args obj wrld)
  (declare (ignore obj wrld))
  (prog2$ (and (not (equal (first args) (list 'quote t)))
	       (cw "~x0~%" (first args)))
	  t))

(defun report-fail-start (args obj wrld)
  (declare (ignore args obj wrld))
  (prog2$ (cw "~%~%*******BEGINNING OF FAILING CASE REPORT*******~%~%") t))

(defun report-fail-end (args obj wrld)
  (declare (ignore args obj wrld))
  (prog2$ (cw "~%**********END OF FAILING CASE REPORT**********~%~%") t))

(defthm rfl-leaf-case
  (implies (and (sieve (:funcall 'report-cw-false leaf))
		(sieve (:funcall 'report-fail-end)))
           (equal (rfl leaf x) x)))

;; NOTE, if the non-nil rfl theorem below fails, then the following theorem
;; should fire instead:

(defthm rfl-if-tbr-case
  (implies (sieve (:funcall 'report-cw-true tst))
           (equal (rfl (if tst tbr fbr) x)
                  (rfl tbr x))))

(defthm rfl-if-fbr-case
  (implies (and (sieve (:non-nilp tbr))
                (sieve (:funcall 'report-cw-false tst)))
           (equal (rfl (if tst tbr fbr) x)
                  (rfl fbr x))))

(defthm gfl-creates-rfl
  (implies (sieve (:funcall 'report-fail-start))
	   (equal (gfl x) (fail (rfl x x)))))

(defthm gfl-reduce-t (equal (gfl t) t))

(in-theory (disable gfl rfl fail (fail) (gfl) (rfl)))


#| Section 10. -- macro expanding RHS lambdas into functions |#

(defun pseudo-term-uniq-bindp (x)
  (or (null x)
      (and (consp x)
           (symbolp (first (first x)))
           (pseudo-termp (second (first x)))
           (pseudo-term-uniq-bindp (rest x))
           (not (assoc-eq (first (first x)) (rest x))))))

(defun parse-letthm (form)
  (if (and (consp form)
           (eq (first form) 'equal)
           (consp (third form))
           (eq (first (third form)) 'let*)
           (pseudo-term-uniq-bindp (second (third form)))
           (eq (first (car (last (second (third form)))))
               (third (third form))))
      (mv (second form) (second (third form)))
    (mv (er hard 'defletthm "unsupported form: ~x0" form) nil)))

(defun binds-vars1 (binds bound rslt)
  (if (endp binds) rslt
    (binds-vars1 (rest binds)
                 (cons (first (first binds)) bound)
                 (union-eq (set-difference-eq (all-vars (second (first binds)))
                                              bound)
                           rslt))))

(defun binds-vars (binds)
  (binds-vars1 binds () ()))

(program)

(defun binds-fns (binds name)
  (cond
   ((endp binds) ())
   ((endp (rest binds))
    (let* ((tvar (first (first binds)))
           (texpr (second (first binds)))
           (params (all-vars texpr))
           (tname (symbol-append name '- tvar)))
      (list `(defun ,tname ,params
               (declare (xargs :verify-guards nil))
               ,texpr))))
   (t
    (let* ((tvar (first (first binds)))
           (texpr (second (first binds)))
           (tname (symbol-append name '- tvar))
           (nvar (first (second binds)))
           (nname (symbol-append name '- nvar))
           (params (binds-vars binds))
           (args (binds-vars (rest binds)))
           (args (replace-var args tvar texpr)))
      (append (binds-fns (rest binds) name)
              (list `(defun ,tname ,params
                       (declare (xargs :verify-guards nil))
                       (,nname ,@args))))))))

(defun letthm-fns (name form)
  (mv-let (lhs binds) (parse-letthm form)
    (declare (ignore lhs))
    (binds-fns binds name)))

(defun letthm-body (name form)
  (mv-let (lhs binds) (parse-letthm form)
    (let* ((tvar (first (first binds)))
           (fn (symbol-append name '- tvar))
           (args (binds-vars binds)))
      `(equal ,lhs (,fn ,@args)))))

(logic)

(defmacro defletthm (name form &rest aux)
  `(encapsulate
    ()
    ,@(letthm-fns name form)
    (defthm ,name ,(letthm-body name form) ,@aux)))

#|

(defun foo (x y) (* (+ x y) (+ x y)))

(defletthm foogo
  (equal (foo x y)
         (let* ((a (+ x y))
                (r (* a a)))
           r)))

|#

#| Section 11. -- Orienting commutative and symmetric functions |#

(defthm equal-orient-rule
  (implies (sieve (:termordp x y))
	   (equal (fak (equal x y)) (equal y x))))


#| Section 12. -- Some wrapper macros for theorems proven using BDDs and case splitting |#

(defmacro defthmk-bdd  (name form &rest aux) `(progn (bdd-on) (defthmk-generic ,name ,form ,@aux) (bdd-off)))
(defmacro defthmk      (name form &rest aux) `(defthmk-generic ,name (gfl (prv ,form)) ,@aux))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; We now include records definitions (although not really part of kbasis.lisp) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; total-order.lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun << (x y)
  (declare (xargs :guard t))
  (and (lexorder x y)
       (not (equal x y))))

(defthm <<-irreflexive
  (not (<< x x)))

(defthm <<-transitive
  (implies (and (<< x y)
                (<< y z))
           (<< x z)))

(defthm <<-asymmetric
  (implies (<< x y)
           (not (<< y x))))

(defthm <<-trichotomy
  (implies (and (not (<< y x))
                (not (equal x y)))
           (<< x y)))

(defthm <<-implies-lexorder
  (implies (<< x y)
	   (lexorder x y)))

(in-theory (disable <<))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; records.lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rcdp (x)
  (or (null x)
      (and (consp x)
           (consp (car x))
           (rcdp (cdr x))
           (cdar x)
           (or (null (cdr x))
               (<< (caar x) (caadr x))))))

(defun ifrp (x) ;; ill-formed rcdp
  (or (not (rcdp x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (null (caar x))
           (ifrp (cdar x)))))

(defun acl2->rcd (x)
  (if (ifrp x) (list (cons nil x)) x))

(defun rcd->acl2 (x)
  (if (ifrp x) (cdar x) x))

(defun g-aux (a x)
  (cond ((or (endp x)
             (<< a (caar x)))
         nil)
        ((equal a (caar x))
         (cdar x))
        (t
         (g-aux a (cdr x)))))

(defun g (a x)
  (g-aux a (acl2->rcd x)))

(defun s-aux (a v r)
  (cond ((or (endp r)
             (<< a (caar r)))
         (if v (cons (cons a v) r) r))
        ((equal a (caar r))
         (if v (cons (cons a v) (cdr r)) (cdr r)))
        (t
         (cons (car r) (s-aux a v (cdr r))))))

(defun s (a v x)
  (rcd->acl2 (s-aux a v (acl2->rcd x))))


;;;; basic property of records ;;;;

(local
(defthm rcdp-implies-true-listp
  (implies (rcdp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; initial properties of s-aux and g-aux ;;;;

(local
(defthm s-aux-is-bounded
  (implies (and (rcdp r)
                (s-aux a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (s-aux a v r))))))

(local
(defthm s-aux-preserves-rcdp
  (implies (rcdp r)
           (rcdp (s-aux a v r)))))

(local
(defthm g-aux-same-s-aux
  (implies (rcdp r)
           (equal (g-aux a (s-aux a v r))
                  v))))

(local
(defthm g-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (g-aux a (s-aux b v r))
                  (g-aux a r)))))

(local
(defthm s-aux-same-g-aux
  (implies (rcdp r)
           (equal (s-aux a (g-aux a r) r)
                  r))))

(local
(defthm s-aux-same-s-aux
  (implies (rcdp r)
           (equal (s-aux a y (s-aux a x r))
                  (s-aux a y r)))))

(local
(defthm s-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (s-aux b y (s-aux a x r))
                  (s-aux a x (s-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s))))))

(local
(defthm s-aux-non-nil-cannot-be-nil
  (implies (and v (rcdp r))
           (s-aux a v r))))

(local
(defthm g-aux-is-nil-for-<<
  (implies (and (rcdp r)
                (<< a (caar r)))
           (equal (g-aux a r) nil))))


;;;; properties of acl2->rcd and rcd->acl2 ;;;;

(local
(defthm acl2->rcd-rcd->acl2-of-rcdp
  (implies (rcdp x)
           (equal (acl2->rcd (rcd->acl2 x))
                  x))))

(local
(defthm acl2->rcd-returns-rcdp
  (rcdp (acl2->rcd x))))

(local
(defthm acl2->rcd-preserves-equality
  (iff (equal (acl2->rcd x) (acl2->rcd y))
       (equal x y))))

(local
(defthm rcd->acl2-acl2->rcd-inverse
  (equal (rcd->acl2 (acl2->rcd x)) x)))

(local
(defthm rcd->acl2-of-record-non-nil
  (implies (and r (rcdp r))
           (rcd->acl2 r))))

(in-theory (disable acl2->rcd rcd->acl2))


;;;; final properties of record g(et) and s(et) ;;;;


(defthm g-over-if
  (equal (g k (if a r1 r2))
	 (if a
	     (g k r1)
	   (g k r2))))

(defthm s-over-if
  (equal (s k (if a v1 v2) r)
	 (if a
	     (s k v1 r)
	   (s k v2 r))))

(in-theory (disable g-over-if s-over-if))

(defthm g-same-s-
  (implies (equal r1 (s a v r))
	   (equal (g a r1)
		  v)))

(defthm g-diff-s-
  (implies (and (equal r1 (s b v r))
		(not (equal a b)))
           (equal (g a r1)
                  (g a r))))

(in-theory (disable g-same-s- g-diff-s-))

;;;; NOTE: I often use the following instead of the above rules
;;;; to force ACL2 to do a case-split. In some cases, I will
;;;; disable this rule ACL2 is sluggish or if the number of cases
;;;; is unreasonable

(defthm g-of-s-redux
  (equal (g a (s b v r))
         (if (equal a b) v (g a r))))

(in-theory (disable g-of-s-redux))

(defthm g-same-s
  (equal (g a (s a v r))
	 v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

(defthm s-same-g
  (equal (s a (g a r) r)
	 r))

(defthm s-same-s
  (equal (s a y (s a x r))
	 (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

(defthm g-of-nil-is-nil
  (not (g a nil)))

(defthm s-non-nil-cannot-be-nil
  (implies v (s a v r))
  :hints (("Goal"
           :in-theory (disable rcd->acl2-of-record-non-nil)
           :use (:instance rcd->acl2-of-record-non-nil
                           (r (s-aux a v (acl2->rcd r)))))))

(defthm non-nil-if-g-non-nil
  (implies (g a r) r)
  :rule-classes :forward-chaining)


;; We disable s and g, assuming the rules proven in this book are sufficient to
;; manipulate record terms which are encountered

(in-theory (disable s g))

(defmacro <- (x a) `(g ,a ,x))

(defmacro -> (x a v) `(s ,a ,v ,x))

(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simple BDD example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun bits-equiv (x y)
  (if (endp x) (endp y)
    (and (consp y) (iff (car x) (car y))
         (bits-equiv (cdr x) (cdr y)))))

(defthm bits-equiv-nil-reduce
  (equal (bits-equiv () ()) t))

(defthm bits-equiv-cons-reduce
  (equal (bits-equiv (cons a x) (cons b y))
         (and (iff a b) (bits-equiv x y))))

(defthmk-bdd bits-equiv-symmetric-2
  (let ((x (list (bv x1) (bv x0)))
        (y (list (bv y1) (bv y0))))
     (equal (bits-equiv x y) (bits-equiv y x))))

(defthmk-bdd bits-equiv-symmetric-5
  (let ((x (list (bv x4) (bv x3) (bv x2) (bv x1) (bv x0)))
        (y (list (bv y4) (bv y3) (bv y2) (bv y1) (bv y0))))
     (equal (bits-equiv x y) (bits-equiv y x))))

(in-theory (disable if-if-lift))
(base-if-lifts-off)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Case splitting pipeline example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstub src1 (*) => *)
(defstub src2 (*) => *)
(defstub op (*) => *)
(defstub dest(*) => *)
(defstub alu (* * *) => *)
(defstub GetRegWrite(*) => *)
(defstub GetMemToReg(*) => *)
(defstub GetuseImm(*) => *)
(defstub GetImm(*) => *)
(defstub GetMemWrite(*) => *)

(defun bor-macro (lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst) nil (list 'bif (car lst) t (bor-macro (cdr lst)))))

(defmacro bor (&rest args)
  (declare (xargs :guard (true-listp args)))
  (bor-macro args))

(defun band-macro (lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst) t (list 'bif (car lst) (band-macro (cdr lst)) nil)))

(defmacro band (&rest args)
  (declare (xargs :guard (true-listp args)))
  (band-macro args))

(defconst *ma-fields*
  '(pPC pRF pDMem pIMem
    deOP deARG1 deARG2 deDEST deWRT deSRC1 deSRC2
    deRegWrite deImm deuseImm deMemToReg deMemWrite dePC
    fdWRT fdINST fdPC
    emDEST emWRT emRegWrite emMemWrite emResult emMemToReg emARG2 emPC
    mwVAL mwDEST mwWRT mwRegWrite mwPC mwDMem))

(defconst *isa-fields*
  '(sPC sRF sDMem sIMem))

(defun get-fields (st)
  (case st
        (ma *ma-fields*)
        (isa *isa-fields*)))

;; We now define accessor/updater creation macros. The updater macro
;; will also introduce nth-update-nth style outside-in rewrite rules
;; for the update functions.

(program)

(defun create-accessor (fld st)
  `(defun ,fld (,st) (g (quote ,fld) ,st)))

(defun create-accessors (flds st)
  (if (endp flds) ()
    (cons (create-accessor (first flds) st)
          (create-accessors (rest flds) st))))

(defun make-st-fields (flds)
  (if (endp flds) ()
    (let ((fld (first flds)))
      `(s (quote ,fld) ,fld
          ,(make-st-fields (rest flds))))))

(defun create-make-st (flds st)
  `(defun ,(symbol-append 'make- st) ,flds
     (s 'type (quote ,st) ,(make-st-fields flds))))

(defun update-fields (flds st)
  (if (endp flds) ()
    (let ((fld (first flds)))
      (cons `(,(symbol-append fld '+) ,st)
	    (update-fields (rest flds) st)))))

(defun create-updater (flds st)
  `(defun ,st (,st)
     (,(symbol-append 'make- st) ,@(update-fields flds st))))

(defun next-fns (flds)
  (if (endp flds) ()
    (cons (symbol-append (first flds) '+)
          (next-fns (rest flds)))))

(defun acc-upd-rule (fld st)
  `(defthm ,(symbol-append fld '-of- st '-step)
     (equal (,fld (,st ,st))
            (,(symbol-append fld '+) ,st))))

(defun acc-upd-rules (flds st)
  (if (endp flds) ()
    (cons (acc-upd-rule (first flds) st)
          (acc-upd-rules (rest flds) st))))

(defun acc-s-rule (fld)
  `(defthm ,(symbol-append fld '-of-s-rdx)
     (equal (,fld (s a v r))
	    (g (quote ,fld) (s a v r)))))

(defun acc-s-rules (flds)
  (if (endp flds) ()
    (cons (acc-s-rule (first flds))
	  (acc-s-rules (rest flds)))))

(logic)

(defmacro defaccessors (st)
  (declare (xargs :guard (symbolp st)))
  (let ((flds (get-fields st)))
    (list* 'progn
           (create-make-st flds st)
           (create-accessors flds st))))

(defmacro defupdater (st)
  (declare (xargs :guard (symbolp st)))
  (let ((flds (get-fields st)))
    (list* 'progn
           (create-updater flds st)
           `(in-theory (disable ,@(next-fns flds)))
           (append (acc-upd-rules flds st)
;		   (acc-s-rules flds)
                   `((in-theory (enable ,@(next-fns flds)))
		     (in-theory (disable ,@flds))
                     (in-theory (disable ,st)))))))

(defun incr (x) x)
(defun decr (x) x)

(defthm decr-incr-redux (equal (decr (incr x)) x))
(defthm incr-decr-redux (equal (incr (decr x)) x))

(in-theory (disable incr decr))

(defun b (x) (if x t nil))

(defthm b-equal-redx (equal (b (equal x y)) (equal x y)))
(defthm b-of-b-redx  (equal (b (b x)) (b x)))
(defthm b-of-if-lift (equal (b (if x y z)) (if x (b y) (b z))))

(in-theory (disable b))

(defmacro bif (x y z) `(if (b ,x) ,y ,z))

;; pipeline implementation

(defaccessors ma)

; "wire" functions

(defun inst             (ma) (g (pPC ma) (pIMem ma)))
(defun prev-inst        (ma) (g (decr (pPC ma)) (pIMem ma)))
(defun IF_ID_Src1       (ma) (src1 (fdINST ma)))
(defun IF_ID_Src2       (ma) (src2 (fdINST ma)))
(defun ID_RegWrite      (ma) (GetRegWrite (fdINST ma)))
(defun ID_MemWrite      (ma) (GetMemWrite (fdINST ma)))
(defun EX_WB_Equal_Src1 (ma) (band (mwWRT ma) (mwRegWrite ma) (equal (deSRC1 ma) (mwDEST ma))))
(defun EX_WB_Equal_Src2 (ma) (band (mwWRT ma) (mwRegWrite ma) (equal (deSRC2 ma) (mwDEST ma))))
(defun EX_WB_Fwd_Src1   (ma) (bif (EX_WB_Equal_Src1 ma) (mwVAL ma) (deARG1 ma)))
(defun EX_WB_Fwd_Src2   (ma) (bif (EX_WB_Equal_Src2 ma) (mwVAL ma) (deARG2 ma)))
(defun EX_Data2         (ma) (bif (deuseImm ma)         (deImm ma) (EX_WB_Fwd_Src2 ma)))
(defun Result           (ma) (alu (deOP ma) (EX_WB_Fwd_Src1 ma) (EX_Data2 ma)))
(defun ReadData         (ma) (g (emResult ma) (pDMem ma)))
(defun stall            (ma) (band (deRegWrite ma) (deWRT ma) (fdWRT ma)
				   (bor (equal (IF_ID_Src1 ma) (deDEST ma))
					(equal (IF_ID_Src2 ma) (deDEST ma)))))


; "next-state" functions

(defun pPC+   (ma) (bif (stall ma) (pPC ma) (incr (pPC ma))))
(defun pRF+   (ma) (bif (band (mwWRT ma) (mwRegWrite ma))
			(s (mwDEST ma) (mwVAL ma) (pRF ma))
		      (pRF ma)))
(defun pDMem+ (ma) (bif (band (emWRT ma) (emMemWrite ma))
			(s (emResult ma) (emARG2 ma) (pDMem ma))
		      (pDMem ma)))
(defun pIMem+ (ma) (pIMem ma))

(defun fdWRT+      (ma) (bif (stall ma) (b (fdWRT ma))  t))
(defun fdINST+     (ma) (bif (stall ma) (prev-inst ma)  (inst ma)))
(defun fdPC+       (ma) (bif (stall ma) (decr (pPC ma)) (pPC ma)))

(defun deSRC1+     (ma) (IF_ID_Src1 ma))
(defun deSRC2+     (ma) (IF_ID_Src2 ma))
(defun deARG1+     (ma) (g (IF_ID_Src1 ma) (pRF+ ma)))
(defun deARG2+     (ma) (g (IF_ID_Src2 ma) (pRF+ ma)))
(defun deDEST+     (ma) (dest (fdINST ma)))
(defun deOP+       (ma) (op (fdINST ma)))
(defun deImm+      (ma) (GetImm (fdINST ma)))
(defun deuseImm+   (ma) (GetuseImm (fdINST ma)))
(defun deRegWrite+ (ma) (ID_RegWrite ma))
(defun deMemWrite+ (ma) (ID_MemWrite ma))
(defun deMemtoReg+ (ma) (GetMemtoReg (fdINST ma)))
(defun deWRT+      (ma) (bif (stall ma) nil (b (fdWRT ma))))
(defun dePC+       (ma) (fdPC ma))

(defun emARG2+     (ma) (EX_WB_Fwd_Src2 ma))
(defun emResult+   (ma) (Result ma))
(defun emDEST+     (ma) (deDEST ma))
(defun emWRT+      (ma) (b (deWRT ma)))
(defun emRegWrite+ (ma) (deRegWrite ma))
(defun emMemWrite+ (ma) (deMemWrite ma))
(defun emMemToReg+ (ma) (deMemToReg ma))
(defun emPC+       (ma) (dePC ma))

(defun mwVAL+      (ma) (bif (emMemToReg ma) (ReadData ma) (emResult ma)))
(defun mwDEST+     (ma) (emDEST ma))
(defun mwWRT+      (ma) (b (emWRT ma)))
(defun mwRegWrite+ (ma) (emRegWrite ma))
(defun mwPC+       (ma) (emPC ma))
(defun mwDMem+     (ma) (pDMem ma))

(defupdater ma)

;; isa specification

(defaccessors isa)

; "wire" functions

(defun i-inst     (isa) (g (sPC isa) (sIMem isa)))
(defun RegWrite   (isa) (GetRegWrite (i-inst isa)))
(defun MemToReg   (isa) (GetMemToReg (i-inst isa)))
(defun MemWrite   (isa) (GetmemWrite (i-inst isa)))
(defun useImm     (isa) (GetuseImm (i-inst isa)))
(defun Imm        (isa) (GetImm (i-inst isa)))
(defun arg1       (isa) (g (src1 (i-inst isa)) (sRF isa)))
(defun arg2_temp  (isa) (g (src2 (i-inst isa)) (sRF isa)))
(defun arg2       (isa) (bif (useImm isa) (Imm isa) (arg2_temp isa)))
(defun i-Result   (isa) (alu (op (i-inst isa)) (arg1 isa) (arg2 isa)))
(defun i-ReadData (isa) (g (i-Result isa) (sDMem isa)))
(defun i-val      (isa) (bif (MemToReg isa) (i-ReadData isa) (i-Result isa)))

; "next-state" functions

(defun sIMem+ (isa) (sIMem isa))
(defun sPC+   (isa) (incr (sPC isa)))
(defun sRF+   (isa) (bif (RegWrite isa) (s (dest (i-inst isa)) (i-val isa) (sRF isa))  (sRF isa)))
(defun sDMem+ (isa) (bif (MemWrite isa) (s (i-Result isa) (arg2_temp isa) (sDMem isa)) (sDMem isa)))

(defupdater isa)


;; relating pipeline to isa:

(defun flush  (m) (s 'dewrt nil (s 'emwrt nil (s 'fdwrt nil (s 'mwwrt nil m)))))

(program)

(defun make-flush-thm (fld flshd)
  `(defthm ,(symbol-append fld '-of-flush)
     (equal (,fld (flush m)) ,(if (member fld flshd) 'nil `(,fld m)))))

(defun make-flushes-thms (lst flshd)
  (if (endp lst) ()
    (cons (make-flush-thm (first lst) flshd)
	  (make-flushes-thms (rest lst) flshd))))

(logic)

(defmacro make-flushes (st &rest flshd)
  (let ((flds (get-fields st)))
    (list* 'progn
	   `(in-theory (enable ,@flds))
	   (append (make-flushes-thms flds flshd)
		   `((in-theory (disable ,@flds)))))))

(make-flushes ma dewrt emwrt fdwrt mwwrt)
(in-theory (disable flush))

(defun maX4 (m) (ma (ma (ma (ma (flush m))))))
(defun maX5 (m) (ma (maX4 m)))
(defun maX6 (m) (ma (maX5 m)))
(defun maX7 (m) (ma (maX6 m)))
(defun maX8 (m) (ma (maX7 m)))

(defun rank   (m) (bif (mwWRT m) 0 (bif (emWRT m) 1 (bif (deWRT m) 2 (bif (fdWRT m) 3 4)))))
(defun rep    (m) (make-isa (mwPC m) (pRF m) (mwDMem m) (pIMem m)))
(defun commit (m) (b (mwWRT m)))

(defthm sPC-of-rep (equal (sPC (rep m)) (mwPC m))
  :hints (("Goal" :in-theory (enable sPC))))
(defthm sRF-of-rep (equal (sRF (rep m)) (pRF m))
  :hints (("Goal" :in-theory (enable sRF))))
(defthm sDMem-of-rep (equal (sDMem (rep m)) (mwDMem m))
  :hints (("Goal" :in-theory (enable sDMem))))
(defthm sIMem-of-rep (equal (sIMem (rep m)) (pIMem m))
  :hints (("Goal" :in-theory (enable sIMem))))

(in-theory (disable sPC+ sRF+ sDMem+ sIMem+))

(defthm equal-rep-isa
  (equal (equal (rep m) (isa x))
	 (and (equal (mwPC m) (sPC+ x))
	      (equal (pRF m) (sRF+ x))
	      (equal (mwDMem m) (sDMem+ x))
	      (equal (pIMem m) (sIMem+ x))))
  :hints (("Goal" :in-theory (enable s s-aux rcd->acl2 acl2->rcd isa))))

(in-theory (enable sPC+ sRF+ sDMem+ sIMem+))

(defthm equal-rep-rep
  (equal (equal (rep m) (rep x))
	 (and (equal (mwPC m) (mwPC x))
	      (equal (pRF m) (pRF x))
	      (equal (mwDMem m) (mwDMem x))
	      (equal (pIMem m) (pIMem x))))
  :hints (("Goal" :in-theory (enable s s-aux rcd->acl2 acl2->rcd))))

(in-theory (disable g-diff-s- G-SAME-S-))
(in-theory (enable g-of-s-redux))
(in-theory (disable make-isa rep isa))

(defun ma-matches-isa (x)
  (if (commit x)
      (equal (rep (ma x)) (isa (rep x)))
    (and (equal (rep (ma x)) (rep x))
	 (< (rank (ma x)) (rank x)))))

(defthmk maX4-proof (ma-matches-isa (maX4 m)))
(defthmk maX5-proof (ma-matches-isa (maX5 m)))
(defthmk maX6-proof (ma-matches-isa (maX6 m)))
(defthmk maX7-proof (ma-matches-isa (maX7 m)))

; Of course, we can avoid anything this nonsense by proving for
; any 4 steps away from some start arbitrary state:

(defthmk ma-proof (ma-matches-isa (ma (ma (ma (ma m))))))
