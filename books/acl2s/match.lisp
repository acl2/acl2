#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

;; Author: Pete Manolios

(in-package "ACL2S")
(include-book "acl2s/ccg/ccg" :dir :system 
  :uncertified-okp nil :ttags ((:ccg))
  :load-compiled-file nil)
(set-termination-method :ccg)

(include-book "definec" :ttags :all)
(include-book "base-lists" :ttags :all)
(include-book "base-arithmetic" :ttags :all)
; (acl2s-defaults :set testing-enabled t)

(definec get-type-from-keyword (k :keyword) :symbol
  (case k
    (:atom 'atom)
    (otherwise (make-symbl `(,(symbol-name k) p) "ACL2S"))))

(local (in-theory (enable strip-cars strip-cdrs)))

(defthm acl2s-size-consp
  (=> (consp x)
      (< 0 (acl2s-size x)))
  :rule-classes ((:linear) (:type-prescription)))

(defthm acl2s-size-of-car
  (implies (equal (acl2s-size (car x))
                  (acl2s-size x))
           (atom x))
  :rule-classes (:forward-chaining))

(defthm acl2s-size-cdr
  (<= (acl2s-size (cdr x))
      (acl2s-size x))
  :rule-classes :linear)

(defthm acl2s-size-car
  (<= (acl2s-size (car x))
      (acl2s-size x))
  :rule-classes :linear)

(defthm acl2s-size-<=-strip-cdrs
  (<= (acl2s-size (strip-cdrs x))
      (acl2s-size x))
  :rule-classes :linear)

(defthm acl2s-size-<=-strip-cars
  (<= (acl2s-size (strip-cars x))
      (acl2s-size x))
  :rule-classes :linear)

(defthm acl2s-size-<-strip-cars
  (=> (consp (car x))
      (< (acl2s-size (strip-cars x))
         (acl2s-size x)))
  :rule-classes :linear)

(defthm acl2s-size-<-strip-cdrs
  (=> (consp (car x))
      (< (acl2s-size (strip-cdrs x))
         (acl2s-size x)))
  :rule-classes :linear)

(defthm strip-cars-cdrs-=
  (=> (alistp x)
      (= (+ (acl2s-size (strip-cars x))
            (acl2s-size (strip-cdrs x)))
         (acl2s-size x)))
  :rule-classes :linear)

(definec len1tl (x :all) :bool
  (and (consp x)
       (null (cdr x))))

(definec match-type (pat :all) :symbol
  (or (and (keywordp pat)
           (get-type-from-keyword pat))
      (and (consp pat)
           (consp (cdr pat))
           (null (cddr pat))
           (eq (car pat) :r)
           (symbolp (second pat))
           (second pat))))

(definec match-or (pat :all) :tl
  (and (consp pat)
       (consp (cdr pat))
       (eq (car pat) :or)
       (tlp pat)
       (cdr pat)))

(definec match-t (pat :all) :tl
  (and (consp pat)
       (consp (cdr pat))
       (null (cddr pat))
       (eq (car pat) :t)
       (list (second pat))))

(definec match-pats-codes (pats :tl codes :true-list-list) :bool
  (declare (xargs :consider-only-ccms ((acl2s-size codes))))
  (cond
   ((endp pats)
    (endp codes))
   ((endp codes)
    (endp pats))
   (t (b* ((pat (car pats))
           (code (car codes))
           (type? (match-type pat)))
        (cond
         ((! type?)
          (^ (len1tl code)
             (match-pats-codes (cdr pats) (cdr codes))))
         ((len1tl code)
          (match-pats-codes (cdr pats) (cdr codes)))
         (t (^ (alistp code)
               (b* ((npats (strip-cars code))
                    (ncodes (strip-cdrs code)))
                 (^ (true-list-listp ncodes)
                    (match-pats-codes npats ncodes)
                    (match-pats-codes (cdr pats) (cdr codes)))))))))))

(defthm march-pats-codes-or
  (=> (and (match-pats-codes (cons (list* :or pats5 pats6) pats2) codes)
           (true-list-listp codes)
           (tlp pats2))
      (match-pats-codes (cons (cons :or pats6) pats2) codes)))

(definec gen-match-body1
  (exp :all pats :tl codes :true-list-list) :tl
  :pre (match-pats-codes pats codes)
  :skip-tests t
  :timeout 500
  (declare (xargs :consider-only-ccms ((acl2s-size codes) (acl2s-size pats))))
  (if (endp pats)
      nil
    (b* ((pat (car pats))
         (code (car codes))
         (type? (match-type pat))
         (or? (match-or pat))
         (t? (match-t pat))
         (pat (if (and or? (null (cdr or?))) (car or?) pat))
         (or? (if (and or? (null (cdr or?))) nil or?)))
      (cond
       (type?
        (if (atom (cdr code))
            (cons `((,type? ,exp) ,(car code))
                  (gen-match-body1 exp (cdr pats) (cdr codes)))
          (cons `((,type? ,exp)
                  ,(cons 'cond
                         (append
                          (gen-match-body1
                           exp
                           (strip-cars code)
                           (strip-cdrs code))
                          '((t (illegal 'match "match is not exhaustive" ()))))))
                (gen-match-body1 exp (cdr pats) (cdr codes)))))
       (or?
        (append (gen-match-body1 exp (list (car or?)) (list code))
                (gen-match-body1 exp `((:or ,@(cdr or?)) ,@(cdr pats)) codes)))
       (t? (cons `(,(car t?) ,(car code))
                 (gen-match-body1 exp (cdr pats) (cdr codes))))
       (t (if (eq pat '&)
              (list (acl2::match-clause exp '& code))
            (cons (acl2::match-clause exp pat code)
                  (gen-match-body1 exp (cdr pats) (cdr codes)))))))))

(definec gen-match-body
  (exp :all pats :tl codes :true-list-list) :tl
  :pre (match-pats-codes pats codes)
  :skip-tests t
  :timeout 500
  (declare (xargs :consider-only-ccms ((acl2s-size codes))))
  ;; To enforce exhaustiveness
  (append (gen-match-body1 exp pats codes)
          '((t (illegal 'match "match is not exhaustive" ())))))
  
(definec match-fun (exp :all args :alist) :tl
  :pre (true-list-listp (strip-cdrs args))
  :pre (tlp (strip-cars args))
  :pre (match-pats-codes (strip-cars args)
                         (strip-cdrs args))
  (b* ((pats  (strip-cars args))
       (codes (strip-cdrs args)))
    (cons 'cond
          (gen-match-body exp pats codes))))

(defmacro match (exp &rest args)
  (match-fun exp args))

;(in-theory (disable strip-cars strip-cdrs))

(include-book "xdoc/top" :dir :system)

(defxdoc match
  :parents (acl2::acl2-sedan acl2::defdata)
  :short "Pattern matching supporting predicates, including
  recognizers automatically generated by @(see defdata),
  disjunctive patterns and patterns containing arbitrary code.
  Can be thought of as ACL2s version of @(see? case-match)."
  :long
  "
<h3>Examples</h3>

@({

  ;; Predicate/recognizer patterns are defined using keywords.
  ;; The keyword pos corresponds to the recognizer posp. For all
  ;; keywords except atom, we generate the corresponding
  ;; predicate/recognizer by adding a p to the end of the symbol.
  
  ;; This function, given an integer as input, returns 1 if it is
  ;; positive, else 2 if it is even, else 3. Match forms are checked
  ;; to make sure that they are exhaustive. If not, that is an error,
  ;; e.g., if you remove one of the cases to match, you will get an
  ;; error. Note that :even gets turned into the predicate evenp,
  ;; which is not a recognizer (as its domain is not all).
  
  (definec int-class (x :int) :pos
    (match x
      (:pos 1)
      (:even 2)
      (:neg 3)))

  ;; Here is a more complex example, showing that predicate/recognizer
  ;; patterns can be nested. The match form matches any positive x,
  ;; and then checks if it even or odd. The nested match forms must
  ;; also be exhaustive, given that x is positive. If x is not
  ;; positive, then we check if it is negative and then we perform
  ;; another nested check. 

  ;; Finally, we check if x is 0. Constants such as 0 can be used as
  ;; patterns, as shown below.
  
  (definec int-class2 (x :int) :pos
    (match x
      (:pos 
       (:even 1)
       (:odd 2))
      (:neg
       (:even 3)
       (:odd 4))
      (0 5)))
    
  ;; The next definition is equivalent to the previous definition, but
  ;; makes maximal use of &.
  
  ;; & matches anything and is not bound. Repeated occurrences of &
  ;; may match different structures. 

  (definec int-class3 (x :int) :pos
    (match x
      (:pos 
       (:even 1)
       (& 2))
      (:neg
       (:even 3)
       (& 4))
      (& 5)))
  
  (definec fact (n :nat) :pos
    (match n
      (0 1)
      (& (* n (fact (1- n))))))

  ;; The following three definitions of fib are equivalent.

  ;; Disjunctive patterns are defined with the use of :or, as shown in
  ;; the first definition of fib. This match form can be thought of as
  ;; expanding into the match form of the second version of fib. A
  ;; disjunctive pattern can have any positive number of patterns.
  
  (definec fib (n :nat) :pos
    :skip-tests t
    (match n
      ((:or 0 1) 1)
      (& (+ (fib (1- n)) (fib (- n 2))))))
  
  (definec fib (n :nat) :pos
    :skip-tests t
    (match n
      (0 1)
      (1 1)
      (& (+ (fib (1- n)) (fib (- n 2))))))

  ;; Patterns with arbitrary code are defined with the use of :t, as
  ;; shown below, where the pattern checks if n is less than 2.
  
  (definec fib (n :nat) :pos
    :skip-tests t
    (match n
      ((:t (< n 2)) 1)
      (& (+ (fib (1- n)) (fib (- n 2))))))

  ;; The following definitions of pascal are equivalent.

  ;; !sym, where sym is a symbol that is already bound in the context
  ;; of the match form, matches only the current binding of
  ;; sym. Hence, in the first definition of pascal, the last pattern
  ;; in the :or form matches a list whose first element is anything,
  ;; but whose second element is i (the first argument to
  ;; pascal). Notice that the first argument is also i, which explains
  ;; the equivalence between the two versions of pascal.
  
  (definec pascal (i :nat j :nat) :pos
    :skip-tests t
    (match (list i j)
      ((:or (0 &) (& 0) (& !i)) 1)
      (& (+ (pascal (1- i) (1- j))
            (pascal (1- i) j)))))

  (definec pascal (i :nat j :nat) :pos
    :skip-tests t
    (match (list i j)
      ((0 &) 1)
      ((& 0) 1)
      ((!i !i) 1)
      (& (+ (pascal (1- i) (1- j))
            (pascal (1- i) j)))))

  ;; The following examples show how to use match with conses.  In mem,
  ;; we first check if x is nil. The symbols nil, t, *sym* and cannot
  ;; be bound and only match their global values, as was the case for
  ;; constants, as we have seen above. The pattern (f . r) matches any
  ;; cons, with f being the car and r being the cdr. Since mem is
  ;; checking whether e is a member of x, notice the use of !e to
  ;; match e with the first element of x.
  
  (definec mem (e :all x :tl) :bool
    (match x
      (nil nil)
      ((!e . &) t)
      ((& . r) (mem e r))))

  (definec subset (x :tl y :tl) :bool
    (match x
      (nil t)
      ((f . r) (and (mem f y) (subset r y)))))

  ;; More complex patterns than (f . r) can be used to match with
  ;; conses and lists. For example, (x x y) and ('x (:x x) . t) are
  ;; allowed patterns. The first pattern matches (1 1 2), ((1 2) (1 2)
  ;; (3)), etc, and the second pattern only matches lists whose first
  ;; element is the symbol x, whose second element is a list of length
  ;; two whose first element is the keyword x and whose cddr is t.
  
  ;; If you want to match an object, say obj, you can use the pattern
  ;; 'obj.  This allows you to match keywords that may otherwise be
  ;; interpreted as types.
  
  ;; Here is the definition of the built-in function acl2-count.

  (defun acl2-count (x)
    (declare (xargs :guard t :mode :program))
    (if (consp x)
        (+ 1 (acl2-count (car x))
           (acl2-count (cdr x)))
      (if (rationalp x)
          (if (integerp x)
              (integer-abs x)
            (+ (integer-abs (numerator x))
               (denominator x)))
        (if (complex/complex-rationalp x)
            (+ 1 (acl2-count (realpart x))
               (acl2-count (imagpart x)))
          (if (stringp x)
              (length x)
            0)))))

  ;; Here is an equivalent definition using match. 

  (definec acl2-count2 (x :all) :nat
    (match x
      ((a . b) (+ 1 (acl2-count2 a) (acl2-count2 b)))
      (:rational
       (:integer (integer-abs x))
       (& (+ (integer-abs (numerator x))
             (denominator x))))
      ((:r complex/complex-rationalp)
       (+ 1 (acl2-count2 (realpart x))
          (acl2-count2 (imagpart x))))
      (:string (length x))
      (& 0)))

  
  ;; Note that the two definitions are equivalent, 
  ;; as the following is a theorem. 

  (thm (equal (acl2-count2 x) (acl2-count x)))


})

<h3>Purpose</h3>

<p> The macro @(see match) Provides pattern matching.  It includes the
functionality similar to that provided by @(see? case-match) and more.
It supports predicate/recognizer patterns in a style similar to how
@(see?  definec) allows you to specify @(see? defdata) types. These
patterns can be nested. The @(see match) macro also provides
disjunctive patterns and patters containing arbitrary code.  Patterns
are required to be exhaustive.  </p>

<p> There are two ways to specify predicates/recognizers. One is to
use a keyword, such as :rational; see the examples above. Such
keywords are turned into predicates/recognizers by creating a regular
symbol with a \"p\" at the end, e.g., :rational gets turned into
rationalp (the only special case is that :atom gets turned into
atom). The generated symbols are in the ACL2s package. The more
general mechanism is to specify a predicate/recognizer using the
(:r predicate/recognizer) form; an example is
(:r complex/complex-rationalp) in the acl2-count2 definition above. In
this way, you can also specify the package of the
predicate/recognizer.  </p>

<p>If you want to match a keyword, you can do that by quoting it.
So <tt>':rational</tt> matches the keyword, not the type.</p>

<p> If you are matching a predicate/recognizer, you can either have a
single form after that, in which case, that form is an ACL2 expression
that gets associated with the predicate/recognizer, or you can have a
list of forms, in which case they are treated as nested matching
forms.  An example of such nesting is shown in the :rational case of
the match in the definition of acl2-count2, above.  </p>

<p>
Disjunctive patterns and patterns containing arbitrary code are also
supported. See the examples above.
</p>

<p>
If you are not matching any of the above patterns
(predicate/recognizer, disjunctive, code), then match behaves like
@(see? case-match).  </p>

<p> One important difference with @(see? case-match) is that match
requires that the cases are exhaustive (or complete). It does this by,
essentially, adding the following as a final case.  </p>

@({

 (& (illegal 'match \"match is not exhaustive\" ()))

})

<p> During contract checking (or guard verification), if the above
case is reachable, that will lead to an error.  The reason for this is
to not have any hidden control flow, which can make debugging hard.
Finally, we note that nested patterns are also required to be
exhaustive. 
</p>

"
  )

#|

Examples and proof mentioned in documentation.

(definec acl2s-size- (x :all) :nat
  (match x
    ((a . b) (+ 1 (acl2s-size- a) (acl2s-size- b)))
    (:rational (integer-abs (numerator x)))
    ((:r stringp) (length x))
    (& 0)))

(definec acl2-count2 (x :all) :nat
  (match x
    ((a . b) (+ 1 (acl2-count2 a) (acl2-count2 b)))
    (:rational
     (:integer (integer-abs x))
     (& (+ (integer-abs (numerator x))
           (denominator x))))
    ((:r complex/complex-rationalp)
     (+ 1 (acl2-count2 (realpart x))
        (acl2-count2 (imagpart x))))
    (:string (length x))
    (& 0)))

(thm (equal (acl2-count2 x) (acl2-count x)))
|#

#|

Testing.

(include-book "xdoc/debug" :dir :system)
:doc match

|#


#|

Maybe be useful at some point

(defdata alist2 (or nil (cons (list* all all all) alist2)))

(definec strip-cadrs (x :alist2) :tl
  (if (endp x)
      nil
    (cons (cadr (car x))
          (strip-cadrs (cdr x)))))

(defdata
  (sterm (or atom quote (cons fsterm lsterm)))
  (fsterm (or symbol (list 'lambda symbol-list sterm)))
  (lsterm (listof sterm)))

(defun nth-simple-term-builtin (n)
  (declare (xargs :guard (natp n) :mode :program))
  (nth-sterm-builtin n))

(defun nth-simple-term-list-builtin (n)
  (declare (xargs :guard (natp n) :mode :program))
  (nth-lsterm-builtin n))

(register-type
  simple-term :predicate simple-termp
  :enumerator nth-simple-term-builtin)

(register-type
  simple-term-list :predicate simple-term-listp
  :enumerator nth-simple-term-list-builtin)

|#

