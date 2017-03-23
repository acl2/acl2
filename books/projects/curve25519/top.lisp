(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "axioms"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; This book is a proof of the group axioms for the addition operation
;; on the elliptic curver known as Curve25519.

;; For documentation, see www.russinoff.com/papers/group.pdf.

;;******************************************************************
;;                      The Galois Field Fp
;;******************************************************************

(defund p () (- (expt 2 255) 19))

(in-theory (disable (p)))

;; The primality of p is proved here:

(include-book "projects/quadratic-reciprocity/pratt" :dir :system)

(defthm primep-p
  (primep (p)))

;; Field element recognizer:

(defun fp (n) (and (natp n) (< n (p))))

;; Field operations:

(defun f+ (m n)
  (mod (+ m n) (p)))

(defun f- (m n)
  (mod (- m n) (p)))

(defun f* (m n)
  (mod (* m n) (p)))

(defun fexpt (n e)
  (mod-expt n e (p)))

;; Multiplicative inverse, based on Fermat's theorem, w2hich is proved
;; in "projects/quadratic-reciprocity/fermat.lisp":

(defund frcp (n)
  (fexpt n (- (p) 2)))

(defthmd frcp-inverts
  (implies (and (fp n) (not (= n 0)))
           (equal (f* (frcp n) n)
                  1)))

;; Division:

(defun f/ (m n)
  (mod (* m (frcp n)) (p)))

;;******************************************************************
;;                   The Elliptic Curve
;;******************************************************************

;; The group EC consists of the point at infinity and the points (x,y)
;; in Fp x Fp such that y^2 = x^3 + A*x^2 + x, where A = 486662.

(defun inf () 'infinity)

(defun x (r) (car r))

(defun y (r) (cdr r))

(defun a () 486662)

(defund ecp (r)
  (or (eql r (inf))
      (and (fp (x r))
           (fp (y r))
           (= (fexpt (y r) 2)
              (f+ (f+ (fexpt (x r) 3) 
                      (f* (a) (fexpt (x r) 2)))
                  (x r))))))

;; The inverse and addition operations of the group:

(defund ec- (r)
  (if (equal r (inf))
      (inf)
    (cons (x r) (f- 0 (y r)))))

(defund ec+ (r1 r2)
  (if (equal r1 (inf))
      r2
    (if (equal r2 (inf))
        r1
      (if (equal r2 (ec- r1))
          (inf)
        (let* ((x1 (x r1)) (y1 (y r1)) (x2 (x r2)) (y2 (y r2))
               (lam (if (= x1 x2)
                       (f/ (f+ (f+ (f* 3 (fexpt x1 2))
                                   (f* (f* 2 (a)) x1))
                               1)
                           (f* 2 y1))
                     (f/ (f- y1 y2)
                         (f- x1 x2))))
              (x (f- (f- (f- (fexpt lam 2)
                             (a))
                         x1)
                     x2))
              (y (f- (f* lam (f- x1 x))
                     y1)))
          (cons x y))))))

(defthm ec-inverse
  (implies (ecp p)
           (and (ecp (ec- p))
                (equal (ec+ (ec- p) p)
                       (inf)))))

;; Infinity is the identity element:

(defthm ec-identity
  (implies (ecp p)
           (equal (ec+ (inf) p)
                  p)))

;; The origin is the unique element of order 2:

(defun o () '(0 . 0))

(defthm r=-r
  (implies (ecp r)
           (iff (equal r (ec- r))
                (or (equal r (inf))
                    (equal r (o)))))
  :rule-classes ())

;; Our objective is to prove the following three properties:

(defthm ec-closure
  (implies (and (ecp p) (ecp q))
           (ecp (ec+ p q))))

(defthm ec-commutativity
  (implies (and (ecp p) (ecp q))
           (equal (ec+ p q) (ec+ q p)))
  :rule-classes ())

(defthm ec-associativity
  (implies (and (ecp p) (ecp q) (ecp r))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ())

;; We begin with two simple properties:

(defthm p+q<>p
  (implies (and (ecp p)
                (ecp q)
                (not (equal q (inf))))
           (not (equal (ec+ p q) p)))
  :rule-classes ())

(defthm p+q=p-q
  (implies (and (ecp p)
                (ecp q)
                (equal (ec+ p q) (ec+ p (ec- q))))
           (or (equal p (inf))
               (equal q (inf))
               (equal p (o))
               (equal q (o))))
  :rule-classes ())


;;******************************************************************
;;              Encoding Points as Integer Triples
;;******************************************************************

;; The sum of two points may be conveniently represented in the form
;; (u/z^2, v/z^2), where z, u, and v are polynomials in the coordinates
;; of the addends.  The two lemmas below will allow us to represent
;; the result of a composition of additions in such a form in certain
;; cases.  This provides a means of verifying the identities that we 
;; need to establish the group properties: By applying these lemmas to
;; both sides of a conjectured identity and cross-multiplying, we can 
;; convert the identity to a polynomial congruence, which we can verify 
;; computationally by converting the polynomials to sparse Horner 
;; normal form.

;; A decodable triple is characterized as follows:

(defund tripp (x)
  (and (true-listp x)
       (= (len x) 3)
       (integerp (car x))
       (integerp (cadr x))
       (integerp (caddr x))
       (not (= (mod (caddr x) (p)) 0))))

;; the decoding function:

(defund dx (p)
  (f/ (car p) (expt (caddr p) 2)))

(defund dy (p)
  (f/ (cadr p) (expt (caddr p) 3)))

(defun decode3 (p)
  (cons (dx p) (dy p)))

;; Note that any point (x,y) admits the canonical encoding (x,y,1).

;; This method is applicable in two cases: (1) the two triples coincide,
;; and (2) one of the triples is canonical.

;; Case (1): P + P, where P = decode3(u,v,z) 
;; We define polynomial functions zdbl, udbl, and vdbl 
;; such that

;;       P + P = (u'/z'^2, v',z'^3),

;; where

;;   z' = zdbl(P),
;;   u' = udbl(P),
;;   v' = vdbl(P).

(defund lamdbl (p)
  (f/ (+ (* 3 (expt (dx p) 2))
         (* 2 (a) (dx p))
         1)
      (* 2 (dy p))))

(defund xdbl (p)
  (f- (expt (lamdbl p) 2) (+ (a) (* 2 (dx p)))))

(defund ydbl (p)
  (f- (f* (lamdbl p) (- (dx p) (xdbl p)))
      (dy p)))

(defund zdbl (p)
  (let ((v (cadr p))
        (z (caddr p)))
    (* 2 v z)))

(defund wdbl (p)
  (let ((u (car p))
        (z (caddr p)))
    (+ (* 3 (expt u 2))
       (* 2 (a) u (expt z 2))
       (expt z 4))))

(defund udbl (p)
  (let ((u (car p))
        (v (cadr p))
        (z (caddr p)))
    (- (expt (wdbl p) 2)
      (* 4
         (expt v 2)
         (+ (* (a) (expt z 2))
            (* 2 u))))))

(defund vdbl (p)
  (let ((u (car p))
        (v (cadr p)))
    (- (* (wdbl p)
          (- (* 4 u (expt v 2))
             (udbl p)))
       (* 8 (expt v 4)))))

(defund dbl (p)
  (list (udbl p)
        (vdbl p)
        (zdbl p)))

(defthmd dbl-formula
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (decode3 (dbl p))
                  (ec+ (decode3 p) (decode3 p)))))

;; Case (2): P1 + P2, where P1 = (x,y) = decode3(x,y,1) and
;; P2 = decode3(u,v,z) <> P1. 

;; We define polynomial functions zsum, usum, and vsum such that
;; P1 + P2 = (u'/z'^2, v',z'^2), where
;;   z' = zsum(P, Q),
;;   u' = usum(P, Q),
;;   v' = vsum(P. Q).

(defund lamsum (p1 p2)
  (f/ (f- (dy p1) (dy p2))
      (f- (dx p1) (dx p2))))

(defund zsum (p1 p2)
  (let ((u (car p2))
        (z (caddr p2))
        (x (car p1)))
    (* z
       (- (* x (expt z 2))
          u))))

(defund usum (p1 p2)
  (let ((u (car p2))
        (v (cadr p2))
        (z (caddr p2))
        (x (car p1))
        (y (cadr p1)))
    (- (expt (- (* (expt z 3) y)
                v)
             2)
       (* (+ (* (expt z 2) (+ (a) x))
             u)
          (expt (- (* (expt z 2) x)
                   u)
                2)))))

(defund vsum (p1 p2)
  (let ((v (cadr p2))
        (z (caddr p2))
        (x (car p1))
        (y (cadr p1)))
    (- (* (- (* (expt z 3) y)
             v)
          (- (* (expt (zsum p1 p2) 2) x)
             (usum p1 p2)))
       (* (expt (zsum p1 p2) 3)
          y))))

(defund sum (p1 p2)
  (list (usum p1 p2)
        (vsum p1 p2)
        (zsum p1 p2)))

(defthmd sum-formula
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
            (equal (decode3 (sum p1 p2))
                  (ec+ (decode3 p1) (decode3 p2)))))


;;*********************************************************************************
;;                              Reducing SHNFs
;;*********************************************************************************

;; The theory of sparse Horner normal form (SHNF) lives here:

(include-book "projects/shnf/top" :dir :system)

;; The following functions are defined in that book:

;;   polyp(x, vars) recognizes x as a polynomial over the variable list vars.

;;   evalp(x, alist) computes the value of the polynomial x under the variable
;;   assignment given by alist.

;;   shnfp(x) recognizes x as a SHNF.

;;   norm(x, vars) converts a polynomial x over the variable list vars to a SHNF.
;;   It calls these auxiliary functions:
;;      norm-add(x, y) adds the SHNFs x and y.
;;      norm-mul(x, y) multiplies the SHNFs x and y.
;;      norm-expt(x, k) computes the kth power of the SHNF x.
;;      norm-pop(i, p) normalizes (POP i p), where i is a nat and p is a SHNF
;;      norm-pow(i, p, q) normalizes (POW i p q), where i is a positive integer
;;      and p and q are SHNFs.

;;   evalh(x, vals) takes a SHNF x = norm(z, vars), where z is a polynomial over
;;   vars, and computes evalp(z, pairlis$(vars, vals)),

;; We constrain three points, pi = (xi . yi), i=1,2,3, to lie on the curve EC:

(encapsulate (((y0) => *) ((y1) => *) ((y2) => *)
              ((x0) => *) ((x1) => *) ((x2) => *))
  (local (defun y0 () 0))
  (local (defun y1 () 0))
  (local (defun y2 () 0))
  (local (defun x0 () 0))
  (local (defun x1 () 0))
  (local (defun x2 () 0))
  (defun p0 () (cons (x0) (y0)))
  (defun p1 () (cons (x1) (y1)))
  (defun p2 () (cons (x2) (y2)))
  (defthm ecp-assumption
    (and (ecp (p0)) (ecp (p1)) (ecp (p2)))))

;; We focus on the case of a polynomial in x0, y0, x1, y1, x2, and y2.

(defun vars () '(y0 y1 y2 x0 x1 x2))

(defund vals () (list (y0) (y1) (y2) (x0) (x1) (x2)))

(defund vlist () (pairlis$ (vars) (vals)))

(defun polyp$ (x) (polyp x (vars)))

 (defun evalp$ (x) (evalp x (vlist)))

(defun evalh$ (x) (evalh x (vals)))

;; We shall define a function, reduce$, that converts such a polynomial to 
;; a SHNF and systematically rewrites the result according to the assumption 
;; that the three points satisfy the curve equation.

;; The above ordering of vars is designed to maximize the efficiency of reduce$.

;; The guts of reduce$ is the function split$.  Its arguments are as follows:
;;   (1) h is a SHNF
;;   (2) j is in {0,1,2), representing Yj
;;   (3) k is a nat
;; It returns a multiple value (mv h0 h1), where h0 and h1 are SHNFs that are
;; independent of Yj such that under the assumptions noted above,

;;     evalh(h, vals) = evalh(h0, vals) + evalh(Yj, vals) * evalh(h1, vals).

;; Note that according to the definition, when y is at the head of vars, split
;; effectively replaces y^2 with the value of

;;     (pop 3 (pow 1 (pow 1 (pow 1 1 486662) 1) 0),

;; which is xi^3 + a * xi^2 + xi when y = yi.

;; The following SHNF is used in the reduction:

(defund theta () `(pop 3 (pow 1 (pow 1 (pow 1 1 ,(a)) 1) 0)))

(defthm shnfp-theta
  (shnfp (theta)))

(defthmd theta-0-mod
  (equal (mod (evalh (theta) (vals)) (p))
         (mod (expt (y0) 2) (p))))

(defthmd theta-1-mod
  (equal (mod (evalh (theta) (cdr (vals))) (p))
         (mod (expt (y1) 2) (p))))

(defthmd theta-2-mod
  (equal (mod (evalh (theta) (cddr (vals))) (p))
         (mod (expt (y2) 2) (p))))
         
(defun split$ (h j k)
  (if (or (atom h) (< j k))
      (mv h 0)
    (if (eql (car h) 'pop)
        (let ((i (cadr h)) (p (caddr h)))
          (mv-let (p0 p1) (split$ p j (+ i k))
            (mv (norm-pop i p0) (norm-pop i p1))))
      (let ((i (cadr h)) (p (caddr h)) (q (cadddr h)))
        (mv-let (p0 p1) (split$ p j k)
          (mv-let (q0 q1) (split$ q j (1+ k))
            (if (= j k)
                (if (evenp i)
                    (mv (norm-add (norm-mul (norm-expt (theta) (/ i 2)) p0)
                                  (norm-pop 1 q0))
                        (norm-add (norm-mul (norm-expt (theta) (/ i 2)) p1)
                                  (norm-pop 1 q1)))
                  (mv (norm-add (norm-mul (norm-expt (theta) (/ (1+ i) 2)) p1)
                                (norm-pop 1 q0))
                      (norm-add (norm-mul (norm-expt (theta) (/ (1- i) 2)) p0) 
                                (norm-pop 1 q1))))
              (mv (norm-pow i p0 q0)
                  (norm-pow i p1 q1)))))))))

(defthm split$-lemma
  (implies (and (natp j)
                (<= j 2)
                (natp k)
                (shnfp h))
           (mv-let (h0 h1) (split$ h j k)
             (and (shnfp h0)
                  (shnfp h1)
                  (equal (mod (evalh h (nthcdr k (vals))) (p))
                         (mod (+ (evalh h0 (nthcdr k (vals)))
                                 (* (nth j (vals))
                                    (evalh h1 (nthcdr k (vals)))))
                              (p)))))))

;; Thus, evalh(rewrite$(h, j), (vars)) = evalh(h, vars):

(defun rewrite$ (h j)
  (mv-let (h0 h1) (split$ h j 0)
    (norm-add h0 (norm-mul h1 (norm (nth j (vars)) (vars))))))

(defthm rewrite$-lemma
  (implies (and (natp j)
                (<= j 2)
                (shnfp h))
           (let ((r (rewrite$ h j)))
             (and (shnfp r)
                  (equal (mod (evalh$ r) (p))
                         (mod (evalh$ h) (p)))))))

;; reduce successively rewrites powers of Y0, Y1, and Y2:

(defun reduce$ (x)
  (rewrite$ (rewrite$ (rewrite$ (norm x (vars)) 0) 1) 2))

(defthm reduce$-correct
  (implies (polyp$ x)
           (and (shnfp (reduce$ x))
                (equal (mod (evalh$ (reduce$ x)) (p))
                       (mod (evalp$ x) (p))))))


;;*********************************************************************************
;;                         Encoding Points as Term Triples
;;*********************************************************************************

;; The evaluation of terms induces a mapping from the set of term triples, as
;; recognized by the following predicate, to points in Fp x Fp:

(defund tripp$ (x)
  (and (true-listp x)
       (= (len x) 3)
       (polyp$ (car x))
       (polyp$ (cadr x))
       (polyp$ (caddr x))
       (not (= (mod (evalp$ (caddr x)) (p)) 0))))

(defun eval3$ (p)
  (list (evalp$ (car p))
        (evalp$ (cadr p))
        (evalp$ (caddr p))))

(defun decode3$ (p)
  (decode3 (eval3$ p)))

;; The following triples arer mapped to the points P1, P2, P3, and O:

(defund p0$ () (list 'x0 'y0 1))
(defund p1$ () (list 'x1 'y1 1))
(defund p2$ () (list 'x2 'y2 1))
(defund o$ () '(0 0 1))

(defthm tripp$p
  (and (tripp$ (p0$))
       (tripp$ (p1$))
       (tripp$ (p2$))))

(defthm tripp$o$
  (tripp$ (o$)))

(defthm decode3$p$
  (and (equal (decode3$ (p0$)) (p0))
       (equal (decode3$ (p1$)) (p1))
       (equal (decode3$ (p2$)) (p2))))

(defthm decode3$o$
  (equal (decode3$ (o$)) (o)))

;; We define addition operations on term triples corresponding to the
;; two addition operations on integer triples.

;; Doubling:

(defun zdbl$ (p)
  (let ((v (cadr p))
        (z (caddr p)))
    `(* 2 (* ,v ,z))))

(defun wdbl$ (p)
  (let ((u (car p))
        (z (caddr p)))
    `(+ (* 3 (expt ,u 2))
        (+ (* 2 (* ,(a) (* ,u (expt ,z 2))))
           (expt ,z 4)))))

(defun udbl$ (p)
  (let ((u (car p))
        (v (cadr p))
        (z (caddr p)))
    `(- (expt ,(wdbl$ p) 2)
        (* 4
           (* (expt ,v 2)
              (+ (* ,(a) (expt ,z 2))
                 (* 2 ,u)))))))

(defun vdbl$ (p)
  (let ((u (car p))
        (v (cadr p)))
    `(- (* ,(wdbl$ p)
           (- (* 4 (* ,u (expt ,v 2)))
              ,(udbl$ p)))
        (* 8 (expt ,v 4)))))

(defun dbl$ (p)
  (list (udbl$ p)
        (vdbl$ p)
        (zdbl$ p)))

(defthmd tripp$-dbl$
  (implies (and (tripp$ p)
                (ecp (decode3$ p))
                (not (equal (decode3$ p) (o))))
           (tripp$ (dbl$ p))))

(defthmd dbl$-formula
  (implies (and (tripp$ p)
                (ecp (decode3$ p))
                (not (equal (decode3$ p) (o))))
           (equal (decode3$ (dbl$ p))
                  (ec+ (decode3$ p) (decode3$ p)))))

;; Addition of distinct points, one of which is canonical:

(defun zsum$ (p1 p2)
  (let ((u (car p2))
        (z (caddr p2))
        (x (car p1)))
    `(* ,z
        (- (* ,x (expt ,z 2))
           ,u))))

(defun usum$ (p1 p2)
  (let ((u (car p2))
        (v (cadr p2))
        (z (caddr p2))
        (x (car p1))
        (y (cadr p1)))
    `(- (expt (- (* (expt ,z 3) ,y)
                 ,v)
              2)
        (* (+ (* (expt ,z 2) (+ ,(a) ,x))
              ,u)
           (expt (- (* (expt ,z 2) ,x)
                    ,u)
                 2)))))

(defun vsum$ (p1 p2)
  (let ((v (cadr p2))
        (z (caddr p2))
        (x (car p1))
        (y (cadr p1)))
    `(- (* (- (* (expt ,z 3) ,y)
              ,v)
           (- (* (expt ,(zsum$ p1 p2) 2) ,x)
              ,(usum$ p1 p2)))
        (* (expt ,(zsum$ p1 p2) 3)
           ,y))))

(defun sum$ (p1 p2)
  (list (usum$ p1 p2)
        (vsum$ p1 p2)
        (zsum$ p1 p2)))

(defthm zdbl$-rewrite
  (equal (evalp$ (zdbl$ p))
         (zdbl (eval3$ p))))

(defthm udbl$-rewrite
  (equal (evalp$ (udbl$ p))
         (udbl (eval3$ p))))

(defthm vdbl$-rewrite
  (equal (evalp$ (vdbl$ p))
         (vdbl (eval3$ p))))
                   
(defthm zsum$-rewrite
  (equal (evalp$ (zsum$ p1 p2))
         (zsum (eval3$ p1) (eval3$ p2))))

(defthm usum$-rewrite
  (equal (evalp$ (usum$ p1 p2))
         (usum (eval3$ p1) (eval3$ p2))))

(defthm vsum$-rewrite
  (equal (evalp$ (vsum$ p1 p2))
         (vsum (eval3$ p1) (eval3$ p2))))

(defthm tripp$-sum$
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (tripp$ (sum$ p1 p2))))

(defthmd sum$-formula
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (not (= (x (decode3$ p1)) (x (decode3$ p2))))
                (= (caddr p1) 1))
           (equal (decode3$ (sum$ p1 p2))
                  (ec+ (decode3$ p1) (decode3$ p2)))))

;; Negation:

(defun neg$ (p)
  (list (car p) (list '- (cadr p)) (caddr p)))

(defthm tripp$-neg$
  (implies (and (tripp$ p)
                (ecp (decode3$ p)))
           (tripp$ (neg$ p))))

(defthmd neg$-formula
  (implies (and (tripp$ p)
                (ecp (decode3$ p)))
           (equal (decode3$ (neg$ p))
                  (ec- (decode3$ p)))))

;; The next two lemmas will be critical in establishing the group axioms.

;; EC-encodings:

(defun ecp$-term (p)
  (let* ((u (car p))
         (v (cadr p))
         (z (caddr p)))
    `(- (expt ,v 2)
        (+ (expt ,u 3)
           (+ (* ,(a) (expt (* ,u ,z) 2))
              (* ,u (expt ,z 4)))))))

(defun ecp$ (p)
  (equal (reduce$ (ecp$-term p))
         0))

(defthmd ecp$ecp 
  (implies (and (tripp$ p)
                (ecp$ p))
           (ecp (decode3$ p))))

;; The equivalence relation:

(defun eq$ (p1 p2)
  (let ((u1 (car p1))
        (v1 (cadr p1))
        (z1 (caddr p1))
        (u2 (car p2))
        (v2 (cadr p2))
        (z2 (caddr p2)))
    (and (equal (reduce$ `(* ,u1 (expt ,z2 2)))
                (reduce$ `(* ,u2 (expt ,z1 2))))
         (equal (reduce$ `(* ,v1 (expt ,z2 3)))
                (reduce$ `(* ,v2 (expt ,z1 3)))))))

(defthmd eq$eq
  (implies (and (tripp$ p1)
                (tripp$ p2)
                (eq$ p1 p2))
           (equal (decode3$ p1) (decode3$ p2))))


;;*********************************************************************************
;;                              Group Axioms
;;*********************************************************************************

(defthm comp-1
  (and (ecp$ (dbl$ (p0$)))
       (ecp$ (sum$ (p0$) (p1$))))
  :rule-classes ())

;; [0.02 seconds]

(defthm ec-closure
  (implies (and (ecp p) (ecp q))
           (ecp (ec+ p q))))

(defthm comp-2
  (eq$ (sum$ (p0$) (p1$))
       (sum$ (p1$) (p0$)))
  :rule-classes ())

;; [0.01 seconds]

(defthm ec-commutativity
  (implies (and (ecp p) (ecp q))
           (equal (ec+ p q) (ec+ q p)))
  :rule-classes ())

;; (-P0) + (-P0) = -(P0 + P0)

(defthm comp-3
  (eq$ (dbl$ (neg$ (p0$)))
       (neg$ (dbl$ (p0$))))
  :rule-classes ())

;; [0.01 seconds]

;; (-P0) + (-P1) = -(P0 + P1)

(defthm comp-4
  (eq$ (sum$ (neg$ (p0$)) (neg$ (p1$)))
       (neg$ (sum$ (p0$) (p1$))))
  :rule-classes ())

;; [0.01 seconds]

(defthm lemma-15
  (implies (and (ecp p) (ecp q))
           (equal (ec+ (ec- p) (ec- q))
                  (ec- (ec+ p q))))
  :rule-classes ())

;; P0 + P0 <> -P0 => (-P0) + (P0 + P0) = P0

(defthm comp-5
  (eq$ (sum$ (neg$ (p0$))
             (dbl$ (p0$)))
       (p0$))
  :rule-classes ())

;; [0.01 seconds]

;; P0 <> +-P1 and P0 + P1 <> -P0 => (-P0) + (P0 + P1) = P1

(defthm comp-6
  (eq$ (sum$ (neg$ (p0$))
             (sum$ (p0$) (p1$)))
       (p1$))
  :rule-classes ())

;; [0.04 seconds]

(defthm lemma-16
  (implies (and (ecp p) (ecp q)
                (not (equal (ec+ p q) (ec- p))))
           (equal (ec+ (ec- p) (ec+ p q))
                  q))
  :rule-classes ())

;; P0 <> +-P1 and P0 + P1 <> +-P2 and P0 <> +-P2 and P0 + P2 <> +-P1 => P2 + (P0 + P1) = P1 + (P0 + P2)

(defthm comp-7
  (eq$ (sum$ (p2$) (sum$ (p0$) (p1$)))             
       (sum$ (p1$) (sum$ (p0$) (p2$))))
  :rule-classes ())

;; [3.94 seconds]

;; P0 <> +-P1 and P0 + P0 <> +-P1 and P0 + P1 <> -P0 => P1 + (P0 + P0) = P0 + (P0 + P1)

(defthm comp-8
  (eq$ (sum$ (p1$) (dbl$ (p0$)))
       (sum$ (p0$) (sum$ (p0$) (p1$))))
  :rule-classes ())

(defthm lemma-17
  (implies (and (ecp p) (ecp q) (ecp r)
                (not (equal (ec+ p q) r))
                (not (equal (ec+ p q) (ec- r)))
                (not (equal (ec+ p r) q))
                (not (equal (ec+ p r) (ec- q))))
           (equal (ec+ r (ec+ p q))
                  (ec+ q (ec+ p r))))
  :rule-classes ())

;; (P0 + P0 <> -P0 and (P0 + P0) + P0 <> -P0 => (P0 + P0) + (P0 + P0) = P0 + (P0 + (P0 + P0))

(defthm comp-9
  (eq$ (dbl$ (dbl$ (p0$)))
       (sum$ (p0$) (sum$ (p0$) (dbl$ (p0$)))))
  :rule-classes ())

;; [0.22 seconds]

;; P0 <> +-P1 and (P0 + P1 <> -P0 and (P0 + P1) + P0 <> +-P1 => (P0 + P1) + (P0 + P1) = P0 + (P1 + (P0 + P1))

(defthm comp-10
  (eq$ (dbl$ (sum$ (p0$) (p1$)))
       (sum$ (p0$) (sum$ (p1$) (sum$ (p0$) (p1$)))))
  :rule-classes ())

;; [26.23 seconds}

(defthm lemma-18
  (implies (and (ecp p) (ecp q)
                (not (equal (ec+ p q) (ec- q)))
                (not (equal (ec+ q (ec+ p q)) p))
                (not (equal (ec+ q (ec+ p q)) (ec- p))))
           (equal (ec+ (ec+ p q) (ec+ p q))
                  (ec+ p (ec+ q (ec+ p q)))))
  :rule-classes ())

;; P0 + P1 = -P0 => P1 = -(P0 + P0)

(defun phi ()
  (let* ((s (sum$ (p0$) (p1$)))
         (u (car s))
         (z (caddr s)))
    `(- (expt (+ (- ,u (* x0 (expt ,z 2)))
                 (* 2 (* y0 y1)))
              2)
        (expt (* 2 (* y0 y1)) 2))))

(defun psi ()
  (let* ((s (sum$ (p0$) (p1$)))
         (d (dbl$ (p0$)))
         (zs (caddr s))
         (ud (car d))
         (zd (caddr d)))
    `(* (- ,ud (* x1 (expt ,zd 2)))
        (expt ,zs 2))))

(defthm comp-11
  (equal (reduce$ (phi))
         (reduce$ (psi)))
  :rule-classes ())

;; [0.01 seconds}

(defthm lemma-19
  (implies (and (ecp p) (ecp q)
                (equal (ec+ p q) (ec- p)))
           (equal q (ec- (ec+ p p))))
  :rule-classes ())

(defthm lemma-20
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r)))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ())

(defthm lemma-21
  (implies (and (ecp p) (ecp q))
           (equal (ec+ (ec+ p p) q)
                  (ec+ p (ec+ p q))))
  :rule-classes ())

;; (P0 + O) + (P0 + O) = P0 + P0 + P0

(defthm comp-12
  (eq$ (dbl$ (sum$ (p0$) (o$)))
       (dbl$ (p0$)))
  :rule-classes ())

;; [0.01 seconds]

;; (O + (P0 + O) = P0

(defthm comp-13
  (eq$ (sum$ (o$) (sum$ (p0$) (o$)))
       (p0$))
  :rule-classes ())

;; [0.00 seconds]

(defthm lemma-22
  (implies (ecp p)
           (equal (ec+ (ec+ p (o))
                       (ec+ p (o)))
                  (ec+ p (ec+ (o) (ec+ p (o))))))
  :rule-classes ())

(defthm ec-associativity
  (implies (and (ecp p) (ecp q) (ecp r))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ())
