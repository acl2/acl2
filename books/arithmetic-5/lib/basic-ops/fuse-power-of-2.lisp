; Fusing Powers of Two
; J Moore
; July, 2026

; Note: This book is not included in arithmetic-5/top or any other arithmetic-5
; book, despite its residing on a subdirectory of arithmetic-5.  It was developed
; with the intention of integrating it into arithmetic-5 but I decided it might be
; too disruptive because it would rearrange certain nests of products and thereby
; possibly removing targets of user's rewrite rules.

; Merriam-Webster Dictionary
; Definition: fuse (verb)

; sense 2:
; to blend thoroughly by or as if by melting: combine
; ``Particles are fused to form a new compound.''

; In this file I build a metafunction, named fuse-power-of-2, that combines
; powers of 2 constants with expt expressions with powers-of-2 bases.  I verify
; correctness and the well-formedness of the output.  The function is triggered
; by applications of the dummy function fuse-power-of-2-target, which is just
; another name for binary-*.  By introducing this dummy function I planned to
; change such lemmas as SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL so as to use
; fuse-power-of-2-target instead of binary-* when it rewrites an equation by
; multiplying both sides by some heuristically chosen x (if that x happens to
; be a power of 2).  That way the metafunction is not invoked on every binary-*
; expression the rewriter sees.  But, like I said above, I decided not to make
; this change.  Here is the metafunction in action.

; (and
;  (equal (fuse-power-of-2
;          '(fuse-power-of-2-target
;            '256
;            (binary-* a
;                      (binary-* (expt '2 i)
;                                (mod u v)))))
;         '(BINARY-* A
;                    (BINARY-* (EXPT '2 (BINARY-+ '8 I))
;                              (MOD U V))))
;  (equal (fuse-power-of-2
;          '(fuse-power-of-2-target
;            '1/256
;            (binary-* a
;                      (binary-* (expt '2 i)
;                                (mod u v)))))
;         '(BINARY-* A
;                    (BINARY-* (EXPT '2 (BINARY-+ '-8 I))
;                              (MOD U V))))
;  (equal (fuse-power-of-2
;          '(fuse-power-of-2-target
;            '1/256
;            (binary-* a
;                      (binary-* (expt '256 i)
;                                (mod u v)))))
;         '(BINARY-* A
;                    (BINARY-* (EXPT '2 (BINARY-+ '-8 (BINARY-* '8 I)))
;                              (MOD U V))))
;  (equal (fuse-power-of-2
;          '(fuse-power-of-2-target
;            '1/256
;            (binary-* a
;                      (binary-* (expt '1/256 i)
;                                (mod u v)))))
;         '(BINARY-* A
;                    (BINARY-* (EXPT '2 (BINARY-+ '-8 (BINARY-* '-8 I)))
;                              (MOD U V)))))

; Of course, this same idea could be extended to powers of arbitrary bases.
; E.g., (* 27 a (expt 81 n)) = (* a (expt 3 (+ 3 (* 4 n)))).  But base 2 is
; very important because of its role in the logical/arithmetic operators like
; logand and ash (via floor and mod) which are extensively supported by
; arithmetic-5.  See for example the special handling of base 2 in
; factor-pattern-gather-exponents which is used in the key lemma
; normalize-factors-gather-exponents.  So rather than first implementing the
; metafunction for arbitrary bases I decided to implement it only for base 2.

; Despite not using this book as part of arithmetic-5 I found its correctness
; and well-formedness theorems interesting enough to preserve, so I left it in
; this directory.

(in-package "ACL2")

(include-book "arithmetic-5/lib/basic-ops/building-blocks" :dir :system)

(encapsulate nil
  (local (include-book "arithmetic-5/lib/basic-ops/basic" :dir :system))
  (local (include-book "arithmetic-5/lib/basic-ops/simple-equalities-and-inequalities" :dir :system))
  (local (include-book "arithmetic-5/lib/basic-ops/expt" :dir :system))

  (defun positive-pow2p (x)
    (declare (xargs :guard t))
    (if (and (integerp x)
             (< 0 x))
        (or (= x 1)
            (and (integerp (/ x 2))
                 (positive-pow2p (/ x 2))))
        nil))

  (defun positive-pow2 (x)
    (declare (xargs :guard (positive-pow2p x)))
    (if (= x 1)
        0
        (if (mbt (positive-pow2p x))
            (+ 1 (positive-pow2 (/ x 2)))
            0)))

  (defthm expt-2-positive-pow2
    (implies (positive-pow2p x)
             (equal (expt 2 (positive-pow2 x)) x)))

  (defun pow2p (x)
    (declare (xargs :guard t))
    (cond
     ((natp x)
      (if (= x 0)
          nil
          (positive-pow2p x)))
     ((and (rationalp x)
           (< 0 x)
           (< x 1))
      (positive-pow2p (/ x)))
     (t nil)))

  (defun pow2 (x)
    (declare (xargs :guard (pow2p x)))
    (if (< x 1)
        (- (positive-pow2 (/ x)))
        (positive-pow2 x)))

  (defthm expt-2-pow2
    (implies (pow2p x)
             (equal (expt 2 (pow2 x)) x))
    :hints (("Goal"
             :use
             ((:instance |(/ (expt x n))|
                         (x 2)
                         (n (- (positive-pow2 (/ x))))))
             :in-theory (disable |(/ (expt x n))|))))
  )

(defun find-expt-pow2p-term (term)

; Term is expected to be a right-associated nest of BINARY-* terms, i.e., a
; ``linear list'' of factor terms glued together with BINARY-*.  We look for
; the first EXPT term along the ``spine'' in which the base of the EXPT is a
; power of 2.  If there is one, we return it.  Otherwise, we return nil.  For
; example, we return (EXPT '8 I) on the input
; (BINARY-* A
;           (BINARY-* (BINARY-* (EXPT 2 I)
;                               (EXPT 4 I))
;                     (EXPT '8 I)))

; Note that if term is not right-associated we may miss an ``earlier'' EXPT
; term.  But that won't affect soundness; we'll find it when this function is
; applied again after the term has been fully normalized.

; The reason we limit ourselves here to treating term as right-associated is so
; that we can easily find the identified EXPT expression later.  If we treated
; term as a binary tree of factors then when we replace it with another term
; we'd have to ensure that we only replace one occurrence.

  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term) nil)
        ((fquotep term)

; We don't consider, say, '256, to be an EXPT expression.  Since our caller,
; fuse-power-of-2, has already picked off the leading constant of its
; input and calls this function on the rest, we do not expect to find another
; constant.  If there is one, it will eventually be commuted to the front and
; folded later.

         nil)
        ((and (eq (ffn-symb term) 'EXPT)
              (quotep (fargn term 1))
              (or (eql (unquote (fargn term 1)) 2) ; optimization
                  (pow2p (unquote (fargn term 1))))
              (consp (cddr term)))
         term)
        ((eq (ffn-symb term) 'BINARY-*)
         (if (and (nvariablep (fargn term 1))
                  (not (fquotep (fargn term 1)))
                  (eq (ffn-symb (fargn term 1)) 'EXPT)
                  (quotep (fargn (fargn term 1) 1))
                  (or (eql (unquote (fargn (fargn term 1) 1)) 2) ; optimization
                      (pow2p (unquote (fargn (fargn term 1) 1))))
                  (consp (cddr (fargn term 1))))
             (fargn term 1)
             (find-expt-pow2p-term (fargn term 2))))
        (t nil)))

(defun is-a-factor-term (host term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((and (eq (ffn-symb term) 'expt)
              (equal term host))
         t)
        ((eq (ffn-symb term) 'BINARY-*)
         (if (equal (fargn term 1) host)
             t
             (is-a-factor-term host (fargn term 2))))
        (t nil)))

(defthm properties-of-find-expt-pow2p-term
  (implies (find-expt-pow2p-term term)
           (and (equal (ffn-symb (find-expt-pow2p-term term)) 'EXPT)
                (consp (fargn (find-expt-pow2p-term term) 1))
                (equal (ffn-symb (fargn (find-expt-pow2p-term term) 1)) 'QUOTE)
                (consp (cdr (fargn (find-expt-pow2p-term term) 1)))
                (pow2p (unquote (fargn (find-expt-pow2p-term term) 1)))
                (consp (cddr (find-expt-pow2p-term term)))
                (is-a-factor-term (find-expt-pow2p-term term) term)))

; The induct hint below is necessary due to the last conjunct in the
; conclusion.  Without the hint, we merge the inductions of
; find-expt-pow2p-term and is-a-factor-term.  If we omit the last conjunct we
; prove the theorem without help, and can prove the is-a-factor-term theorem
; subsequently without help.  But we thought it would be cool to have all the
; necessary properties in one place.

  :hints (("Goal" :induct (find-expt-pow2p-term term)))
  :rule-classes :forward-chaining)

(defun replace-host-with-expanded-expt-2 (host expanded-host term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term) term)
        ((fquotep term) term)
        ((and (eq (ffn-symb term) 'expt)
              (equal term host))
         expanded-host)
        ((eq (ffn-symb term) 'BINARY-*)
         (if (equal (fargn term 1) host)
             `(binary-* ,expanded-host ,(fargn term 2))
             `(binary-* ,(fargn term 1)
                        ,(replace-host-with-expanded-expt-2 host expanded-host
                                                           (fargn term 2)))))
        (t term)))

(in-theory (disable pow2p pow2))

; The following function will be used to mark targets of the metafunction.  We
; will disable it at the end of this book and it should remain disabled!

(defun fuse-power-of-2-target (x y) (* x y))

(defun fuse-power-of-2 (target)

; This is a metafunction.  Target is expected to be of the form:

; (FUSE-POWER-OF-2-TARGET '2^n y)

; where '2^n is some quoted power of two.  This function rewrites the product
; by finding a factor, called the ``host,'' in y that is of the form (expt '2^m
; k) and returns y with the host replaced by (expt '2 (+ n (* m k))).  Note
; that successful fusion results in a term without the fuse-power-of-2-target
; marker.

; If no such host is found, we return the target term, still marked with
; fuse-power-of-2-target.  

; The reason this metafunction rewrites a marked product is that we wish to
; encorporate this metafunction into arithmetic-5 but have it available only
; under the syntaxp hypotheses checking that we are to use Moore's ``new''
; version of that book and that we are gathering exponents.  But metafunction
; correctness theorems, which install metafunctions, cannot carry syntaxp hyps.
; If we made the metafunction an extended metafunction, thereby making mfc
; available, we could do the necessary checks on enabled runes, but we would
; have to verify the rather complicated guards of disabledp-fn.  So instead we
; provide, in the defthm deploy-fuse-power-of-2 below, a :rewrite rule that
; marks a product (leading with a power of two) with fuse-power-of-2-target,
; thus triggering this metafunction, and that :rewrite rule ignores the result
; and fails if it comes back still marked.

  (declare (xargs :guard (pseudo-termp target)))
  (cond
   ((and (consp target)
         (eq (ffn-symb target) 'fuse-power-of-2-target))
    (let ((c (fargn target 1))
          (y (fargn target 2)))
      (cond
       ((and (quotep c)
             (pow2p (unquote c)))
        (let ((host (find-expt-pow2p-term y)))
          (cond
           ((null host) target)

; We know that host is of the form (expt 'base &), where base is a power of 2.
; In the most common case base will be 2.  We know nothing about &!

           ((eql (unquote (fargn host 1)) 2)
            (replace-host-with-expanded-expt-2
             host
             `(EXPT '2 (BINARY-+ ',(pow2 (unquote c))
                                 (IFIX ,(fargn host 2))))
             y))
           (t (replace-host-with-expanded-expt-2
               host
               `(EXPT '2 (BINARY-+ ',(pow2 (unquote c))
                                   (BINARY-* ',(pow2 (unquote (fargn host 1)))
                                             (IFIX ,(fargn host 2)))))
               y)))))
       (t target))))
   (t target)))

(defevaluator eva eva-list
  ((expt r i)
   (binary-+ x y)
   (binary-* x y)
   (ifix x)
   (fuse-power-of-2-target c y)))

(encapsulate nil
  (local (include-book "arithmetic-5/lib/basic-ops/basic" :dir :system))
  (defthm eva-replace-host-with-expanded-expt-2
    (implies (and (is-a-factor-term host term)
                  (rationalp (eva host a))
                  (not (equal (eva host a) 0))
                  (rationalp (eva expanded-host a))
                  (not (equal (eva expanded-host a) 0)))
             (equal (eva (replace-host-with-expanded-expt-2 host expanded-host term) a)
                    (* (eva expanded-host a) (/ (eva term a) (eva host a)))))))

(defthm termp-find-expt-pow2p-term
  (implies (and (termp term w)
                (arities-okp '((expt . 2)
                               (binary-+ . 2)
                               (binary-* . 2)
                               (ifix . 1)
                               (fuse-power-of-2-target . 2))
                             w)
                (find-expt-pow2p-term term))
           (termp (find-expt-pow2p-term term) w)))

(defthm termp-replace-host-with-expanded-expt-2
  (implies (and (termp host w)
                (termp expanded-host w)
                (termp term w)
                (arities-okp '((expt . 2)
                               (binary-+ . 2)
                               (binary-* . 2)
                               (ifix . 1)
                               (fuse-power-of-2-target . 2))
                             w))
           (termp (replace-host-with-expanded-expt-2 host expanded-host term) w)))

(defthm termp-args-of-host
  (implies (and (termp host w)
                (eq (ffn-symb host) 'EXPT)
                (arities-okp '((expt . 2)
                               (binary-+ . 2)
                               (binary-* . 2)
                               (ifix . 1)
                               (fuse-power-of-2-target . 2))
                             w))
           (and (termp (fargn host 1) w)
                (termp (fargn host 2) w))))

(defthm logic-fnsp-replace-host-with-expanded-expt-2
  (implies (and (logic-fnsp host w)
                (logic-fnsp expanded-host w)
                (logic-fnsp term w)
                (arities-okp '((expt . 2)
                               (binary-+ . 2)
                               (binary-* . 2)
                               (ifix . 1)
                               (fuse-power-of-2-target . 2))
                             w))
           (logic-fnsp (replace-host-with-expanded-expt-2 host expanded-host term) w)))

(defthm logic-fnsp-find-expt-pow2p-term
  (implies (and (logic-fnsp term w)
                (arities-okp '((expt . 2)
                               (binary-+ . 2)
                               (binary-* . 2)
                               (ifix . 1)
                               (fuse-power-of-2-target . 2))
                             w))
           (logic-fnsp (find-expt-pow2p-term term) w)))

(defthm logic-fnsp-args-of-host
  (implies (and (logic-fnsp host w)
                (eq (ffn-symb host) 'EXPT)
                (arities-okp '((expt . 2)
                               (binary-+ . 2)
                               (binary-* . 2)
                               (ifix . 1)
                               (fuse-power-of-2-target . 2))
                             w))
           (and (logic-fnsp (fargn host 1) w)
                (logic-fnsp (fargn host 2) w))))

(defthm fuse-power-of-2-is-well-formed
  (implies (and (logic-termp term w)
                (arities-okp '((expt . 2)
                               (binary-+ . 2)
                               (binary-* . 2)
                               (ifix . 1)
                               (fuse-power-of-2-target . 2))
                             w))
           (logic-termp (fuse-power-of-2 term) w))
  :rule-classes nil)

; These lemmas would cause arithmetic-5 to loop and so they are
; kept local to this book.

(local
 (encapsulate nil
   (local (include-book "arithmetic-5/lib/basic-ops/basic" :dir :system))
   (local (include-book "arithmetic-5/lib/basic-ops/expt" :dir :system))
   (defthm lemma1
     (implies (and (force (integerp a))
                   (force (integerp b)))
              (equal (expt 2 (+ a b))
                     (* (expt 2 a)
                        (expt 2 b)))))
   (defthm lemma2
     (implies (and (force (integerp a))
                   (force (integerp b)))
              (equal (expt 2 (* a b))
                     (expt (expt 2 a) b))))
   (defthm lemma3
     (implies (and (force (acl2-numberp b))
                   (force (not (equal b 0))))
              (equal (* a (/ b) c b)
                     (* a c)))
     :hints (("Goal"
              :use (:instance |(* a (/ a) b)| (x b)(y (* a c)))
              :in-theory (disable |(* a (/ a) b)|))))))

(defthm correctness-of-fuse-power-of-2
  (implies (alistp a)
           (equal (eva term a)
                  (eva (fuse-power-of-2 term) a)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (pow2p)
                           (properties-of-find-expt-pow2p-term))
           :use ((:instance properties-of-find-expt-pow2p-term
                            (term (caddr term))))))
  :rule-classes ((:meta :trigger-fns (fuse-power-of-2-target)
                        :well-formedness-guarantee fuse-power-of-2-is-well-formed)))

; Here is the :rewrite rule that marks a potential target, conditionally on
; the status of two runes.

(defthm deploy-fuse-power-of-2
  (implies (and (syntaxp
                 (not (disabledp-fn '(:e use-new-arith-5-rules)
                                    (access rewrite-constant
                                            (access metafunction-context mfc :rcnst)
                                            :current-enabled-structure)
                                    (w state))))
                (syntaxp
                 (not (disabledp-fn 'NORMALIZE-FACTORS-GATHER-EXPONENTS
                                    (access rewrite-constant
                                            (access metafunction-context mfc :rcnst)
                                            :current-enabled-structure)
                                    (w state))))
                (syntaxp (and (quotep c)
                              (pow2p (unquote c))))
; Mark the target, rewrite it (which invokes our metafunction, and bind rewritten
; term to the result.
                (equal rewritten-term
                       (fuse-power-of-2-target c y))
; Check whether the metafunction actually succeeded.
                (syntaxp (not (and (consp rewritten-term)
                                   (eq (car rewritten-term)
                                       'fuse-power-of-2-target)))))
           (equal (* c y)
                  rewritten-term)))

; This is an important last step! 

(in-theory (disable fuse-power-of-2-target))
