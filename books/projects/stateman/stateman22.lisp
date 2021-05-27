; Copyright (C) 2014, ForrestHunt, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Symbolic State Management -- Version 22
; J Strother Moore
; Fall/Winter, 2014/2015
; Georgetown, TX and Edinburgh, Scotland
;
; (ld "stateman22.lisp" :ld-pre-eval-print t)
; (certify-book "stateman22")

(in-package "SMAN")

; Matt K.: Avoid ACL2(p) error (type error during hons-copy)
(set-waterfall-parallelism nil)

(set-state-ok t)

(defmacro hlist (&rest x) (xxxjoin 'hons (append x '(nil))))

; -----------------------------------------------------------------

; We define and verify an abstract interpreter for certain arithmetic
; expressions that computes the ``value'' of an expression as a Tau interval.

; Signature:
; (AINNI term ...) ==> (mv flg hyps int)

; where: term is a term; flg indicates whether we were able to compute a
; suitable interval; when flg is non-nil, hyps is the list of hypotheses which
; must hold and int is a Tau interval (over the naturals) known to contain all
; possible values of term (under those hypotheses).

(include-book "byte-addressed-state")

(include-book "tau/bounders/elementary-bounders" :dir :system)

(include-book "tools/mv-nth" :dir :system)

(in-theory (disable mod floor ash logior logxor)) ; these disables were inherited from the b-code5x-reduced days

; -----------------------------------------------------------------

(encapsulate
 nil
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm commutivity-2-of-+
   (equal (+ x y z) (+ y x z)))

 (defthm mod-+-*-8
   (implies (and (natp a)
                 (natp b))
            (equal (mod (+ a (* 8 b)) 8)
                   (mod a 8))))

 (defthm integerp-mod
   (implies (and (integerp x) (integerp y))
            (integerp (mod x y)))
   :rule-classes (:rewrite :type-prescription))

 (defthm mod-8-separation
   (implies (and (integerp addr1)
                 (integerp addr2)
                 (<= 0 addr1)
                 (<= addr1 addr2)
                 (< addr2 (+ 8 addr1))
                 (equal (mod addr1 8) 0)
                 (equal (mod addr2 8) 0))
            (equal addr2 addr1))
   :rule-classes nil))

(defevaluator stateman-eval stateman-eval-lst
  ((IFIX x)
   (NOT p)
   (< x y)
   (IF x y z)
   (BINARY-+ x y)
   (BINARY-* x y)
   (UNARY-- x)
   (HIDE x)
   (FORCE x)


   (MOD x y)
   (ASH x i)
   (BINARY-LOGAND x y)
   (BINARY-LOGXOR x y)
   (BINARY-LOGIOR x y)

   (I st)
   (!I val st)
   (S st)
   (!S val st)
   (R ma sz st)
   (!R ma sz val st)))

(defmacro ainni-let* (bindings body)
; This is a very unsafe macro.  It binds flg and hyps and it assumes hyps is
; used in body.
  (cond
   ((endp bindings) body)
   (t `(mv-let (flg hyps ,(car (car bindings)))
               ,(cadr (car bindings))
               (if flg
                   (ainni-let* ,(cdr bindings) ,body)
                   (mv nil nil nil))))))

(defmacro ainni-value (body)
  `(mv t hyps ,body))

; these terms are handled by bit-width -- all the fns except r are handled by elementary-bounders

; * 'k, where k is a natural
; * (R addr 'k st), where k is a natural and 0 < k <= 8
; * (MOD x 'k), where M:x and k is a non-negative power of 2
; * (ASH x 'i), where M:x and i is an integer
; * (LOGAND x y), where M:x,y
; * (LOGIOR x y), where M:x,y
; * (LOGXOR x y), where M:x,y

(defun find-inclusive-natp-lower-bound-from-<-on-type-alist (term type-alist)

  (declare (xargs :guard (type-alistp type-alist)))

; WE ASSUME THE VALUE OF TERM IS A NATURAL and we look at type-alist to find
; the initial lower bound.  Do not call this function on a term that is not of
; ``type'' NATP!  We convert the assumption (< 'c term) to (<= 'c+1 term),
; which is not legal if term is merely a RATIONALP.  This particular conversion
; is legal for INTEGERP terms but we also assume (when searching for
; non-equalities excluding certain bounds) that term is bounded below by 0.

; Some relevant facts about the type-alist: <= is a macro and won't be found on
; the type-alist.  Lower bound entries on x are either (< 'c x) assumed true or
; (< x 'c) assumed false.  The implied bound in the former caseis c+1 and in
; the latter is c -- assuming c and x are natural valued.  Furthermore, the
; first lower bound entry on the type-alist has the largest lower bound assumed
; for x.  (There may be other lower bound entries for x on the type-alist, but
; they will be for smaller bounds that have been shadowed out but not removed.)

; Note: The bound found here is only preliminary.  We will go back to the
; type-alist in a separate function and may push the bound up by using
; non-equalities we find.  More on this in a moment.

  (cond
   ((endp type-alist) nil)
   ((and (consp (car (car type-alist)))
         (eq (ffn-symb (car (car type-alist))) '<))
    (cond
     ((and (equal (fargn (car (car type-alist)) 1) term)
           (quotep (fargn (car (car type-alist)) 2))
           (natp (cadr (fargn (car (car type-alist)) 2)))
           (equal (cadr (car type-alist)) *ts-nil*))

; Found (< term 'c) assumed false, so this entry suggests the lower bound of c.

      (cadr (fargn (car (car type-alist)) 2)))
     ((and (equal (fargn (car (car type-alist)) 2) term)
           (quotep (fargn (car (car type-alist)) 1))
           (natp (cadr (fargn (car (car type-alist)) 1)))
           (ts= (cadr (car type-alist)) *ts-t*))

; Found (< 'c term) assumed true, so this entry suggests the lower bound of c+1

      (+ 1 (cadr (fargn (car (car type-alist)) 1))))
     (t (find-inclusive-natp-lower-bound-from-<-on-type-alist term (cdr type-alist)))))
   (t (find-inclusive-natp-lower-bound-from-<-on-type-alist term (cdr type-alist)))))

; Suppose we have found that the upper bound on term is 27, e.g., by finding
; the equivalent of (<= 27 term) assumed true on the type-alist.  Next, we look
; for (NOT (EQUAL term 27)) assumed true, using not-equal-term-c-p below.  If
; we find it, the lower bound can be pushed up to 28, and we repeat until we
; don't find a suitable non-equality.

(defun not-equal-term-c-p (term c type-alist)

; Is (EQUAL term 'c) assumed false on type-alist?

  (declare (xargs :guard (type-alistp type-alist)))
  (cond
   ((endp type-alist) nil)
   ((and (ts= (cadr (car type-alist)) *ts-nil*)
         (consp (car (car type-alist)))
         (eq (ffn-symb (car (car type-alist))) 'EQUAL)
         (equal (fargn (car (car type-alist)) 1) term)
         (quotep (fargn (car (car type-alist)) 2))
         (equal (cadr (fargn (car (car type-alist)) 2)) c))
    t)
   (t (not-equal-term-c-p term c (cdr type-alist)))))

; Termination of the search described above, pushing the lower bound up one by
; one via non-equalities, is problematic!  There are only a finite number of
; non-equalities of term with natural constants on the type-alist and so there
; is a maximal such constant.  Everytime we recur we push the bound closer to
; this maximal constant.

(defun maximal-not-equal-term-nat (term type-alist)

; We search up type-alist for an assumption of the form (NOT (EQUAL term 'n))
; where n is a natural.  We return the largest such n we find.  We are assuming
; that term always returns a natural.  So if we exhaust the type-alist, we can
; pretend we found (NOT (EQUAL term '-1)).

  (declare (xargs :guard (type-alistp type-alist)))
  (cond
   ((endp type-alist) -1)
   ((and (ts= (cadr (car type-alist)) *ts-nil*)
         (consp (car (car type-alist)))
         (eq (ffn-symb (car (car type-alist))) 'EQUAL)
         (equal (fargn (car (car type-alist)) 1) term)
         (quotep (fargn (car (car type-alist)) 2))
         (natp (cadr (fargn (car (car type-alist)) 2))))
    (let ((c1 (cadr (fargn (car (car type-alist)) 2)))
          (c2 (maximal-not-equal-term-nat term (cdr type-alist))))
      (cond
       ((<= c2 c1) c1)
       (t c2))))
   (t (maximal-not-equal-term-nat term (cdr type-alist)))))

(encapsulate
 nil
 (local
  (defthm improve-inclusive-natp-lower-bound-lemma1
    (implies (and (NOT-EQUAL-TERM-C-P TERM C TYPE-ALIST)
                  (natp c))
             (<= C (MAXIMAL-NOT-EQUAL-TERM-NAT TERM TYPE-ALIST)))
    :rule-classes :linear))

 (defun improve-inclusive-natp-lower-bound (term c type-alist)

; We know that type-alist implies (<= 'c term), where c is a natural and is the
; largest such bound found in any assumed < for term in type-alist.  We now try
; to improve (raise) c still further by looking for (EQUAL term c) assumed
; false.  That is, it is possible that the type-alist constains (< term '7)
; assumed false -- meaning (<= 7 term) is true -- but also contains (equal term
; '7) and (equal term '8) assumed false -- meaning term is neither 7 or 8.  In
; this example, the bound of 9 is implied.

   (declare (xargs :measure (nfix (- (+ 1 (maximal-not-equal-term-nat term type-alist))
                                     (nfix c)))
                   :guard (type-alistp type-alist)))
   (cond ((not (natp c)) 0)
         ((not-equal-term-c-p term c type-alist)
          (improve-inclusive-natp-lower-bound term (+ 1 c) type-alist))
         (t c))))

(defun find-largest-inclusive-natp-lower-bound (term type-alist)

; WE ASSUME THE VALUE OF TERM IS A NATURAL.  Do not call this function on a
; term that is not of ``type'' NATP!

  (declare (xargs :guard (type-alistp type-alist)))
  (let ((c (find-inclusive-natp-lower-bound-from-<-on-type-alist term type-alist)))
    (cond
     (c (improve-inclusive-natp-lower-bound term c type-alist))
     (t nil))))

#||
; For example,

(find-largest-inclusive-natp-lower-bound
 'x
 '(((EQUAL X '28) 64)
   ((EQUAL X '27) 64)
   (X 38)
   ((< X '27) 64)))
; ==> 29
||#

(defun find-inclusive-natp-upper-bound-from-<-on-type-alist (term type-alist)

; WE ASSUME THE VALUE OF TERM IS A NATURAL.  Do not call this function on a
; term that is not of ``type'' NATP!  See the comments in
; find-inclusive-natp-lower-bound-from-<-on-type-alist for the spec of the
; symmetric function.

  (declare (xargs :guard (type-alistp type-alist)))
  (cond
   ((endp type-alist) nil)
   ((and (consp (car (car type-alist)))
         (eq (ffn-symb (car (car type-alist))) '<))
    (cond
     ((and (equal (fargn (car (car type-alist)) 2) term)
           (quotep (fargn (car (car type-alist)) 1))
           (natp (cadr (fargn (car (car type-alist)) 1)))
           (equal (cadr (car type-alist)) *ts-nil*))

; Found (< 'c term) assumed false, so this entry suggests the upper bound of c.

      (cadr (fargn (car (car type-alist)) 1)))
     ((and (equal (fargn (car (car type-alist)) 1) term)
           (quotep (fargn (car (car type-alist)) 2))
           (integerp (cadr (fargn (car (car type-alist)) 2)))
           (< 0 (cadr (fargn (car (car type-alist)) 2)))
           (ts= (cadr (car type-alist)) *ts-t*))

; Found (< term 'c) assumed true, so this entry suggests the upper bound of c-1

      (- (cadr (fargn (car (car type-alist)) 2)) 1))
     (t (find-inclusive-natp-upper-bound-from-<-on-type-alist term (cdr type-alist)))))
   (t (find-inclusive-natp-upper-bound-from-<-on-type-alist term (cdr type-alist)))))

(defun improve-inclusive-natp-upper-bound (term c type-alist)

; We know that type-alist implies (<= 'c term), where c is a natural and is the
; largest such bound found in any assumed < for term in type-alist.  We now try
; to improve (raise) c still further by looking for (EQUAL term c) assumed
; false.  That is, it is possible that the type-alist constains (< term '7)
; assumed false -- meaning (<= 7 term) is true -- but also contains (equal term
; '7) and (equal term '8) assumed false -- meaning term is neither 7 or 8.  In
; this example, the bound of 9 is implied.

  (declare (xargs :guard (and (natp c) (type-alistp type-alist))))
  (cond ((zp c) 0)
        ((not-equal-term-c-p term c type-alist)
         (improve-inclusive-natp-upper-bound term (- c 1) type-alist))
        (t c)))

(defun find-smallest-inclusive-natp-upper-bound (term type-alist)
; WE ASSUME THE VALUE OF TERM IS A NATURAL.  Do not call this function on a
; term that is not of ``type'' NATP!

  (declare (xargs :guard (type-alistp type-alist)))
  (let ((c (find-inclusive-natp-upper-bound-from-<-on-type-alist term type-alist)))
    (cond
     (c (improve-inclusive-natp-upper-bound term c type-alist))
     (t nil))))

#||
; For example,

(find-smallest-inclusive-natp-upper-bound
 'x
 '(((EQUAL X '28) 64)
   ((EQUAL X '27) 64)
   (X 38)
   ((< '28 X) 64)))
; ==> 26
||#

(defun tau-interval-r (term hyps type-alist)

; Term is of the form (R a 'n b), where n is a natural.  Hyps and type-alist
; are the list of hyps we assume are true and type-alist is the governing
; type-alist.  We return (mv flg hyps' interval), where flg is t or nil and t
; indicates that interval is an INTEGERP tau-interval containing the value of
; term, provided hyps' are all true.  If flg is nil, the other values are nil
; and indicates that we found a contradiction on the type-alist, namely, that
; the assumed or known-from-type-prescriptions lower bound is above the upper
; bound.

  (declare (xargs :guard (and (pseudo-termp term)
                              (nvariablep term)
                              (eq (ffn-symb term) 'R)
                              (quotep (fargn term 2))
                              (natp (cadr (fargn term 2)))
                              (true-listp hyps)
                              (type-alistp type-alist))))
  (let* ((n (cadr (fargn term 2)))
         (lo (or (find-largest-inclusive-natp-lower-bound term type-alist) 0))
         (hyps (if (equal lo 0)
                   hyps ; no new hyp req'd because of :type-prescription
                   (add-to-set-equal (hlist 'FORCE
                                            (hlist 'NOT (hlist '< term (hlist 'QUOTE lo))))
                                     hyps)))
         (hi1 (find-smallest-inclusive-natp-upper-bound term type-alist))
         (hi (if (null hi1)
                 (- (expt 256 n) 1)
                 (min hi1
                      (- (expt 256 n) 1))))
         (hyps (if (null hi1)
                   hyps ; no new hyp req'd because of :type-prescription
                   (add-to-set-equal (hlist 'FORCE
                                            (hlist 'NOT (hlist '< (hlist 'QUOTE hi) term)))
                                     hyps))))
    (cond
     ((<= lo hi)
      (mv t
          hyps
          (make-tau-interval 'integerp nil lo nil hi)))
     (t

; If lo > hi, then there is a contradiciton on the type-alist.  We fail and hope
; that the theorem prover notices the contradiction!

      (mv nil nil nil)))))

(defthm tau-interval-r-correct-lemma-1
  (implies (and (pseudo-termp term)
                (eq (ffn-symb term) 'r)
                (quotep (fargn term 2))
                (natp (cadr (fargn term 2)))
                (member-equal
                 (list 'force
                       (list 'not
                             (list '< (list 'quote upper-bound) term)))
                 hyps)
                (natp upper-bound)
                (stateman-eval (conjoin hyps) alist))
           (<= (R (STATEMAN-EVAL (CADR TERM) ALIST)
                    (cadr (fargn term 2))
                    (STATEMAN-EVAL (CADDDR TERM) ALIST))
               upper-bound)))

(defthm properties-of-expt
  (implies (and (natp b)
                (< 0 b)
                (natp n))
           (and (integerp (expt b n))
                (< 0 (expt b n))))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (and (natp b)(< 0 b)(natp n)) (integerp (expt b n))))
   (:linear :corollary
            (implies (and (natp b)(< 0 b)(natp n)) (< 0 (expt b n))))))

(defthm tau-interval-r-correct-lemma-2
  (implies (and (pseudo-termp term)
                (eq (ffn-symb term) 'r)
                (quotep (fargn term 2))
                (natp (cadr (fargn term 2)))
                (member-equal
                 (list 'force
                       (list
                        'not
                        (list '< term (list 'quote lower-bound))))
                 hyps)
                (natp lower-bound)
                (stateman-eval (conjoin hyps) alist))
           (<= lower-bound
               (R (STATEMAN-EVAL (CADR TERM) ALIST)
                    (cadr (fargn term 2))
                    (STATEMAN-EVAL (CADDDR TERM) ALIST)))))

; This goes through but the corollaries aren't really corollaries!  Notice the
; missing stateman-eval hyp!!!

(defthm tau-interval-r-correct
  (implies (and (pseudo-termp term)
                (eq (ffn-symb term) 'R)
                (quotep (fargn term 2))
                (natp (cadr (fargn term 2)))
                (mv-nth 0 (tau-interval-r term hyps type-alist))
                (stateman-eval (conjoin (mv-nth 1 (tau-interval-r term hyps type-alist))) alist))
           (and (tau-intervalp (mv-nth 2 (tau-interval-r term hyps type-alist)))
                (equal (tau-interval-dom (mv-nth 2 (tau-interval-r term hyps type-alist)))
                       'integerp)
                (tau-interval-lo (mv-nth 2 (tau-interval-r term hyps type-alist)))
                (tau-interval-hi (mv-nth 2 (tau-interval-r term hyps type-alist)))
                (<= 0 (tau-interval-lo (mv-nth 2 (tau-interval-r term hyps type-alist))))
                (in-tau-intervalp (r (stateman-eval (cadr term) alist)
                                       (cadr (caddr term))
                                       (stateman-eval (cadddr term) alist))
                                  (mv-nth 2 (tau-interval-r term hyps type-alist)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (pseudo-termp term)
                  (eq (ffn-symb term) 'R)
                  (quotep (fargn term 2))
                  (natp (cadr (fargn term 2)))
                  (mv-nth 0 (tau-interval-r term hyps type-alist)))
             (and (tau-intervalp (mv-nth 2 (tau-interval-r term hyps type-alist)))
                  (equal (tau-interval-dom (mv-nth 2 (tau-interval-r term hyps type-alist)))
                         'integerp)
                  (tau-interval-lo (mv-nth 2 (tau-interval-r term hyps type-alist)))
                  (tau-interval-hi (mv-nth 2 (tau-interval-r term hyps type-alist))))))
   (:rewrite
    :corollary
    (implies (and (pseudo-termp term)
                  (eq (ffn-symb term) 'R)
                  (quotep (fargn term 2))
                  (natp (cadr (fargn term 2)))
                  (mv-nth 0 (tau-interval-r term hyps type-alist))
                  (stateman-eval (conjoin (mv-nth 1 (tau-interval-r term hyps type-alist))) alist))
             (in-tau-intervalp (r (stateman-eval (cadr term) alist)
                                    (cadr (caddr term))
                                    (stateman-eval (cadddr term) alist))
                               (mv-nth 2 (tau-interval-r term hyps type-alist)))))
   (:linear
    :corollary
    (implies (and (pseudo-termp term)
                  (eq (ffn-symb term) 'R)
                  (quotep (fargn term 2))
                  (natp (cadr (fargn term 2)))
                  (mv-nth 0 (tau-interval-r term hyps type-alist)))
             (<= 0 (tau-interval-lo (mv-nth 2 (tau-interval-r term hyps type-alist))))))
   (:type-prescription
    :corollary
    (implies (and (pseudo-termp term)
                  (eq (ffn-symb term) 'R)
                  (quotep (fargn term 2))
                  (natp (cadr (fargn term 2)))
                  (mv-nth 0 (tau-interval-r term hyps type-alist)))
             (natp (tau-interval-lo (mv-nth 2 (tau-interval-r term hyps type-alist))))))
   (:type-prescription
    :corollary
    (implies (and (pseudo-termp term)
                  (eq (ffn-symb term) 'R)
                  (quotep (fargn term 2))
                  (natp (cadr (fargn term 2)))
                  (mv-nth 0 (tau-interval-r term hyps type-alist)))
             (natp (tau-interval-hi (mv-nth 2 (tau-interval-r term hyps type-alist))))))))

(defun distributed-difference (term)
  (declare (xargs :guard t))
  (case-match term
    (('BINARY-+ ('BINARY-* ('QUOTE c) x) ('BINARY-* ('QUOTE c) ('UNARY-- y)))
     (mv t c x y))
    (('BINARY-+ ('BINARY-* ('QUOTE c) ('UNARY-- y)) ('BINARY-* ('QUOTE c) x))
     (mv t c x y))
    (('BINARY-+ x ('UNARY-- y))
     (mv t 1 x y))
    (('BINARY-+ ('UNARY-- y) x)
     (mv t 1 x y))
    (& (mv nil nil nil nil))))

(defthm pseudo-termp-distributed-difference-2
  (implies (and (pseudo-termp term)
                (mv-nth 0 (distributed-difference term)))
           (pseudo-termp
            (mv-nth 2 (distributed-difference term))))
  :rule-classes (:rewrite :type-prescription))

(defthm pseudo-termp-distributed-difference-3
  (implies (and (pseudo-termp term)
                (mv-nth 0 (distributed-difference term)))
           (pseudo-termp
            (mv-nth 3 (distributed-difference term))))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))

; In a world without arithmetic-5, the normal form of (* a (- b c)) is (+ (* a
; b) (* a (- c))).  But in a world with arithmetic-5, the normal form is (+ (*
; a b) (- (* a c))) which could be written (- (* a b) (* a c)).  The lemma we
; prove below rewrites (stateman-eval term alist), for distributed-difference
; terms, into the normal form for worlds without arithmetic-5.  Of course, if
; arithmetic-5 is available, that form will be converted to the other.

 (defthm stateman-eval-distributed-difference
   (implies (and (pseudo-termp term)
                 (mv-nth 0 (distributed-difference term))
                 (natp (mv-nth 1 (distributed-difference term))))
            (equal (stateman-eval term alist)
                   (+ (* (mv-nth 1 (distributed-difference term))
                         (stateman-eval
                          (mv-nth 2 (distributed-difference term))
                          alist))
                      (* (mv-nth 1 (distributed-difference term))
                         (- (stateman-eval
                             (mv-nth 3 (distributed-difference term))
                             alist))))))))

(defun ainni (term hyps type-alist)

; Term is a natural-valued term.  However, as the code stands right now it may
; only use quoted integers [virtually all of which must in fact be naturals as
; described below] and the following function symbols: BINARY-+, BINARY-*,
; UNARY-- (but only as part of a natural-number-difference), MOD,
; BINARY-LOGAND, BINARY-LOGIOR, BINARY-LOGXOR, ASH, and R.  The second
; argument of ASH must be a quoted integer and may be negative.  Otherwise, all
; quoted constants must be nats.  R expressions must have a quoted natural as
; the sz argument and the other two arguments may be arbitrary.  Note that all
; variables occurring in term must occur within those two arguments of the R
; expressions!

; Hyps is a list of hypotheses to be relieved in order for the answer to hold
; under type-alist.

; We return (mv flg hyps tau-interval) where flg is boolean with T indicating
; that an answer was found and nil indicating that we can't deduce anything
; about term.  In the latter case, the returned hyps and interval are nil.
; When flg is T, hyps is the list of hypotheses to relieve and interval is a
; tau interval such that (in-tau-intervalp term tau-interval) is true under
; type-alist.

  (declare (xargs
            :hints (("Goal" :in-theory (enable distributed-difference)))
            :guard (and (pseudo-termp term)
                        (pseudo-term-listp hyps)
                        (type-alistp type-alist))
            :verify-guards nil))
  (cond
   ((variablep term)

; In this case, as well as in the unrecognized function symbol case at the end
; of this cond, we could go to the type-alist and look for lower and upper
; bounds.  For the variable case that wouldn't be a bad idea, except that in
; our intended application of this book variables never arise outside R
; expressions so it's an improvement that gains nothing.  In the unrecognized
; fn case, we'd have to figure out how to handle built-in type-prescription
; rules of the sort we handle for R, i.e., we know that R always has a
; lower bound of 0.  Thus, not only would we never find it on the type-alist
; but we exploit in computing our answer.  In addition, we would have to ensure
; that term is NATP since that is a precondition of calling the
; find-largest[smallest]-inclusive-natp-lower[upper]-bound functions.  Again,
; that could be done by searching the type-alist for a natp term entry, but it
; would be subject to the same problem with any built-in type-prescription
; rules which would remove any such assumption.  Rather than solve the problems,
; we just claim no knowledge of the bounds of term.

    (mv nil nil nil))
   ((fquotep term)
    (cond
     ((natp (cadr term))
      (ainni-value (make-tau-interval 'integerp nil (cadr term) nil (cadr term))))
     (t (mv nil nil nil))))
   ((eq (ffn-symb term) 'BINARY-+)

; We recognize the special form (+ (* c x) (* c (- y))) and treat it like (* c
; (- x y)).  There is no predefined ``tau-bounder-minus'' so we basically code
; it here.  For simplicity, we insist here that c is a natural quoted constant.

    (mv-let
     (differencep c x y)
     (distributed-difference term)
     (cond
      (differencep

; Term is of the form (* 'c (- x y)), but we additionally insist that c is an
; integer greater than 0.  (It would not surprise me if c=0 works but the proof
; breaks.  Furthermore, c=0 will never arise because (* 0 x) will always be
; simplified away.)

       (cond
        ((not (and (integerp c) (< 0 c)))
         (mv nil nil nil))
        (t
         (ainni-let*
          ((intx (ainni x hyps type-alist))
           (inty (ainni y hyps type-alist)))
          (let ((lo (* c
                       (max (- (tau-interval-lo intx)
                               (tau-interval-hi inty))
                            0)))
                (hi (* c (- (tau-interval-hi intx)
                            (tau-interval-lo inty)))))
            (cond ((< hi lo) (mv nil nil nil))
                  (t (mv t
                         (add-to-set-equal (hlist 'FORCE (hlist 'NOT (hlist '< x y)))
                                           hyps)
                         (make-tau-interval 'integerp nil lo nil hi)))))))))
      (t
       (ainni-let*
        ((int1 (ainni (fargn term 1) hyps type-alist))
         (int2 (ainni (fargn term 2) hyps type-alist)))
        (ainni-value (tau-bounder-+ int1 int2)))))))
   ((eq (ffn-symb term) 'HIDE)
    (ainni (fargn term 1) hyps type-alist))
   ((eq (ffn-symb term) 'BINARY-*)
    (ainni-let*
     ((int1 (ainni (fargn term 1) hyps type-alist))
      (int2 (ainni (fargn term 2) hyps type-alist)))
     (ainni-value (tau-bounder-* int1 int2))))
   ((eq (ffn-symb term) 'MOD)
    (ainni-let*
     ((int1 (ainni (fargn term 1) hyps type-alist))
      (int2 (ainni (fargn term 2) hyps type-alist)))
     (ainni-value (tau-bounder-mod int1 int2))))
   ((eq (ffn-symb term) 'BINARY-LOGAND)
    (ainni-let*
     ((int1 (ainni (fargn term 1) hyps type-alist))
      (int2 (ainni (fargn term 2) hyps type-alist)))
     (ainni-value (tau-bounder-logand int1 int2))))
   ((eq (ffn-symb term) 'BINARY-LOGIOR)
    (ainni-let*
     ((int1 (ainni (fargn term 1) hyps type-alist))
      (int2 (ainni (fargn term 2) hyps type-alist)))
     (ainni-value (tau-bounder-logior int1 int2))))
   ((eq (ffn-symb term) 'BINARY-LOGXOR)
    (ainni-let*
     ((int1 (ainni (fargn term 1) hyps type-alist))
      (int2 (ainni (fargn term 2) hyps type-alist)))
     (ainni-value (tau-bounder-logxor int1 int2))))
   ((eq (ffn-symb term) 'ASH)
; We require the 2nd arg of ASH to be an integer constant but allow that
; constnat to be negative.
    (cond
     ((and (quotep (fargn term 2))
           (integerp (cadr (fargn term 2))))
      (let ((int2 (make-tau-interval 'integerp
                                     nil (cadr (fargn term 2))
                                     nil (cadr (fargn term 2)))))
        (ainni-let*
         ((int1 (ainni (fargn term 1) hyps type-alist)))
         (ainni-value (tau-bounder-ash int1 int2)))))
     (t (mv nil nil nil))))
   ((eq (ffn-symb term) 'R)

    (cond
     ((and (quotep (fargn term 2))
           (natp (cadr (fargn term 2))))

; We need lower and upper bounds on (R a 'k st).  There is a
; type-prescription that tells us 0 <= (R a 'k st) <= (256^k)-1, so no
; additional hyps are necessary if those are our respective bounds.  But if we
; use different bounds, we extend hyps to record the necessary assumptions.
; Rather than recover the exact literals from the type-alist entries used, we
; just generate the inequalities that we've deduced.  I.e., if we change the
; lower bound to 5 because we find the equivalents of (<= 4 (R a 'k st)) and
; (NOT (EQUAL (R a 'k st) 4)) on the type-alist, we generate the new hyp (<=
; 5 (R a 'k st)) rather than add the two literals we actually used from the
; type-alist.  We believe that the derived literal will be easily proved by
; linear.

      (tau-interval-r term hyps type-alist))
     (t (mv nil nil nil))))
   (t

; Unrecognized function symbol: See the large comment on the variable case at
; the top of this cond.

    (mv nil nil nil))))

(in-theory (disable distributed-difference))

(defthm ainni-correct-part-1
  (implies (and (pseudo-termp term)
                (pseudo-term-listp hyps))
           (pseudo-term-listp (mv-nth 1 (ainni term hyps type-alist))))
  :hints
  (("Goal" :in-theory
    (disable tau-bounder-+
             tau-bounder-*
;             tau-bounder--
             tau-bounder-logand
             tau-bounder-logior
             tau-bounder-logxor
             tau-bounder-ash
             make-tau-interval
             find-largest-inclusive-natp-lower-bound
             find-smallest-inclusive-natp-upper-bound))))

(defthm natp-tau-bounder-+
  (IMPLIES (AND (tau-intervalp int1)
                (equal (tau-interval-dom int1) 'integerp)
                (tau-interval-lo int1)
                (tau-interval-hi int1)
                (<= 0 (tau-interval-lo int1))
                (tau-intervalp int2)
                (equal (tau-interval-dom int2) 'integerp)
                (tau-interval-lo int2)
                (tau-interval-hi int2)
                (<= 0 (tau-interval-lo int2)))
           (and (tau-intervalp (TAU-BOUNDER-+ INT1 INT2))
                (equal (tau-interval-dom (TAU-BOUNDER-+ INT1 INT2))
                       'integerp)
                (tau-interval-lo (TAU-BOUNDER-+ INT1 INT2))
                (tau-interval-hi (TAU-BOUNDER-+ INT1 INT2))
                (<= 0 (tau-interval-lo (TAU-BOUNDER-+ INT1 INT2)))))
  :rule-classes
  ((:rewrite
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (and (tau-intervalp (TAU-BOUNDER-+ INT1 INT2))
                  (equal (tau-interval-dom (TAU-BOUNDER-+ INT1 INT2))
                         'integerp)
                  (tau-interval-lo (TAU-BOUNDER-+ INT1 INT2))
                  (tau-interval-hi (TAU-BOUNDER-+ INT1 INT2)))))
   (:linear
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (<= 0 (tau-interval-lo (TAU-BOUNDER-+ INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-lo (TAU-BOUNDER-+ INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-hi (TAU-BOUNDER-+ INT1 INT2)))))))

(encapsulate
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))
 (local
  (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
                                                HIST PSPV))))
 (defthm natp-tau-bounder-*
   (IMPLIES (AND (tau-intervalp int1)
                 (equal (tau-interval-dom int1) 'integerp)
                 (tau-interval-lo int1)
                 (tau-interval-hi int1)
                 (<= 0 (tau-interval-lo int1))
                 (tau-intervalp int2)
                 (equal (tau-interval-dom int2) 'integerp)
                 (tau-interval-lo int2)
                 (tau-interval-hi int2)
                 (<= 0 (tau-interval-lo int2)))
            (and (tau-intervalp (TAU-BOUNDER-* INT1 INT2))
                 (equal (tau-interval-dom (TAU-BOUNDER-* INT1 INT2))
                        'integerp)
                 (tau-interval-lo (TAU-BOUNDER-* INT1 INT2))
                 (tau-interval-hi (TAU-BOUNDER-* INT1 INT2))
                 (<= 0 (tau-interval-lo (TAU-BOUNDER-* INT1 INT2)))))
   :rule-classes
   ((:rewrite
     :corollary
     (IMPLIES (AND (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (<= 0 (tau-interval-lo int1))
                   (tau-intervalp int2)
                   (equal (tau-interval-dom int2) 'integerp)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2)
                   (<= 0 (tau-interval-lo int2)))
              (and (tau-intervalp (TAU-BOUNDER-* INT1 INT2))
                   (equal (tau-interval-dom (TAU-BOUNDER-* INT1 INT2))
                          'integerp)
                   (tau-interval-lo (TAU-BOUNDER-* INT1 INT2))
                   (tau-interval-hi (TAU-BOUNDER-* INT1 INT2)))))
    (:linear
     :corollary
     (IMPLIES (AND (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (<= 0 (tau-interval-lo int1))
                   (tau-intervalp int2)
                   (equal (tau-interval-dom int2) 'integerp)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2)
                   (<= 0 (tau-interval-lo int2)))
              (<= 0 (tau-interval-lo (TAU-BOUNDER-* INT1 INT2)))))
    (:type-prescription
     :corollary
     (IMPLIES (AND (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (<= 0 (tau-interval-lo int1))
                   (tau-intervalp int2)
                   (equal (tau-interval-dom int2) 'integerp)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2)
                   (<= 0 (tau-interval-lo int2)))
              (natp (tau-interval-lo (TAU-BOUNDER-* INT1 INT2)))))
    (:type-prescription
     :corollary
     (IMPLIES (AND (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (<= 0 (tau-interval-lo int1))
                   (tau-intervalp int2)
                   (equal (tau-interval-dom int2) 'integerp)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2)
                   (<= 0 (tau-interval-lo int2)))
              (natp (tau-interval-hi (TAU-BOUNDER-* INT1 INT2))))))))

(defthm natp-tau-bounder-mod
  (IMPLIES (AND (tau-intervalp int1)
                (equal (tau-interval-dom int1) 'integerp)
                (tau-interval-lo int1)
                (tau-interval-hi int1)
                (<= 0 (tau-interval-lo int1))
                (tau-intervalp int2)
                (equal (tau-interval-dom int2) 'integerp)
                (tau-interval-lo int2)
                (tau-interval-hi int2)
                (<= 0 (tau-interval-lo int2)))
           (and (tau-intervalp (TAU-BOUNDER-mod INT1 INT2))
                (equal (tau-interval-dom (TAU-BOUNDER-mod INT1 INT2))
                       'integerp)
                (tau-interval-lo (TAU-BOUNDER-mod INT1 INT2))
                (tau-interval-hi (TAU-BOUNDER-mod INT1 INT2))
                (<= 0 (tau-interval-lo (TAU-BOUNDER-mod INT1 INT2)))))
  :rule-classes
  ((:rewrite
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (and (tau-intervalp (TAU-BOUNDER-mod INT1 INT2))
                  (equal (tau-interval-dom (TAU-BOUNDER-mod INT1 INT2))
                         'integerp)
                  (tau-interval-lo (TAU-BOUNDER-mod INT1 INT2))
                  (tau-interval-hi (TAU-BOUNDER-mod INT1 INT2)))))
   (:linear
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (<= 0 (tau-interval-lo (TAU-BOUNDER-mod INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-lo (TAU-BOUNDER-mod INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-hi (TAU-BOUNDER-mod INT1 INT2)))))))

; LOGAND uses two functions, find-minimal-logand and find-maximal-logand to
; narrow the computed interval if it is deemed heuristically worthwhile.  Then,
; LOGIOR and LOGXOR are defined in terms of LOGAND and LOGNOT.  Because of
; LOGNOT, some LOGANDs sometimes receive negative inputs.  So I need to
; characterize the signs of find-minimal-logand and find-maximal-logand for the
; four cases on the signs of the input intervals.

; To make matters more complicated, find-minimal-logand is defined in terms of
; find-minimal-logand1 which is defined in terms of find-minimal-logand2.
; Find-maximal-logand is strictly analogous.  So basically for each top-level
; function we need two lemmas that carry the appropriate combination of sign
; information along.

; We start by defining the negative analogue of NATP and giving ourselves some
; arithmetic we use when we start to expand LOGIOR and LOGXOR.

(defun negp (x)(and (integerp x) (< x 0)))

(defthm negp-is-a-recognizer
  (iff (negp x)
       (and (integerp x) (< x 0)))
  :rule-classes :compound-recognizer)

(encapsulate
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))

 (defthm a0
   (implies (integerp x)
            (equal (- (+ -1 (- x)))
                   (+ 1 x))))

 (defthm a1
   (implies (integerp x)
            (equal (+ -1 (+ 1 x))
                   x))))

; For each of find-minimal-logand and find-maximal-logand we will prove a
; signature lemma relating the signs of the input pairs to the signs of the
; output.  We'll need two lemmas to support the proof of each top-level
; function.  The top-level functions take four arguments: lox, hix, loy, hiy.
; Each pair represents an input interval, [lox,hix] and [loy,hiy].  In the
; normal case we know these are all naturals and so the answer is a natural.
; But when LOGNOT comes along, the intervals are reflected across 0.  So we
; need to consider the cases that both input intervals are in nonnegative
; territory, both are in negative territory, and that one is nonnegative and
; the other is negative.

; -----------------------------------------------------------------
; find-minimal-logand:  natp x natp ==> natp
; find-maximal-logand:  natp x natp ==> natp

(defthm find-minimal-logand2-natp-x-natp==>natp
  (implies (and (natp x)
                (natp loy)
                (natp hiy)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-minimal-logand2 X LOY HIY min)))
  :rule-classes :type-prescription)

(defthm find-minimal-logand1-natp-x-natp==>natp
  (implies (and (natp lox)
                (natp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-minimal-logand1 lox hix loy hiy min)))
  :rule-classes :type-prescription)

(defthm find-minimal-logand-natp-x-natp==>natp
  (implies (and (natp lox)
                (natp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (natp (find-minimal-logand lox hix loy hiy)))
  :hints (("Goal" :in-theory (enable find-minimal-logand)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (implies (and (natp lox)
                (natp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (find-minimal-logand lox hix loy hiy)))
   (:linear
    :corollary
    (implies (and (natp lox)
                (natp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (<= 0 (find-minimal-logand lox hix loy hiy))))))

; ---

(defthm find-maximal-logand2-natp-x-natp==>natp
  (implies (and (natp x)
                (natp loy)
                (natp hiy)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-maximal-logand2 X LOY HIY min)))
  :rule-classes :type-prescription)

(defthm find-maximal-logand1-natp-x-natp==>natp
  (implies (and (natp lox)
                (natp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-maximal-logand1 lox hix loy hiy min)))
  :rule-classes :type-prescription)

(defthm find-maximal-logand-natp-x-natp==>natp
  (implies (and (natp lox)
                (natp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (natp (find-maximal-logand lox hix loy hiy)))
  :hints (("Goal" :in-theory (enable find-maximal-logand)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (implies (and (natp lox)
                (natp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (find-maximal-logand lox hix loy hiy)))
   (:linear
    :corollary
    (implies (and (natp lox)
                (natp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (<= 0 (find-maximal-logand lox hix loy hiy))))))

; -----------------------------------------------------------------
; find-minimal-logand:  negp x negp ==> negp
; find-maximal-logand:  negp x negp ==> negp

(defthm find-minimal-logand2-negp-x-negp==>negp
  (implies (and (negp x)
                (negp loy)
                (negp hiy)
                (<= loy hiy)
                (or (null min) (negp min)))
           (negp (find-minimal-logand2 X LOY HIY min)))
  :rule-classes :type-prescription)

(defthm find-minimal-logand1-negp-x-negp==>negp
  (implies (and (negp lox)
                (negp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy)
                (or (null min) (negp min)))
           (negp (find-minimal-logand1 lox hix loy hiy min)))
  :rule-classes :type-prescription)

(defthm find-minimal-logand-negp-x-negp==>negp
  (implies (and (negp lox)
                (negp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (negp (find-minimal-logand lox hix loy hiy)))
  :hints (("Goal" :in-theory (enable find-minimal-logand)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (implies (and (negp lox)
                (negp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (find-minimal-logand lox hix loy hiy)))
   (:linear
    :corollary
    (implies (and (negp lox)
                (negp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (< (find-minimal-logand lox hix loy hiy) 0)))))

; ---

(defthm find-maximal-logand2-negp-x-negp==>negp
  (implies (and (negp x)
                (negp loy)
                (negp hiy)
                (<= loy hiy)
                (or (null min) (negp min)))
           (negp (find-maximal-logand2 X LOY HIY min)))
  :rule-classes :type-prescription)

(defthm find-maximal-logand1-negp-x-negp==>negp
  (implies (and (negp lox)
                (negp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy)
                (or (null min) (negp min)))
           (negp (find-maximal-logand1 lox hix loy hiy min)))
  :rule-classes :type-prescription)

(defthm find-maximal-logand-negp-x-negp==>negp
  (implies (and (negp lox)
                (negp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (negp (find-maximal-logand lox hix loy hiy)))
  :hints (("Goal" :in-theory (enable find-maximal-logand)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (implies (and (negp lox)
                (negp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (find-maximal-logand lox hix loy hiy)))
   (:linear
    :corollary
    (implies (and (negp lox)
                (negp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (< (find-maximal-logand lox hix loy hiy) 0)))))

; -----------------------------------------------------------------
; find-minimal-logand:  natp x negp ==> natp
; find-maximal-logand:  natp x negp ==> natp

(defthm find-minimal-logand2-natp-x-negp==>natp
  (implies (and (natp x)
                (negp loy)
                (negp hiy)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-minimal-logand2 X LOY HIY min)))
  :rule-classes :type-prescription)

(defthm find-minimal-logand1-natp-x-negp==>natp
  (implies (and (natp lox)
                (natp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-minimal-logand1 lox hix loy hiy min)))
  :rule-classes :type-prescription)

(defthm find-minimal-logand-natp-x-negp==>natp
  (implies (and (natp lox)
                (natp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (natp (find-minimal-logand lox hix loy hiy)))
  :hints (("Goal" :in-theory (enable find-minimal-logand)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (implies (and (natp lox)
                (natp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (find-minimal-logand lox hix loy hiy)))
   (:linear
    :corollary
    (implies (and (natp lox)
                (natp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (<= 0 (find-minimal-logand lox hix loy hiy))))))

; ---

(defthm find-maximal-logand2-natp-x-negp==>natp
  (implies (and (natp x)
                (negp loy)
                (negp hiy)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-maximal-logand2 X LOY HIY min)))
  :rule-classes :type-prescription)

(defthm find-maximal-logand1-natp-x-negp==>natp
  (implies (and (natp lox)
                (natp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-maximal-logand1 lox hix loy hiy min)))
  :rule-classes :type-prescription)

(defthm find-maximal-logand-natp-x-negp==>natp
  (implies (and (natp lox)
                (natp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (natp (find-maximal-logand lox hix loy hiy)))
  :hints (("Goal" :in-theory (enable find-maximal-logand)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (implies (and (natp lox)
                (natp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (find-maximal-logand lox hix loy hiy)))
   (:linear
    :corollary
    (implies (and (natp lox)
                (natp hix)
                (negp loy)
                (negp hiy)
                (<= lox hix)
                (<= loy hiy))
           (<= 0 (find-maximal-logand lox hix loy hiy))))))

; -----------------------------------------------------------------
; find-minimal-logand:  negp x natp ==> natp
; find-maximal-logand:  negp x natp ==> natp

(defthm find-minimal-logand2-negp-x-natp==>natp
  (implies (and (negp x)
                (natp loy)
                (natp hiy)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-minimal-logand2 X LOY HIY min)))
  :rule-classes :type-prescription)

(defthm find-minimal-logand1-negp-x-natp==>natp
  (implies (and (negp lox)
                (negp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-minimal-logand1 lox hix loy hiy min)))
  :rule-classes :type-prescription)

(defthm find-minimal-logand-negp-x-natp==>natp
  (implies (and (negp lox)
                (negp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (natp (find-minimal-logand lox hix loy hiy)))
  :hints (("Goal" :in-theory (enable find-minimal-logand)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (implies (and (negp lox)
                (negp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (find-minimal-logand lox hix loy hiy)))
   (:linear
    :corollary
    (implies (and (negp lox)
                (negp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (<= 0 (find-minimal-logand lox hix loy hiy))))))

; ---

(defthm find-maximal-logand2-negp-x-natp==>natp
  (implies (and (negp x)
                (natp loy)
                (natp hiy)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-maximal-logand2 X LOY HIY min)))
  :rule-classes :type-prescription)

(defthm find-maximal-logand1-negp-x-natp==>natp
  (implies (and (negp lox)
                (negp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy)
                (or (null min) (natp min)))
           (natp (find-maximal-logand1 lox hix loy hiy min)))
  :rule-classes :type-prescription)

(defthm find-maximal-logand-negp-x-natp==>natp
  (implies (and (negp lox)
                (negp hix)
                (natp loy)
                (natp hiy)
                (<= lox hix)
                (<= loy hiy))
           (natp (find-maximal-logand lox hix loy hiy)))
  :hints (("Goal" :in-theory (enable find-maximal-logand)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (implies (and (negp lox)
                  (negp hix)
                  (natp loy)
                  (natp hiy)
                  (<= lox hix)
                  (<= loy hiy))
             (find-maximal-logand lox hix loy hiy)))
   (:linear
    :corollary
    (implies (and (negp lox)
                  (negp hix)
                  (natp loy)
                  (natp hiy)
                  (<= lox hix)
                  (<= loy hiy))
             (<= 0 (find-maximal-logand lox hix loy hiy))))))

; -----------------------------------------------------------------
; Now we are ready to handle the tau-bounders for LOGAND, LOGIOR, and LOGXOR.

(defthm natp-tau-bounder-logand
  (IMPLIES (AND (tau-intervalp int1)
                (equal (tau-interval-dom int1) 'integerp)
                (tau-interval-lo int1)
                (tau-interval-hi int1)
                (<= 0 (tau-interval-lo int1))
                (tau-intervalp int2)
                (equal (tau-interval-dom int2) 'integerp)
                (tau-interval-lo int2)
                (tau-interval-hi int2)
                (<= 0 (tau-interval-lo int2)))
           (and (tau-intervalp (TAU-BOUNDER-logand INT1 INT2))
                (equal (tau-interval-dom (TAU-BOUNDER-logand INT1 INT2))
                       'integerp)
                (tau-interval-lo (TAU-BOUNDER-logand INT1 INT2))
                (tau-interval-hi (TAU-BOUNDER-logand INT1 INT2))
                (<= 0 (tau-interval-lo (TAU-BOUNDER-logand INT1 INT2)))))
  :rule-classes
  ((:rewrite
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (and (tau-intervalp (TAU-BOUNDER-logand INT1 INT2))
                  (equal (tau-interval-dom (TAU-BOUNDER-logand INT1 INT2))
                         'integerp)
                  (tau-interval-lo (TAU-BOUNDER-logand INT1 INT2))
                  (tau-interval-hi (TAU-BOUNDER-logand INT1 INT2)))))
   (:linear
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (<= 0 (tau-interval-lo (TAU-BOUNDER-logand INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-lo (TAU-BOUNDER-logand INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-hi (TAU-BOUNDER-logand INT1 INT2)))))))

(defthm natp-tau-bounder-logior
  (IMPLIES (AND (tau-intervalp int1)
                (equal (tau-interval-dom int1) 'integerp)
                (tau-interval-lo int1)
                (tau-interval-hi int1)
                (<= 0 (tau-interval-lo int1))
                (tau-intervalp int2)
                (equal (tau-interval-dom int2) 'integerp)
                (tau-interval-lo int2)
                (tau-interval-hi int2)
                (<= 0 (tau-interval-lo int2)))
           (and (tau-intervalp (TAU-BOUNDER-logior INT1 INT2))
                (equal (tau-interval-dom (TAU-BOUNDER-logior INT1 INT2))
                       'integerp)
                (tau-interval-lo (TAU-BOUNDER-logior INT1 INT2))
                (tau-interval-hi (TAU-BOUNDER-logior INT1 INT2))
                (<= 0 (tau-interval-lo (TAU-BOUNDER-logior INT1 INT2)))))
  :hints
  (("Goal"
    :use (:instance tau-bounder-logior-correct
                    (x (tau-interval-lo int1))
                    (y (tau-interval-lo int2)))
    :in-theory (disable tau-bounder-logior-correct)))
  :rule-classes
  ((:rewrite
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (and (tau-intervalp (TAU-BOUNDER-logior INT1 INT2))
                  (equal (tau-interval-dom (TAU-BOUNDER-logior INT1 INT2))
                         'integerp)
                  (tau-interval-lo (TAU-BOUNDER-logior INT1 INT2))
                  (tau-interval-hi (TAU-BOUNDER-logior INT1 INT2)))))
   (:linear
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (<= 0 (tau-interval-lo (TAU-BOUNDER-logior INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-lo (TAU-BOUNDER-logior INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-hi (TAU-BOUNDER-logior INT1 INT2)))))))

(defthm natp-tau-bounder-logxor
  (IMPLIES (AND (tau-intervalp int1)
                (equal (tau-interval-dom int1) 'integerp)
                (tau-interval-lo int1)
                (tau-interval-hi int1)
                (<= 0 (tau-interval-lo int1))
                (tau-intervalp int2)
                (equal (tau-interval-dom int2) 'integerp)
                (tau-interval-lo int2)
                (tau-interval-hi int2)
                (<= 0 (tau-interval-lo int2)))
           (and (tau-intervalp (TAU-BOUNDER-logxor INT1 INT2))
                (equal (tau-interval-dom (TAU-BOUNDER-logxor INT1 INT2))
                       'integerp)
                (tau-interval-lo (TAU-BOUNDER-logxor INT1 INT2))
                (tau-interval-hi (TAU-BOUNDER-logxor INT1 INT2))
                (<= 0 (tau-interval-lo (TAU-BOUNDER-logxor INT1 INT2)))))
  :hints
  (("Goal"
    :use (:instance tau-bounder-logxor-correct
                    (x (tau-interval-lo int1))
                    (y (tau-interval-lo int2)))
    :in-theory (disable tau-bounder-logxor-correct
                        distributivity-of-minus-over-+)))

  :rule-classes
  ((:rewrite
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (and (tau-intervalp (TAU-BOUNDER-logxor INT1 INT2))
                  (equal (tau-interval-dom (TAU-BOUNDER-logxor INT1 INT2))
                         'integerp)
                  (tau-interval-lo (TAU-BOUNDER-logxor INT1 INT2))
                  (tau-interval-hi (TAU-BOUNDER-logxor INT1 INT2)))))
   (:linear
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (<= 0 (tau-interval-lo (TAU-BOUNDER-logxor INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-lo (TAU-BOUNDER-logxor INT1 INT2)))))
   (:type-prescription
    :corollary
    (IMPLIES (AND (tau-intervalp int1)
                  (equal (tau-interval-dom int1) 'integerp)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (<= 0 (tau-interval-lo int1))
                  (tau-intervalp int2)
                  (equal (tau-interval-dom int2) 'integerp)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int2)))
             (natp (tau-interval-hi (TAU-BOUNDER-logxor INT1 INT2)))))))

(encapsulate
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))

 (local
  (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
                                                HIST PSPV))))
 (defthm natp-tau-bounder-ash
   (IMPLIES (AND (tau-intervalp int1)
                 (equal (tau-interval-dom int1) 'integerp)
                 (tau-interval-lo int1)
                 (tau-interval-hi int1)
                 (<= 0 (tau-interval-lo int1))
                 (tau-intervalp int2)
                 (equal (tau-interval-dom int2) 'integerp)
                 (tau-interval-lo int2)
                 (tau-interval-hi int2)
                 ; (<= 0 (tau-interval-lo int2))  ; This lemma is different!
                 )                                ; Negative shifts are ok!
            (and (tau-intervalp (TAU-BOUNDER-ash INT1 INT2))
                 (equal (tau-interval-dom (TAU-BOUNDER-ash INT1 INT2))
                        'integerp)
                 (tau-interval-lo (TAU-BOUNDER-ash INT1 INT2))
                 (tau-interval-hi (TAU-BOUNDER-ash INT1 INT2))
                 (<= 0 (tau-interval-lo (TAU-BOUNDER-ash INT1 INT2)))))
   :rule-classes
   ((:rewrite
     :corollary
     (IMPLIES (AND (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (<= 0 (tau-interval-lo int1))
                   (tau-intervalp int2)
                   (equal (tau-interval-dom int2) 'integerp)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2))
              (and (tau-intervalp (TAU-BOUNDER-ash INT1 INT2))
                   (equal (tau-interval-dom (TAU-BOUNDER-ash INT1 INT2))
                          'integerp)
                   (tau-interval-lo (TAU-BOUNDER-ash INT1 INT2))
                   (tau-interval-hi (TAU-BOUNDER-ash INT1 INT2)))))
    (:linear
     :corollary
     (IMPLIES (AND (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (<= 0 (tau-interval-lo int1))
                   (tau-intervalp int2)
                   (equal (tau-interval-dom int2) 'integerp)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2))
              (<= 0 (tau-interval-lo (TAU-BOUNDER-ash INT1 INT2)))))
    (:type-prescription
     :corollary
     (IMPLIES (AND (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (<= 0 (tau-interval-lo int1))
                   (tau-intervalp int2)
                   (equal (tau-interval-dom int2) 'integerp)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2))
              (natp (tau-interval-lo (TAU-BOUNDER-ash INT1 INT2)))))
    (:type-prescription
     :corollary
     (IMPLIES (AND (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (<= 0 (tau-interval-lo int1))
                   (tau-intervalp int2)
                   (equal (tau-interval-dom int2) 'integerp)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2))
              (natp (tau-interval-hi (TAU-BOUNDER-ash INT1 INT2))))))))

(local
(defthm tau-interval-dom-make-tau-interval
  (equal (tau-interval-dom (make-tau-interval dom lo-rel lo hi-rel hi))
         dom)))

(local
(defthm tau-intervalp-make-tau-interval-integerp
  (implies (and (integerp lo)
                (integerp hi)
                (<= lo hi))
           (tau-intervalp
            (make-tau-interval 'integerp nil lo nil hi)))))

(local
(defthm tau-interval-lo-make-tau-interval-integerp
  (equal
   (tau-interval-lo
    (make-tau-interval 'integerp nil lo nil hi))
   lo)))

(local
(defthm tau-interval-hi-make-tau-interval-integerp
  (equal
   (tau-interval-hi
    (make-tau-interval 'integerp nil lo nil hi))
   hi)))

; BTW: These next two can't be type-prescriptions because the typed term occurs
; in the hyp.

(local
 (defthm integerp-intervals-have-integerp-lo
   (implies (and (tau-intervalp int)
                 (equal (tau-interval-dom int) 'integerp)
                 (tau-interval-lo int))
            (integerp (tau-interval-lo int)))
   :rule-classes
   ((:rewrite)
    (:type-prescription
     :corollary
     (implies (and (tau-intervalp int)
                   (equal (tau-interval-dom int) 'integerp))
              (or (null (tau-interval-lo int))
                  (integerp (tau-interval-lo int))))))))

(local
 (defthm integerp-intervals-have-integerp-hi
   (implies (and (tau-intervalp int)
                 (equal (tau-interval-dom int) 'integerp)
                 (tau-interval-hi int))
            (integerp (tau-interval-hi int)))
   :rule-classes
   ((:rewrite)
    (:type-prescription
     :corollary
     (implies (and (tau-intervalp int)
                   (equal (tau-interval-dom int) 'integerp))
              (or (null (tau-interval-hi int))
                  (integerp (tau-interval-hi int))))))))

(local
 (DEFTHM embarrassing-integerp-fact
   (IMPLIES (AND (INTEGERP A) (INTEGERP B))
            (INTEGERP (+ A B)))))

(encapsulate
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))

; We shift into the following theory temporarily.  We could do this with an
; :in-theory hint, but that wouldn't apply to the proofs of the :corollaries.

 (local
  (in-theory (disable tau-intervalp
                      tau-interval-lo
                      tau-interval-hi
                      tau-bounder-+
                      tau-bounder-*
;                      tau-bounder--
                      tau-bounder-mod
                      tau-bounder-logand
                      tau-bounder-logior
                      tau-bounder-logxor
                      tau-bounder-ash
                      tau-interval-r
                      tau-interval-dom
                      make-tau-interval
                      )))

 (local
  (defthm tau-intervalp-make-tau-interval-integerp-forced
    (implies (and (force (integerp lo))
                  (force (integerp hi))
                  (force (<= lo hi)))
             (tau-intervalp
              (make-tau-interval 'integerp nil lo nil hi)))))


 (defthm ainni-correct-part-2a
   (implies (and (pseudo-termp term)
                 (MV-NTH 0 (AINNI term HYPS TYPE-ALIST)))
            (and (tau-intervalp (mv-nth 2 (ainni term hyps type-alist)))
                 (equal (tau-interval-dom (mv-nth 2 (ainni term hyps type-alist)))
                        'integerp)
                 (tau-interval-lo (mv-nth 2 (ainni term hyps type-alist)))
                 (tau-interval-hi (mv-nth 2 (ainni term hyps type-alist)))
                 (<= 0 (tau-interval-lo (mv-nth 2 (ainni term hyps type-alist))))))
   :rule-classes
   ((:rewrite
     :corollary
     (implies (and (pseudo-termp term)
                   (mv-nth 0 (ainni term hyps type-alist)))
              (and (tau-intervalp (mv-nth 2 (ainni term hyps type-alist)))
                   (equal (tau-interval-dom (mv-nth 2 (ainni term hyps type-alist)))
                          'integerp)
                   (tau-interval-lo (mv-nth 2 (ainni term hyps type-alist)))
                   (tau-interval-hi (mv-nth 2 (ainni term hyps type-alist)))))
     :hints (("Goal" :in-theory (disable ainni))))
    (:type-prescription
     :corollary
     (implies (and (pseudo-termp term)
                   (mv-nth 0 (ainni term hyps type-alist)))
              (natp (tau-interval-lo (mv-nth 2 (ainni term hyps type-alist)))))
     :hints (("Goal" :in-theory (disable ainni))))
    (:linear
     :corollary
     (implies (and (pseudo-termp term)
                   (MV-NTH 0 (AINNI term HYPS TYPE-ALIST)))
              (<= 0 (tau-interval-lo (mv-nth 2 (ainni term hyps type-alist)))))
     :hints (("Goal" :in-theory (disable ainni))))

; This next one isn't actually subsumed by a clause of the just-proved main
; goal, but is easily proved if you expand the definition of tau-intervalp.

    (:type-prescription
     :corollary
     (implies (and (pseudo-termp term)
                   (mv-nth 0 (ainni term hyps type-alist)))
              (natp (tau-interval-hi (mv-nth 2 (ainni term hyps type-alist)))))
     :hints (("Goal" :in-theory (e/d (tau-intervalp) (ainni)))))
    )))

(local
 (defthm subsetp-equal-reflexive-lemma
   (implies (and (consp hyps)
                 (subsetp-equal a (cdr hyps)))
            (subsetp-equal a hyps))))

(local
 (defthm subsetp-equal-reflexive
   (subsetp-equal hyps hyps)))

(local
 (defthm subsetp-equal-transitive
   (implies (and (subsetp-equal a b)
                 (subsetp-equal b c))
            (subsetp-equal a c))))

(local
 (defthm subsetp-equal-mv-nth-1-ainni
   (implies (mv-nth 0 (ainni term hyps type-alist))
            (subsetp-equal hyps
                           (mv-nth 1 (ainni term hyps type-alist))))
   :hints
   (("Goal" :in-theory (disable tau-bounder-+
                                tau-bounder-*
;                                tau-bounder--
                                tau-bounder-mod
                                tau-bounder-logand
                                tau-bounder-logior
                                tau-bounder-logxor
                                tau-bounder-ash
;                               tau-interval-r
                                tau-interval-dom
                                tau-intervalp
                                in-tau-intervalp
                                make-tau-interval)))))

(defthm stateman-eval-conjoin-mv-nth-1-ainni
  (implies (and (mv-nth 0 (ainni term hyps type-alist))
                (not (stateman-eval (conjoin hyps) alist)))
           (not (stateman-eval (conjoin (mv-nth 1 (ainni term hyps type-alist))) alist)))
     :hints
   (("Goal" :in-theory (disable tau-bounder-+
                                tau-bounder-*
;                                tau-bounder--
                                tau-bounder-mod
                                tau-bounder-logand
                                tau-bounder-logior
                                tau-bounder-logxor
                                tau-bounder-ash
;                               tau-interval-r
                                tau-interval-dom
                                tau-intervalp
                                in-tau-intervalp
                                make-tau-interval))))

(defthm in-tau-intervalp-difference
  (implies (and (tau-intervalp int1)
                (tau-intervalp int2)
                (eq (tau-interval-dom int1) 'integerp)
                (eq (tau-interval-dom int2) 'integerp)
                (in-tau-intervalp x int1)
                (in-tau-intervalp y int2)
                (tau-interval-lo int1)
                (tau-interval-hi int1)
                (tau-interval-lo int2)
                (tau-interval-hi int2)
                (<= 0 (tau-interval-lo int1))
                (<= 0 (tau-interval-lo int2))
                (<= (max (- (tau-interval-lo int1)
                            (tau-interval-hi int2))
                         0)
                    (- (tau-interval-hi int1)
                       (tau-interval-lo int2)))
                (<= y x))
           (in-tau-intervalp (+ x (- y))
                             (make-tau-interval 'integerp
                                                nil
                                                (max (- (tau-interval-lo int1)
                                                        (tau-interval-hi int2))
                                                     0)
                                                nil
                                                (- (tau-interval-hi int1)
                                                   (tau-interval-lo int2)))))
  :rule-classes
  ((:rewrite)
   (:rewrite
    :corollary
    (implies (and (tau-intervalp int1)
                  (tau-intervalp int2)
                  (eq (tau-interval-dom int1) 'integerp)
                  (eq (tau-interval-dom int2) 'integerp)
                  (in-tau-intervalp x int1)
                  (in-tau-intervalp y int2)
                  (tau-interval-lo int1)
                  (tau-interval-hi int1)
                  (tau-interval-lo int2)
                  (tau-interval-hi int2)
                  (<= 0 (tau-interval-lo int1))
                  (<= 0 (tau-interval-lo int2))
                  (<= (max (- (tau-interval-lo int1)
                              (tau-interval-hi int2))
                           0)
                      (- (tau-interval-hi int1)
                         (tau-interval-lo int2)))
                  (<= y x))
             (in-tau-intervalp (+ (- y) x)
                               (make-tau-interval 'integerp
                                                  nil
                                                  (max (- (tau-interval-lo int1)
                                                          (tau-interval-hi int2))
                                                       0)
                                                  nil
                                                  (- (tau-interval-hi int1)
                                                     (tau-interval-lo int2))))))))

(encapsulate
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))
 (local
  (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
                                                HIST PSPV))))
 (defthm in-tau-intervalp-times-difference
   (implies (and (tau-intervalp int1)
                 (tau-intervalp int2)
                 (eq (tau-interval-dom int1) 'integerp)
                 (eq (tau-interval-dom int2) 'integerp)
                 (force (in-tau-intervalp x int1))
                 (force (in-tau-intervalp y int2))
                 (tau-interval-lo int1)
                 (tau-interval-hi int1)
                 (tau-interval-lo int2)
                 (tau-interval-hi int2)
                 (<= 0 (tau-interval-lo int1))
                 (<= 0 (tau-interval-lo int2))
                 (force (<= (max (- (tau-interval-lo int1)
                                    (tau-interval-hi int2))
                                 0)
                            (- (tau-interval-hi int1)
                               (tau-interval-lo int2))))
                 (<= y x)
                 (natp c))
            (in-tau-intervalp (+ (* c x) (* c (- y)))
                              (make-tau-interval 'integerp
                                                 nil
                                                 (* c (max (- (tau-interval-lo int1)
                                                              (tau-interval-hi int2))
                                                           0))
                                                 nil
                                                 (+ (* c (tau-interval-hi int1))
                                                    (* c (- (tau-interval-lo int2)))))))
   :rule-classes
   ((:rewrite)
    (:rewrite
     :corollary
     (implies (and (tau-intervalp int1)
                   (tau-intervalp int2)
                   (eq (tau-interval-dom int1) 'integerp)
                   (eq (tau-interval-dom int2) 'integerp)
                   (force (in-tau-intervalp x int1))
                   (force (in-tau-intervalp y int2))
                   (tau-interval-lo int1)
                   (tau-interval-hi int1)
                   (tau-interval-lo int2)
                   (tau-interval-hi int2)
                   (<= 0 (tau-interval-lo int1))
                   (<= 0 (tau-interval-lo int2))
                   (force (<= (max (- (tau-interval-lo int1)
                                      (tau-interval-hi int2))
                                   0)
                              (- (tau-interval-hi int1)
                                 (tau-interval-lo int2))))
                   (<= y x)
                   (natp c))
              (in-tau-intervalp (+ (* c (- y)) (* c x))
                                (make-tau-interval 'integerp
                                                   nil
                                                   (* c (max (- (tau-interval-lo int1)
                                                                (tau-interval-hi int2))
                                                             0))
                                                   nil
                                                   (+ (* c (tau-interval-hi int1))
                                                      (* c (- (tau-interval-lo int2)))))))))))

(defthm in-tau-intervalp-make-tau-interval-integerp-const
  (implies (integerp const)
           (in-tau-intervalp const
                             (make-tau-interval 'integerp nil const nil const))))

(encapsulate
 nil
 (local
  (defthm lemma1
    (implies (and (PSEUDO-TERM-LISTP (CDDR TERM))
                  (EQUAL (CAR (CADDR TERM)) 'UNARY--)
                  )
             (pseudo-termp (CAR (CDR (CAR (CDR (CDR TERM)))))))))

 (local
  (defthm lemma2
    (implies (and (member-equal (LIST 'FORCE (LIST 'NOT (LIST '< x y))) hyps)
                  (stateman-eval (conjoin hyps) alist))
             (not (< (stateman-eval x alist)
                     (stateman-eval y alist))))))

 (local
  (defthm lemma3
    (implies (and (not (stateman-eval (conjoin hyps) alist))
                  (mv-nth 0 (ainni term hyps type-alist)))
             (consp (mv-nth 1 (ainni term hyps type-alist))))
    :hints (("Goal" :in-theory (disable ainni
                                        subsetp-equal-mv-nth-1-ainni)
             :use subsetp-equal-mv-nth-1-ainni))))

 (local
  (defthm lemma4
    (implies (and (not (stateman-eval (conjoin hyps1) alist))
                  (subsetp-equal hyps1 hyps2))
             (not (equal (conjoin hyps2) *t*)))))

; The following horrible encapsulate proves four theorems that would have been
; FORCEd otherwise during the proof of ainni-correct-part-2b below.  They could
; probably be cleaned up but I've taken the subgoals verbatim.  These goals
; were forced by in-tau-intervalp-times-difference, above.  All are provable
; with arithmetic-5 and non-linear, under the same disable hints from
; ainni-correct-part-2b except that it is no longer necessary to open ainni (so
; it's disabled) and it is best to expand max (so it is not disabled).

 (local
  (encapsulate
   nil
   (local
    (include-book "arithmetic-5/top" :dir :system))

   (local
    (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
                                                  HIST PSPV))))
   (local
    (in-theory
     (disable ainni                  ; <--- added
              ; max                  ; <--- removed
              in-tau-intervalp
              tau-intervalp
              make-tau-interval
              tau-interval-dom
              tau-interval-lo
              tau-interval-hi
              tau-bounder-+
              tau-bounder-*
;              tau-bounder--
              tau-bounder-mod
              tau-bounder-logand
              tau-bounder-logior
              tau-bounder-logxor
              tau-bounder-ash
              tau-interval-r
              )))

   (defthm |[1]Subgoal 4''|
     (IMPLIES
      (AND
       (CONSP TERM)
       (EQUAL (CAR TERM) 'BINARY-+)
       (MV-NTH 0 (DISTRIBUTED-DIFFERENCE TERM))
       (INTEGERP (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM)))
       (< 0
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM)))
       (MV-NTH 0
               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                      HYPS TYPE-ALIST))
       (MV-NTH 0
               (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                      (MV-NTH 1
                              (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                     HYPS TYPE-ALIST))
                      TYPE-ALIST))
       (<=
        (*
         (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
         (MAX
          (+
           (TAU-INTERVAL-LO
            (MV-NTH 2
                    (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                           HYPS TYPE-ALIST)))
           (-
            (TAU-INTERVAL-HI
             (MV-NTH
              2
              (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                     (MV-NTH 1
                             (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                    HYPS TYPE-ALIST))
                     TYPE-ALIST)))))
          0))
        (+
         (*
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
          (TAU-INTERVAL-HI (MV-NTH 2
                                   (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                          HYPS TYPE-ALIST))))
         (*
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
          (-
           (TAU-INTERVAL-LO
            (MV-NTH 2
                    (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                           (MV-NTH 1
                                   (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                          HYPS TYPE-ALIST))
                           TYPE-ALIST)))))))
       (IN-TAU-INTERVALP (STATEMAN-EVAL (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        ALIST)
                         (MV-NTH 2
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST)))
       (IN-TAU-INTERVALP
        (STATEMAN-EVAL (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       ALIST)
        (MV-NTH 2
                (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       (MV-NTH 1
                               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                      HYPS TYPE-ALIST))
                       TYPE-ALIST)))
       (PSEUDO-TERMP TERM)
       (NOT
        (MEMBER-EQUAL
         (LIST 'FORCE
               (LIST 'NOT
                     (LIST '<
                           (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                           (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM)))))
         (MV-NTH 1
                 (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                        (MV-NTH 1
                                (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                       HYPS TYPE-ALIST))
                        TYPE-ALIST))))
       (CONSP
        (MV-NTH 1
                (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       (MV-NTH 1
                               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                      HYPS TYPE-ALIST))
                       TYPE-ALIST)))
       (NOT
        (EQUAL
         (CONJOIN
          (MV-NTH 1
                  (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                         (MV-NTH 1
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST))
                         TYPE-ALIST)))
         ''NIL))
       (NOT
        (EQUAL
         (CONJOIN
          (MV-NTH 1
                  (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                         (MV-NTH 1
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST))
                         TYPE-ALIST)))
         ''T))
       (<= (STATEMAN-EVAL (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                          ALIST)
           (STATEMAN-EVAL (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                          ALIST))
       (STATEMAN-EVAL
        (CONJOIN
         (MV-NTH 1
                 (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                        (MV-NTH 1
                                (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                       HYPS TYPE-ALIST))
                        TYPE-ALIST)))
        ALIST))
      (<=
       (MAX
        (+
         (TAU-INTERVAL-LO (MV-NTH 2
                                  (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                         HYPS TYPE-ALIST)))
         (-
          (TAU-INTERVAL-HI
           (MV-NTH 2
                   (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                          (MV-NTH 1
                                  (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                         HYPS TYPE-ALIST))
                          TYPE-ALIST)))))
        0)
       (+
        (TAU-INTERVAL-HI (MV-NTH 2
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST)))
        (-
         (TAU-INTERVAL-LO
          (MV-NTH 2
                  (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                         (MV-NTH 1
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST))
                         TYPE-ALIST))))))))

   (defthm |[1]Subgoal 3''|
     (IMPLIES
      (AND
       (CONSP TERM)
       (EQUAL (CAR TERM) 'BINARY-+)
       (MV-NTH 0 (DISTRIBUTED-DIFFERENCE TERM))
       (INTEGERP (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM)))
       (< 0
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM)))
       (MV-NTH 0
               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                      HYPS TYPE-ALIST))
       (MV-NTH 0
               (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                      (MV-NTH 1
                              (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                     HYPS TYPE-ALIST))
                      TYPE-ALIST))
       (<=
        (*
         (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
         (MAX
          (+
           (TAU-INTERVAL-LO
            (MV-NTH 2
                    (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                           HYPS TYPE-ALIST)))
           (-
            (TAU-INTERVAL-HI
             (MV-NTH
              2
              (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                     (MV-NTH 1
                             (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                    HYPS TYPE-ALIST))
                     TYPE-ALIST)))))
          0))
        (+
         (*
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
          (TAU-INTERVAL-HI (MV-NTH 2
                                   (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                          HYPS TYPE-ALIST))))
         (*
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
          (-
           (TAU-INTERVAL-LO
            (MV-NTH 2
                    (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                           (MV-NTH 1
                                   (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                          HYPS TYPE-ALIST))
                           TYPE-ALIST)))))))
       (IN-TAU-INTERVALP (STATEMAN-EVAL (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        ALIST)
                         (MV-NTH 2
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST)))
       (IN-TAU-INTERVALP
        (STATEMAN-EVAL (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       ALIST)
        (MV-NTH 2
                (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       (MV-NTH 1
                               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                      HYPS TYPE-ALIST))
                       TYPE-ALIST)))
       (PSEUDO-TERMP TERM)
       (CONSP
        (MEMBER-EQUAL
         (LIST 'FORCE
               (LIST 'NOT
                     (LIST '<
                           (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                           (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM)))))
         (MV-NTH 1
                 (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                        (MV-NTH 1
                                (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                       HYPS TYPE-ALIST))
                        TYPE-ALIST))))
       (STATEMAN-EVAL
        (CONJOIN
         (MV-NTH 1
                 (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                        (MV-NTH 1
                                (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                       HYPS TYPE-ALIST))
                        TYPE-ALIST)))
        ALIST))
      (<=
       (MAX
        (+
         (TAU-INTERVAL-LO (MV-NTH 2
                                  (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                         HYPS TYPE-ALIST)))
         (-
          (TAU-INTERVAL-HI
           (MV-NTH 2
                   (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                          (MV-NTH 1
                                  (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                         HYPS TYPE-ALIST))
                          TYPE-ALIST)))))
        0)
       (+
        (TAU-INTERVAL-HI (MV-NTH 2
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST)))
        (-
         (TAU-INTERVAL-LO
          (MV-NTH 2
                  (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                         (MV-NTH 1
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST))
                         TYPE-ALIST))))))))

   (defthm |[1]Subgoal 2''|
     (IMPLIES
      (AND
       (CONSP TERM)
       (EQUAL (CAR TERM) 'BINARY-+)
       (MV-NTH 0 (DISTRIBUTED-DIFFERENCE TERM))
       (INTEGERP (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM)))
       (< 0
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM)))
       (MV-NTH 0
               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                      HYPS TYPE-ALIST))
       (MV-NTH 0
               (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                      (MV-NTH 1
                              (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                     HYPS TYPE-ALIST))
                      TYPE-ALIST))
       (<=
        (*
         (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
         (MAX
          (+
           (TAU-INTERVAL-LO
            (MV-NTH 2
                    (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                           HYPS TYPE-ALIST)))
           (-
            (TAU-INTERVAL-HI
             (MV-NTH
              2
              (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                     (MV-NTH 1
                             (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                    HYPS TYPE-ALIST))
                     TYPE-ALIST)))))
          0))
        (+
         (*
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
          (TAU-INTERVAL-HI (MV-NTH 2
                                   (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                          HYPS TYPE-ALIST))))
         (*
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
          (-
           (TAU-INTERVAL-LO
            (MV-NTH 2
                    (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                           (MV-NTH 1
                                   (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                          HYPS TYPE-ALIST))
                           TYPE-ALIST)))))))
       (IN-TAU-INTERVALP (STATEMAN-EVAL (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        ALIST)
                         (MV-NTH 2
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST)))
       (IN-TAU-INTERVALP
        (STATEMAN-EVAL (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       ALIST)
        (MV-NTH 2
                (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       (MV-NTH 1
                               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                      HYPS TYPE-ALIST))
                       TYPE-ALIST)))
       (PSEUDO-TERMP TERM)
       (NOT
        (CONSP
         (MV-NTH 1
                 (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                        (MV-NTH 1
                                (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                       HYPS TYPE-ALIST))
                        TYPE-ALIST))))
       (<= (STATEMAN-EVAL (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                          ALIST)
           (STATEMAN-EVAL (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                          ALIST)))
      (<=
       (MAX
        (+
         (TAU-INTERVAL-LO (MV-NTH 2
                                  (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                         HYPS TYPE-ALIST)))
         (-
          (TAU-INTERVAL-HI
           (MV-NTH 2
                   (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                          (MV-NTH 1
                                  (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                         HYPS TYPE-ALIST))
                          TYPE-ALIST)))))
        0)
       (+
        (TAU-INTERVAL-HI (MV-NTH 2
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST)))
        (-
         (TAU-INTERVAL-LO
          (MV-NTH 2
                  (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                         (MV-NTH 1
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST))
                         TYPE-ALIST))))))))

   (defthm |[1]Subgoal 1''|
     (IMPLIES
      (AND
       (CONSP TERM)
       (EQUAL (CAR TERM) 'BINARY-+)
       (MV-NTH 0 (DISTRIBUTED-DIFFERENCE TERM))
       (INTEGERP (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM)))
       (< 0
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM)))
       (MV-NTH 0
               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                      HYPS TYPE-ALIST))
       (MV-NTH 0
               (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                      (MV-NTH 1
                              (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                     HYPS TYPE-ALIST))
                      TYPE-ALIST))
       (<=
        (*
         (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
         (MAX
          (+
           (TAU-INTERVAL-LO
            (MV-NTH 2
                    (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                           HYPS TYPE-ALIST)))
           (-
            (TAU-INTERVAL-HI
             (MV-NTH
              2
              (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                     (MV-NTH 1
                             (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                    HYPS TYPE-ALIST))
                     TYPE-ALIST)))))
          0))
        (+
         (*
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
          (TAU-INTERVAL-HI (MV-NTH 2
                                   (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                          HYPS TYPE-ALIST))))
         (*
          (MV-NTH 1 (DISTRIBUTED-DIFFERENCE TERM))
          (-
           (TAU-INTERVAL-LO
            (MV-NTH 2
                    (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                           (MV-NTH 1
                                   (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                          HYPS TYPE-ALIST))
                           TYPE-ALIST)))))))
       (IN-TAU-INTERVALP (STATEMAN-EVAL (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        ALIST)
                         (MV-NTH 2
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST)))
       (IN-TAU-INTERVALP
        (STATEMAN-EVAL (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       ALIST)
        (MV-NTH 2
                (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                       (MV-NTH 1
                               (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                      HYPS TYPE-ALIST))
                       TYPE-ALIST)))
       (PSEUDO-TERMP TERM)
       (NOT
        (MEMBER-EQUAL
         (LIST 'FORCE
               (LIST 'NOT
                     (LIST '<
                           (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                           (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM)))))
         (MV-NTH 1
                 (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                        (MV-NTH 1
                                (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                       HYPS TYPE-ALIST))
                        TYPE-ALIST))))
       (EQUAL
        (CONJOIN
         (MV-NTH 1
                 (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                        (MV-NTH 1
                                (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                       HYPS TYPE-ALIST))
                        TYPE-ALIST)))
        ''T)
       (<= (STATEMAN-EVAL (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                          ALIST)
           (STATEMAN-EVAL (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                          ALIST)))
      (<=
       (MAX
        (+
         (TAU-INTERVAL-LO (MV-NTH 2
                                  (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                         HYPS TYPE-ALIST)))
         (-
          (TAU-INTERVAL-HI
           (MV-NTH 2
                   (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                          (MV-NTH 1
                                  (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                         HYPS TYPE-ALIST))
                          TYPE-ALIST)))))
        0)
       (+
        (TAU-INTERVAL-HI (MV-NTH 2
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST)))
        (-
         (TAU-INTERVAL-LO
          (MV-NTH 2
                  (AINNI (MV-NTH 3 (DISTRIBUTED-DIFFERENCE TERM))
                         (MV-NTH 1
                                 (AINNI (MV-NTH 2 (DISTRIBUTED-DIFFERENCE TERM))
                                        HYPS TYPE-ALIST))
                         TYPE-ALIST))))))))))

 (defthm ainni-correct-part-2b
   (implies (and (pseudo-termp term)
                 (mv-nth 0 (ainni term hyps type-alist))
                 (stateman-eval (conjoin (mv-nth 1 (ainni term hyps type-alist))) alist))
            (in-tau-intervalp (stateman-eval term alist)
                              (mv-nth 2 (ainni term hyps type-alist))))
   :hints (("Goal"
            :in-theory (disable max
                                in-tau-intervalp
                                tau-intervalp
                                make-tau-interval
                                tau-interval-dom
                                tau-interval-lo
                                tau-interval-hi
                                tau-bounder-+
                                tau-bounder-*
;                                tau-bounder--
                                tau-bounder-mod
                                tau-bounder-logand
                                tau-bounder-logior
                                tau-bounder-logxor
                                tau-bounder-ash
                                tau-interval-r
                                )
            :expand ((:free (x) (hide x)))))))

; Before we added the difference terms that ainni can now process, it was
; possible to prove the conclusion below given only the hypothesis that ainni's
; flag result was non-nil.  But since (- x y) always adds the hypothesis that
; y<=x, that's no longer true.

(defthm natp-stateman-eval
  (implies (and (pseudo-termp term)
                (mv-nth 0 (ainni term hyps type-alist))
                (stateman-eval (conjoin (mv-nth 1 (ainni term hyps type-alist))) alist))
           (natp (stateman-eval term alist)))
  :hints (("Goal" :in-theory (disable ainni
                                      ainni-correct-part-2a
                                      ainni-correct-part-2b)
           :use (ainni-correct-part-2a
                 ainni-correct-part-2b)))
  :rule-classes
  (:rewrite :type-prescription))

(in-theory (disable ainni))

; These rules are ugly and were added when we started proving guards.  Consider
; the first rule.  The problem is that some function we call has a guard of
; true-listp but our guard is pseudo-term-listp.  So we need the implication.
; Most of the problems stem from elementary-bounders, whose guards are phrased
; in terms of primitives like consp and cdr instead of defined functions like
; tau-intervalp.  So we need the linkages.

(DEFTHM the-guard-mismatch-rules
  (and (IMPLIES (PSEUDO-TERM-LISTP X)
                (TRUE-LISTP X))
       (IMPLIES
        (AND (PSEUDO-TERMP TERM)
             (MV-NTH 0 (AINNI TERM HYPS TYPE-ALIST)))
        (AND (CONSP (MV-NTH 2 (AINNI TERM HYPS TYPE-ALIST)))
             (CONSP (CDR (MV-NTH 2 (AINNI TERM HYPS TYPE-ALIST))))
             (CONSP (CADR (MV-NTH 2 (AINNI TERM HYPS TYPE-ALIST))))
             (CONSP (CDDR (MV-NTH 2 (AINNI TERM HYPS TYPE-ALIST))))
             (rationalp (cdr (cadr (MV-NTH 2 (AINNI TERM HYPS TYPE-ALIST)))))
             (rationalp (cdddr (MV-NTH 2 (AINNI TERM HYPS TYPE-ALIST))))))
       (AND
        (EQUAL (TAU-INTERVALP (LIST* 'INTEGERP
                                     (CONS NIL LO)
                                     (CONS NIL HI)))
               (AND (OR (NULL LO) (INTEGERP LO))
                    (OR (NULL HI) (INTEGERP HI))
                    (OR (NULL LO) (NULL HI) (<= LO HI))))
        (EQUAL
         (TAU-INTERVAL-DOM (LIST* DOM (CONS NIL LO) (CONS NIL HI)))
         DOM)
        (EQUAL (TAU-INTERVAL-LO-REL
                (LIST* DOM (CONS NIL LO) (CONS NIL HI)))
               NIL)
        (EQUAL
         (TAU-INTERVAL-LO (LIST* DOM (CONS NIL LO) (CONS NIL HI)))
         LO)
        (EQUAL (TAU-INTERVAL-HI-REL
                (LIST* DOM (CONS NIL LO) (CONS NIL HI)))
               NIL)
        (EQUAL
         (TAU-INTERVAL-HI (LIST* DOM (CONS NIL LO) (CONS NIL HI)))
         HI)))
  :HINTS (("Goal" :IN-THEORY (DISABLE AINNI-CORRECT-PART-2A)
           :USE AINNI-CORRECT-PART-2A)))

(in-theory (disable the-guard-mismatch-rules))

(verify-guards ainni
               :hints (("Goal"
                        :do-not-induct t
                        :in-theory (e/d (the-guard-mismatch-rules)
                                        (tau-intervalp
                                         tau-interval-dom
                                         tau-interval-lo-rel
                                         tau-interval-lo
                                         tau-interval-hi-rel
                                         tau-interval-hi
                                         in-tau-intervalp
                                         max
                                         tau-bounder-+
                                         tau-bounder-*
                                         tau-bounder-mod
                                         tau-bounder-logand
                                         tau-bounder-logior
                                         tau-bounder-logxor
                                         tau-bounder-ash
                                         tau-interval-r)))))

; -----------------------------------------------------------------
; Syntactic Integers -- terms that are obviously integerp valued

(defun syntactic-integerp (x)

; We determine if pseudo-term x has an integer value.  But this function is a
; little stronger than that: it also checks that certain ASHes are applied to
; syntactic-integerp expressions even though that is not necessary to insure
; the integerp value ASH expression itself.  (ASH always returns an integer.)

; The dive through x is potentially expensive: x may contain thousands of
; function symbols.  But in a test on the largest state produced by Codewalker
; on the DES algorithm (a state containing 2+ million function symbols) in
; which we looked at every value expression in every !R (all of which are
; expected to be integers) we found that this function never looked at more
; than 10 function symbols before answering the question.  Despite the fact
; that the largest value expression inspected contained 147,233 function calls.
; The most expensive value expression we encountered (in terms of how many
; calls of syntactic-integerp are required) contained only 7 function calls,
; was of the form

; (+ '<int> (+ (* '<int> (R ...) (* '<int> (- (R ...)))))

; where the ... denote uninspected subterms, and required 10 calls of
; syntactic-integerp.  The truly gigantic value terms were cheap to analyze
; because they involved calls of obviously integral functions (like LOGAND)
; near the top.  So it is not clear the theoretical inefficiency of this
; function matters in practice.

  (declare (xargs :guard (pseudo-termp x)))
  (cond ((variablep x) nil)
        ((fquotep x) (integerp (cadr x)))
        (t (case (ffn-symb x)
             ((BINARY-+ BINARY-* MOD)
              (and (syntactic-integerp (fargn x 1))
                   (syntactic-integerp (fargn x 2))))
             (ASH (syntactic-integerp (fargn x 1)))
             ((HIDE UNARY--)
              (syntactic-integerp (fargn x 1)))
             ((IFIX BINARY-LOGAND BINARY-LOGIOR BINARY-LOGXOR R)
              t)
             (otherwise nil)))))

(local
 (defthm integerp-stateman-eval-syntactic-integerp
   (implies (syntactic-integerp x)
            (integerp (stateman-eval x alist)))
   :hints (("Goal" :expand (:free (x) (hide x))))
   :rule-classes (:rewrite :type-prescription)))

; -----------------------------------------------------------------
; Term Constructor:  IFIX

(defun cons-term-IFIX (x)

; Return a pseudo-term equivalent to (IFIX x).

  (declare (xargs :guard (pseudo-termp x)))
  (cond ((syntactic-integerp x)
         x)
        (t (hlist 'IFIX x))))

(defthm cons-term-IFIX-correct
  (equal (stateman-eval (cons-term-IFIX x) alist)
         (ifix (stateman-eval x alist))))

(defthm syntactic-integerp-cons-term-IFIX
  (syntactic-integerp (cons-term-IFIX x)))

(defthm pseudo-termp-cons-term-IFIX
  (implies (pseudo-termp x)
           (pseudo-termp (cons-term-IFIX x))))

(in-theory (disable cons-term-IFIX))

; -----------------------------------------------------------------
; Term Constructor:  MOD
; Metafunction for:  MOD

#+non-standard-analysis
(defthm rewrite-hack-for-acl2r
  (implies (rationalp x)
           (realp x)))

(defun meta-mod1-ainni (x k type-alist)

; X is a term, k is a natp, and we use ainni to return a term' equivalent to
; (MOD x 'k) under some hyps.  We return (mv term' hyps).

  (declare (xargs :guard (and (pseudo-termp x)
                              (natp k)
                              (type-alistp type-alist))
                  :guard-hints (("Goal"
                                 :in-theory (enable the-guard-mismatch-rules)))))

  (mv-let
   (flg hyps int)
   (ainni x nil type-alist)
   (cond
    ((and flg
          (< (tau-interval-hi int) k))
     (mv x hyps))
    (t (mv (hlist 'MOD x (hlist 'QUOTE k)) nil)))))

(defthm meta-mod1-ainni-correct-part-1
  (implies (and (pseudo-termp term)
                (natp k))
           (and (pseudo-termp (mv-nth 0 (meta-mod1-ainni term k type-alist)))
                (pseudo-term-listp (mv-nth 1 (meta-mod1-ainni term k type-alist))))))

(defthm meta-mod1-ainni-correct-part-2
  (implies (and (pseudo-termp term)
                (natp k)
                (stateman-eval (conjoin (mv-nth 1 (meta-mod1-ainni term k type-alist))) alist))
           (equal (stateman-eval (mv-nth 0 (meta-mod1-ainni term k type-alist)) alist)
                  (mod (stateman-eval term alist)
                       k)))
  :hints
  (("Goal" :use ((:instance ainni-correct-part-2a
                            (term term)
                            (hyps nil)
                            (type-alist type-alist))
                 (:instance ainni-correct-part-2b
                            (term term)
                            (hyps nil)
                            (type-alist type-alist)))
    :in-theory (disable ainni-correct-part-2a
                        ainni-correct-part-2b))))

(defthm syntactic-integerp-meta-mod1-ainni
  (implies (and (syntactic-integerp term)
                (natp k))
           (syntactic-integerp (mv-nth 0 (meta-mod1-ainni term k type-alist)))))

(in-theory (disable meta-mod1-ainni))

(defun mod-plus-meta-mod1 (term k2)

; Term is a term, treated like a sum, and k2 is non-zp.  We search down the
; addends of term and anytime we see a (MOD i 'k1) where i is a (syntactic)
; integerp and k2 | k1, we strip off the MOD.

  (declare (xargs :guard (and (pseudo-termp term)
                              (integerp k2)
                              (not (equal k2 0)))))
  (cond ((variablep term) term)
        ((fquotep term) term)
        ((eq (ffn-symb term) 'BINARY-+)
         (hlist 'BINARY-+
               (mod-plus-meta-mod1 (fargn term 1) k2)
               (mod-plus-meta-mod1 (fargn term 2) k2)))
        ((and (eq (ffn-symb term) 'MOD)
              (quotep (fargn term 2))
              (natp (cadr (fargn term 2)))
              (integerp (/ (cadr (fargn term 2)) k2)))
         (fargn term 1))
        (t term)))


(defthm syntactic-integerp-mod-plus-meta-mod1
  (implies (syntactic-integerp term)
           (syntactic-integerp (mod-plus-meta-mod1 term k2))))

(defthm mod-plus-meta-mod1-correct-part-1
   (implies (pseudo-termp term)
            (pseudo-termp (mod-plus-meta-mod1 term k2))))
(encapsulate
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))
 (defthm mod-plus-meta-mod1-correct-part-2
   (implies (and (syntactic-integerp term)
                 (not (zp k2)))
            (equal (mod (stateman-eval (mod-plus-meta-mod1 term k2) alist)
                        k2)
                   (mod (stateman-eval term alist)
                        k2)))))

(in-theory (disable mod-plus-meta-mod1))

(defun meta-mod1 (term type-alist)

; We return (mv term' hyps), where term' is equivalent to term under hyps.
; This function is interesting only if term is of the form (MOD x 'k) for some
; natp k.  Roughly speaking, it has the following rules built into it, for
; constants i, j, and k.

; [*1] (MOD x 0) = x, if x is a syntactic integer
; [*2] (MOD i k) = <computed answer>, if i and k are constants
; [*3] (MOD (MOD m j) k) = (MOD m j), if j<=k
; [*4] (MOD (MOD m j) k) = (MOD m k), if k divides j
; [*5] (MOD (R a i st) k) = (R a i st), if 256^i <= k
; [*6] (MOD x k) = x, if ainni says x < k
; [*7] (MOD (+ ... (MOD i k1) ..) k2) = (MOD (+ ... i ..) k2), if k2 divides k1

; (We apply [*6] to the output of [*7], so [*7] is tried before [*6].)

; This function is the workhorse in the meta-mod metafunction for simplifying
; MOD expressions and in the cons-term-MOD function for constructing new MOD terms.
; The metafunction version, meta-mod, uses the returned hyps to return an IF
; expression and the term constructor version, cons-term-MOD, passes the hyps on up.

  (declare (xargs :guard (and (pseudo-termp term)
                              (type-alistp type-alist))))
  (cond
   ((and (consp term)
         (eq (ffn-symb term) 'MOD)
         (quotep (fargn term 2))
         (natp (cadr (fargn term 2))))

; We know the term is of the form (MOD x 'k), where k is a natural.

    (let ((x (fargn term 1))
          (k (cadr (fargn term 2))))
      (cond
       ((eql k 0)                                      ; [*1]
        (mv (cond ((syntactic-integerp x)
                   x)
                  (t term))
            nil))
       ((variablep x)
        (mv term nil))
       ((quotep x)                                     ; [*2]
        (mv (if (rationalp (cadr x))
                (hlist 'QUOTE (mod (cadr x) k))
                term)
            nil))
       ((and (consp x)
             (eq (ffn-symb x) 'MOD)
             (quotep (fargn x 2))
             (natp (cadr (fargn x 2)))
             (not (eql (cadr (fargn x 2)) 0)))
        (let ((m (fargn x 1))
              (j (cadr (fargn x 2))))
          (cond
           ((<= j k) (mv x nil))                       ; [*3]
           ((and (integerp (/ j k))
                 (syntactic-integerp m))
            (meta-mod1 (hlist 'MOD m (hlist 'QUOTE k)) type-alist))      ; [*4]
           (t (meta-mod1-ainni x k type-alist)))))
       ((and (eq (ffn-symb x) 'R)
             (quotep (fargn x 2))
             (natp (cadr (fargn x 2)))
             (<= (expt 256 (cadr (fargn x 2))) k))

; Simplification of (MOD (R a 'i st) 'k), where 2^{8i} <= k, since
; (R a 'i st) < 2^{8i}.
        (mv x nil))                                    ; [*5]
       ((syntactic-integerp x)
        (meta-mod1-ainni                               ; [*6]([*7])
           (mod-plus-meta-mod1 x k)
           k type-alist))
       (t (meta-mod1-ainni                             ; [*6]
           x k type-alist)))))
   (t (mv term nil))))

#||
; Examples:
(defthm examples-of-meta-mod1
  (let ((ta `(((< (r '0 '8 st) '16) ,*ts-t*))))
    (and
     (equal (meta-mod1 '(MOD v '0) ta)
            (mv '(MOD V '0) nil))
     (equal (meta-mod1 '(MOD '26 '5) ta)
            (mv ''1 nil))
     (equal (meta-mod1 '(MOD (MOD v '11) '14) ta)
            (mv '(MOD V '11) nil))
     (equal (meta-mod1 '(MOD (MOD (R '123 '8 st) '15) '3) ta)
            (mv '(MOD (R '123 '8 ST) '3) nil))
     (equal (meta-mod1 '(MOD (MOD (MOD (R '123 '8 st) '15) '21) '3) ta)
            (mv '(MOD (R '123 '8 ST) '3) nil))
     (equal (meta-mod1 '(MOD (R '0 '1 st) '512) ta)
            (mv '(R '0 '1 ST) nil))
     (equal (meta-mod1 '(MOD (R '0 '8 st) '32) ta)
            (mv '(R '0 '8 ST)
                '((FORCE (NOT (< '15 (R '0 '8 ST)))))))
     (equal (meta-mod1 '(MOD (BINARY-+ '80
                                       (BINARY-* '8
                                                 (BINARY-LOGAND '32 (R '40 '8 ST))))
                             '1024)
                       nil)
            (mv '(BINARY-+ '80
                           (BINARY-* '8
                                     (BINARY-LOGAND '32 (R '40 '8 ST))))
                nil))
; Here is an example showing MOD of an arithmetic difference.  We know from the
; type-alist that R[40] is less than or equal to 34 and that R[48] is less than
; or equal to 44.  Their natural difference lies in the interval [0,34], so is
; below 35.

     (equal (meta-mod1 '(MOD (BINARY-+  (R '40 '8 ST) (UNARY-- (R '48 '8 st))) '35)
                       `(((< (R '40 '8 ST) '35) ,*ts-t*)
                         ((< (R '48 '8 ST) '45) ,*ts-t*)))
            (mv '(BINARY-+ (R '40 '8 ST)
                           (UNARY-- (R '48 '8 ST)))
                '((FORCE (NOT (< (R '40 '8 ST) (R '48 '8 ST))))
                  (FORCE (NOT (< '44 (R '48 '8 ST))))
                  (FORCE (NOT (< '34 (R '40 '8 ST)))))))))
  :rule-classes nil)
||#

(defthm syntactic-integerp-meta-mod1
  (implies (syntactic-integerp term)
           (syntactic-integerp (mv-nth 0 (meta-mod1 term type-alist)))))

(defthm meta-mod1-correct-part-1
   (implies (pseudo-termp term)
            (and (pseudo-termp (mv-nth 0 (meta-mod1 term type-alist)))
                 (pseudo-term-listp (mv-nth 1 (meta-mod1 term type-alist))))))

(encapsulate
 nil
 (local
  (include-book "arithmetic-5/top" :dir :system))

 (defthm meta-mod1-correct-part-2
   (implies (and (pseudo-termp term)
                 (stateman-eval (conjoin (mv-nth 1 (meta-mod1 term type-alist))) alist))
            (equal (stateman-eval (mv-nth 0 (meta-mod1 term type-alist)) alist)
                   (stateman-eval term alist)))))

(in-theory (disable meta-mod1))

(defun honjoin2 (t1 t2)
  (declare (xargs :guard t))
  (cond ((equal t1 *nil*) *nil*)
        ((equal t2 *nil*) *nil*)
        ((equal t1 *t*) t2)
        ((equal t2 *t*) t1)
        (t (hlist 'IF t1 t2 *nil*))))

(defun honjoin (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) *t*)
        ((endp (cdr l)) (car l))
        (t (honjoin2 (car l) (honjoin (cdr l))))))

(defthm honjoin-is-conjoin
  (equal (honjoin l) (conjoin l)))

(defun memoizable-meta-mod (term type-alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (type-alistp type-alist))))
  (mv-let (term1 hyps)
          (meta-mod1 term type-alist)
          (if hyps
              (hlist 'IF
                     (honjoin hyps)
                     term1
                     term)
              term1)))

(defun meta-mod (term mfc state)
  (declare (xargs :guard (pseudo-termp term))
           (ignore state))
  (memoizable-meta-mod (hons-copy term)
                       (hons-copy (mfc-type-alist mfc))))

(defun cons-term-MOD (x k type-alist)

; This is a ``term constructor'' in the sense that given a pseudo-term x and a
; natural k it returns (MOD x k), sort of.  More precisely, it returns (mv
; modxk hyps), where modxk is a pseudo-term equivalent to (MOD x 'k) provided
; hyps is true.  This is the term constructor version of the meta-mod
; metafunction; instead of returning an IF that tests the hyps this function
; passes the hyps up.

  (declare (xargs :guard (and (pseudo-termp x)
                              (natp k)
                              (type-alistp type-alist))))
  (meta-mod1 (hlist 'MOD x (hlist 'QUOTE k)) type-alist))

; Because cons-term-MOD is just a simple call of meta-mod1 (with the same signature)
; and meta-mod1 has been proved correct and disabled, there is no point in
; proving cons-term-MOD correct explicitly.  We just let it expand.

; -----------------------------------------------------------------
; Bounded Addresses

(defun bounded-address (a n type-alist)

; A is a term used as a read (or write) address and n is a non-0 natural.
; Consider reading n bytes starting at the value of a.  What byte addresses
; might be touched?  If a were a quoted natural, 'aconst, then the answer would
; be [aconst, aconst+n-1].  But in general we use ainni to bound a, picking up
; some hyps from the type-alist, and then increment the upper bound by n-1.
; Furthermore, the entire range of addresses must fix within *m-size*.  We
; return (mv flg hyps interval), where flg indicates whether we succeeded in
; bounding the range.

  (declare (xargs :guard (and (pseudo-termp a)
                              (natp n)
                              (not (eql n 0))
                              (type-alistp type-alist))
                  :guard-hints (("Goal"
                                 :in-theory (enable the-guard-mismatch-rules)))))

  (mv-let (flg hyps int)
          (ainni a nil type-alist)
          (if (and flg
                   (< (+ (- n 1) (tau-interval-hi int)) *m-size*))
              (mv t hyps
                  (make-tau-interval 'integerp
                                     nil (tau-interval-lo int)
                                     nil (+ (- n 1) (tau-interval-hi int))))
              (mv nil nil nil))))

(local
 (defthm in-tau-intervalp-linear-implications
   (implies (and (tau-intervalp int)
                 (in-tau-intervalp x int)
                 (tau-interval-lo int)
                 (tau-interval-hi int)
                 (eq (tau-interval-dom int) 'integerp) ; thus, rels are <=
                 )
            (and (<= (tau-interval-lo int) x)
                 (<= x (tau-interval-hi int))))
   :rule-classes (:rewrite :linear)))

(local
 (defthm in-tau-intervalp-make-tau-interval-integerp
   (implies (and (integerp lo)
                 (integerp hi))
            (equal (in-tau-intervalp
                    x
                    (make-tau-interval 'integerp nil lo nil hi))
                   (and (integerp x)
                        (<= lo x)
                        (<= x hi))))))

(local
 (defthm bounded-address-correct-part-1
   (implies (and (pseudo-termp x)
                 (not (zp n))
                 (mv-nth 0 (bounded-address x n type-alist)))
            (and (pseudo-term-listp (mv-nth 1 (bounded-address x n type-alist)))
                 (tau-intervalp (mv-nth 2 (bounded-address x n type-alist)))
                 (eq (tau-interval-dom (mv-nth 2 (bounded-address x n type-alist))) 'integerp)
                 (natp (tau-interval-lo (mv-nth 2 (bounded-address x n type-alist))))
                 (natp (tau-interval-hi (mv-nth 2 (bounded-address x n type-alist))))
                 (< (tau-interval-hi (mv-nth 2 (bounded-address x n type-alist))) *m-size*)))
   :hints (("Goal" :use ((:instance ainni-correct-part-2a
                                    (term x)
                                    (hyps nil)
                                    (type-alist type-alist)))
            :in-theory (disable ainni-correct-part-2a)))
   :rule-classes
   ((:rewrite
     :corollary
     (implies (and (pseudo-termp x)
                   (not (zp n))
                   (mv-nth 0 (bounded-address x n type-alist)))
              (and (pseudo-term-listp (mv-nth 1 (bounded-address x n type-alist)))
                   (tau-intervalp (mv-nth 2 (bounded-address x n type-alist)))
                   (eq (tau-interval-dom (mv-nth 2 (bounded-address x n type-alist))) 'integerp))))
    (:type-prescription
     :corollary
     (implies (and (pseudo-termp x)
                   (not (zp n))
                   (mv-nth 0 (bounded-address x n type-alist)))
              (natp (tau-interval-lo (mv-nth 2 (bounded-address x n type-alist))))))
    (:type-prescription
     :corollary
     (implies (and (pseudo-termp x)
                   (not (zp n))
                   (mv-nth 0 (bounded-address x n type-alist)))
              (natp (tau-interval-hi (mv-nth 2 (bounded-address x n type-alist))))))
    (:linear
     :corollary
     (implies (and (pseudo-termp x)
                   (not (zp n))
                   (mv-nth 0 (bounded-address x n type-alist)))
              (< (tau-interval-hi (mv-nth 2 (bounded-address x n type-alist))) *m-size*))))))

(local
 (defthm bounded-address-correct-part-2
   (implies (and (pseudo-termp x)
                 (not (zp n))
                 (mv-nth 0 (bounded-address x n type-alist))
                 (stateman-eval (conjoin (mv-nth 1 (bounded-address x n type-alist)))
                                alist))
            (and (in-tau-intervalp (stateman-eval x alist)
                                   (mv-nth 2 (bounded-address x n type-alist)))
                 (natp (stateman-eval x alist))
                 (<= (tau-interval-lo (mv-nth 2 (bounded-address x n type-alist)))
                     (stateman-eval x alist))
                 (<= (+ (- n 1) (stateman-eval x alist))
                     (tau-interval-hi (mv-nth 2 (bounded-address x n type-alist))))
                 (< (+ (- n 1) (stateman-eval x alist)) *m-size*)))
   :hints (("Goal" :use ((:instance ainni-correct-part-2a
                                    (term x)
                                    (hyps nil)
                                    (type-alist type-alist))
                         (:instance ainni-correct-part-2b
                                    (term x)
                                    (hyps nil)
                                    (type-alist type-alist)))
            :expand ((:free (x) (hide x)))
            :in-theory (disable ainni-correct-part-2a
                                ainni-correct-part-2b)))
   :rule-classes
   ((:rewrite
     :corollary
     (implies (and (mv-nth 0 (bounded-address x n type-alist))
                   (pseudo-termp x)
                   (not (zp n))
                   (stateman-eval (conjoin (mv-nth 1 (bounded-address x n type-alist)))
                                  alist))
              (and (in-tau-intervalp (stateman-eval x alist)
                                     (mv-nth 2 (bounded-address x n type-alist)))
                   (integerp (stateman-eval x alist)))))
    (:type-prescription
     :corollary
     (implies (and (mv-nth 0 (bounded-address x n type-alist))
                   (pseudo-termp x)
                   (not (zp n))
                   (stateman-eval (conjoin (mv-nth 1 (bounded-address x n type-alist)))
                                  alist))
              (natp (stateman-eval x alist))))
    (:linear
     :corollary
     (implies (and (mv-nth 0 (bounded-address x n type-alist))
                   (pseudo-termp x)
                   (not (zp n))
                   (stateman-eval (conjoin (mv-nth 1 (bounded-address x n type-alist)))
                                  alist))
              (and (<= 0 (stateman-eval x alist))
                   (<= (tau-interval-lo (mv-nth 2 (bounded-address x n type-alist)))
                       (stateman-eval x alist))
                   (<= (+ (- n 1) (stateman-eval x alist))
                       (tau-interval-hi (mv-nth 2 (bounded-address x n type-alist))))
                   (< (+ (- n 1) (stateman-eval x alist)) *m-size*))))
    )))

(in-theory (disable bounded-address))

(defthm stateman-eval-conjoin-lemma1
  (implies (member-equal ''nil a)
           (not (stateman-eval (conjoin a) alist))))

(defthm stateman-eval-conjoin-lemma-2
  (implies (and (stateman-eval (conjoin a) alist)
                (member-equal hyp a))
           (stateman-eval hyp alist)))

(defthm stateman-eval-conjoin-union-equal
  (iff (stateman-eval (conjoin (union-equal a b)) alist)
       (and (stateman-eval (conjoin a) alist)
            (stateman-eval (conjoin b) alist))))

; Note About the (consp (cdd...dr x)) Tests Below: Pseudo-termp does not check
; the arity of ``function calls.''  So just knowing that x is a pseudo-term
; that starts with !R, say, doesn't tell us that (fargn x 1), ..., (fargn x 4)
; are pseudo-terms.  By checking that sufficient args exist we can get
; pseudo-termp to expand to tell us those things.

; Essay on the Design Decisions Regarding Mixed Write-Over-Write versus Mixed
; Read-Over-Write

; When we are trying to add a new write expression to a state expression we can
; just stack it on top of the existing nest, regardless of how it overlaps the
; other writes.  As an optimization, we can delete any earlier writes that are
; shadowed out by it.  But we don't have to.  We choose to delete the
; ``perfectly shadowed'' writes but not imperfectly shadowed ones.  An example of
; perfect shadowing would be if we were have this state expression:

; (!r 0 8 v0 (!r 300 8 v300 (!r 12 4 v12 st)))

; and wished to write w12 to the 4 bytes starting at 12.  Instead of creating

; (!r 12 4 w12 (!r 0 8 v0 (!r 300 8 v300 (!r 12 4 v12 st))))

; we would delete the (!r 12 4 v12 ...) and return

; (!r 12 4 w12 (!r 0 8 v0 (!r 300 8 v300 st)))

; But if we started with that same initial state

; (!r 0 8 v0 (!r 300 8 v300 (!r 12 4 v12 st)))

; and wrote to address 7 with (!r 7 8 xxx ...)

; we would return

; (!r 7 8 xxx (!r 0 8 v0 (!r 300 8 v300 (!r 12 4 v12 st))))

; even though that outer write ``imperfectly'' shadows part of the write at 0 and
; part of the write at 12.

; We think that it will be rare for a state expression to get large because of
; many imperfect shadowing writes.  Chances are (we guess) that repeated
; imperfect shadowing writes will perfectly shadow each other and thus be
; eliminated.  For example, if one wrote (!r 7 8 yyy ...) over the state above,
; it perfectly shadows the (!r 7 8 xxx ...) and would thus eliminate that inner
; one.  Furthermore, dealing with imperfect shadows by changing the earlier
; writes they touch will generally increase the size of the state expression.

; Note that the decision to delete perfectly shadowed writes means that the
; now-redundant write can be identified by its depth in the expression.
; For example, the write in

; (!r 0 8 v0 (!r 300 8 v300 (!r 12 4 v12 st)))

; that is perfectly shadowed by (!r 12 4 w12 ...) is at depth 2.  Thus, when we
; identify the first (only) perfectly shadowed write in a state expression we
; return its depth, which means we can dive in and delete it without having to
; do any interval analysis.

; Meanwhile, we do not use this function to resolve read-over-write.  That is
; done by mx-rover (``mixed read-over-write''), which carefully walks down the
; nest, possibly taking bytes from multiple writes in the state expression.
; For example to read 8 bytes starting at 7 in (!r 0 8 v0 (!r 300 8 v300 (!r 12
; 4 v12 st))) we would take the byte at 7 from v0, and bytes at 8, 9, 10, and
; 11 from st, and the bytes at 12, 13, and 14 from v12.  Note that the write at
; 300 is irrelevant even though it happened chronologically between relevant
; writes.

; While this design is a bit asymmetric -- we handle completely general
; read-over-write with full precision but permit some level of shadowing in
; write-over-write -- we think it is a good heuristic balance.

; In a generic sense, !I, !S, and !R are all ``writes.''  But in the first two
; there is no address or extent involved.  Furthermore, no hyps are involved.
; So the question arises: when looking for a !I or !S write (and its depth) do
; we use the same function as for !R?  Or do we write separate functions?  We
; have decided to write two separate functions: one for finding !I/!S style
; writes and one for !R.  In earlier versions of this package (up through
; stateman12.lisp) we combined them into one function but it just got too
; confusing, especially after adding mx-rover and obviating the need for the
; function in resolving R over !R.  While separate functions is a bit
; redundant, it's simpler and more direct: we don't take arguments or return
; results that are never used.

; For want of better terminology we call !I and !S ``scalar writes'' and !R
; ``vector writes''.  Of course, a typical state expression is a nest of both
; but looking for the relevant scalar write is easier, so we start with it.

; The finding of a scalar or a vector write results in a 0-based depth in the
; original state expression at which the relevant write was found.  We will
; later develop one function for deleting the write at that depth.  That is, we
; won't bother to define ``delete scalar write at depth k'' and a separate
; ``delete vector write at k.''

; Finally, when searching for a particular scalar write we either find one or
; we don't, right?  If we find it, we need to know the depth (so we can delete
; the shadowed write in the write-over-write case) and we need the old value
; written (so we can return it in the read-over-write case).  If we don't find
; a shadowed write, we need the state at the bottom of the state expression (so
; we can transform the read-over-write to a read of the base state).

; So find-assignment to scalar returns (mv flg ans), where if flg is non-nil it
; is the depth and ans is the value written to the target scalar by the write
; at that depth, and if flg is nil, then ans is the base state of the state
; expression.

; But when we move from finding scalar writes to finding vector writes the
; situation is a little different.  That function is only used in
; write-over-write.  So if we find a perfect shadowed write in the state, we
; return its depth and the hyps to justify the equivalence of the two targets
; involved.  But if we fail to find a shadowed write, we just return (mv nil
; nil).  We don't need a base state.

(defthm pseudo-termp-caddr-opener
  (implies (and (pseudo-termp x)
                (consp (cddr x)))
           (pseudo-termp (caddr x)))
  :hints (("Goal" :expand (pseudo-termp x))))

(defthm pseudo-termp-caddddr-opener
  (implies (and (pseudo-termp x)
                (consp (cddddr x)))
           (pseudo-termp (car (cddddr x))))
  :hints (("Goal" :expand (pseudo-termp x))))

(defun find-assignment-to-scalar (fn st)

; Fn is one of the scalar write operations, !I or !S, and st is a state
; expression.  We return (mv flg ans) where flg is either a natp or nil and
; indicates whether there is an assignment to fn in st: if flg is a natp, there
; is such an assignment, flg is the (0-based) depth of that assignment in st,
; and ans is the value assigned by the write at that depth.  If flg is nil, ans
; is the base state of st.

; Note on PR v AC (tail-recursive) versions of this function.  Proofs are
; simpler if this is PR function but execution is faster if we make it tail
; recursive by introducing an accumulator for storing the current depth.
; However, there is not much difference.

; An Experiment:

; We constructed a state expression containing one million !R expressions around
; (!I PC ST).  We coded this function as is and via tail recursion, with and
; without guards verified.  We then ran all four versions.

;              not-guard-verified guard-verified
;  PR              0.06 sec           0.05 sec
;  AC              0.06 sec           0.04 sec

; The biggest state expression constructed in the DES codewalk contains
; millions of function calls but is only of depth 60!  We don't expect the PR v
; AC difference to show up much in such shallow expressions and so opt to code
; elegantly.

  (declare (xargs :measure (acl2-count st)
                  :guard (and (symbolp fn)
                              (pseudo-termp st))))

; The consp tests below are to ensure that the fargs we dive into remain
; pseudo-termps.  They're actually necessary only for guard verification.

  (cond
   ((atom st) (mv nil st))
   ((or (eq (ffn-symb st) '!I)
        (eq (ffn-symb st) '!S))
    (cond ((consp (cddr st))
           (cond
            ((eq fn (ffn-symb st))
             (mv 0 (fargn st 1)))
            (t (mv-let (flg ans)
                       (find-assignment-to-scalar
                        fn
                        (fargn st 2))
                       (mv (if flg (+ 1 flg) nil)
                           ans)))))
          (t (mv nil st))))
   ((and (eq (ffn-symb st) '!R)
         (consp (cddddr st)))
    (mv-let (flg ans)
            (find-assignment-to-scalar
             fn
             (fargn st 4))
            (mv (if flg (+ 1 flg) nil)
                ans)))
   (t (mv nil st))))

(defthm natp-mv-nth-0-find-assignment-to-scalar
  (implies (mv-nth 0 (find-assignment-to-scalar fn st))
           (natp (mv-nth 0 (find-assignment-to-scalar fn st))))
  :rule-classes :forward-chaining)

(defthm find-assignment-to-scalar-!i-correct
  (implies (pseudo-termp st)
           (equal (i (stateman-eval st alist))
                  (if (mv-nth 0 (find-assignment-to-scalar '!i st))
                      (stateman-eval (mv-nth 1 (find-assignment-to-scalar '!i st)) alist)
                      (i (stateman-eval (mv-nth 1 (find-assignment-to-scalar '!i st)) alist)))))

; The above formula is a bad rewrite rule because it can attempt to loop.  I
; don't think it will loop but it will at least waste time trying.  The rules
; below are tamed: if the appropriate (mv-nth 0 (find-assignment-to-scalar
; ...)) is on the type-alist, the appropriate rule will try to fire.

  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (mv-nth 0 (find-assignment-to-scalar '!i st))
                  (pseudo-termp st))
             (equal (i (stateman-eval st alist))
                    (stateman-eval (mv-nth 1 (find-assignment-to-scalar '!i st)) alist)))
    :backchain-limit-lst (0 nil))
   (:rewrite
    :corollary
    (implies (and (not (mv-nth 0 (find-assignment-to-scalar '!i st)))
                  (pseudo-termp st))
             (equal (i (stateman-eval st alist))
                    (i (stateman-eval (mv-nth 1 (find-assignment-to-scalar '!i st)) alist))))
    :backchain-limit-lst (0 nil))))

(defthm find-assignment-to-scalar-!s-correct
  (implies (pseudo-termp st)
           (equal (s (stateman-eval st alist))
                  (if (mv-nth 0 (find-assignment-to-scalar '!s st))
                      (stateman-eval (mv-nth 1 (find-assignment-to-scalar '!s st)) alist)
                      (s (stateman-eval (mv-nth 1 (find-assignment-to-scalar '!s st)) alist)))))

; The above formula is a bad rewrite rule because it can attempt to loop.  I
; don't think it will loop but it will at least waste time trying.  The rules
; below are tamed: if the appropriate (mv-nth 0 (find-assignment-to-scalar
; ...)) is on the type-alist, the appropriate rule will try to fire.

  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (mv-nth 0 (find-assignment-to-scalar '!s st))
                  (pseudo-termp st))
             (equal (s (stateman-eval st alist))
                    (stateman-eval (mv-nth 1 (find-assignment-to-scalar '!s st)) alist)))
    :backchain-limit-lst (0 nil))
   (:rewrite
    :corollary
    (implies (and (not (mv-nth 0 (find-assignment-to-scalar '!s st)))
                  (pseudo-termp st))
             (equal (s (stateman-eval st alist))
                    (s (stateman-eval (mv-nth 1 (find-assignment-to-scalar '!s st)) alist))))
    :backchain-limit-lst (0 nil))))

; We will later develop and prove the code for deleting the assignment at depth
; k.  Now we develop the code for finding an assignment to a vector address.
; Remember that this function is only used to resolve a !R over !R (not R over
; !R) and looks for perfect shadowing only.  Furthermore, recall the principle
; of ``absorbtion'' from byte-addressed-state:

;  (!R a n va1
;      (!R b1 k1 vb1
;          (!R b2 k2 vb2
;              ...
;              (!R a n va2 st)...)))
; =
;  (!R a n va1
;      (!R b1 k1 vb1
;          (!R b2 k2 vb2
;              ...
;              st...)))

; even if a.n and one or more of the bi.ki are equal or overlap.  A suitable
; version of this general fact is proved as the !r-inner-absorbtion rule of
; byte-addressed-state.lisp and will be used when we prove meta-!R correct.

; Because of absorbtion, we do not need to maintain the hypotheses that might
; establish that a.n is different from bi.ki.  We just scan down the state
; expression looking for a !R to an address and extension equivalent to the
; target and return its depth and the hyps necessary to establish the
; equivalence of that pair of addresses.  But because this scan requires
; comparing the interval of the known target to each of the intervals of
; addresses in the original state, we compute the interval of the target and
; then start the scan.

; Possible optimization: It might be more efficient to make a preliminary pass
; through the state looking for a syntactically identical write address and
; thereby often avoid interval analysis on the target.

; The function we develop below is named find-assignment-to-vector but it has a
; recursive helper.  For sanity, here are the informal specs of the two
; functions:

; * find-assignment-to-vector1: for a given target address, a.n, with known
;     hyps and interval, hyps-a and int-a, we find the first !R that matches
;     it.  We return (mv depth hyps) or (mv nil nil).  This function uses the
;     predicate perfectly-shadowedp, defined below.

; * find-assignment-to-vector: for a given target address, a.n, we compute the
;     containing interval and hyps and then use find-assignment-to-vector1 to
;     find out if there is a match.  We return (mv depth hyps) or (mv nil nil).

(defun perfectly-shadowedp (a n hyps-a int-a st type-alist)

; St is known to be of the form (!R b 'k v st), where k is a natp.  We
; determine whether this write to b.k is perfectly shadowed by a write to a.n.
; Hyps-a and int-a are the hyps and bounded interval containing a.  N is a
; non-zero natural.  We return either (mv t hyps) or (mv nil nil), where hyps
; justifies the equivalence of a.n with b.k if that is established.

  (declare (xargs :guard (and (pseudo-termp a)
                              (natp n)
                              (not (eql n 0))
                              (pseudo-term-listp hyps-a)
                              (tau-intervalp int-a)
                              (tau-interval-lo int-a)
                              (tau-interval-hi int-a)
                              (pseudo-termp st)
                              (nvariablep st)
                              (not (fquotep st))
                              (eq (ffn-symb st) '!R)
                              (quotep (fargn st 2))
                              (natp (cadr (fargn st 2)))
                              (type-alistp type-alist))

; This hint is necessary for reasons not unlike those explained above
; the-guard-mismatch-rules.

                  :guard-hints
                  (("Subgoal 2"
                    :in-theory (disable bounded-address-correct-part-1)
                    :use (:instance bounded-address-correct-part-1
                                    (x (CADR ST))
                                    (n (CADR (CADDR ST)))
                                    (type-alist type-alist))))))
  (cond
   ((equal n (cadr (fargn st 2)))

; St is of the form (!R b 'k v st1) where k=n (the non-zero nat extension).  So
; we can ask whether a=b.  We have two ways of answering that, described below.
; But if indeed a=b then the top-level !R of st is perfectly shadowed by the
; write we're about to do.  One way to establish a=b is to ask if they're
; syntactically identical.  The other is interval analysis, but we don't want
; to do analysis on b if it is not necessary.

    (cond
     ((equal a (fargn st 1))
; We don't even needs the hyps of a.
      (mv t nil))
     ((equal (tau-interval-lo int-a)
             (+ (- n 1) (tau-interval-hi int-a)))

; A.n is confined to an interval exactly as long its extension.  So a is
; the lower bound of that interval and if we could confirm that b is in
; the same interval we know a=b.

      (mv-let (flg hyps-b int-b)
              (bounded-address (fargn st 1) (cadr (fargn st 2)) type-alist)
              (cond
               ((and flg
                     (equal (tau-interval-lo int-a) (tau-interval-lo int-b))
                     (equal (tau-interval-hi int-a) (tau-interval-hi int-b)))
                (mv t (union-equal hyps-a hyps-b)))
               (t (mv nil nil)))))
     (t (mv nil nil))))
   (t (mv nil nil))))

(defthm pseudo-term-listp-union-equal
  (implies (pseudo-term-listp a)
           (equal (pseudo-term-listp (union-equal a b))
                  (pseudo-term-listp b))))

(defthm perfectly-shadowedp-correct-part-1
  (implies (and (mv-nth 0 (perfectly-shadowedp a n hyps-a int-a st type-alist))
                (pseudo-termp a)
                (not (zp n))
                (pseudo-term-listp hyps-a)
                (pseudo-termp st))
           (pseudo-term-listp (mv-nth 1 (perfectly-shadowedp a n hyps-a int-a st type-alist)))))

(defthm perfectly-shadowedp-correct-part-2
  (implies (and (mv-nth 0 (perfectly-shadowedp
                           a n
                           (mv-nth 1 (bounded-address a n type-alist))
                           (mv-nth 2 (bounded-address a n type-alist))
                           st
                           type-alist))
                (mv-nth 0 (bounded-address a n type-alist))
                (eq (ffn-symb st) '!R)
                (quotep (fargn st 2))
                (natp (cadr (fargn st 2)))
                (consp (cddddr st)) ; <----- needed?
                (pseudo-termp a)
                (not (zp n))
                (pseudo-termp st)
                (stateman-eval
                 (conjoin
                  (mv-nth 1 (perfectly-shadowedp
                             a n
                             (mv-nth 1 (bounded-address a n type-alist))
                             (mv-nth 2 (bounded-address a n type-alist))
                             st
                             type-alist)))
                 alist))
           (and (equal (stateman-eval (cadr st) alist)
                       (stateman-eval a alist))
                (equal (stateman-eval (caddr st) alist)
                       n)))
  :hints (("Goal"
           :in-theory (disable tau-interval-dom
                               tau-interval-lo-rel
                               tau-interval-lo
                               tau-interval-hi-rel
                               tau-interval-hi
                               in-tau-intervalp))))

(in-theory (disable perfectly-shadowedp))

(defun find-assignment-to-vector1 (a n hyps-a int-a st type-alist)

; For a given target address and non-zero extent, a.n, with known hyps and
; interval, hyps-a and int-a, we find the first (most shallow) !R that matches
; it.  We return (mv depth hyps) or (mv nil nil).  Depth is 0-based.

  (declare (xargs :guard (and (pseudo-termp a)
                              (natp n)
                              (not (eql n 0))
                              (pseudo-term-listp hyps-a)
                              (tau-intervalp int-a)
                              (tau-interval-lo int-a)
                              (tau-interval-hi int-a)
                              (pseudo-termp st)
                              (type-alistp type-alist))))

  (cond
   ((variablep st) (mv nil nil))
   ((fquotep st) (mv nil nil))
   ((and (or (eq (ffn-symb st) '!i)
             (eq (ffn-symb st) '!s))
         (consp (cddr st)))
    (mv-let (flg hyps)
            (find-assignment-to-vector1 a n hyps-a int-a
                                        (fargn st 2)
                                        type-alist)
            (if flg
                (mv (+ 1 flg) hyps)
                (mv nil nil))))
   ((and (eq (ffn-symb st) '!R)
         (quotep (fargn st 2))
         (natp (cadr (fargn st 2)))
         (consp (cddddr st)))

; Note: At one point the checks on (fargn st 2), above, were inside
; perfectly-shadowedp instead.  However, if we encounter a !R with a
; non-natural extension, our !r-inner-absorbtion rule isn't applicable.  So
; making the checks above we can fall through the (mv nil nil) case instead of
; claiming to step over this !R.

    (mv-let (flg hyps)
            (perfectly-shadowedp a n hyps-a int-a st type-alist)
            (cond
             (flg ; st is a !R that is perfectly shadowed by a write to a.n
              (mv 0 hyps))
             (t
              (mv-let (flg hyps)
                      (find-assignment-to-vector1 a n hyps-a int-a
                                                  (fargn st 4)
                                                  type-alist)
                      (if flg
                          (mv (+ 1 flg) hyps)
                          (mv nil nil)))))))
   (t (mv nil nil))))

(defun find-assignment-to-vector (a n st type-alist)

; For a given target address, a.n, we compute the containing interval and hyps
; and then use find-assignment-to-vector1 to find out if there is a match.  We
; return (mv depth hyps) or (mv nil nil).

  (declare (xargs :guard (and (pseudo-termp a)
                              (natp n)
                              (not (eql n 0))
                              (pseudo-termp st)
                              (type-alistp type-alist))
                  :guard-hints
                  (("Goal"
                    :in-theory (disable bounded-address-correct-part-1)
                    :use (:instance bounded-address-correct-part-1
                                    (x a)
                                    (n n)
                                    (type-alist type-alist))))))

  (mv-let
   (flg hyps-a int-a)
   (bounded-address a n type-alist)
   (cond
    ((null flg)
     (mv nil nil))
    (t (find-assignment-to-vector1 a n hyps-a int-a st type-alist)))))

(defun strip-optional-hide (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((and (consp term)
              (eq (ffn-symb term) 'HIDE)
              (consp (cdr term)))
         (mv t (fargn term 1)))
        (t (mv nil term))))

(defun memoizable-meta-i (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond
   ((and (consp term)
         (eq (ffn-symb term) 'I)
         (consp (cdr term)))
    (mv-let (hiddenp st-arg)
            (strip-optional-hide (fargn term 1))
            (mv-let
             (flg ans)
             (find-assignment-to-scalar '!I st-arg)
             (cond
              (flg ans)
              ((and hiddenp
                    (equal ans (fargn (fargn term 1) 1)))
               term)
              (t (hlist 'I ans))))))
   (t term)))

(defun meta-i (term)
  (declare (xargs :guard (pseudo-termp term)))
  (memoizable-meta-i (hons-copy term)))

(defun memoizable-meta-s (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond
   ((and (consp term)
         (eq (ffn-symb term) 'S)
         (consp (fargn term 1)))
    (mv-let (hiddenp st-arg)
            (strip-optional-hide (fargn term 1))
            (mv-let
             (flg ans)
             (find-assignment-to-scalar '!S st-arg)
             (cond
              (flg ans)
              ((and hiddenp
                    (equal ans (fargn (fargn term 1) 1)))
               term)
              (t (hlist 'S ans))))))
   (t term)))

(defun meta-s (term)
  (declare (xargs :guard (pseudo-termp term)))
  (memoizable-meta-s (hons-copy term)))

; -----------------------------------------------------------------
; Term Constructor:  HIDE

(defun add-HIDE (hiddenp x)

; If hiddenp is t, add a HIDE to x unless x is a variable, quote, IF, HIDE, or
; R.  If hiddenp is nil, don't add a HIDE.  The idea is as follows: x is a
; value recovered from a state by associng down and finding an assignment to
; the relevant address.  Hiddenp is t if that original state was embedded in a
; HIDE.  If so, we are acting as though the values recorded in it have already
; been rewritten and thus we should HIDE them when we extract them.  If that
; original state wasn't hidden, we shouldn't HIDE extracted values.

  (declare (xargs :guard (pseudo-termp x)))
  (if hiddenp
      (cond ((variablep x) x)
            ((fquotep x) x)
            ((eq (ffn-symb x) 'IF)
             x)
            ((eq (ffn-symb x) 'HIDE)
             x)
            ((eq (ffn-symb x) 'R)
             x)
            (t (hlist 'HIDE x)))
      x))

(defthm stateman-eval-add-HIDE
  (equal (stateman-eval (add-HIDE hiddenp x) alist)
         (stateman-eval x alist))
  :hints (("Goal" :expand (:free (x) (HIDE x)))))

(in-theory (disable add-HIDE))

;-----------------------------------------------------------------
; Now we begin the development of mx-rover

(defun meta-binary-+-with-const (k a)

; K is a natp and a is a term.  We return a term equivalent to
; `(BINARY-+ ',k ,a) except in the expected normal form.

  (declare (xargs :guard (and (natp k)
                              (pseudo-termp a))))
  (cond ((variablep a)
         (hlist 'BINARY-+ (hlist 'QUOTE k) a))
        ((fquotep a)
         (cond ((acl2-numberp (cadr a))
                (hlist 'QUOTE (+ k (cadr a))))
               (t (hlist 'QUOTE k))))
        ((and (eq (ffn-symb a) 'BINARY-+)
              (nvariablep (fargn a 1))
              (fquotep (fargn a 1))
              (acl2-numberp (cadr (fargn a 1))))
         (hlist 'BINARY-+
                (hlist 'QUOTE
                       (+ k (cadr (fargn a 1))))
                (fargn a 2)))
        (t (hlist 'BINARY-+ (hlist 'QUOTE k) a))))

(defthm pseudo-termp-meta-binary-+-with-const
  (implies (and (acl2-numberp k)
                (pseudo-termp a))
           (pseudo-termp (meta-binary-+-with-const k a))))

(defthm stateman-meta-binary-+-with-const
  (implies (and (acl2-numberp k)
                (pseudo-termp a))
           (equal (stateman-eval (meta-binary-+-with-const k a) alist)
                  (+ k (stateman-eval a alist)))))

(in-theory (disable meta-binary-+-with-const))

(defun syntactic-natp (x)

; We determine if pseudo-term x has a natural number value.

; This function just punts on UNARY--, which in context means that we will not
; be able to simplify (r a n (!r b k v st)) when b is an expression involving
; subtraction!  To fix this, would have to augment the function in two ways:
; first, it would produce a second answer containing the hyps we're assuming to
; make its answer correct, and then it could look for (+ y (- x)) and insist
; that x and y are natps (syntactically) and that (<= x y), where this last
; hypothesis is spit out.

; But we don't bother here.  The DES algorithm never writes to any address
; expression involving subtraction.  It never writes to anything but the stack,
; which is always a quoted constant!

; The dive through x is potentially expensive: x may contain thousands of
; function symbols.  This function is an excellent candidate for memoization.
; By the way, in an earlier version of Stateman, we called ainni on every write
; address to confirm that it was natp valued, and ainni is more expensive than
; this.

  (declare (xargs :guard (pseudo-termp x)))
  (cond ((variablep x) nil)
        ((fquotep x) (natp (cadr x)))
        (t (case (ffn-symb x)
             ((BINARY-+ BINARY-* BINARY-LOGAND BINARY-LOGIOR BINARY-LOGXOR ASH MOD)
              (and (syntactic-natp (fargn x 1))
                   (syntactic-natp (fargn x 2))))
             (HIDE (syntactic-natp (fargn x 1)))
             (R t)
             (otherwise ; including UNARY--
              nil)))))

(defthm syntactic-natp-correct
  (implies (syntactic-natp x)
           (natp (stateman-eval x alist)))
  :hints (("Goal" :expand (:free (x) (hide x))))
  :rule-classes :type-prescription)

(in-theory (disable syntactic-natp))

(defun common-reference-address1 (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((variablep x) (mv 0 x))
        ((fquotep x)
         (if (natp (cadr x))
             (mv (cadr x) *0*)
             (mv 0 x)))
        ((and (eq (ffn-symb x) 'BINARY-+)
              (quotep (fargn x 1))
              (natp (cadr (fargn x 1))))
         (mv (cadr (fargn x 1)) (fargn x 2)))
        (t (mv 0 x))))

(defun common-reference-address (a b)

; Given two terms, a and b, we determine whether they are both offsets from a
; common reference address.  We return either (mv nil nil nil) or (mv ca cb
; ref) such that ca and cb are naturals, a = (+ ca ref), and b = (+ cb ref).

  (declare (xargs :guard (and (pseudo-termp a)
                              (pseudo-termp b))))
  (mv-let (ca refa)
          (common-reference-address1 a)
          (mv-let (cb refb)
                  (common-reference-address1 b)
                  (cond ((and (equal refa refb)
                              (syntactic-natp refb))
                         (mv ca cb refa))
                        (t (mv nil nil nil))))))

; We divide correctness into five parts to avoid free var problems when possible.

(defthm common-reference-address-correct-part-1
  (implies (and (pseudo-termp a)
                (pseudo-termp b))
           (pseudo-termp (mv-nth 2 (common-reference-address a b)))))

(defthm common-reference-address-correct-part-2
  (implies (mv-nth 0 (common-reference-address a b))
           (and (natp (mv-nth 0 (common-reference-address a b)))
                (natp (mv-nth 1 (common-reference-address a b)))))
  :rule-classes (:forward-chaining))

(defthm common-reference-address-correct-part-3
  (implies (mv-nth 0 (common-reference-address a b))
           (equal (stateman-eval a alist)
                  (+ (mv-nth 0 (common-reference-address a b))
                     (stateman-eval (mv-nth 2 (common-reference-address a b)) alist)))))

(defthm common-reference-address-correct-part-4
  (implies (mv-nth 0 (common-reference-address a b))
           (equal (stateman-eval b alist)
                  (+ (mv-nth 1 (common-reference-address a b))
                     (stateman-eval (mv-nth 2 (common-reference-address a b)) alist)))))

(defthm common-reference-address-correct-part-5
  (implies (mv-nth 0 (common-reference-address a b))
           (natp (stateman-eval (mv-nth 2 (common-reference-address a b)) alist)))
  :rule-classes
  ((:forward-chaining
    :trigger-terms ((stateman-eval (mv-nth 2 (common-reference-address a b)) alist)))))

(in-theory (disable common-reference-address))

(defun extended-bounded-integerp-intervals-intersectp (int1 n int2 k)

; Int1 and int2 are bounded INTEGERP intervals and n and k are non-zero
; naturals.  Let int1' and int2' be int1 and int2 with their upper bounds
; extended by n-1 and k-1 respectively.  We determine int1' and int2'
; intersect.  We could just extend both and use
; tau-integerp-intervals-intersectp but we're trying to avoid consing.  The
; context in which this is used is: int1 and int2 are the intervals containing
; two addresses, a and b, and we wish to do byte-level operations (R or !R) on
; n bytes starting at a and k bytes starting from b.

  (declare (xargs :guard (and (tau-intervalp int1)
                              (eq (tau-interval-dom int1) 'integerp)
                              (tau-interval-lo int1)
                              (tau-interval-hi int1)
                              (tau-intervalp int2)
                              (eq (tau-interval-dom int2) 'integerp)
                              (tau-interval-lo int2)
                              (tau-interval-hi int2)
                              (natp n)
                              (natp k)
                              (not (eql n 0))
                              (not (eql k 0)))))

  (let ((lo1 (tau-interval-lo int1))
        (hi1 (+ -1 n (tau-interval-hi int1)))
        (lo2 (tau-interval-lo int2))
        (hi2 (+ -1 k (tau-interval-hi int2))))
    (or (and (<= lo1 lo2)
             (<= lo2 hi1))
        (and (<= lo2 lo1)
             (<= lo1 hi2)))))

; This is a rewrite rule so we backchain!  In action, b is sometimes a
; difference expression.

(local
 (defthm integerp-expt-as-rewrite
   (implies (and (natp a)
                 (natp b))
            (integerp (expt a b)))))

(local
 (defthm nzp-expt-as-linear
   (implies (not (zp a))
            (< 0 (expt a b)))
   :rule-classes :linear))

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defun mx-rover (a hyps1 int1 n st type-alist)

  (declare (xargs :measure (llist (nfix n) (acl2-count st))
                  :well-founded-relation l<
                  :guard (and (pseudo-termp a)
                              (pseudo-term-listp hyps1)
                              (tau-intervalp int1)
                              (eq (tau-interval-dom int1) 'integerp)
                              (tau-interval-lo int1)
                              (tau-interval-hi int1)
                              (natp (tau-interval-lo int1))
                              (natp n)
                              (pseudo-termp st)
                              (type-alistp type-alist))
                  :verify-guards nil))

; Think of this function as simplifying
;  (R 'a 'n (!R 'b 'k v st))
; where st is some state expression.  We know that a-hyps --> a \in a-int.

; A is a term (possibly a quoted number).  N is a natural.  Int1 is an interval
; containing the value of a and hyps1 is the list of hypotheses assumed for
; that to be true.  St is the state expression from which we're reading bytes.
; We return (mv ans hyps) where ans is either nil (meaning we couldn't do
; anything) or an algebraic expression whose value is equal to (R a 'n st) and
; hyps is a list of relevant hyps.  When ans is nil, hyps is nil too.  Examples
; of cases where ans = nil include when we encounter an address ainni cannot
; bound and when we encounter a pair of addresses that may or may not overlap.

; Termination: This function removes one updater (!I, !S, or !R) at a time from
; st until we have determined the answer, except sometimes we won't remove a !R
; and will instead shrink the R interval.  So termination depends on the
; lexicographic combination of the length of the R interval, n, and the size of
; st.

; Note: The name of this function is derived from ``mixed read-over-write'' or
; ``mixed R over !R'', except that we don't like putting the exclamation mark
; in the middle of a symbol because Emacs doesn't parse it well.  Besides,
; ``rover'' is pronouceable!

  (cond
   ((zp n) (mv ''0 hyps1))
   ((or (variablep st)
        (fquotep st))
    (mv (hlist 'R a (hlist 'QUOTE n) st) hyps1))
   ((or (eq (ffn-symb st) '!I)
        (eq (ffn-symb st) '!S))
    (mx-rover a hyps1 int1 n (fargn st 2) type-alist))
   ((and (eq (ffn-symb st) '!R)
         (quotep (fargn st 2))
         (natp (cadr (fargn st 2))))
    (let ((b (fargn st 1))
          (k (cadr (fargn st 2)))
          (v (fargn st 3))
          (st1 (fargn st 4)))
      (cond
       ((zp k) ; Won't happen but we need to know k>0 below.
        (mx-rover a hyps1 int1 n st1 type-alist))

; At this point we know we are dealing with (R a 'n (!R b 'k v st1)).  In
; general there are 5 cases and have to be able to determine which case we're
; in.  We can do this if we can put a and b into the forms:

; a = ca + ref
; b = cb + ref

; for some natural constants ca and cb, and some common term ref.  Among other
; situations, this describes the case where a and b are known integer addresses
; (let ref = 0) and the case where a and b are non-constant but identical terms
; (let ca = cb = 0).

       (t
        (mv-let
         (ca cb ref)
         (common-reference-address a b)
         (cond
          (ca

; So we now have a and b in the desired form.  We now figure out which of the 5
; cases we're in.

; Note on Our Cyptic Notation: We illustrate the way the 5 ways the read can
; overlap the write in a linear memory.  Imagine lower addresses to the left
; and higher ones to the right on the line.  We use {a...n} or {a--n} to denote
; the interval to be read and [b---k] to indicate the interval written.  We put
; dots in the interval to be read when the bytes read are independent of the
; write and we put hyphens in when the bytes read are extracted from the value
; written.  So ``{a...n} [b---'' is meant to denote the case where we are
; reading entirely to the left or below the address to which we're writing.  In
; this case, the upper bound of the write interval ``k]'' is irrelevant.  After
; the case description we show the algebraic expression we test to confirm that
; we're in that case.  The first time we write the test we phrase it in terms
; of the actual read and write addresses, a and b, and their byte counts, n and
; k, respectively.  But then we simplify the test expression to express it in
; terms of the constants we actually have, namely ca, cb, n, and k.

; (Case 1) Read before Write: {a...n}     [b---
;  Test:
;  (<= (+ a n) b)
;  = (<= (+ ca ref n) (+ cb ref))
;  = (<= (+ ca n) cb)

; (Case 2) Read after Write:  [b--k]     {a...
;  Test:
;  (<= (+ b k) a)
;  = (<= (+ cb ref k) (+ ca ref))
;  = (<= (+ cb k) ca)

; (Case 3) Read from the value Written: [b--{a--n}--k]
;  Test:
;  (and (<= b a) (<= (+ a n) (+ b k)))
;  = (and (<= (+ cb ref) (+ ca ref)) (<= (+ ca ref n) (+ cb ref k)))
;  = (and (<= cb ca) (<= (+ ca n) (+ cb k)))

; (Case 4) Read some of value written and then continue:  [b--{a------k]...
;  Note that the write interval ends before we get all n bytes needed.
;  Test:
;  (and (<= b a) (< a (+ b k)) (< (+ b k) (+ a n)))
;  (and (<= (+ cb ref) (+ ca ref)) (< (+ ca ref) (+ cb ref k)) (< (+ cb ref k) (+ ca ref n)))
;  (and (<= cb ca) (< ca (+ cb k)) (< (+ cb k) (+ ca n)))

; (Case 5) Read some before Write and then continue: {a..[b---
;  Test:
;  (and (< a b) (< b (+ a n)))
;  = t (if all of the above are false)

; Below we show that these five cases are mutually exclusive and exhaustive.

; (defun 1of5 (p1 p2 p3 p4 p5)
; Exactly one of these five propositions is true ;
;  (cond (p1 (and (not p2) (not p3) (not p4) (not p5)))
;        (p2 (and (not p1) (not p3) (not p4) (not p5)))
;        (p3 (and (not p1) (not p2) (not p4) (not p5)))
;        (p4 (and (not p1) (not p2) (not p3) (not p5)))
;        (t p5)))

; (thm
; (implies (and (natp a) (natp b) (not (zp n)) (not (zp k)))
;          (1of5 (<= (+ a n) b)                                        ; (Case 1)
;                (<= (+ b k) a)                                        ; (Case 2)
;                (and (<= b a) (<= (+ a n) (+ b k)))                   ; (Case 3)
;                (and (<= b a) (< a (+ b k)) (< (+ b k) (+ a n)))      ; (Case 4)
;                (and (< a b) (< b (+ a n)))                           ; (Case 5)
;                )))

           (cond

; So now we test the 5 cases, in order:

; (Case 1) Read before Write: {a...n}     [b---
            ((<= (+ ca n) cb)
             (mx-rover a hyps1 int1 n st1 type-alist))

; (Case 2) Read after Write:  [b--k]     {a...
            ((<= (+ cb k) ca)
             (mx-rover a hyps1 int1 n st1 type-alist))

; (Case 3) Read from the value Written: [b--{a--n}--k]
            ((and (<= cb ca)
                  (<= (+ ca n) (+ cb k)))
             (mv-let (mod-term mod-hyps)
                     (cons-term-MOD (if (zp (- ca cb))
                                        (cons-term-IFIX v)
                                        (hlist 'ASH
                                               (cons-term-IFIX v)
                                               (hlist 'QUOTE (* -8 (- ca cb)))))
                                    (expt 256 n)
                                    type-alist)
                     (mv mod-term
                         (union-equal mod-hyps hyps1))))

; (Case 4) Read some of value written and then continue:  [b--{a------k]...
            ((and (<= cb ca)
                  (< ca (+ cb k))
                  (< (+ cb k) (+ ca n)))

; We will read a certain number of bytes from v and then recur by reading the
; rest of the n bytes we need from the address b+k.  So we have to create the
; new read address b+k = cb + ref + k = (cb + k) + ref.  Of course, if ref =
; *0* we just use the constant part.  Note that we know the constant part is
; positive: cb is a natural and k is non-zero.

; We also need an interval containing this address.  But we know that the
; interval for ca+ref is int1, so the interval (cb+k)+ref -- with apologies for
; overloading our notation -- is int1-ca+cb+k.  Is this an interval over the
; naturals?  Yes.  The lower bound of int1 is at least ca, so subtracting ca
; away at worst sets the lower bound to 0.

             (let* ((bytes-read (- k (- ca cb))))
               (mv-let (ans2 hyps2)
                       (mx-rover (if (equal ref *0*)
                                     (hlist 'QUOTE (+ cb k))
                                     (hlist 'BINARY-+ (hlist 'QUOTE (+ cb k)) ref))
                                 hyps1
                                 (make-tau-interval
                                  'INTEGERP
                                  nil
                                  (+ (tau-interval-lo int1) (- ca) cb k)
                                  nil
                                  (+ (tau-interval-hi int1) (- ca) cb k))
                                 (- n bytes-read) st1 type-alist)
                       (cond
                        ((null ans2) (mv nil nil))
                        (t (mv-let (mod-term mod-hyps)
                                   (if (zp bytes-read)
                                       (mv *0* nil)
                                       (cons-term-MOD (if (zp (- ca cb))
                                                          (cons-term-IFIX v)
                                                          (hlist 'ASH
                                                                 (cons-term-IFIX v)
                                                                 (hlist 'QUOTE (* -8 (- ca cb)))))
                                                      (expt 256 bytes-read)
                                                      type-alist))
                                   (mv (hlist 'BINARY-+
                                              mod-term
                                              (if (zp bytes-read)
                                                  ans2
                                                  (hlist 'ASH ans2 (hlist 'QUOTE (* 8 bytes-read)))))
                                       (union-equal mod-hyps hyps2))))))))

; (Case 5) Read some before Write and then continue: {a..[b---
            (t ; (and (< ca cb) (< cb (+ ca n)))
             (let ((bytes-read (- cb ca)))
               (mv-let (ans1 hyps2)
                       (mx-rover a hyps1 int1 bytes-read st1 type-alist)
                       (cond
                        ((not ans1) (mv nil nil))
                        (t
                         (let ((new-a (meta-binary-+-with-const k b)))
                           (mv-let (ans2 hyps3)
                                   (if (< (+ cb k) (+ ca n))
                                       (mv-let (temp hyps4)
                                               (mx-rover new-a
                                                         hyps2
                                                         (make-tau-interval 'INTEGERP
                                                                            nil
                                                                            (+ (tau-interval-lo int1)
                                                                               (- ca)
                                                                               cb k)
                                                                            nil
                                                                            (+ (tau-interval-hi int1)
                                                                               (- ca)
                                                                               cb k))
                                                         (+ ca (- cb) (- k) n)
                                                         st1
                                                         type-alist)
                                               (cond
                                                ((null temp) (mv nil nil))
                                                (t
                                                 (mv-let (mod-term mod-hyps)
                                                         (cons-term-MOD (cons-term-IFIX v)
                                                                        (EXPT 256 k)
                                                                        type-alist)
                                                         (mv (hlist 'BINARY-+
                                                                    mod-term
                                                                    (hlist 'ASH
                                                                           temp
                                                                           (hlist 'QUOTE (* 8 k))))
                                                             (union-equal mod-hyps hyps4))))))
                                       (mv-let (mod-term mod-hyps)
                                               (cons-term-MOD (cons-term-IFIX v)
                                                              (EXPT 256 (+ ca (- cb) n))
                                                              type-alist)
                                               (mv mod-term
                                                   (union-equal mod-hyps hyps2))))
                                   (cond
                                    ((not ans2) (mv nil nil))
                                    (t (mv (hlist 'BINARY-+
                                                  ans1
                                                  (hlist 'ASH ans2 (hlist 'QUOTE (* 8 bytes-read))))
                                           hyps3))))))))))))
          (t

; At this point we know we are dealing with (R a 'n (!R b 'k v st1)) except we
; know of no obvious relationship between terms a and b.  So all we can do is
; rely on intervals to determine that they are equal or disjoint.

           (mv-let (flg hyps1+2 int2)
                   (ainni b hyps1 type-alist)
                   (cond
                    ((not flg) (mv nil nil))
                    ((and (eql (tau-interval-lo int1) (tau-interval-hi int1))
                          (eql (tau-interval-lo int2) (tau-interval-hi int2))
                          (eql (tau-interval-lo int1) (tau-interval-lo int2)))

; According to ainni, a and b have exactly the same value.  Since we know they
; are not identical terms, this can only happen if hyps on the type-alist
; restrict both to specific values.  But, hey, it happened.  We use the same
; code we used for the (equal a (fargn st 1)) case above.

                     (cond
                      ((<= n k)
                       (mv-let (mod-term mod-hyps)
                               (cons-term-MOD (cons-term-IFIX v)
                                              (expt 256 n)
                                              type-alist)
                               (mv mod-term
                                   (union-equal mod-hyps hyps1+2))))
                      (t (mv-let
                          (mod-term mod-hyps)
                          (cons-term-MOD (cons-term-IFIX v)
                                         (expt 256 k)
                                         type-alist)
                          (let ((new-a (meta-binary-+-with-const k a)))
                            (mv-let (ans2 hyps3)
                                    (mx-rover new-a
                                              hyps1+2
                                              (make-tau-interval
                                               'INTEGERP
                                               nil (+ k (tau-interval-lo int1))
                                               nil (+ k (tau-interval-hi int1)))
                                              (- n k)
                                              st1 type-alist)
                                    (cond
                                     ((not ans2) (mv nil nil))
                                     (t (mv (hlist 'BINARY-+ mod-term (hlist 'ASH ans2 (hlist 'QUOTE (* 8 k))))
                                            (union-equal mod-hyps hyps3))))))))))
                    ((extended-bounded-integerp-intervals-intersectp int1 n int2 k)

; In this case, reading n bytes starting at a may or may not overlap with the k
; bytes starting at b.  There is nothing we can do.

                     (mv nil nil))

; Reading n successive bytes starting from a will not overlap the k bytes
; written successively starting at b.  So we can just recur.

                    (t (mx-rover a hyps1+2 int1 n st1 type-alist)))))))))))
   (t
; This case should never arise:  we're dealing with (R a 'n st) where st is not a
; state expression.
    (mv nil nil))))

(local
 (defthm subsetp-equal-union-equal-2
   (subsetp-equal hyps1 (union-equal hyps1 hyps))))

(local
 (defthm subsetp-equal-union-equal-1-lemma-1
   (implies (and (not (member e hyps))
                 (member e b))
            (not (subsetp-equal b hyps)))))

(local
 (defthm subsetp-equal-union-equal-1-lemma-2
   (implies (and (not (member e hyps))
                 (member e b))
            (not (subsetp-equal (union-equal a b) hyps)))
   :hints (("Goal" :induct (union-equal a b)))))

(local
 (defthm subsetp-equal-union-equal-1
   (equal (subsetp-equal (union-equal hyps1 hyps2) hyps)
          (and (subsetp-equal hyps1 hyps)
               (subsetp-equal hyps2 hyps)))))

(local
 (defthm subsetp-equal-union-equal-3
   (subsetp-equal hyps (union-equal hyps1 hyps))))

(local
 (defthm stateman-eval-member-equal
   (implies (and (member-equal e b)
                 (not (stateman-eval e alist)))
            (not (stateman-eval (conjoin b) alist)))))

(local
 (defthm stateman-eval-subsetp-equal
   (implies (and (not (stateman-eval (conjoin a) alist))
                 (subsetp-equal a b))
            (not (stateman-eval (conjoin b) alist)))))

(local
 (defthm member-equal-union-equal
   (iff (member-equal e (union-equal a b))
        (or (member-equal e a)
            (member-equal e b)))))

(local
 (defthm union-equal-associative
   (equal (union-equal (union-equal a b) c)
          (union-equal a (union-equal b c)))))

(local
 (defthm subsetp-equal-union-equal-4
   (implies (subsetp-equal a b)
            (subsetp-equal a (union-equal b c)))))

(local
 (defthm subsetp-equal-union-equal-5
   (implies (subsetp-equal a b)
            (subsetp-equal a (union-equal c b)))))

(encapsulate
 nil

 (local
  (encapsulate
   nil

; The proofs here are being done with minimal arithmetic theory, so I need
; to make a few simple facts explicit for the next main theorem...

   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm double-negative
     (equal (- (- a)) (fix a)))

   (defthm sum-of-opposites-a
     (and (equal (+ a (- a)) 0)
          (equal (+ a (- a) b) (fix b))))

   (defthm sum-of-opposite-b
     (equal (+ (* -8 x)
               (* -8 (- x)))
            0))

   (defthm sum-of-opposite-c
     (equal (+ (* 8 x)
               (* 8 (- x)))
            0))

   (defthm ash-non-integer
     (implies (not (integerp v))
              (equal (ash v n) 0)))

   (defthm ash-0
     (equal (ash 0 n) 0))

   (defthm ash-v-0
     (equal (ash v 0) (ifix v)))

   (defthm mod-0
     (equal (mod 0 n) 0))

   ))

 (local
  (defthm bounded-tau-interval-facts-part-1
    (and (equal (tau-interval-dom (make-tau-interval dom lo-rel lo hi-rel hi)) dom)
         (equal (tau-interval-lo-rel (make-tau-interval dom lo-rel lo hi-rel hi)) lo-rel)
         (equal (tau-interval-lo (make-tau-interval dom lo-rel lo hi-rel hi)) lo)
         (equal (tau-interval-hi-rel (make-tau-interval dom lo-rel lo hi-rel hi)) hi-rel)
         (equal (tau-interval-hi (make-tau-interval dom lo-rel lo hi-rel hi)) hi)
         (implies (and (tau-intervalp int1)
                       (equal (tau-interval-dom int1) 'integerp))
                  (and (equal (tau-interval-lo-rel int1) nil)
                       (equal (tau-interval-hi-rel int1) nil))))))

 (local
  (defthm bounded-tau-interval-facts-part-2
    (implies (and (tau-intervalp int1)
                  (eq (tau-interval-dom int1) 'integerp)
                  (natp (tau-interval-lo int1)) ; finite lower bound
                  (natp (tau-interval-hi int1))) ; finite upper bound
             (<= (tau-interval-lo int1)
                 (tau-interval-hi int1)))
    :rule-classes :linear))

 (local
  (in-theory (disable make-tau-interval
                      tau-intervalp
                      tau-interval-dom
                      tau-interval-lo-rel
                      tau-interval-lo
                      tau-interval-hi-rel
                      tau-interval-hi)))

 (local
  (defthm r-at-size-0
    (implies (zp n)
             (equal (r a n st) 0))
    :hints (("Goal" :in-theory (enable r)))))

 (local
  (defthm nth-nil
    (equal (nth a nil) nil)
    :hints (("Goal" :in-theory (enable nth)))))

 (local
  (defthm r-nil
    (equal (r a n nil) 0)
    :hints (("Goal" :in-theory (enable r mi)))))

 (defthm mx-rover-preserves-hyps
   (implies (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))
            (subsetp-equal hyps1
                           (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist))))
   :hints (("Subgoal *1/27"
            :in-theory (disable SUBSETP-EQUAL-TRANSITIVE)
            :use (:instance SUBSETP-EQUAL-TRANSITIVE
                            (a hyps1)
                            (b (MV-NTH 1 (AINNI (CADR ST) HYPS1 TYPE-ALIST)))
                            (c (MV-NTH 1
                                       (MX-ROVER A
                                                  (MV-NTH 1 (AINNI (CADR ST) HYPS1 TYPE-ALIST))
                                                  INT1 N
                                                  (CAR (CDDDDR ST))
                                                  TYPE-ALIST)))))
           ("Subgoal *1/24"
            :in-theory (disable SUBSETP-EQUAL-TRANSITIVE)
            :use (:instance SUBSETP-EQUAL-TRANSITIVE
                            (a hyps1)
                            (b (MV-NTH 1 (AINNI (CADR ST) HYPS1 TYPE-ALIST)))
                            (c (mv-nth 1 (MX-ROVER (META-BINARY-+-WITH-CONST (CADR (CADDR ST))
                                                                              A)
                                                    (MV-NTH 1 (AINNI (CADR ST) HYPS1 TYPE-ALIST))
                                                    (MAKE-TAU-INTERVAL 'INTEGERP
                                                                       NIL
                                                                       (+ (TAU-INTERVAL-HI INT1)
                                                                          (CADR (CADDR ST)))
                                                                       NIL
                                                                       (+ (TAU-INTERVAL-HI INT1)
                                                                          (CADR (CADDR ST))))
                                                    (+ N (- (CADR (CADDR ST))))
                                                    (CAR (CDDDDR ST))
                                                    TYPE-ALIST))))
            )))

 (defthm mx-rover-preserves-pseudo-term-listp
   (implies (and (pseudo-termp a)
                 (pseudo-term-listp hyps1)
                 (pseudo-termp st))
            (pseudo-term-listp (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist)))))

; This rule introduces a lot of cases and we don't want it in general.  But it
; is also very useful because it rewrites an almost arbitrary (r a n (!r b k v
; st)) to eliminate the !r.  So we don't make it local since that would
; preclude its outside of Stateman.  We simply disable it when this development
; is done.

 (defthm explosive-r-!r
   (implies (and (natp a)
                 (natp b)
                 (not (zp n))
                 (not (zp k)))
            (equal (r a n (!r b k v st))
                   (cond
                    ((<= (+ a n) b) ; (Case 1)
                     (r a n st))
                    ((<= (+ b k) a) ; (Case 2)
                     (r a n st))
                    ((and (<= b a) (<= (+ a n) (+ b k))) ; (Case 3)
                     (mod (if (zp (- a b))
                              (ifix v)
                              (ash (ifix v) (* -8 (- a b))))
                          (expt 256 n)))
                    ((and (<= b a) (< a (+ b k)) (< (+ b k) (+ a n))) ; (Case 4)
                     (let* ((bytes-read (- k (- a b)))
                            (ans2 (r (+ b k)
                                     (- n bytes-read)
                                     st)))
                       (if (zp bytes-read)
                           (+ (mod (ifix v)
                                   (expt 256 bytes-read))
                              ans2)
                           (+ (mod (ash (ifix v) (* -8 (- a b)))
                                   (expt 256 bytes-read))
                              (ash ans2 (* 8 bytes-read))))))
                    (t ; (and (< a b) (< b (+ a n)))                  ; (Case 5)
                     (let* ((bytes-read (- b a))
                            (ans1 (r a bytes-read st))
                            (ans2 (if (< (+ b k) (+ a n))
                                      (+ (mod (ifix v) (expt 256 k))
                                         (ash (r (+ b k) (+ a (- b) (- k) n) st)
                                              (* 8 k)))
                                      (mod (ifix v) (expt 256 (+ a (- b) n))))))
                       (+ ans1 (ash ans2 (* 8 bytes-read))))))))
   :hints (("Goal"
            :in-theory (enable mx-rover-correct-lemma1
                               mx-rover-correct-lemma2
                               mx-rover-correct-lemma3)))
   :rule-classes :rewrite)

; Aesthetically, the next lemma, r-!r-nil-nil, belongs up with r-nil, but it's
; easiest to prove by using explosive-r-!r so we delayed its proof.

 (local
  (defthm r-!r-nil-nil
    (implies (and (natp a)
                  (natp b)
                  (not (zp n))
                  (not (zp k)))
             (equal (r a n (!r b k nil nil)) 0))
    :hints (("Goal" :in-theory (enable r !r)))))

 (defthm mx-rover-correct
   (implies (and (pseudo-termp a)
                 (pseudo-term-listp hyps1)
                 (tau-intervalp int1)
                 (equal (tau-interval-dom int1) 'integerp)
                 (natp (tau-interval-lo int1))
                 (natp (tau-interval-hi int1))
                 (in-tau-intervalp (stateman-eval a alist) int1)
                 (natp n)
                 (pseudo-termp st)
                 (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))
                 (stateman-eval (conjoin (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist)))
                                alist))
            (equal (stateman-eval (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))
                                  alist)
                   (R (stateman-eval a alist)
                      n
                      (stateman-eval st alist))))
   :hints (("Goal"
            :induct (mx-rover a hyps1 int1 n st type-alist)

; Because we have no real constraints on st (other than that it is a
; pseudo-termp) the proof entertains the possibilities that either or both of v
; and st1 in (!I v st1), (!S v st1), and (!R a n v st1) are NIL.  But when ACL2
; tries to evaluate !I or !S on two nils, it fails and a HIDE is wrapped around
; it.  To avoid that, we disable the executable-counterparts of those two
; updaters.  Our proof does not confront the prover with !R expressions applied
; to constants.

            :in-theory (disable (:executable-counterpart !I)
                                (:executable-counterpart !S)))

           ("Subgoal *1/18"
            :use ((:instance ainni-correct-part-2a
                             (term (cadr st))
                             (hyps hyps1)
                             (type-alist type-alist))
                  (:instance ainni-correct-part-2b
                             (term (cadr st))
                             (hyps hyps1)
                             (type-alist type-alist)))
            :in-theory (disable ainni-correct-part-2a
                                ainni-correct-part-2b))
           ("Subgoal *1/16"
            :use ((:instance ainni-correct-part-2a
                             (term (cadr st))
                             (hyps hyps1)
                             (type-alist type-alist))
                  (:instance ainni-correct-part-2b
                             (term (cadr st))
                             (hyps hyps1)
                             (type-alist type-alist)))
            :in-theory (disable ainni-correct-part-2a
                                ainni-correct-part-2b))
           ("Subgoal *1/14"
            :use ((:instance ainni-correct-part-2a
                             (term (cadr st))
                             (hyps hyps1)
                             (type-alist type-alist))
                  (:instance ainni-correct-part-2b
                             (term (cadr st))
                             (hyps hyps1)
                             (type-alist type-alist)))
            :in-theory (disable ainni-correct-part-2a
                                ainni-correct-part-2b
                                ))
           )
   :rule-classes
   ((:rewrite)
; This next rule handles the case where no hyps are generated.
    (:rewrite
     :corollary
     (implies (and (pseudo-termp a)
                   (pseudo-term-listp hyps1)
                   (tau-intervalp int1)
                   (equal (tau-interval-dom int1) 'integerp)
                   (natp (tau-interval-lo int1))
                   (natp (tau-interval-hi int1))
                   (in-tau-intervalp (stateman-eval a alist) int1)
                   (natp n)
                   (pseudo-termp st)
                   (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))
                   (not (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist))))
              (equal (stateman-eval (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))
                                    alist)
                     (R (stateman-eval a alist)
                        n
                        (stateman-eval st alist)))))))
 (defthm mx-rover-preserves-pseudo-termp
   (implies (and (pseudo-termp a)
                 (pseudo-term-listp hyps1)
                 (pseudo-termp st)
                 (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist)))
            (pseudo-termp (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist)))))


 )

(in-theory (disable mx-rover explosive-r-!r))

; -----------------------------------------------------------------


(verify-guards mx-rover
               :hints
               (("Goal" :do-not-induct t
                 :in-theory (e/d (the-guard-mismatch-rules)
                                 (tau-interval-dom
                                  tau-interval-lo-rel
                                  tau-interval-lo
                                  tau-interval-hi-rel
                                  tau-interval-hi
                                  in-tau-intervalp)))))

; Below I prove two simple corollaries about mx-rover.  I'll call them A and B
; for short.  A follows from MX-ROVER-PRESERVES-HYPS and
; STATEMAN-EVAL-SUBSETP-EQUAL, above.  B follows trivially from A, since the
; CONJOIN of NIL is 'T.

; Note that A and B have the same first hyps (which, coincidentally take care
; of all the free vars) and the same conclusions.  So A will be tried whenever
; B is needed.  B is proved simply by rewriting with A.

; It took me a long time to figure out that I needed to state B explicitly.  I
; sort of have a heuristic that says it is not necessary to state a rewrite
; rule that follows from other rewrite rules by simple rewriting.

; I thought that since B follows by applying A and rewriting that having A
; would be sufficient in any context.  Unfortunately, during the proof of
; META-R-CORRECT below B is needed to relieve a hypothesis in another lemma
; (BOUNDED-ADDRESS-CORRECT-PART-2).  When A is tried for that purpose the
; ancestors check stops us from rewriting the second hyp of A because it is
; more complicated than an ancestor, so we can't use A.  But if you have B
; around explicitly, you can use it because its second hyp is different and
; simpler.

(defthm stateman-eval-conjoin-mx-rover-A
  (implies
   (and (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))
        (stateman-eval
         (conjoin (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist)))
         alist))
   (stateman-eval (conjoin hyps1) alist)))

(defthm stateman-eval-conjoin-mx-rover-B
  (implies
   (and (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))
        (not (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist))))
   (stateman-eval (conjoin hyps1) alist)))

; -----------------------------------------------------------------

; This next section develops a little simplifier, named meta-ash-ash, for
; normalizing certain ASH expressions.  We export the minimal theory that
; establishes the correctness of our little simplifier.  Meta-R will use
; meta-ash-ash to normalize the result of mx-rover.

(defun meta-map-ash (lst i)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (natp i))))
  (cond
   ((endp lst) nil)
   (t (let ((x1 (cond
                 ((variablep (car lst)) (hlist 'ASH (car lst) (hlist 'QUOTE i)))
                 ((quotep (car lst))
                  (cond ((integerp (cadr (car lst)))
                         (hlist 'QUOTE (ash (cadr (car lst)) i)))
                        (t *0*)))
                 ((and (eq (ffn-symb (car lst)) 'ash)
                       (quotep (fargn (car lst) 2))
                       (natp (cadr (fargn (car lst) 2))))
                  (hlist 'ASH
                         (fargn (car lst) 1)
                         (hlist 'QUOTE (+ i (cadr (fargn (car lst) 2))))))
                 (t (hlist 'ASH (car lst) (hlist 'QUOTE i))))))
        (cons x1 (meta-map-ash (cdr lst) i))))))

(defun meta-ash-ash1 (x)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((variablep x) (list x))
        ((fquotep x) (list x))
        ((eq (ffn-symb x) 'binary-+)
         (append (meta-ash-ash1 (fargn x 1))
                 (meta-ash-ash1 (fargn x 2))))
        ((and (eq (ffn-symb x) 'ash)
              (quotep (fargn x 2))
              (natp (cadr (fargn x 2))))
         (meta-map-ash (meta-ash-ash1 (fargn x 1)) (cadr (fargn x 2))))
        (t (list x))))

(defthm pseudo-term-listp-meta-ash-ash1
  (implies (pseudo-termp x)
           (pseudo-term-listp (meta-ash-ash1 x))))

(defthm pseudo-term-listp-merge-term-order
  (implies (and (pseudo-term-listp l1)
                (pseudo-term-listp l2))
           (pseudo-term-listp (merge-term-order l1 l2))))

(defthm pseudo-term-listp-evens
  (implies (pseudo-term-listp l)
           (pseudo-term-listp (evens l))))

(defthm pseudo-term-listp-merge-sort-term-order
  (implies (pseudo-term-listp l)
           (pseudo-term-listp (merge-sort-term-order l))))

(defun hhhjoin (fn args)
; Like xxxjoin except uses HONS
  (declare (xargs :guard (if (true-listp args) (cdr args) nil)))
  (if (cdr (cdr args))
      (hons fn
            (hons (car args)
                  (hons (hhhjoin fn (cdr args)) nil)))
      (hons fn args)))

(defthm hhhjoin-is-xxxjoin
  (equal (hhhjoin fn args) (xxxjoin fn args)))

(defun meta-ash-ash (x)

; Normalize term x by applying these rules at the top-level:

; (ASH (+ i j) k) = (+ (ASH i k) (ASH j k))
; (ASH (ASH i j) k) = (ASH i (+ j k))

; to generate a list of ASH-expressions and and then building a term-ordered,
; right-associated +-nest.  Essentially we flatten x into a list of ASH
; expressions and then xxxjoin them with +.  But you can't call xxxjoin on a
; singleton list, thus the (endp (cdr lst)) check below.  This is really
; checking for lst being a singleton, since we know meta-ash-ash1 always
; returns a consp.

  (declare (xargs :guard (pseudo-termp x)

; The problem here is the same as that solved for ainni by
; the-guard-mismatch-rules, namely, we can prove pseudo-term-listp of something
; (in this case merge-sort-term-order) but are challenged to prove true-listp
; of it.  There's not a backchaining link and we don't think we want to make
; one.

                  :guard-hints (("Goal"
                                 :in-theory
                                 (disable pseudo-term-listp-merge-sort-term-order)
                                 :use (:instance pseudo-term-listp-merge-sort-term-order
                                       (l (META-ASH-ASH1 X)))))))
  (let ((lst (merge-sort-term-order
              (meta-ash-ash1 x))))
    (cond
     ((endp (cdr lst)) (car lst))
     (t (hhhjoin 'binary-+ lst)))))

#||
; Example:
(meta-ash-ash '(BINARY-+ (MOD (ASH (IFIX V) '-24) '256)
                         (ASH (BINARY-+ (R '4 '2 ST)
                                        (ASH (MOD (IFIX W) '256) '16))
                              '8)))
; ==>
(BINARY-+ (ASH (R '4 '2 ST) '8)
          (BINARY-+ (ASH (MOD (IFIX W) '256) '24)
                    (MOD (ASH (IFIX V) '-24) '256)))
||#

; We will prove that the term returned by (meta-ash-ash x) has the same value as
; x, provided x is a ``syntactic integer-valued expression.''

; To use the correctness of meta-ash-ash in the proof of meta-R we will have to
; show that meta-R supplies meta-ash-ash with a syntactic-integerp expression.
; That expression is the first value of a successful mx-rover call.  So after
; proving meta-ash-ash correct we go on to prove that the first result of
; mx-rover is a syntactic-integerp.

; Essay on the History of Meta-Ash-Ash and its Proof of Correctness

; The development of meta-ash-ash proceeded in two steps.  The first version
; did not have merge-sort-term-order and thus returned the addends in the order
; they were left after distributing.

; Handling the singleton case turned out to be messy, even in
; verison one of this function.  If (meta-ash-ash1 x) is a singleton the
; element of that list is not necessarily x!  If x were (ASH (ASH i j) k), the
; singleton will contain (ASH i (+ j k)).  They eval to the same thing.  This
; proof was bulled through as a special case of meta-ash-ash-correct, which
; talks about summing a list of numbers (singleton or not).
; See the hint for "Subgoal 1" in meta-ash-ash-correct below.

; In step two of the development of meta-ash-ash we added
; merge-sort-term-order.  Naturally, this required revisiting the singleton
; case, only this time through the lens of an intervening
; merge-sort-term-order.

; In the spirit of the old proof we bulled through it.  For each property of
; merge-sort-term-order that we needed we started by proving the corresponding
; property of evens and odds and then moved up to merge-term-order before
; tackling merge-sort-term-order.  The whole exercise was frustratingly
; complicated.  We thought we were done and tried the meta-ash-ash proof only
; to discover we needed one more property, about the len of
; merge-sort-term-order.

; Humorous Aside: I am reminded of Robin Williams' superb if obscene monologue
; on the invention of golf by a drunken Scotsman which includes: ``Oh!  This is
; fuckin' brilliant!  Right near the end I'll put a flat piece with a little
; flag to give ya fuckin' hope! ... But then I'll put a pool and a sand trap to
; fuck with your ball again.''  That's how I felt when I realized I needed
; len-merge-sort-term-order.

; Of course, the lemmas about merge-sort-term-order are mathematically trivial
; if looked at from the perspective of equivalence and congruence relations.
; But initially we underestimated the effort and did everything by the
; direct-from-the-definitions perspective.  When we realized congruences might
; have been better we were already deeply committed to brute force.  To quote
; Robin Williams again, ``Goodmorning Vietnam!''

; So when we completed the brute force approach we backed up and did it with
; congruences.  In all the brute force approach required 20 events while the
; congruence approach only required 14: 6 to prove that merge-sort-term-order
; returns a permutation, 1 disable, 5 defcongs with 1 supporting lemma, and 1
; patterned congruence.  While 20 isn't that much greater than 14, the
; intellectual burden and tedium of the brute force approach was really
; off-putting.

; Now we establish that merge-sort-term-order just permutes its arguments and
; prove a few congruence rules allowing us to rewrite with that fact.

(local (include-book "sorting/convert-perm-to-how-many" :dir :system))

(local
 (defthm how-many-merge-term-order
   (implies (and (true-listp x) (true-listp y))
            (equal (how-many e (merge-term-order x y))
                   (+ (how-many e x) (how-many e y))))
   :hints (("Goal" :in-theory (disable term-order)))))

(local
 (defthm how-many-evens-and-odds
   (implies (consp x)
            (equal (+ (how-many e (evens x))
                      (how-many e (evens (cdr x))))
                   (how-many e x)))))

(local
 (defthm true-listp-merge-sort-term-order
   (implies (true-listp x)
            (true-listp (merge-sort-term-order x)))))

(local
 (defthm how-many-merge-sort-term-order
   (equal (how-many e (merge-sort-term-order x))
          (how-many e x))))

(local
 (defthm perm-merge-sort-term-order
   (perm (merge-sort-term-order x) x)))

; So now we know we can eliminate merge-sort-term-order in an perm-congruent
; slot.  We turn off the lemma that converts perms to how-many and proceed
; to establish the necessary congruences.

(local (in-theory (disable convert-perm-to-how-many)))

(local
 (defcong perm equal (consp x) 1))

(local
 (defcong perm equal (len x) 1))

; This is a patterned congruence:
(local
 (defthm perm-equal-consp-cdr
   (implies (perm x x-equiv)
            (equal (consp (cdr x))
                   (consp (cdr x-equiv))))
   :rule-classes :congruence))

;This lemma is necessary to prove the congruence below.
(local
 (defthm memb-stateman-eval-lst
   (implies (memb e lst)
            (memb (stateman-eval e alist)
                  (stateman-eval-lst lst alist)))))

(local
 (defcong perm perm (stateman-eval-lst x alist) 1))

; Now we prove the lemmas leading to the theorem taht meta-ash-ash preserves
; the values of syntactic-integerp expressions.

(encapsulate
 nil
 (local
  (encapsulate
   nil
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm ash-+
     (implies (and (integerp a) (integerp b) (natp k))
              (equal (ash (+ a b) k)
                     (+ (ash a k) (ash b k)))))
   (defthm ash-ash
     (implies (and (natp i) (natp k))
              (equal (ash (ash a i) k)
                     (ash a (+ i k)))))))

 (local
  (defun syntactic-integerp-listp (x)
    (cond ((endp x) t)
          (t (and (syntactic-integerp (car x))
                  (syntactic-integerp-listp (cdr x)))))))

 (local
  (defun map-ash (lst i)
    (cond ((endp lst) nil)
          (t (cons (ash (car lst) i)
                   (map-ash (cdr lst) i))))))

 (local
  (defthm meta-map-ash-correct
    (implies (natp i)
             (equal (stateman-eval-lst (meta-map-ash lst i)
                                       alist)
                    (map-ash (stateman-eval-lst lst alist)
                             i)))
    :hints (("subgoal *1/2.7'" :in-theory (enable ash)))))

 (local
  (defun sumlist (lst)
    (cond ((endp lst) 0)
          (t (+ (car lst) (sumlist (cdr lst)))))))

 (local
  (defthm syntactic-integerp-listp-meta-map-ash
    (implies (and (syntactic-integerp-listp lst)
                  (natp i))
             (syntactic-integerp-listp (meta-map-ash lst i)))))

 (local
  (defthm syntactic-integerp-listp-meta-ash-ash1
    (implies (syntactic-integerp x)
             (syntactic-integerp-listp (meta-ash-ash1 x)))
    :hints (("Goal" :expand (:free (x) (hide x))))))

 (local
  (defthm integer-sumlist
    (implies (integer-listp lst)
             (integerp (sumlist lst)))
    :rule-classes :type-prescription))

 (local
  (defthm sumlist-map-ash
    (implies (and (integer-listp lst) (natp i))
             (equal (sumlist (map-ash lst i))
                    (ash (sumlist lst) i)))))

 (local
  (defthm integer-listp-stateman-eval-lst-syntactic-integerp-listp
    (implies (syntactic-integerp-listp lst)
             (integer-listp (stateman-eval-lst lst alist)))))


 (local
  (defthm
    meta-ash-ash1-correct
    (implies (syntactic-integerp x)
             (equal (sumlist (stateman-eval-lst (meta-ash-ash1 x)
                                                alist))
                    (stateman-eval x alist)))
    :hints (("Goal" :expand (:free (x) (hide x))))))

 (local
  (defthm stateman-eval-xxxjoin-binary-+
    (implies (force (<= 2 (len lst)))
             (equal (stateman-eval (xxxjoin 'binary-+ lst)
                                   alist)
                    (sumlist (stateman-eval-lst lst alist))))))

 (local
  (defthm consp-meta-ash-ash1
    (consp (meta-ash-ash1 x))
    :rule-classes :type-prescription))

 (local
  (defthm consp-meta-map-ash
    (equal (consp (meta-map-ash x i))
           (consp x))))

 (local
  (defthm stateman-eval-car-meta-map-ash
    (implies (and (syntactic-integerp-listp lst)
                  (consp lst)
                  (natp i))
             (equal (stateman-eval (car (meta-map-ash lst i))
                                   alist)
                    (ash (stateman-eval (car lst) alist)
                         i)))
    :hints (("Goal" :do-not-induct t
             :expand ((meta-map-ash lst i))))))

 (local
  (defthm car-append
    (equal (car (append a b))
           (if (consp a) (car a) (car b)))))

 (local
  (defcong perm equal (syntactic-integerp-listp x) 1))

 (local
  (defcong perm equal (sumlist x) 1))

 (defthm
   meta-ash-ash-correct
   (implies (syntactic-integerp x)
            (equal (stateman-eval (meta-ash-ash x) alist)
                   (stateman-eval x alist)))
   :hints
   (("Goal" :do-not-induct t
     :in-theory (disable xxxjoin meta-ash-ash1
                         stateman-eval-constraint-5))
; The hints below are the brute force attack on the singleton case for
; the first version of meta-ash-ash.
    ("Subgoal 1"
     :expand ((meta-ash-ash1 x))
     :in-theory
     (disable meta-ash-ash1-correct
              syntactic-integerp-listp-meta-ash-ash1)
     :use ((:instance meta-ash-ash1-correct (x x)
                      (alist alist))
           (:instance syntactic-integerp-listp-meta-ash-ash1
                      (x x))))
    ("Subgoal 1.1.7''" :expand ((syntactic-integerp (cadr x)))
     :in-theory (enable ash))))

; This theorem actually exploits the fact that pseudo-termp doesn't check arity!
 (local
  (defthm pseudo-termp-xxxjoin
    (implies (and (pseudo-term-listp lst)
                  (symbolp fn)
                  (not (equal fn 'quote)))
             (pseudo-termp (xxxjoin fn lst)))))

 (defthm pseudo-termp-meta-ash-ash
   (implies (pseudo-termp x)
            (pseudo-termp (meta-ash-ash x)))
   :hints (("Goal"
            :in-theory (disable pseudo-term-listp-merge-sort-term-order)
            :use (:instance pseudo-term-listp-merge-sort-term-order
                            (l (META-ASH-ASH1 X))))
           ("Subgoal 1"
            :in-theory (disable pseudo-term-listp-meta-ash-ash1)
            :use (:instance pseudo-term-listp-meta-ash-ash1))))

 (in-theory (disable meta-ash-ash)))

(local
 (defthm syntactic-integerp-meta-binary-+-with-const
   (implies (and (syntactic-integerp a)
                 (natp c))
            (syntactic-integerp (meta-binary-+-with-const c a)))
   :hints
   (("Goal" :in-theory (enable meta-binary-+-with-const)))))

(local
 (defthm syntactic-integerp-mv-nth-0-mx-rover
   (implies (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))
            (syntactic-integerp (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist))))
   :hints (("Goal" :in-theory (enable mx-rover)))))

; -----------------------------------------------------------------

(defun memoizable-meta-R (x type-alist)
  (declare (xargs :guard (and (pseudo-termp x)
                              (type-alistp type-alist))
                  :guard-hints
                  (("Goal"
                    :in-theory (e/d (the-guard-mismatch-rules)
                                    (in-tau-intervalp
                                     tau-intervalp
                                     make-tau-interval
                                     tau-interval-dom
                                     tau-interval-lo
                                     tau-interval-hi))))))

; Check the basic form of x and name the pieces.

  (cond
   ((and (consp x)
         (eq (ffn-symb x) 'R)
         (quotep (fargn x 2))
         (integerp (cadr (fargn x 2)))
         (< 0 (cadr (fargn x 2)))
         (consp (fargn x 3)))
    (let ((a (fargn x 1))
          (n (cadr (fargn x 2)))
          (st (fargn x 3)))

; Strip top-level HIDE in st to get st1 and let
; hiddenp record whether a HIDE was found.

      (mv-let
       (hiddenp st1)
       (strip-optional-hide st)
       (declare (ignore hiddenp))
       (mv-let
        (flg hyps1 int1)
        (bounded-address a 1 type-alist)

; Note that we call bounded-address with 1 instead of n.  That way we get an
; interval containing just a.  Mx-rover accounts for n.
; (i-am-here) Do ever check that a+n<=*m-size*?  If not, how does this work?

        (cond
         (flg
          (mv-let (v hyps2)
                  (mx-rover a hyps1 int1 n st1 type-alist)
                  (cond
                   (v
                    (let ((normalized-v (meta-ash-ash v)))
                      (if hyps2
                          (hlist 'IF
                                 (honjoin hyps2)
                                 (add-HIDE t normalized-v)
                                 x)
                          (add-HIDE t normalized-v))))
                   (t x))))
         (t x))))))
   (t x)))

(defun meta-R (x mfc state)
  (declare (xargs :stobjs (state)
                  :guard (pseudo-termp x))
           (ignore state))
  (memoizable-meta-R (hons-copy x)
                     (hons-copy (mfc-type-alist mfc))))

(defun memoizable-meta-< (term type-alist)
  (declare (xargs :guard (and (pseudo-termp term)
                              (type-alistp type-alist))
                  :guard-hints
                  (("Goal"
                    :in-theory (enable the-guard-mismatch-rules)))))

; We only operate on (< x y) if one of x or y is a constant and the other can
; be confined to an interval by ainni.

  (cond
   ((and (consp term)
         (eq (ffn-symb term) '<))
    (let ((x (fargn term 1))
          (y (fargn term 2)))
      (cond
       ((and (quotep x)
             (natp (cadr x)))
        (mv-let (flg hyps int)
                (ainni y nil type-alist)
                (cond
                 ((not flg) term)
                 ((< (cadr x) (tau-interval-lo int))
                  (if hyps
                      (hlist 'IF
                             (honjoin hyps)
                             *t*
                             term)
                      *t*))
                 ((<= (tau-interval-hi int) (cadr x))
                  (if hyps
                      (hlist 'IF
                             (honjoin hyps)
                             *nil*
                             term)
                      *nil*))
                 (t term))))
       ((and (quotep y)
             (natp (cadr y)))
        (mv-let (flg hyps int)
                (ainni x nil type-alist)
                (cond
                 ((not flg) term)
                 ((< (tau-interval-hi int) (cadr y))
                  (if hyps
                      (hlist 'IF
                             (honjoin hyps)
                             *t*
                             term)
                      *t*))
                 ((<= (cadr y) (tau-interval-lo int))
                  (if hyps
                      (hlist 'IF
                             (honjoin hyps)
                             *nil*
                             term)
                      *nil*))
                 (t term))))
       (t term))))
   (t term)))

(defun meta-< (term mfc state)
  (declare (xargs :stobjs (state)
                  :guard (pseudo-termp term))
           (ignore state))
  (memoizable-meta-< (hons-copy term)
                     (hons-copy (mfc-type-alist mfc))))

; Now we develop meta-!i, meta-!s, and meta-!r...

; Originally, these metafunctions did not fire unless there is a HIDE around
; the state to which they're applied.  They then lifted the HIDE up one level,
; transforming, say (!i pc (HIDE st)) to (HIDE (!i pc st')), where st' is st
; with the (first) !i assignment, if any, removed because it is now superceded
; by the most recent !i.  However, we have changed them so they fire even if
; there is no HIDE and they hide their results only if the previous state was
; in a HIDE.  The reason we backed off the more aggressive stance is that we
; were getting nests of unsimplified (S (!S ...)), for example, because the
; state in ... was not hidden and it was impossible even to do call-graph
; tracing.

; However, another key is that the functions do not fire at all if there are
; IFs or LAMBDAs in the parts of the term that would be hidden if the functions
; fire.  We say a term is ``obnoxious'' if it contains an IF or a LAMBDA.
; Thus, if pc is obnoxious, then (!i pc (HIDE st)) will not change.  This gives
; the rewriter a chance to get rid of the obnoxious subterms before we HIDE
; them forever.  Meanwhile, because the new state is not a HIDE, the
; PCODE-OPENER will not fire on it.

(mutual-recursion
 (defun obnoxiousp (term)

; Return t iff term contains an IF or a LAMBDA.  We assume that hidden subterm
; of term contains IF or LAMBDA.  That is, we return nil on (HIDE x) without
; looking at x.

   (declare (xargs :guard (pseudo-termp term)))
   (cond
    ((variablep term) nil)
    ((fquotep term) nil)
    ((flambdap (ffn-symb term)) t)
    ((eq (ffn-symb term) 'IF) t)
    ((eq (ffn-symb term) 'HIDE) nil)
    (t (obnoxiousp-lst (fargs term)))))

 (defun obnoxiousp-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (cond
    ((endp terms) nil)
    (t (or (obnoxiousp (car terms))
           (obnoxiousp-lst (cdr terms)))))))

; The following function was originally controlled by depth rather than the
; shape of st.  However, the guards were complicated: depth had to be shallow
; enough and st had to consist of a well-formed !I/!S/!R nest -- which we might
; not actually have.  So we defined the function more safely:

(defun delete-assignment-at-depth (depth st)

; Delete the assignment at the given depth in st.

  (declare (xargs :guard (and (natp depth)
                              (pseudo-termp st))))
  (cond
   ((variablep st) st)
   ((fquotep st) st)
   ((eq (ffn-symb st) '!R)
    (if (zp depth)
        (fargn st 4)
        (hlist '!r
              (fargn st 1)
              (fargn st 2)
              (fargn st 3)
              (delete-assignment-at-depth (- depth 1) (fargn st 4)))))
   ((or (eq (ffn-symb st) '!I)
        (eq (ffn-symb st) '!S))
    (if (zp depth)
        (fargn st 2)
        (hlist (ffn-symb st)
              (fargn st 1)
              (delete-assignment-at-depth (- depth 1) (fargn st 2)))))
   (t st)))

(defthm pseudo-termp-delete-assignment-at-depth
  (implies (pseudo-termp st)
           (pseudo-termp (delete-assignment-at-depth depth st))))

(defun memoizable-meta-!i (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond
   ((and (consp term)
         (eq (ffn-symb term) '!I)
         (not (obnoxiousp (fargn term 1)))
         (consp (cddr term)))
    (mv-let (hiddenp st-arg)
            (strip-optional-hide (fargn term 2))
            (cond
             ((eq st-arg 'ST)
              (hlist 'HIDE term))
             (t
              (mv-let (flg ans)
                      (find-assignment-to-scalar '!I st-arg)
                      (declare (ignore ans))
                      (cond
                       (flg
                        (add-HIDE hiddenp
                                  (hlist '!I
                                        (fargn term 1)
                                        (delete-assignment-at-depth flg st-arg))))
                       (t (add-HIDE hiddenp
                                    (hlist '!I
                                          (fargn term 1)
                                          st-arg)))))))))
   (t term)))

(defun meta-!i (term)
  (declare (xargs :guard (pseudo-termp term)))
  (memoizable-meta-!i (hons-copy term)))

(local
 (defthm lemma1
   (implies
    (and
     (mv-nth 0 (find-assignment-to-scalar '!i st))
     (pseudo-termp st))
    (equal
     (!i val (stateman-eval st alist))
     (!i val
         (stateman-eval
          (delete-assignment-at-depth
           (mv-nth 0 (find-assignment-to-scalar '!i st))
           st)
          alist))))
   :hints
   (("Subgoal *1/9.2'"
     :in-theory (disable !r-!i)
     :use
     ((:instance !r-!i
                 (pc VAL)
                 (ma (stateman-eval (CADR ST) alist))
                 (sz (stateman-eval (caddr st) alist))
                 (v (STATEMAN-EVAL (CADDDR ST) ALIST))
                 (st (STATEMAN-EVAL
                      (DELETE-ASSIGNMENT-at-depth
                       (mv-nth 0 (find-assignment-to-scalar '!i (CAR (CDDDDR ST))))
                       (CAR (CDDDDR ST)))
                      ALIST)))
      (:instance !r-!i
                 (pc VAL)
                 (ma (stateman-eval (CADR ST) alist))
                 (sz (stateman-eval (caddr st) alist))
                 (v (STATEMAN-EVAL (CADDDR ST) ALIST))
                 (st (STATEMAN-EVAL (CAR (CDDDDR ST))
                                    ALIST)))))
    ("Subgoal *1/5.2'"
     :in-theory (disable !s-!i)
     :use
     ((:instance !s-!i
                 (pc VAL)
                 (st (STATEMAN-EVAL
                      (DELETE-ASSIGNMENT-at-depth
                       (mv-nth 0 (find-assignment-to-scalar '!i (caddr st)))
                       (caddr st))
                      ALIST))
                 (s (stateman-eval (cadr st) alist)))
      (:instance !s-!i
                 (pc val)
                 (s (STATEMAN-EVAL (CADR ST) ALIST))
                 (st (STATEMAN-EVAL (CADDR ST) ALIST))))))))

(defun memoizable-meta-!s (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond
   ((and (consp term)
         (eq (ffn-symb term) '!S)
         (not (obnoxiousp (fargn term 1)))
         (consp (cddr term)))
    (mv-let (hiddenp st-arg)
            (strip-optional-hide (fargn term 2))
            (cond
             ((eq st-arg 'ST)
              (hlist 'HIDE term))
             (t
              (mv-let (flg ans)
                      (find-assignment-to-scalar '!S st-arg)
                      (declare (ignore ans))
                      (cond
                       (flg
                        (add-HIDE hiddenp
                                  (hlist '!S
                                        (fargn term 1)
                                        (delete-assignment-at-depth flg st-arg))))
                       (t (add-HIDE hiddenp
                                    (hlist '!S
                                          (fargn term 1)
                                          st-arg)))))))))
   (t term)))

(defun meta-!s (term)
  (declare (xargs :guard (pseudo-termp term)))
  (memoizable-meta-!s (hons-copy term)))

(local
 (defthm lemma2
   (IMPLIES
    (AND (MV-NTH 0 (FIND-ASSIGNMENT-to-scalar '!s ST))
         (PSEUDO-TERMP ST))
    (EQUAL
     (!s VAL (STATEMAN-EVAL ST ALIST))
     (!s VAL
         (STATEMAN-EVAL
          (DELETE-ASSIGNMENT-at-depth
           (MV-NTH 0 (FIND-ASSIGNMENT-to-scalar '!s ST))
           ST)
          ALIST))))
   :hints
   (("Subgoal *1/9.2'"
     :in-theory (disable !r-!s)
     :use
     ((:instance !r-!s
                 (s VAL)
                 (ma (stateman-eval (CADR ST) alist))
                 (sz (stateman-eval (caddr st) alist))
                 (v (STATEMAN-EVAL (CADDDR ST) ALIST))
                 (st (STATEMAN-EVAL
                      (DELETE-ASSIGNMENT-at-depth
                       (mv-nth 0 (find-assignment-to-scalar '!s (CAR (CDDDDR ST))))
                       (CAR (CDDDDR ST)))
                      ALIST)))
      (:instance !r-!s
                 (s VAL)
                 (ma (stateman-eval (CADR ST) alist))
                 (sz (stateman-eval (caddr st) alist))
                 (v (STATEMAN-EVAL (CADDDR ST) ALIST))
                 (st (STATEMAN-EVAL (CAR (CDDDDR ST))
                                    ALIST)))))
    ("Subgoal *1/5.2'"
     :in-theory (disable !s-!i)
     :use
     ((:instance !s-!i
                 (pc VAL)
                 (st (STATEMAN-EVAL
                      (DELETE-ASSIGNMENT-at-depth
                       (mv-nth 0 (find-assignment-to-scalar '!s (caddr st)))
                       (caddr st))
                      ALIST))
                 (s (stateman-eval (cadr st) alist)))
      (:instance !s-!i
                 (pc val)
                 (s (STATEMAN-EVAL (CADR ST) ALIST))
                 (st (STATEMAN-EVAL (CADDR ST) ALIST))))))))

; -----------------------------------------------------------------

(defun unresolved-read-writep (term)

; A term is an ``unresolved read-write'' (urw) if it is a (S st), (I st), or
; (R ... st) where st is a !S, !I, or !R term or the HIDE of one of those
; three kinds of terms.  So, for example, there are six forms that are
; unresolved read-writes starting with R:

; (R a n (!I  ... st))
; (R a n (!S  ... st))
; (R a n (!R ... st))
; (R a n (HIDE (!I  ... st)))
; (R a n (HIDE (!S  ... st)))
; (R a n (HIDE (!R ... st)))

  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((or (eq (ffn-symb term) 'S)
             (eq (ffn-symb term) 'I)
             (eq (ffn-symb term) 'R))
         (let ((next (if (eq (ffn-symb term) 'R) (fargn term 3) (fargn term 1))))
           (and (nvariablep next)
                (not (fquotep next))
                (or (eq (ffn-symb next) '!S)
                    (eq (ffn-symb next) '!I)
                    (eq (ffn-symb next) '!R)
                    (and (eq (ffn-symb next) 'HIDE)
                         (nvariablep (fargn next 1))
                         (not (fquotep (fargn next 1)))
                         (or (eq (ffn-symb (fargn next 1)) '!S)
                             (eq (ffn-symb (fargn next 1)) '!I)
                             (eq (ffn-symb (fargn next 1)) '!R)))))))
        (t nil)))

(mutual-recursion
 (defun contains-unresolved-read-writep (term)
   (declare (xargs :guard (pseudo-termp term)))
   (cond
    ((variablep term) nil)
    ((fquotep term) nil)
    ((unresolved-read-writep term) t)
    (t (contains-unresolved-read-writep-lst (fargs term)))))
 (defun contains-unresolved-read-writep-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (cond
    ((endp terms) nil)
    (t (or (contains-unresolved-read-writep (car terms))
           (contains-unresolved-read-writep-lst (cdr terms)))))))

(mutual-recursion
 (defun deepest-hide (term)

; We return the level at which the deepest HIDE occurs.  For example, in (HIDE
; (f (g (h a)))) the level is 0, in (f (g (h a))) it is nil, and in (f (HIDE a)
; (g (h (HIDE b)))) it is 3.  We removing HIDEs from a term there is no need to
; go deeper than this depth.

   (declare (xargs :guard (pseudo-termp term)))
   (cond
    ((variablep term) nil)
    ((fquotep term) nil)
    ((eq (ffn-symb term) 'HIDE) 0)
    (t (let ((n (deepest-hide-lst (fargs term))))
         (if n (+ 1 n) nil)) )))

 (defun deepest-hide-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (cond
    ((endp terms) nil)
    (t (let ((n1 (deepest-hide (car terms)))
             (n2 (deepest-hide-lst (cdr terms))))
         (if n1
             (if n2
                 (max n1 n2)
                 n1)
             (if n2
                 n2
                 nil)))))))

(defun remove-all-hides1 (flg depth x)
  (declare (xargs :guard
                  (and (if flg (pseudo-termp x) (pseudo-term-listp x))
                       (integerp depth))))
  (if flg
      (cond ((< depth 0) x)
            ((variablep x) x)
            ((fquotep x) x)
            ((eq (ffn-symb x) 'HIDE)
             (remove-all-hides1 t (- depth 1) (fargn x 1))) ; ??? (a)
            #||
; I believe that (MOD (HIDE (MOD x y)) z) can introduce simplifiable
; (MOD (MOD x y) z).  But I want to try ignoring that possibility for right
; now!  If I go back to removing these hidden mod-mods, I'll have to
; field and return the hyps now generated by cons-term-MOD below.  This function
; is used in meta-!R and so could field the hyps and include them its own.

            ((eq (ffn-symb x) 'MOD)
             (let ((m (fargn x 1))
                   (i (fargn x 2)))
               (cond
                ((and (quotep i)
                      (not (zp (cadr i)))
                      (nvariablep m)
                      (not (fquotep m))
                      (eq (ffn-symb m) 'HIDE)
                      (nvariablep (fargn m 1))
                      (not (fquotep (fargn m 1)))
                      (eq (ffn-symb (fargn m 1)) 'MOD))
                 (cons-term-MOD (fargn m 1) (cadr i))) ; ??? (b)
                (t (hons (ffn-symb x)
                         (remove-all-hides1 nil (- depth 1) (fargs x)))))))||#
            (t (hons (ffn-symb x)
                     (remove-all-hides1 nil (- depth 1) (fargs x)))))
      (cond ((endp x) nil)
            (t (hons (remove-all-hides1 t depth (car x))
                     (remove-all-hides1 nil depth (cdr x)))))))

(defthm len-remove-all-hides1
  (equal (len (remove-all-hides1 nil depth x))
         (len x)))

(defthm pseudo-termp-remove-all-hides1
  (implies (if flg
               (pseudo-termp x)
               (pseudo-term-listp x))
           (if flg
               (pseudo-termp (remove-all-hides1 flg depth x))
               (pseudo-term-listp (remove-all-hides1 flg depth x))))
  :rule-classes nil)

(defthm pseudo-termp-remove-all-hides1-corollary
  (implies (pseudo-termp x)
           (pseudo-termp (remove-all-hides1 t depth x)))
  :hints (("Goal" :use (:instance pseudo-termp-remove-all-hides1
                                  (flg t)))))

(defun remove-all-hides (x)

; This function removes all hides from term x and returns (mv flg x'), where
; flg is t or nil to indicate whether any hides were removed and x' is the
; result.  It actually doesn't dive any deeper into x than it has to.  We won't
; actually have to prove that this function removes all HIDEs, only that it
; returns a pseudo-termp whose stateman-eval is the same.

  (declare (xargs :guard (pseudo-termp x)))
  (let ((depth (deepest-hide x)))
    (if depth
        (mv t (remove-all-hides1 t depth x))
        (mv nil x))))

(defthm stateman-eval-remove-all-hides1
  (and (implies flg
                (equal (stateman-eval (remove-all-hides1 flg d x) alist)
                       (stateman-eval x alist)))
       (implies (not flg)
                (equal (stateman-eval-lst (remove-all-hides1 flg d x) alist)
                       (stateman-eval-lst x alist))))
  :hints
  (("Goal" :expand ((:free (x) (hide x)))
    :in-theory (enable STATEMAN-EVAL-CONSTRAINT-0))))

(defthm natp-find-assignment-to-vector1
  (implies (mv-nth 0 (find-assignment-to-vector1 a n hyps-a int-a st type-alist))
           (natp (mv-nth 0 (find-assignment-to-vector1 a n hyps-a int-a st type-alist))))
  :rule-classes :forward-chaining)

(defthm pseudo-term-listp-bounded-address
  (implies (and (pseudo-termp a)
                (mv-nth 0 (bounded-address a n type-alist)))
           (pseudo-term-listp (mv-nth 1 (bounded-address a n type-alist))))
  :hints (("Goal" :in-theory (enable bounded-address))))

(defthm pseudo-term-listp-perfectly-shadowedp
  (implies (and (pseudo-term-listp hyps-a)
                (pseudo-termp st)
                (nvariablep st)
                (not (fquotep st))
                (eq (ffn-symb st) '!R)
                (quotep (fargn st 2))
                (natp (cadr (fargn st 2)))
                (mv-nth 0 (perfectly-shadowedp a n hyps-a int-a st type-alist)))
           (pseudo-term-listp (mv-nth 1 (perfectly-shadowedp a n hyps-a int-a st type-alist))))
  :hints (("Goal" :in-theory (enable perfectly-shadowedp))))

(defthm pseudo-term-listp-find-assignment-to-vector1
  (implies (and (pseudo-term-listp hyps-a)
                (pseudo-termp st)
                (mv-nth 0 (find-assignment-to-vector1 a n hyps-a int-a st type-alist)))
           (pseudo-term-listp (mv-nth 1 (find-assignment-to-vector1 a n hyps-a int-a st type-alist)))))


(defun memoizable-meta-!r (x type-alist)

; ACL2 requires that metafunctions taking mfc as an
; argument must also take state.  But this function
; doesn't use state.

  (declare (xargs :guard (and (pseudo-termp x)
                              (type-alistp type-alist))
                  :guard-hints (("Goal" :in-theory (enable the-guard-mismatch-rules)))))
  (cond

; Check the basic form of x and name the pieces.

   ((and (consp x)
         (eq (ffn-symb x) '!R)
         (quotep (fargn x 2))
         (natp (cadr (fargn x 2)))
         (consp (cddddr x)))
    (let* ((a (fargn x 1))
           (qn (fargn x 2))
           (n (cadr qn))
           (v (fargn x 3))
           (st (fargn x 4)))

; Let hides-in-a and a1 be the results of removing all
; HIDEs from the address expression a.  The flag
; hides-in-a is set to T iff one or more HIDEs are
; found.  A1 is a with all the HIDEs stripped out.

      (mv-let
       (hides-in-a a1)
       (remove-all-hides a)
       (cond

; We first dismiss the case where n=0.  Note that st may be
; hidden or not, but whatever it was it still is.

        ((zp n) st)

; Next we ask if a contains HIDEs, or if either a or v
; contains terms that can likely be further simplified,
; e.g., embedded IFs, unexpanded LAMBDA applications,
; or unresolved read-over-writes.

        ((or hides-in-a
             (obnoxiousp a)
             (contains-unresolved-read-writep a)
             (obnoxiousp v)
             (contains-unresolved-read-writep v))

; If any of the above heuristic checks succeed, we just
; reformat x by stripping out the HIDEs in a, i.e., we
; replace a by a1.  By returning an unhidden !R, we
; allow the ACL2 rewriter to further simplify the
; address term a, with the goal of canonicalizing it.
; Then meta-!R will get another chance.  We leave any
; HIDEs that might be in v because they generally
; surround gigantic values extracted from previous
; states.

         (hlist '!R a1 qn v st))
        (t

; If the heuristic checks allow us to proceed, we
; remove all HIDEs from v to get v1 and we remove a
; top-level HIDE (if any) from st to get st1.  There
; should be at most one HIDE in st and it will be
; top-level.  We remember, with hiddenp, whether st was
; hidden.  Generally, a state expression embedded in a
; HIDE is a signal that the state expression has been
; processed by one of our state management
; metafunctions and is ``normalized.''

         (mv-let
          (hides-in-v v1)
          (remove-all-hides v)
          (declare (ignore hides-in-v))
          (mv-let
           (hiddenp st1)
           (strip-optional-hide st)

; There is nothing to do if st1 is the variable ST,
; except to replace a and v by their unhidden versions.

           (cond
            ((eq st1 'ST)
             (hlist 'HIDE (hlist '!R a1 qn v1 st1)))
            (t

; Determine whether there is a !R assignment to a1 in
; st1, using the givens from the metafunction context.
; We can ignore the last answer, ans.  It is only used
; when simplifying read-over-write expressions and we
; are working on a write-over-write expression.

             (mv-let
              (flg hyps)
              (Find-Assignment-to-vector a1 n st1 type-alist)
              (cond
               (flg

; An assignment to a1.n was found.  We delete it,
; producing st2.  Recall that flg is the depth
; of the assignment found and thus finding the
; assignment to delete is fast.

                (let ((st2 (Delete-Assignment-at-depth flg st1)))

; If the old assignment was to a syntactically
; identical address, we do not depend on the hyps
; generated by find-assignment.  Just insert an
; assignment of v1 to a1 in st2, put a HIDE on that
; expression if the original st was hidden, and return.

                  (if hyps
                      (hlist 'IF
                             (honjoin hyps)
                             (add-HIDE hiddenp
                                       (hlist '!R a1 qn v1 st2))
                             x)
                      (add-HIDE hiddenp
                                (hlist '!R a1 qn v1 st2)))))

; If no old assignment was found, we needn't delete
; anything and thus do not depend on the generated
; hyps.

               (t (add-HIDE hiddenp
                            (hlist '!R a1 qn v1 st1))))))))))))))
   (t

; If x is not of the expected form, make no change.

    x)))

(defun meta-!r (x mfc state)

; ACL2 requires that metafunctions taking mfc as an
; argument must also take state.  But this function
; doesn't use state.

  (declare (xargs :stobjs (state)
                  :guard (pseudo-termp x))
           (ignore state))
  (memoizable-meta-!r (hons-copy x)
                      (hons-copy (mfc-type-alist mfc))))

(local
 (defthm lemma3
   (implies (and (mv-nth 0 (bounded-address ma1 n type-alist))
                 (not (zp n))
                 (mv-nth
                  0
                  (find-assignment-to-vector1
                   ma1
                   n
                   (mv-nth 1 (bounded-address ma1 n type-alist))
                   (mv-nth 2 (bounded-address ma1 n type-alist))
                   st
                   type-alist))
                 (stateman-eval
                  (conjoin (mv-nth 1 (find-assignment-to-vector1
                                      ma1
                                      n
                                      (mv-nth 1 (bounded-address ma1 n type-alist))
                                      (mv-nth 2 (bounded-address ma1 n type-alist))
                                      st
                                      type-alist)))
                  alist)
                 (pseudo-termp st)
                 (pseudo-termp ma1))
            (equal (!r (stateman-eval ma1 alist)
                       n
                       val
                       (stateman-eval
                        (delete-assignment-at-depth
                         (mv-nth 0 (find-assignment-to-vector1
                                    ma1
                                    n
                                    (mv-nth 1 (bounded-address ma1 n type-alist))
                                    (mv-nth 2 (bounded-address ma1 n type-alist))
                                    st
                                    type-alist))
                         st)
                        alist))
                   (!r (stateman-eval ma1 alist)
                       n
                       val
                       (stateman-eval st alist))))
   ))

(defthm type-set-hide
  (equal (hide x) x)
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes :type-prescription)

(defthm r-hide
  (equal (r (hide x) sz st) (r x sz st))
  :hints (("Goal" :expand ((:free (x) (hide x))))))

(in-theory (disable i-!i
                    i-!s
                    i-!r
                    s-!i
                    s-!s
                    s-!r
                    r-!i
                    r-!s
                    r-!r-same
                    r-!r-diff-above
                    r-!r-diff-below
                    !s-!i
                    !r-!s
                    !r-!r-same
                    !r-!r-diff-above
                    !r-!r-diff-below))

;-----------------------------------------------------------------

; Now we prove that all our metafunctions produce termps.  Basically, each of
; these termp theorems is modeled on a pseudo-termp theorem proved above.
; Rather than sprinkle them into the script above, I just do them all here.  An
; unfortunate complication of this decision is that many of the functions
; concerned have been disabled by now and so I have to provide some enable
; hints.  But since the pseudo-termp theorems from which these are derived were
; proved in layers with disabling of non-rec fns each time we stepped up to a
; new layer, I only have to enable the one function I'm dealing with -- there
; will already be termp lemmas dealing with its subroutines.  It is worth
; noting that a few theorems below are not modeled on pseudo-termp theorems.
; We never had to prove that the output of the metafunctions themselves were
; pseudo-termps!  We just often needed that hypothesis about their subroutines.
; So a few theorems below, and in particular all of the ``main'' ones
; establishing that a metafunction returns a termp, are new and that even
; required proving termp theorems about a few subroutines for which we never
; need pseudo-termp theorems.

; Here are the function symbols recognized by stateman-eval and
; thus the ones whose arities we must know:

(defun build-arity-table (alist)
  (if (endp alist)
      nil
      (cons (cons (car (car alist)) (len (cdr (car alist))))
            (build-arity-table (cdr alist)))))

(defconst *stateman-arities*
  (build-arity-table '((IFIX x)
                       (NOT p)
                       (< x y)
                       (IF x y z)
                       (BINARY-+ x y)
                       (BINARY-* x y)
                       (UNARY-- x)
                       (HIDE x)
                       (FORCE x)


                       (MOD x y)
                       (ASH x i)
                       (BINARY-LOGAND x y)
                       (BINARY-LOGXOR x y)
                       (BINARY-LOGIOR x y)

                       (I st)
                       (!I val st)
                       (S st)
                       (!S val st)
                       (R ma sz st)
                       (!R ma sz val st))))

(local
 (defthm termp-distributed-difference-2
   (implies (and (termp term w)
                 (arities-okp *stateman-arities* w)
                 (mv-nth 0 (distributed-difference term)))
            (termp (mv-nth 2 (distributed-difference term))
                   w))
   :hints (("Goal" :in-theory (enable distributed-difference)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm logic-fnsp-distributed-difference-2
   (implies (logic-fnsp term w)
            (logic-fnsp (mv-nth 2 (distributed-difference term))
                        w))
   :hints (("Goal" :in-theory (enable distributed-difference)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm logic-termp-distributed-difference-2
   (implies (and (logic-termp term w)
                 (arities-okp *stateman-arities* w)
                 (mv-nth 0 (distributed-difference term)))
            (logic-termp (mv-nth 2 (distributed-difference term))
                           w))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm termp-distributed-difference-3
   (implies (and (termp term w)
                 (arities-okp *stateman-arities* w)
                 (mv-nth 0 (distributed-difference term)))
            (termp (mv-nth 3 (distributed-difference term))
                   w))
   :hints (("Goal" :in-theory (enable distributed-difference)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm logic-fnsp-distributed-difference-3
   (implies (logic-fnsp term w)
            (logic-fnsp (mv-nth 3 (distributed-difference term))
                        w))
   :hints (("Goal" :in-theory (enable distributed-difference)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm logic-termp-distributed-difference-3
   (implies (and (logic-termp term w)
                 (arities-okp *stateman-arities* w)
                 (mv-nth 0 (distributed-difference term)))
            (logic-termp (mv-nth 3 (distributed-difference term))
                         w))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm term-listp-ainni
   (implies (and (termp term w)
                 (term-listp hyps w)
                 (arities-okp *stateman-arities* w))
            (term-listp (mv-nth 1 (ainni term hyps type-alist)) w))
   :hints
   (("Goal"
     :in-theory (e/d (ainni)
                     (tau-bounder-+
                      tau-bounder-*
                      tau-bounder-logand
                      tau-bounder-logior
                      tau-bounder-logxor
                      tau-bounder-ash
                      make-tau-interval
                      find-largest-inclusive-natp-lower-bound
                      find-smallest-inclusive-natp-upper-bound))))))

(local
 (defthm logic-fns-listp-ainni
   (implies (and (termp term w)
                 (logic-fnsp term w)
                 (term-listp hyps w)
                 (logic-fns-listp hyps w)
                 (arities-okp *stateman-arities* w))
            (logic-fns-listp
             (mv-nth 1 (ainni term hyps type-alist)) w))
   :hints
   (("Goal"
     :in-theory (e/d (ainni)
                     (tau-bounder-+
                      tau-bounder-*
                      tau-bounder-logand
                      tau-bounder-logior
                      tau-bounder-logxor
                      tau-bounder-ash
                      make-tau-interval
                      find-largest-inclusive-natp-lower-bound
                      find-smallest-inclusive-natp-upper-bound))))))

(local
 (defthm logic-term-listp-ainni
   (implies (and (logic-termp term w)
                 (logic-term-listp hyps w)
                 (arities-okp *stateman-arities* w))
            (logic-term-listp
             (mv-nth 1 (ainni term hyps type-alist)) w))
   :hints
   (("Goal"
     :in-theory (e/d (ainni)
                     (tau-bounder-+
                      tau-bounder-*
                      tau-bounder-logand
                      tau-bounder-logior
                      tau-bounder-logxor
                      tau-bounder-ash
                      make-tau-interval
                      find-largest-inclusive-natp-lower-bound
                      find-smallest-inclusive-natp-upper-bound))))))

(local
 (defthm termp-cons-term-IFIX
   (implies (and (termp term w)
                 (arities-okp *stateman-arities* w))
            (termp (cons-term-IFIX term) w))
   :hints (("Goal" :in-theory (enable cons-term-IFIX)))))

(local
 (defthm logic-fnsp-cons-term-IFIX
   (implies (and (logic-fnsp term w)
                 (arities-okp *stateman-arities* w))
            (logic-fnsp (cons-term-IFIX term) w))
   :hints (("Goal" :in-theory (enable cons-term-IFIX)))))

(local
 (defthm logic-termp-cons-term-IFIX
   (implies (and (logic-termp term w)
                 (arities-okp *stateman-arities* w))
            (logic-termp (cons-term-IFIX term) w))))

(local
 (defthm termp-meta-mod1-ainni
   (implies (and (termp term w)
                 (arities-okp *stateman-arities* w)
                 (natp k))
            (and (termp (mv-nth 0 (meta-mod1-ainni term k type-alist)) w)
                 (term-listp (mv-nth 1 (meta-mod1-ainni term k type-alist)) w)))
   :hints (("Goal" :in-theory (enable meta-mod1-ainni)))))

(local
 (defthm logic-fnsp-meta-mod1-ainni
   (implies (and (termp term w)
                 (logic-fnsp term w)
                 (arities-okp *stateman-arities* w))
            (and (logic-fnsp
                  (mv-nth 0 (meta-mod1-ainni term k type-alist)) w)
                 (logic-fns-listp
                  (mv-nth 1 (meta-mod1-ainni term k type-alist)) w)))
   :hints (("Goal" :in-theory (enable meta-mod1-ainni)))))

(local
 (defthm logic-termp-meta-mod1-ainni
   (implies (and (logic-termp term w)
                 (arities-okp *stateman-arities* w))
            (and (logic-termp
                  (mv-nth 0 (meta-mod1-ainni term k type-alist)) w)
                 (logic-term-listp
                  (mv-nth 1 (meta-mod1-ainni term k type-alist)) w)))
   :hints (("Goal" :in-theory (enable meta-mod1-ainni)))))

(local
 (defthm termp-mod-plus-meta-mod1
   (implies (and (termp term w)
                 (arities-okp *stateman-arities* w))
            (termp (mod-plus-meta-mod1 term k2) w))
   :hints (("Goal" :in-theory (enable mod-plus-meta-mod1)))))

(local
 (defthm logic-fnsp-mod-plus-meta-mod1
   (implies (logic-fnsp term w)
            (logic-fnsp (mod-plus-meta-mod1 term k2) w))
   :hints (("Goal" :in-theory (enable mod-plus-meta-mod1)))))

(local
 (defthm logic-termp-mod-plus-meta-mod1
   (implies (and (logic-termp term w)
                 (arities-okp *stateman-arities* w))
            (logic-termp (mod-plus-meta-mod1 term k2) w))
   :hints (("Goal" :in-theory (enable mod-plus-meta-mod1)))))

(local
 (defthm termp-meta-mod1
   (implies (and (termp term w)
                 (arities-okp *stateman-arities* w))
            (and (termp (mv-nth 0 (meta-mod1 term type-alist)) w)
                 (term-listp (mv-nth 1 (meta-mod1 term type-alist)) w)))
   :hints (("Goal" :in-theory (enable meta-mod1)))))

(local
 (defthm logic-fnsp-meta-mod1
   (implies (and (termp term w)
                 (logic-fnsp term w)
                 (arities-okp *stateman-arities* w))
            (and (logic-fnsp (mv-nth 0 (meta-mod1 term type-alist)) w)
                 (logic-fns-listp (mv-nth 1 (meta-mod1 term type-alist)) w)))
   :hints (("Goal" :in-theory (enable meta-mod1)))))

(local
 (defthm logic-termp-meta-mod1
   (implies (and (logic-termp term w)
                 (arities-okp *stateman-arities* w))
            (and (logic-termp (mv-nth 0 (meta-mod1 term type-alist)) w)
                 (logic-term-listp (mv-nth 1 (meta-mod1 term type-alist)) w)))
   :hints (("Goal"
            :in-theory (enable meta-mod1)))))

(local
 (defthm termp-conjoin
   (implies (and (term-listp lst w)
                 (arities-okp *stateman-arities* w))
            (termp (conjoin lst) w))))

(local
 (defthm logic-fnsp-conjoin
   (implies (and (logic-fns-listp lst w)
                 (arities-okp *stateman-arities* w))
            (logic-fnsp (conjoin lst) w))))

(local
 (defthm logic-termp-conjoin
   (implies (and (logic-term-listp lst w)
                 (arities-okp *stateman-arities* w))
            (logic-termp (conjoin lst) w))))

(defthm termp-meta-mod
  (implies (and (termp term w)
                (arities-okp *stateman-arities* w))
           (termp (meta-mod term mfc state) w)))

(defthm logic-fnsp-meta-mod
  (implies (and (termp term w)
                (logic-fnsp term w)
                (arities-okp *stateman-arities* w))
           (logic-fnsp (meta-mod term mfc state) w)))

(defthm logic-termp-meta-mod
  (implies (and (logic-termp term w)
                (arities-okp *stateman-arities* w))
           (logic-termp (meta-mod term mfc state) w))
  :rule-classes nil)

(local
 (defthm term-listp-bounded-address
   (implies (and (termp x w)
                 (arities-okp *stateman-arities* w))
            (term-listp (mv-nth 1 (bounded-address x n type-alist)) w))
   :hints (("Goal" :in-theory (enable bounded-address)))))

(local
 (defthm logic-fns-listp-bounded-address
   (implies (and (termp x w)
                 (logic-fnsp x w)
                 (arities-okp *stateman-arities* w))
            (logic-fns-listp (mv-nth 1 (bounded-address x n type-alist)) w))
   :hints (("Goal" :in-theory (enable bounded-address)))))

(local
 (defthm logic-term-listp-bounded-address
   (implies (and (logic-termp x w)
                 (arities-okp *stateman-arities* w))
            (logic-term-listp (mv-nth 1 (bounded-address x n type-alist)) w))
   :hints (("Goal" :in-theory (enable bounded-address)))))

(local
 (defthm term-listp-union-equal
   (implies (and (term-listp a w)
                 (arities-okp *stateman-arities* w))
            (equal (term-listp (union-equal a b) w)
                   (term-listp b w)))))

(local
 (defthm logic-fns-listp-union-equal
   (implies (and (logic-fns-listp a w)
                 (arities-okp *stateman-arities* w))
            (equal (logic-fns-listp (union-equal a b) w)
                   (logic-fns-listp b w)))))

(local
 (defthm logic-term-listp-union-equal
   (implies (and (logic-term-listp a w)
                 (arities-okp *stateman-arities* w))
            (equal (logic-term-listp (union-equal a b) w)
                   (logic-term-listp b w)))))

(local
 (defthm term-listp-perfectly-shadowedp
   (implies (and (termp a w)
                 (arities-okp *stateman-arities* w)
                 (not (zp n))
                 (term-listp hyps-a w)
                 (termp st w))
            (term-listp (mv-nth 1 (perfectly-shadowedp a n hyps-a int-a st type-alist)) w))
   :hints (("Goal" :in-theory (enable perfectly-shadowedp)))))

(local
 (defthm logic-fns-listp-perfectly-shadowedp
   (implies (and (logic-fnsp a w)
                 (arities-okp *stateman-arities* w)
                 (not (zp n))
                 (logic-fns-listp hyps-a w)
                 (termp st w)
                 (logic-fnsp st w))
            (logic-fns-listp
             (mv-nth 1 (perfectly-shadowedp a n hyps-a int-a st type-alist)) w))
   :hints (("Goal" :in-theory (enable perfectly-shadowedp)))))

(local
 (defthm logic-term-listp-perfectly-shadowedp
   (implies (and (mv-nth 0 (perfectly-shadowedp a n hyps-a int-a st type-alist))
                 (logic-termp a w)
                 (arities-okp *stateman-arities* w)
                 (not (zp n))
                 (logic-term-listp hyps-a w)
                 (logic-termp st w))
            (logic-term-listp (mv-nth 1 (perfectly-shadowedp a n hyps-a int-a st type-alist)) w))
   :hints (("Goal" :in-theory (enable perfectly-shadowedp)))))

(local
 (defthm termp-find-assignment-to-scalar
   (implies (and (termp x w)
                 (arities-okp *stateman-arities* w))
            (termp (mv-nth 1 (find-assignment-to-scalar fn x)) w))
   :hints
   (("Goal" :in-theory (enable find-assignment-to-scalar)))))

(local
 (defthm logic-fnsp-find-assignment-to-scalar
   (implies (logic-fnsp x w)
            (logic-fnsp (mv-nth 1 (find-assignment-to-scalar fn x)) w))
   :hints
   (("Goal" :in-theory (enable find-assignment-to-scalar)))))

(local
 (defthm logic-termp-find-assignment-to-scalar
   (implies (and (logic-termp x w)
                 (arities-okp *stateman-arities* w))
            (logic-termp (mv-nth 1 (find-assignment-to-scalar fn x)) w))
   :hints
   (("Goal" :in-theory (enable find-assignment-to-scalar)))))

; Main:
(defthm logic-termp-meta-i
  (implies (and (logic-termp x w)
                (arities-okp *stateman-arities* w))
           (logic-termp (meta-i x) w))
  :hints
  (("Goal" :in-theory (enable meta-i)))
  :rule-classes nil)

; Main:
(defthm logic-termp-meta-s
  (implies (and (logic-termp x w)
                (arities-okp *stateman-arities* w))
           (logic-termp (meta-s x) w))
  :hints
  (("Goal" :in-theory (enable meta-s)))
  :rule-classes nil)

(local
 (defthm termp-add-hide
   (implies (and (termp x w)
                 (arities-okp *stateman-arities* w))
            (termp (add-hide hiddenp x) w))
   :hints
   (("Goal" :in-theory (enable add-hide)))))

(local
 (defthm logic-fnsp-add-hide
   (implies (and (logic-fnsp x w)
                 (arities-okp *stateman-arities* w))
            (logic-fnsp (add-hide hiddenp x) w))
   :hints
   (("Goal" :in-theory (enable add-hide)))))

(local
 (defthm logic-termp-add-hide
   (implies (and (logic-termp x w)
                 (arities-okp *stateman-arities* w))
            (logic-termp (add-hide hiddenp x) w))
   :hints
   (("Goal" :in-theory (enable add-hide)))))

(local
 (defthm termp-meta-binary-+-with-const
   (implies (and (termp x w)
                 (arities-okp *stateman-arities* w)
                 (acl2-numberp k))
            (termp (meta-binary-+-with-const k x) w))
   :hints
   (("Goal" :in-theory (enable meta-binary-+-with-const)))))

(local
 (defthm logic-fnsp-meta-binary-+-with-const
   (implies (and (logic-fnsp x w)
                 (arities-okp *stateman-arities* w))
            (logic-fnsp (meta-binary-+-with-const k x) w))
   :hints
   (("Goal" :in-theory (enable meta-binary-+-with-const)))))

(local
 (defthm logic-termp-meta-binary-+-with-const
   (implies (and (logic-termp x w)
                 (arities-okp *stateman-arities* w)
                 (acl2-numberp k))
            (logic-termp (meta-binary-+-with-const k x) w))
   :hints
   (("Goal" :in-theory (enable meta-binary-+-with-const)))))

(local
 (defthm termp-common-reference-address
   (implies (and (termp a w)
                 (termp b w)
                 (mv-nth 0 (common-reference-address a b)))
            (termp (mv-nth 2 (common-reference-address a b)) w))
   :hints
   (("Goal" :in-theory (enable common-reference-address)))))

(local
 (defthm logic-fnsp-common-reference-address
   (implies (and (termp a w)
                 (logic-fnsp a w)
                 (termp b w)
                 (logic-fnsp b w)
                 (mv-nth 0 (common-reference-address a b)))
            (logic-fnsp (mv-nth 2 (common-reference-address a b)) w))
   :hints
   (("Goal" :in-theory (enable common-reference-address)))))

(local
 (defthm logic-termp-common-reference-address
   (implies (and (logic-termp a w)
                 (logic-termp b w)
                 (mv-nth 0 (common-reference-address a b)))
            (logic-termp (mv-nth 2 (common-reference-address a b)) w))
   :hints
   (("Goal" :in-theory (enable common-reference-address)))))

(local
 (defthm termp-mx-rover-1
   (implies (and (termp a w)
                 (term-listp hyps1 w)
                 (termp st w)
                 (arities-okp *stateman-arities* w))
            (term-listp (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist)) w))
   :hints
   (("Goal" :in-theory (enable mx-rover)))))

(local
 (defthm logic-fnsp-mx-rover-1
   (implies (and (termp a w)
                 (logic-fnsp a w)
                 (term-listp hyps1 w)
                 (logic-fns-listp hyps1 w)
                 (termp st w)
                 (logic-fnsp st w)
                 (arities-okp *stateman-arities* w))
            (logic-fns-listp
             (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist)) w))
   :hints
   (("Goal" :in-theory (e/d (mx-rover)
                            (assoc-equal))))))

(local
 (defthm logic-termp-mx-rover-1
   (implies (and (logic-termp a w)
                 (logic-term-listp hyps1 w)
                 (logic-termp st w)
                 (arities-okp *stateman-arities* w))
            (logic-term-listp
             (mv-nth 1 (mx-rover a hyps1 int1 n st type-alist)) w))
   :hints
   (("Goal" :in-theory (e/d (mx-rover)
                            (assoc-equal))))))

(local
 (defthm termp-mx-rover-0
   (implies (and (termp a w)
                 (term-listp hyps1 w)
                 (termp st w)
                 (arities-okp *stateman-arities* w)
                 (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist)))
            (termp (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist)) w))
   :hints
   (("Goal" :in-theory (e/d (mx-rover)
                            (assoc-equal))))))

(local
 (defthm logic-fnsp-mx-rover-0
   (implies (and (termp a w)
                 (logic-fnsp a w)
                 (term-listp hyps1 w)
                 (logic-fns-listp hyps1 w)
                 (termp st w)
                 (logic-fnsp st w)
                 (arities-okp *stateman-arities* w)
                 (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist)))
            (logic-fnsp (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist)) w))
   :hints
   (("Goal" :in-theory (e/d (mx-rover)
                            (assoc-equal))))))

(local
 (defthm logic-termp-mx-rover-0
   (implies (and (logic-termp a w)
                 (logic-term-listp hyps1 w)
                 (logic-termp st w)
                 (arities-okp *stateman-arities* w)
                 (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist)))
            (logic-termp (mv-nth 0 (mx-rover a hyps1 int1 n st type-alist)) w))
   :hints
   (("Goal" :in-theory (e/d (mx-rover)
                            (assoc-equal))))))

(local
 (defthm term-listp-merge-term-order
   (implies (and (term-listp l1 w)
                 (term-listp l2 w))
            (term-listp (merge-term-order l1 l2) w))))

(local
 (defthm logic-fns-listp-merge-term-order
   (implies (and (logic-fns-listp l1 w)
                 (logic-fns-listp l2 w))
            (logic-fns-listp (merge-term-order l1 l2) w))))

(local
 (defthm logic-term-listp-merge-term-order
   (implies (and (logic-term-listp l1 w)
                 (logic-term-listp l2 w))
            (logic-term-listp (merge-term-order l1 l2) w))))

(local
 (defthm term-listp-evens
   (implies (term-listp l w)
            (term-listp (evens l) w))))

(local
 (defthm logic-fns-listp-evens
   (implies (logic-fns-listp l w)
            (logic-fns-listp (evens l) w))))

(local
 (defthm logic-term-listp-evens
   (implies (logic-term-listp l w)
            (logic-term-listp (evens l) w))))

(local
 (defthm term-listp-merge-sort-term-order
   (implies (term-listp l w)
            (term-listp (merge-sort-term-order l) w))))

(local
 (defthm logic-fns-listp-merge-sort-term-order
   (implies (logic-fns-listp l w)
            (logic-fns-listp (merge-sort-term-order l) w))))

(local
 (defthm logic-term-listp-merge-sort-term-order
   (implies (logic-term-listp l w)
            (logic-term-listp (merge-sort-term-order l) w))))

(local
 (defthm term-listp-meta-ash-ash1
   (implies (and (termp x w)
                 (arities-okp *stateman-arities* w))
            (term-listp (meta-ash-ash1 x) w))))

(local
 (defthm logic-fns-listp-meta-ash-ash1
   (implies (logic-fnsp x w)
            (logic-fns-listp (meta-ash-ash1 x) w))))

(local
 (defthm logic-term-listp-meta-ash-ash1
   (implies (and (logic-termp x w)
                 (arities-okp *stateman-arities* w))
            (logic-term-listp (meta-ash-ash1 x) w))))

(local
 (defthm termp-xxxjoin
   (implies (and (term-listp lst w)
                 (arities-okp *stateman-arities* w)
                 (consp (cdr lst)))
            (termp (xxxjoin 'binary-+ lst) w))
   :hints (("Goal" :induct (len lst)))))

(local
 (defthm logic-fnsp-xxxjoin
   (implies (and (logic-fns-listp lst w)
                 (arities-okp *stateman-arities* w))
            (logic-fnsp (xxxjoin 'binary-+ lst) w))))

; The following proof attempt loops if you just let xxxjoin expand.
(local
 (defthm logic-termp-xxxjoin
   (implies (and (logic-term-listp lst w)
                 (arities-okp *stateman-arities* w)
                 (consp (cdr lst)))
            (logic-termp (xxxjoin 'binary-+ lst) w))
   :hints (("Goal"
            :in-theory (disable xxxjoin)))))

(local
 (defthm why-do-i-need-this
   (implies (consp (cdr (meta-ash-ash1 x)))
            (consp (cdr (merge-sort-term-order (meta-ash-ash1 x)))))))

(local
 (defthm consp-append
   (equal (consp (append a b))
          (or (consp a)
              (consp b)))))

(local
 (defthm consp-meta-ash-ash1
   (consp (meta-ash-ash1 x))))

(local
 (defthm termp-meta-ash-ash
   (implies (and (termp x w)
                 (arities-okp *stateman-arities* w))
            (termp (meta-ash-ash x) w))
   :hints (("Goal"
            :in-theory (e/d (meta-ash-ash)
                            (term-listp-merge-sort-term-order))
            :use (:instance term-listp-merge-sort-term-order
                            (l (META-ASH-ASH1 X))
                            (w w)))
           ("Subgoal 1"
            :in-theory (disable term-listp-meta-ash-ash1)
            :use (:instance term-listp-meta-ash-ash1)))))

(local
 (defthm logic-fnsp-meta-ash-ash
   (implies (and (logic-fnsp x w)
                 (arities-okp *stateman-arities* w))
            (logic-fnsp (meta-ash-ash x) w))
   :hints (("Goal"
            :in-theory (e/d (meta-ash-ash)
                            (logic-fns-listp-merge-sort-term-order))
            :use (:instance logic-fns-listp-merge-sort-term-order
                            (l (META-ASH-ASH1 X))
                            (w w)))
           ("Subgoal 1"
            :in-theory (e/d ()
                            (logic-fns-listp-meta-ash-ash1))
            :use (:instance logic-fns-listp-meta-ash-ash1)))))

(local
 (defthm logic-termp-meta-ash-ash
   (implies (and (logic-termp x w)
                 (arities-okp *stateman-arities* w))
            (logic-termp (meta-ash-ash x) w))))

(defthm logic-termp-meta-r
  (implies (and (logic-termp x w)
                (arities-okp *stateman-arities* w))
           (logic-termp (meta-r x mfc state) w))
  :rule-classes nil)

; Main:
(defthm logic-termp-meta-<
  (implies (and (logic-termp x w)
                (arities-okp *stateman-arities* w))
           (logic-termp (meta-< x mfc state) w))
  :hints
  (("Goal" :in-theory (enable meta-<)))
  :rule-classes nil)

(local
 (defthm termp-delete-assignment-at-depth
   (implies (and (termp st w)
                 (arities-okp *stateman-arities* w))
            (termp (delete-assignment-at-depth depth st) w))))

(local
 (defthm logic-fnsp-delete-assignment-at-depth
   (implies (logic-fnsp st w)
            (logic-fnsp (delete-assignment-at-depth depth st) w))))

(local
 (defthm logic-termp-delete-assignment-at-depth
   (implies (and (logic-termp st w)
                 (arities-okp *stateman-arities* w))
            (logic-termp (delete-assignment-at-depth depth st) w))))

; Main:
(defthm logic-termp-meta-!i
  (implies (and (logic-termp x w)
                (arities-okp *stateman-arities* w))
           (logic-termp (meta-!i x) w))
  :hints
  (("Goal" :in-theory (enable meta-!i)))
  :rule-classes nil)

; Main:
(defthm logic-termp-meta-!s
  (implies (and (logic-termp x w)
                (arities-okp *stateman-arities* w))
           (logic-termp (meta-!s x) w))
  :hints
  (("Goal" :in-theory (enable meta-!s)))
  :rule-classes nil)

(local
 (defthm termp-remove-all-hides1
   (implies (and (if flg
                     (termp x w)
                     (term-listp x w))
                 (arities-okp *stateman-arities* w))
            (if flg
                (termp (remove-all-hides1 flg depth x) w)
                (term-listp (remove-all-hides1 flg depth x) w)))
   :rule-classes nil))

(local
 (defthm logic-fnsp-remove-all-hides1
   (implies (if flg
                (logic-fnsp x w)
              (logic-fns-listp x w))
            (if flg
                (logic-fnsp (remove-all-hides1 flg depth x) w)
              (logic-fns-listp (remove-all-hides1 flg depth x) w)))
   :rule-classes nil))

(local
 (defthm logic-termp-remove-all-hides1
   (implies (and (if flg
                     (logic-termp x w)
                   (logic-term-listp x w))
                 (arities-okp *stateman-arities* w))
            (if flg
                (logic-termp (remove-all-hides1 flg depth x) w)
              (logic-term-listp (remove-all-hides1 flg depth x) w)))
   :hints (("Goal"
            :use (termp-remove-all-hides1
                  logic-fnsp-remove-all-hides1)))
   :rule-classes nil))

(local
 (defthm termp-remove-all-hides1-corollary
   (implies (and (termp x w)
                 (arities-okp *stateman-arities* w))
            (termp (remove-all-hides1 t depth x) w))
   :hints (("Goal" :use (:instance termp-remove-all-hides1
                                   (flg t))))))

(local
 (defthm logic-fnsp-remove-all-hides1-corollary
   (implies (logic-fnsp x w)
            (logic-fnsp (remove-all-hides1 t depth x) w))
   :hints (("Goal" :use (:instance logic-fnsp-remove-all-hides1
                                   (flg t))))))

(local
 (defthm logic-termp-remove-all-hides1-corollary
   (implies (and (logic-termp x w)
                 (arities-okp *stateman-arities* w))
            (logic-termp (remove-all-hides1 t depth x) w))
   :hints (("Goal" :use (:instance logic-termp-remove-all-hides1
                                   (flg t))))))

(local
 (defthm term-listp-find-assignment-to-vector1
   (implies (and (termp a w)
                 (not (zp n))
                 (term-listp hyps-a w)
                 (termp st w)
                 (arities-okp *stateman-arities* w))
            (term-listp (mv-nth 1 (find-assignment-to-vector1 a n hyps-a int-a st type-alist))
                        w))))

(local
 (defthm logic-fns-listp-find-assignment-to-vector1
   (implies (and (logic-fnsp a w)
                 (not (zp n))
                 (logic-fns-listp hyps-a w)
                 (termp st w)
                 (logic-fnsp st w)
                 (arities-okp *stateman-arities* w))
            (logic-fns-listp
             (mv-nth 1 (find-assignment-to-vector1 a n hyps-a int-a st type-alist))
             w))))

(local
 (defthm logic-term-listp-find-assignment-to-vector1
   (implies (and (logic-termp a w)
                 (not (zp n))
                 (logic-term-listp hyps-a w)
                 (logic-termp st w)
                 (arities-okp *stateman-arities* w))
            (logic-term-listp
             (mv-nth 1 (find-assignment-to-vector1 a n hyps-a int-a st type-alist))
             w))))

; Main:
(defthm logic-termp-meta-!r
  (implies (and (logic-termp x w)
                (arities-okp *stateman-arities* w))
           (logic-termp (meta-!r x mfc state) w))
  :hints
  (("Goal" :in-theory (e/d (meta-!r)
                           (assoc-equal))))
  :rule-classes nil)

; -----------------------------------------------------------------
; The Metatheorems

(defthm meta-mod-correct
  (implies (pseudo-termp term)
           (equal (stateman-eval term alist)
                  (stateman-eval (meta-mod term mfc state) alist)))
  :rule-classes
  ((:meta :trigger-fns (MOD)
          :well-formedness-guarantee logic-termp-meta-mod)))

(defthm meta-i-correct
  (implies (pseudo-termp term)
           (equal (stateman-eval term alist)
                  (stateman-eval (meta-i term) alist)))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes
  ((:meta :trigger-fns (i)
          :well-formedness-guarantee logic-termp-meta-i)))

(defthm meta-s-correct
  (implies (pseudo-termp term)
           (equal (stateman-eval term alist)
                  (stateman-eval (meta-s term) alist)))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes
  ((:meta :trigger-fns (s)
          :well-formedness-guarantee logic-termp-meta-s)))

(defthm meta-r-correct
  (implies (pseudo-termp term)
           (equal (stateman-eval term alist)
                  (stateman-eval (meta-r term mfc state) alist)))
  :hints (("Goal" :in-theory (disable mfc-type-alist
                                      tau-interval-dom
                                      tau-interval-lo-rel
                                      tau-interval-lo
                                      tau-interval-hi-rel
                                      tau-interval-hi
                                      in-tau-intervalp
                                      (:executable-counterpart !i)
                                      (:executable-counterpart !s))
           :expand (:free (x) (hide x))
           ))
  :rule-classes
  ((:meta :trigger-fns (r)
          :well-formedness-guarantee logic-termp-meta-r)))

(defthm meta-<-correct
  (implies (pseudo-termp term)
           (equal (stateman-eval term alist)
                  (stateman-eval (meta-< term mfc state) alist)))
  :hints
  (("Goal" :use ((:instance ainni-correct-part-2a
                            (term (fargn term 1))
                            (hyps nil)
                            (type-alist (mfc-type-alist mfc)))
                 (:instance ainni-correct-part-2a
                            (term (fargn term 2))
                            (hyps nil)
                            (type-alist (mfc-type-alist mfc)))
                 (:instance ainni-correct-part-2b
                            (term (fargn term 1))
                            (hyps nil)
                            (type-alist (mfc-type-alist mfc)))
                 (:instance ainni-correct-part-2b
                            (term (fargn term 2))
                            (hyps nil)
                            (type-alist (mfc-type-alist mfc))))
    :in-theory (e/d (in-tau-intervalp) (ainni-correct-part-2a
                                        ainni-correct-part-2b
                                        mfc-type-alist
                                        tau-interval-lo
                                        tau-interval-hi))))
  :rule-classes
  ((:meta :trigger-fns (<)
          :well-formedness-guarantee logic-termp-meta-<)))

(defthm meta-!i-correct
  (implies (pseudo-termp term)
           (equal (stateman-eval term alist)
                  (stateman-eval (meta-!i term) alist)))
  :hints (("Goal"
           :expand ((:free (x) (hide x)))))
  :rule-classes ((:meta :trigger-fns (!i)
                        :well-formedness-guarantee logic-termp-meta-!i)))

(defthm meta-!s-correct
  (implies (pseudo-termp term)
           (equal (stateman-eval term alist)
                  (stateman-eval (meta-!s term) alist)))
  :hints (("Goal"
           :expand ((:free (x) (hide x)))))
  :rule-classes ((:meta :trigger-fns (!s)
                        :well-formedness-guarantee logic-termp-meta-!s)))

(defthm meta-!r-correct
  (implies (pseudo-termp term)
           (equal (stateman-eval term alist)
                  (stateman-eval (meta-!r term mfc state) alist)))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes ((:meta :trigger-fns (!r)
                        :well-formedness-guarantee logic-termp-meta-!r)))

(memoize 'memoizable-meta-r)
(memoize 'memoizable-meta-!r)
(memoize 'memoizable-meta-mod)
(memoize 'memoizable-meta-<)
(memoize 'acl2::sublis-var1
         :condition '(and (null acl2::alist)
                          (consp acl2::form)
                          (eq (car acl2::form) 'HIDE)))
