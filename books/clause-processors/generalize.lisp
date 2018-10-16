; Copyright (C) 2008 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(include-book "join-thms")
(include-book "term-vars")
(include-book "meta/pseudo-termp-lemmas" :dir :system)


(defevaluator gen-eval gen-eval-lst ((if x y z)) :namedp t)

(def-join-thms gen-eval)


(define replace-alist-to-bindings ((alist alistp) bindings)
  :returns (aa alistp)
  (if (atom alist)
      nil
    (cons (cons (cdar alist) (gen-eval (caar alist) bindings))
          (replace-alist-to-bindings (cdr alist) bindings)))
  ///
  (defthm assoc-equal-replace-alist-to-bindings
    (implies (not (member-equal x (strip-cdrs alist)))
             (not (assoc-equal x (replace-alist-to-bindings alist env)))))

  (defthm assoc-in-replace-alist-to-bindings
    (implies (and (assoc-equal x alist)
                  (no-duplicatesp-equal (strip-cdrs alist)))
             (equal (assoc-equal (cdr (assoc-equal x alist))
                                 (replace-alist-to-bindings alist env))
                    (cons (cdr (assoc-equal x alist))
                          (gen-eval x env))))
    :hints (("goal" :induct (assoc-equal x alist)))))



;; misc lemmas
(local
 (progn
   (local (defthm member-of-union
            (iff (member x (union-equal y z))
                 (or (member x y)
                     (member x z)))))
   (local (defthm intersectp-of-union
            (iff (intersectp-equal x (union-equal y z))
                 (or (intersectp-equal x y)
                     (intersectp-equal x z)))))

   (defthm intersectp-equal-of-components-of-simple-term-vars-1
     (implies (and (not (intersectp-equal lst (simple-term-vars-lst x)))
                   (consp x))
              (not (intersectp-equal lst (simple-term-vars (car x)))))
     :hints(("Goal" :expand ((simple-term-vars-lst x)))))

   (defthm intersectp-equal-of-components-of-simple-term-vars-2
     (implies (and (not (intersectp-equal lst (simple-term-vars-lst x)))
                   (consp x))
              (not (intersectp-equal lst (simple-term-vars-lst (cdr x)))))
     :hints(("Goal" :expand ((simple-term-vars-lst x)))))

   (defthm intersectp-equal-of-components-of-simple-term-vars-3
     (implies (and (consp x) (not (equal (car x) 'quote))
                   (not (intersectp-equal lst (simple-term-vars x))))
              (not (intersectp-equal lst (simple-term-vars-lst (cdr x)))))
     :hints(("Goal" :in-theory (enable simple-term-vars))))

   (defthm simple-term-vars-of-variable
     (implies (and (symbolp X) x)
              (equal (simple-term-vars x) (list x)))
     :hints(("Goal" :in-theory (enable simple-term-vars)))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))


   (defthm intersectp-equal-with-singleton
     (iff (intersectp-equal lst (list x))
          (member-equal x lst)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm assoc-eq-is-assoc-equal
;   (equal (assoc-eq x al) (assoc-equal x al)))

   (defthm assoc-equal-of-append
     (implies (alistp a)
              (equal (assoc-equal x (append a b))
                     (or (assoc-equal x a)
                         (assoc-equal x b)))))


   (defthm symbolp-assoc-equal
     (implies (symbol-listp (strip-cdrs alist))
              (symbolp (cdr (assoc-equal x alist)))))

   (defthm nonnil-values-implies-cdr
     (implies (and (assoc-equal x alist)
                   (not (member-equal nil (strip-cdrs alist))))
              (cdr (assoc-equal x alist))))))


(defines replace-subterms
  :flag-local nil
  (define replace-subterms ((x pseudo-termp)
                            (alist alistp))
    :flag term
    :returns (xx pseudo-termp :hyp (and (pseudo-termp x)
                                        (pseudo-term-val-alistp alist))
                 :hints ((and stable-under-simplificationp
                              '(:expand ((pseudo-termp x))))))
    (let ((lookup (assoc-equal x alist)))
      (if lookup
          (cdr lookup)
        (cond ((atom x) x)
              ((eq (car x) 'quote) x)
              (t (cons (car x) (replace-subterms-list (cdr x) alist)))))))

  (define replace-subterms-list ((x pseudo-term-listp)
                                 (alist alistp))
    :flag list
    :returns (xx (and (implies (and (pseudo-term-listp x)
                                    (pseudo-term-val-alistp alist))
                               (pseudo-term-listp xx))
                      (equal (len xx) (len x))))
    (if (atom x)
        nil
      (cons (replace-subterms (car x) alist)
            (replace-subterms-list (cdr x) alist))))


  ///

  (defthm-replace-subterms-flag
    (defthm replace-subterms-identity
      (implies (and (not (intersectp-equal (strip-cdrs alist)
                                           (simple-term-vars x)))
                    (symbol-listp (strip-cdrs alist))
                    (not (member-equal nil (strip-cdrs alist)))
                    (no-duplicatesp-equal (strip-cdrs alist))
                    ;; (pseudo-termp x)
                    )
               (equal (gen-eval (replace-subterms x alist)
                                (append
                                 (replace-alist-to-bindings alist env)
                                 env))
                      (gen-eval x env)))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable gen-eval-of-fncall-args
                                        gen-eval-of-nonsymbol-atom)))
              (and stable-under-simplificationp
                   '(:cases ((and (symbolp x) x)))))
      :flag term)
    (defthm replace-subterms-list-identity
      (implies (and (not (intersectp-equal (strip-cdrs alist)
                                           (simple-term-vars-lst x)))
                    (symbol-listp (strip-cdrs alist))
                    (not (member-equal nil (strip-cdrs alist)))
                    (no-duplicatesp-equal (strip-cdrs alist))
                    ;; (pseudo-term-listp x)
                    )
               (equal (gen-eval-lst (replace-subterms-list x alist)
                                    (append
                                     (replace-alist-to-bindings alist env)
                                     env))
                      (gen-eval-lst x env)))
      :flag list))




  (defthm disjoin-replace-subterms-list
    (implies (and (not (intersectp-equal (strip-cdrs alist)
                                         (simple-term-vars-lst x)))
                  (symbol-listp (strip-cdrs alist))
                  (not (member-equal nil (strip-cdrs alist)))
                  (no-duplicatesp-equal (strip-cdrs alist)))
             (iff (gen-eval (disjoin (replace-subterms-list x alist))
                            (append (replace-alist-to-bindings alist env)
                                    env))
                  (gen-eval (disjoin x) env)))
    :hints (("goal" :induct (len x))
            ("Subgoal *1/1" :in-theory
             (enable replace-subterms-list
                     simple-term-vars-lst
                     gen-eval-disjoin-when-consp))))

  (defthm consp-replace-subterms-list
    (equal (consp (replace-subterms-list clause alist))
           (consp clause))
    :hints (("goal" :induct (len clause)))))





(define simple-generalize-cp ((clause pseudo-term-listp)
                              alist)
  (b* (((unless (alistp alist)) (list clause))
       (syms (strip-cdrs alist)))
    (if (and (symbol-listp syms)
             (not (intersectp-eq syms (simple-term-vars-lst clause)))
             (not (member-eq nil syms))
             (no-duplicatesp-eq syms))
        (list (replace-subterms-list clause alist))
      (list clause)))
  ///

  (defun alist-for-simple-generalize-cp (clause alist env)
    (let ((syms (strip-cdrs alist)))
      (if (and (alistp alist)
               (symbol-listp syms)
               (not (intersectp-equal syms (simple-term-vars-lst clause)))
               (not (member-equal nil syms))
               (no-duplicatesp-equal syms))
          (append (replace-alist-to-bindings alist env) env)
        env)))

  (defthm simple-generalize-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp env)
                  (gen-eval (conjoin-clauses (simple-generalize-cp clause alist))
                            (alist-for-simple-generalize-cp clause alist env)))
             (gen-eval (disjoin clause) env))
    :hints (("goal" :do-not-induct t))
    :rule-classes :clause-processor))












(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (in-theory (disable floor)))



;; MAKE-N-VARS, below, makes N "fresh" symbols that are not members of a
;; given list and are nonnil.


(define char-of-digit ((n natp))
  :guard (< n 10)
  :returns (d characterp)
  (code-char (+ (char-code #\0)
                (mbe :logic (nfix n) :exec n)))
  ///
  (defthm char-of-digit-unique
    (implies (and (< (nfix n) 10)
                  (< (nfix m) 10))
             (equal (equal (char-of-digit m) (char-of-digit n))
                    (equal (nfix m) (nfix n))))
    :hints(("Goal" :in-theory (disable nfix
                                       char-code-code-char-is-identity)
            :use ((:instance char-code-code-char-is-identity
                   (n (+ (char-code #\0) (nfix n))))
                  (:instance char-code-code-char-is-identity
                   (n (+ (char-code #\0) (nfix m))))))))

  (defthm char-of-digit-equals-const
    (implies (and (syntaxp (quotep c))
                  (< (nfix n) 10))
             (equal (equal (char-of-digit n) c)
                    (and (characterp c)
                         (equal (- (char-code c) (char-code #\0)) (nfix n)))))
    :hints (("goal" :in-theory (disable (force) nfix)))))


(local
 (encapsulate nil
   (local (in-theory (enable char-of-digit)))



   (defconst *digit-chars* '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))

   (local
    (defun char-of-digit-members (n)
      (or (zp n)
          (and (member-equal (char-of-digit (1- n))
                             *digit-chars*)
               (char-of-digit-members (1- n))))))

   (local (defthm char-of-digit-members-n
            (implies (and (integerp m) (<= 0 m) (< m n)
                          (integerp n)
                          (char-of-digit-members n))
                     (member-equal (char-of-digit m) *digit-chars*))))

   (defthm char-of-digit-member-of-digit-chars
     (implies (and (integerp n) (<= 0 n) (< n 10))
              (member-equal (char-of-digit n) *digit-chars*))
     :hints (("Goal" :in-theory (disable char-of-digit-members-n)
              :use ((:instance char-of-digit-members-n (n 10) (m n))))))))




(define nat-to-charlist1 ((n natp))
  :returns (nc character-listp)
  (if (zp n)
      nil
    (cons (char-of-digit (mod n 10))
          (nat-to-charlist1 (floor n 10))))
  ///

  (local
   (defun n2cu-ind (n m)
     (if (or (zp n) (zp m))
         nil
       (n2cu-ind (floor n 10) (floor m 10)))))

  (defthm nat-to-charlist1-unique
    (equal (equal (nat-to-charlist1 n) (nat-to-charlist1 m))
           (equal (nfix n) (nfix m)))
    :hints (("goal" :induct (n2cu-ind n m)))))


(local
 (encapsulate nil
   (local (in-theory (enable nat-to-charlist1)))
   (defthm nat-to-charlist1-intersect-digit-chars
     (implies (not (zp n))
              (intersectp-equal (nat-to-charlist1 n) *digit-chars*)))

  (defthm nat-to-charlist1-not-single-0
    (not (equal (nat-to-charlist1 n) '(#\0)))
    :hints (("goal" :cases  ((and (natp n) (<= 10 n)) (zp n)))))))

(define nat-to-charlist ((n natp))
  :returns (nc character-listp)
  (if (zp n)
      (list #\0)
    (nat-to-charlist1 n))
  ///

  (defthm nat-to-charlist-unique
    (equal (equal (nat-to-charlist n) (nat-to-charlist m))
           (equal (nfix n) (nfix m)))))

(local
 (defsection reverse-charlist-unique

   (local
    (defun rcu-ind (x y xz yz)
      (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
      (if (and (atom x) (atom y))
          (list xz yz)
        (rcu-ind (cdr x) (cdr y)
                 (if (consp x) (cons (car x) xz) xz)
                 (if (consp y) (cons (car y) yz) yz)))))

   (defthm len-revappend
     (equal (len (revappend a b))
            (+ (len a) (len b))))

   (defthm revappend-charlists-unique
     (implies (and (character-listp x) (character-listp y)
                   (equal (len xz) (len yz)))
              (equal (equal (revappend x xz) (revappend y yz))
                     (and (equal x y) (equal xz yz))))
     :hints (("goal" :induct (rcu-ind x y xz yz))))

   (defthm reverse-charlists-unique
     (implies (and (character-listp x) (character-listp y))
              (equal (equal (reverse x) (reverse y))
                     (equal x y))))

   (defthm character-listp-reverse
     (implies (character-listp x)
              (character-listp (reverse x))))

   (defthm intersectp-revappend1
     (implies (intersectp-equal b c)
              (intersectp-equal (revappend a b) c)))

   (defthm intersectp-revappend
     (equal (intersectp-equal (revappend a b) c)
            (or (intersectp-equal a c)
                (intersectp-equal b c))))

   (defthm intersectp-reverse
     (equal (intersectp-equal (reverse a) b)
            (intersectp-equal a b)))

   (defthm intersectp-append
     (equal (intersectp-equal (append a b) c)
            (or (intersectp-equal a c)
                (intersectp-equal b c))))

   (local (in-theory (disable reverse)))

   (defthm coerce-unique-1
     (implies (and (character-listp x) (character-listp y))
              (equal (equal (coerce x 'string) (coerce y 'string))
                     (equal x y)))
     :hints (("goal" :in-theory (disable coerce-inverse-1)
              :use ((:instance coerce-inverse-1
                     (x y))
                    coerce-inverse-1))))

   (defthm coerce-unique-2
     (implies (and (stringp x) (stringp y))
              (equal (equal (coerce x 'list) (coerce y 'list))
                     (equal x y)))
     :hints (("goal" :in-theory (disable coerce-inverse-2)
              :use ((:instance coerce-inverse-2
                     (x y))
                    coerce-inverse-2))))))


(define nat-to-str ((n natp))
  :returns (s stringp)
  (reverse (coerce (nat-to-charlist n) 'string))
  ///

  (defthm nat-to-str-unique
    (equal (equal (nat-to-str n) (nat-to-str m))
           (equal (nfix n) (nfix m)))))

(local
 (encapsulate nil
   (local (in-theory (enable nat-to-str)))
   (defthm nat-to-str-coerce-intersectp
     (intersectp-equal (coerce (nat-to-str n) 'list)
                       *digit-chars*)
     :hints(("Goal" :in-theory (enable nat-to-charlist))))))

(define symbol-n ((base symbolp)
                  (n natp))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name base) (nat-to-str n))
   (and (mbt (symbolp base)) base))
  ///
  (local (defthm append-unique
           (equal (equal (append x y) (append x z))
                  (equal y z))))
  (local
   (defthm intern-in-package-of-symbol-unique
     (implies (and (stringp a) (stringp b) (symbolp base))
              (equal (equal (intern-in-package-of-symbol a base)
                            (intern-in-package-of-symbol b base))
                     (equal a b)))
     :hints (("goal" :in-theory (disable symbol-name-intern-in-package-of-symbol)
              :use ((:instance symbol-name-intern-in-package-of-symbol
                     (s a) (any-symbol base))
                    (:instance symbol-name-intern-in-package-of-symbol
                     (s b) (any-symbol base)))))))

  (defthm symbol-n-unique-n
    (equal (equal (symbol-n base n) (symbol-n base m))
           (equal (nfix n) (nfix m)))
    :hints(("Goal" :in-theory (disable nfix))))

  (local
   (defthm coerce-symbol-n-intersectp-equal
     (intersectp-equal (coerce (symbol-name (symbol-n base n)) 'list)
                       *digit-chars*)
     :hints(("Goal" :in-theory (enable symbol-n)))))

  (defthm symbol-n-nonnil
    (symbol-n base n)
    :hints (("goal" :in-theory (disable coerce-symbol-n-intersectp-equal)
             :use (coerce-symbol-n-intersectp-equal)))))



(local (defthm nfix-when-natp
         (implies (natp x)
                  (equal (nfix x) x))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(define new-symbol1-measure ((n natp)
                             (base symbolp)
                             (avoid symbol-listp))
  ;; Measures (- next-index-not-in-avoid n)
  :verify-guards nil
  :measure (len avoid)
  (let* ((n (nfix n))
         (sym (symbol-n base n)))
    (if (member sym avoid)
        (+ 1 (new-symbol1-measure (1+ n) base (remove sym avoid)))
      0))
  ///
  (local (defthm member-remove
           (iff (member k (remove j x))
                (and (not (equal k j))
                     (member k x)))))

  (local (defun remove-prev-ind (n m base avoid)
           (declare (xargs :measure (len avoid)))
           (let* ((n (nfix n))
                  (sym (symbol-n base n)))
             (if (member sym avoid)
                 (list (remove-prev-ind (1+ n) m base (remove sym avoid))
                       (remove-prev-ind (1+ n) n base (remove (symbol-n base m) (remove sym avoid))))
               avoid))))

  (local (defthmd remove-commute
           (equal (remove m (remove n x))
                  (remove n (remove m x)))))

  (local (defthm new-symbol1-measure-of-remove-prev
           (implies (< (nfix m) (nfix n))
                    (equal (new-symbol1-measure n base (remove (symbol-n base (nfix m)) avoid))
                           (new-symbol1-measure n base avoid)))
           :hints (("goal" :induct (remove-prev-ind n m base avoid)
                    :in-theory (e/d (remove-commute) (nfix))
                    :expand ((:free (avoid) (new-symbol1-measure n base avoid)))))))

  (defthm new-symbol1-measure-decr-with-increasing-n
    (implies (member (symbol-n base (nfix n)) avoid)
             (< (new-symbol1-measure (+ 1 (nfix n)) base avoid)
                (new-symbol1-measure n base avoid)))
    :hints(("Goal" :in-theory (disable nfix)
            :do-not-induct t
            :expand ((new-symbol1-measure n base avoid))))
    :rule-classes :linear))



(define new-symbol1 ((n natp) (base symbolp)
                     (avoid symbol-listp))
  :measure (new-symbol1-measure n base avoid)
  :hints(("Goal" :in-theory (disable nfix)))
  :returns (mv (nn natp :rule-classes :type-prescription)
               (new symbolp :rule-classes :type-prescription))
  (let* ((n (mbe :logic (nfix n) :exec n))
         (new (acl2::symbol-n base n)))
    (if (member-eq new avoid)
        (new-symbol1 (1+ n) base avoid)
      (mv n new)))
  ///

  (defthm new-symbol1-retval
    (b* (((mv idx sym) (new-symbol1 n base avoid)))
      (equal sym
             (symbol-n base idx))))

  (defthm new-symbol1-unique
    (b* (((mv idx &) (new-symbol1 n base avoid)))
      (not (member (symbol-n base idx) avoid))))

  (defthm new-symbol1-idx-incr
    (<= (nfix n) (mv-nth 0 (new-symbol1 n base avoid)))
    :rule-classes :linear))


(define new-symbol ((base symbolp)
                    (avoid symbol-listp))
  :returns (bb (and (symbolp bb) bb) :rule-classes :type-prescription)
  (if (or (not base) (not (mbt (symbolp base))) (member base avoid))
      (b* (((mv & sym) (new-symbol1 0 base avoid)))
        sym)
    base)
  ///
  (defthm new-symbol-unique
    (not (member (new-symbol base avoid) avoid))))

(define make-n-vars ((n natp)
                     (base symbolp)
                     (m natp)
                     (avoid symbol-listp))
  :measure (nfix n)
  :returns (syms symbol-listp)
  (b* (((when (zp n))
        nil)
       ((mv nextm newvar) (new-symbol1 m base avoid))
       (rest (make-n-vars (1- n) base (+ 1 nextm) (cons newvar avoid))))
    (cons newvar rest))
  ///

  (defthm make-n-vars-len
    (equal (len (make-n-vars n base m avoid-lst))
           (nfix n)))

  (local (defthm intersectp-equal-cons-2
           (iff (intersectp-equal a (cons b c))
                (or (intersectp-equal a c)
                    (member b a)))))

  (defthm make-n-vars-not-in-avoid
    (not (intersectp-equal (make-n-vars n base m avoid-lst)
                           avoid-lst)))

  (defthm make-n-vars-member-lemma
    (implies (< (nfix j) (nfix k))
             (not (member-equal (symbol-n base j)
                                (make-n-vars n base k avoid-lst)))))

  (defthm not-member-make-n-vars-when-in-avoid-lst
    (implies (member v avoid-lst)
             (not (member v (make-n-vars n base k avoid-lst)))))

  (defthm make-n-vars-no-dupsp
    (no-duplicatesp-equal (make-n-vars n base m avoid-lst)))

  (defthm make-n-vars-not-nil
    (not (member-equal nil (make-n-vars n base m avoid-lst))))


  (defthm symbol-listp-make-n-vars
    (symbol-listp (make-n-vars n base m avoid-lst))))


(define new-symbols-from-base ((n natp)
                               (base symbolp)
                               (avoid symbol-listp))
  (make-n-vars n base 0 avoid)
  ///

  (defthm new-symbols-from-base-len
    (equal (len (new-symbols-from-base n base avoid-lst))
           (nfix n)))

  (defthm not-member-new-symbols-from-base-when-in-avoid-lst
    (implies (member k avoid-lst)
             (not (member k (new-symbols-from-base n base avoid-lst)))))

  (defthm new-symbols-from-base-not-in-avoid
    (not (intersectp-equal (new-symbols-from-base n base avoid-lst)
                           avoid-lst)))

  (defthm new-symbols-from-base-no-dupsp
    (no-duplicatesp-equal (new-symbols-from-base n base avoid-lst)))

  (defthm new-symbols-from-base-not-nil
    (not (member-equal nil (new-symbols-from-base n base avoid-lst))))


  (defthm symbol-listp-new-symbols-from-base
    (symbol-listp (new-symbols-from-base n base avoid-lst))))

(define new-symbols ((bases symbol-listp) (avoid symbol-listp))
  (if (atom bases)
      nil
    (let ((sym (new-symbol (car bases) avoid)))
      (cons sym
            (new-symbols (cdr bases) (cons sym avoid)))))
  ///
  (defthm new-symbols-len
    (equal (len (new-symbols bases avoid-lst))
           (len bases)))

  (defthm not-member-new-symbols-when-in-avoid-lst
    (implies (member k avoid-lst)
             (not (member k (new-symbols bases avoid-lst)))))

  (defthm new-symbols-not-in-avoid
    (not (intersectp-equal (new-symbols bases avoid-lst)
                           avoid-lst)))

  (defthm new-symbols-no-dupsp
    (no-duplicatesp-equal (new-symbols bases avoid-lst)))

  (defthm new-symbols-not-nil
    (not (member-equal nil (new-symbols bases avoid-lst))))


  (defthm symbol-listp-new-symbols
    (symbol-listp (new-symbols bases avoid-lst))))


(local (defthm alistp-pairlis$
         (alistp (pairlis$ a b))))

(local (defthm strip-cdrs-of-pairlis
         (implies (and (true-listp b)
                       (equal (len a) (len b)))
                  (equal (strip-cdrs (pairlis$ a b))
                         b))))

(local (defthm len-of-strip-cdrs
         (equal (len (strip-cdrs x))
                (len (strip-cars x)))))


(define generalize-termlist-cp ((clause pseudo-term-listp)
                                hint)
  ;; hint is (list list-of-terms base-varname)
  (b* (((unless (and (true-listp hint)
                     (<= (len hint) 2)
                     (pseudo-term-listp (car hint))
                     (symbolp (cadr hint))))
        (raise "malformed hint ~x0" hint)
        (list clause))
       ((list termlist basename) hint)
       (basename (or (and (symbolp basename) basename) 'x))
       (clause-vars (simple-term-vars-lst clause))
       (syms (new-symbols-from-base (len termlist) basename clause-vars))
       (alist (pairlis$ termlist syms)))
    (list (replace-subterms-list clause alist)))

  ///

  (defun generalize-termlist-alist (clause hint env)
    (b* (((unless (and (true-listp hint)
                     (<= (len hint) 2)
                     (pseudo-term-listp (car hint))
                     (symbolp (cadr hint))))
          env)
         ((list termlist basename) hint)
         (basename (or (and (symbolp basename) basename) 'x))
         (clause-vars (simple-term-vars-lst clause))
         (syms (new-symbols-from-base (len termlist) basename clause-vars))
         (alist (pairlis$ termlist syms)))
      (append (replace-alist-to-bindings alist env) env)))

  (defthm generalize-termlist-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp env)
                  (gen-eval (conjoin-clauses (generalize-termlist-cp clause hint))
                            (generalize-termlist-alist clause hint env)))
             (gen-eval (disjoin clause) env))
    :hints (("goal" :do-not-induct t))
    :rule-classes :clause-processor))


(define generalize-with-alist-cp ((clause pseudo-term-listp) alist)
  (b* (((unless (and (alistp alist)
                     (symbol-listp (strip-cdrs alist))
                     (pseudo-term-listp (strip-cars alist))))
        (raise "malformed alist ~x0" alist)
        (list clause))
       (terms (strip-cars alist))
       (syms (strip-cdrs alist))
       (clause-vars (simple-term-vars-lst clause))
       (new-syms (new-symbols syms clause-vars))
       (alist (pairlis$ terms new-syms)))
    (list (replace-subterms-list clause alist)))

  ///

  (defun generalize-with-alist-alist (clause alist env)
    (b* (((unless (and (alistp alist)
                       (symbol-listp (strip-cdrs alist))
                       (pseudo-term-listp (strip-cars alist))))
          env)
         (terms (strip-cars alist))
         (syms (strip-cdrs alist))
         (clause-vars (simple-term-vars-lst clause))
         (new-syms (new-symbols syms clause-vars))
         (alist (pairlis$ terms new-syms)))
      (append (replace-alist-to-bindings alist env) env)))

  (defthm generalize-with-alist-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp env)
                  (gen-eval (conjoin-clauses (generalize-with-alist-cp clause hint))
                            (generalize-with-alist-alist clause hint env)))
             (gen-eval (disjoin clause) env))
    :hints (("goal" :do-not-induct t))
    :rule-classes :clause-processor))

