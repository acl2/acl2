; Copyright (C) 2022 Intel Corporation
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
(include-book "tools/easy-simplify" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/osets/sort" :dir :system)
(include-book "numlist")
(include-book "bound-rewriter")
(include-book "std/strings/hexify" :dir :System)
(include-book "std/strings/suffixp" :dir :System)

(define easy-simplify-sequence (term
                                hints
                                &key
                                (hyp 't)
                                (equiv ''equal)
                                (normalize 't)
                                (rewrite 't)
                                (repeat '1000)
                                (backchain-limit '1000)
                                (state 'state))
  :mode :program
  (b* (((When (atom hints)) (value term))
       ((er next-term) (acl2::easy-simplify-term-fn term hyp (car hints) equiv normalize rewrite repeat backchain-limit state)))
    (easy-simplify-sequence
     next-term (cdr hints)
     :hyp hyp :equiv equiv :normalize normalize :rewrite rewrite :repeat repeat :backchain-limit backchain-limit)))


(define bounds-translate-casesplit (cases state)
  :mode :program
  (b* (((when (atom cases))
        (value nil))
       (wrld (w state))
       (case1 (car cases))
       ((mv negatedp body-term)
        (case-match case1
          (('not body) (mv t body))
          (& (mv nil case1))))
       ((er trans-term)
        (acl2::translate body-term t nil t __function__ wrld state))
       (trans-case (if negatedp (acl2::dumb-negate-lit trans-term) trans-term))
       ((er trans-rest)
        (bounds-translate-casesplit (cdr cases) state)))
    (value (cons trans-case trans-rest))))

(define bounds-range-casesplit-rec (term bounds prev)
  (if (atom bounds)
      `((>= ,term ,prev))
    (cons (if prev
              `(and (>= ,term ,prev)
                    (< ,term ,(car bounds)))
            `(< ,term ,(car bounds)))
          (bounds-range-casesplit-rec term (cdr bounds) (car bounds)))))

(define bounds-range-casesplit (term bounds)
  (b* ((bounds (set::mergesort bounds)))
    (bounds-range-casesplit-rec term bounds nil)))

(define defbounds-from-to-by ((from rationalp)
                    (to rationalp)
                    (by rationalp))
  :guard-hints (("goal" :in-theory (disable ceiling)))
  :prepwork ((local (defthm ceiling-natp-1
                      (implies (and (<= 0 num)
                                    (< 0 den)
                                    (rationalp num)
                                    (rationalp den))
                               (<= 0 (ceiling num den)))
                      :rule-classes :linear))

             (local (defthm ceiling-natp-2
                      (implies (and (<= num 0)
                                    (< den 0)
                                    (rationalp num)
                                    (rationalp den))
                               (<= 0 (ceiling num den)))
                      :rule-classes :linear))
             (local (in-theory (disable ceiling))))
  (if (if (< from to)
          (< 0 by)
        (< by 0))
      (acl2::numlist from by (ceiling (- to from) by))
    (list from)))

(define bounds-cases-expand-range (cases)
  (case-match cases
    ((':ranges term . bounds)
     (bounds-range-casesplit term bounds))
    ((':ranges-from-to-by term from to by)
     (bounds-range-casesplit term (defbounds-from-to-by (rfix from) (rfix to) (rfix by))))
    (& cases)))

;; (define bounds-translate-casesplit (cases state)
;;   (b* ((cases (case-match cases
;;                 ((':range term . bounds)
;;                  (bounds-range-casesplit term bounds))
;;                 (& cases))))
;;     (bounds-translate-casesplit-rec (cdr cases))))

(define bounds-translate-cases (cases state)
  :mode :program
  (b* (((when (atom cases))
        (value nil))
       ((er trans-cases1)
        (bounds-translate-casesplit (car cases) state))
       ((er trans-rest)
        (bounds-translate-cases (cdr cases) state)))
    (value (cons trans-cases1 trans-rest))))


(define hexify-rational ((x rationalp))
  (if (equal (denominator x) 1)
      (str::hexify x)
    (concatenate 'string "(/ " (str::hexify (numerator x)) " " (str::hexify (denominator x)))))

(encapsulate
  (((defbounds-print-case-bounds * * * * * state) => *
    :formals (case term err lower-bound upper-bound state)
    :guard (or err
             (and (rationalp lower-bound)
                  (rationalp upper-bound)))))
 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)
 (local (defun defbounds-print-case-bounds (case term err lower-bound upper-bound state)
          (declare (xargs :guard (or err
                                     (and (rationalp lower-bound)
                                          (rationalp upper-bound)))
                          :stobjs state))
          nil)))

(define defbounds-print-case-bounds-default (case term err lower-bound upper-bound state)
  :guard (or err
             (and (rationalp lower-bound)
                  (rationalp upper-bound)))
  (progn$
   (and case
        (cw-print-base-radix! 16 "Case: ~x0~%" case))
   (and term
        (cw-print-base-radix! 16 "Term: ~x0~%" term))
   (if err
       (cw "Error: ~@0~%" err)
     (b* ((upper-bound-adj (* upper-bound (fix (or (and (boundp-global 'boundrw-trace-multiply state)
                                                        (rfix (f-get-global 'boundrw-trace-multiply state)))
                                                  1))))
         (lower-bound-adj (* lower-bound (fix (or (and (boundp-global 'boundrw-trace-multiply state)
                                                       (rfix (f-get-global 'boundrw-trace-multiply state)))
                                                  1))))
         (upper-str (hexify-rational upper-bound-adj))
         (lower-str (hexify-rational lower-bound-adj)))
       (cw "Lower bound: ~t0~s1~%" (- 90 (length lower-str)) lower-str)
       (cw "Upper bound: ~t0~s1~%" (- 90 (length upper-str)) upper-str))))
  ///
  (defattach (defbounds-print-case-bounds defbounds-print-case-bounds-default)))      
       

(define simplify-and-bound-case (term simp-hints case-conjunct hyp skip-lower skip-upper state)
  :mode :program
  (b* (((er trans-conjunct) (bounds-translate-casesplit case-conjunct state))
       
       (full-hyp `(and ,@trans-conjunct ,hyp))
       ((mv err simp-term state) (easy-simplify-sequence term simp-hints :hyp full-hyp))
       ((when err)
        (defbounds-print-case-bounds case-conjunct nil "couldn't simplify term" nil nil state)
        (value nil))
       ((mv err bound-terms state)
        (acl2::rewrite-bounds-find-bounds-fn simp-term full-hyp nil nil nil t nil nil state))
       ((when err)
        (defbounds-print-case-bounds case-conjunct simp-term
          (if (msgp err)
              (msg "no bounds: ~@0~%" err)
            "no bounds~%")
          nil nil state)
        (value nil))
       ((list lower-bound-term upper-bound-term) bound-terms)
       ((unless (or skip-lower (and (quotep lower-bound-term)
                                    (rationalp (unquote lower-bound-term)))))
        (defbounds-print-case-bounds case-conjunct simp-term
          (msg "Lower bound wasn't a constant: ~x0~%" lower-bound-term)
          nil nil state)
        (value nil))
       ((unless (or skip-upper (and (quotep upper-bound-term)
                                    (rationalp (unquote upper-bound-term)))))
        (defbounds-print-case-bounds case-conjunct simp-term
          (msg "Upper bound wasn't a constant: ~x0~%" upper-bound-term)
          nil nil state)
        (value nil))
       (upper-bound (unquote upper-bound-term))
       (lower-bound (unquote lower-bound-term)))
    (defbounds-print-case-bounds case-conjunct simp-term nil lower-bound upper-bound state)
    (value (cons lower-bound upper-bound))))



(define combine-bounds (bounds1 bounds2) ;; both are (cons lower-bound upper-bound)
  :mode :program
  (b* (((when (atom bounds1)) bounds2)
       ((when (atom bounds2)) bounds1)
       ((cons lower1 upper1) bounds1)
       ((cons lower2 upper2) bounds2))
    (cons (min lower1 lower2) (max upper1 upper2))))

(defines simplify-and-bound-cases
  (define simplify-and-bound-casesplit (cases1 full-cases1 rest-cases case-conjunct hyp term simp-hints skip-lower skip-upper state)
    ;; :measure (acl2::two-nats-measure (len rest-cases) (len cases1))
    ;; Cases1 is a tail of full-cases1.  Full-cases1 is a list of
    ;; possibilities to consider, along with the possibility that all are
    ;; false (like in ACL2's casesplit hint). We recur through cases1 collecting the
    :mode :program
    (if (atom cases1)
        (b* ((case-conjunct (append (acl2::dumb-negate-lit-lst full-cases1) case-conjunct)))
          (simplify-and-bound-cases rest-cases case-conjunct hyp term simp-hints skip-lower skip-upper state))
      (b* (((er bounds-rest)
            (simplify-and-bound-casesplit (cdr cases1) full-cases1 rest-cases case-conjunct hyp term simp-hints skip-lower skip-upper state))
           (case-conjunct (cons (car cases1) case-conjunct))
           ((er bounds-first)
            (simplify-and-bound-cases rest-cases case-conjunct hyp term simp-hints skip-lower skip-upper state)))
        (value (combine-bounds bounds-first bounds-rest)))))

  (define simplify-and-bound-cases (cases case-conjunct hyp term simp-hints skip-lower skip-upper state)
    :mode :program
    (if (atom cases)
        (simplify-and-bound-case term simp-hints case-conjunct hyp skip-lower skip-upper state)
      (b* ((case1 (bounds-cases-expand-range (car cases))))
        (simplify-and-bound-casesplit
         case1 case1 (cdr cases) case-conjunct hyp term simp-hints skip-lower skip-upper state)))))

(define bounds-casesplit-hints (cases)
  (if (atom cases)
      nil
    (cons `'(:cases ,(bounds-cases-expand-range (car cases)))
          (bounds-casesplit-hints (cdr cases)))))

(define bounds-stable-casesplit-hints (cases)
  (cond ((atom cases) nil)
        ((atom (cdr cases))
         `((and stable-under-simplificationp
                '(:cases ,(bounds-cases-expand-range (car cases))))))
        (t `((and stable-under-simplificationp
                  '(:computed-hint-replacement
                    ,(bounds-casesplit-hints (cdr cases))
                    :cases ,(bounds-cases-expand-range (car cases))))))))




(defun hint-seq-stable-under-simplification (hint-seq)
  (if (atom hint-seq)
      nil
    (cons `(and stable-under-simplificationp
                ',(car hint-seq))
          (hint-seq-stable-under-simplification (cdr hint-seq)))))

(define def-simplify-fn (name term hyp hints rule-classes state)
  :mode :program
  (b* (((er simp-term) (easy-simplify-sequence term hints :hyp hyp))
       (concl `(equal ,term ,simp-term))
       (body (if (equal hyp t) concl `(implies ,hyp ,concl))))
    (value `(defthm ,name
              ,body
              :hints ,(and (consp hints)
                           `(',(car hints)
                             ,@(hint-seq-stable-under-simplification (cdr hints))))
              :rule-classes ,rule-classes))))

(defmacro def-simplify (name term
                             &key (hyp 't)
                             hints
                             (rule-classes ':rewrite))
  `(make-event (def-simplify-fn ',name ',term ',hyp ',hints ',rule-classes state)))

(define def-bounds-fn (name
                       term
                       hyp
                       cases
                       simp-hints
                       post-cases-hints
                       integerp
                       skip-lower
                       skip-upper
                       in-theory-override
                       rule-classes
                       state)
  :mode :program
  (b* (;; ((er trans-cases) (bounds-translate-cases cases state))
       ((er simp-term) (easy-simplify-sequence term simp-hints :hyp hyp))
       ((er (cons lower-bound upper-bound))
        (simplify-and-bound-cases cases nil hyp simp-term post-cases-hints skip-lower skip-upper state))
       (- (cw-print-base-radix! 16 "Bounds: ~x0 ~x1~%" lower-bound upper-bound))
       (basename (if (str::strsuffixp "-BOUNDS" (symbol-name name))
                     (subseq (symbol-name name) 0 (- (length (symbol-name name)) (length "-BOUNDS")))
                   (symbol-name name)))
       (lower-bound-name (intern-in-package-of-symbol
                          (concatenate 'string "*" basename "-LOWER-BOUND*")
                          name))
       (upper-bound-name (intern-in-package-of-symbol
                          (concatenate 'string "*" basename "-UPPER-BOUND*")
                          name))
       (lemmaname (intern-in-package-of-symbol
                   (concatenate 'string basename "-BOUNDS-LEMMA")
                   name))
       (lemma-concl `(let ((bounds-val ,term))
                       (and ,@(if skip-lower nil `((<= ,lower-bound bounds-val)))
                            ,@(if skip-upper nil `((<= bounds-val ,upper-bound))))))
       (lemma-body (if (equal hyp t) lemma-concl `(implies ,hyp ,lemma-concl)))
       (theory-override (and in-theory-override
                             `(:in-theory ,in-theory-override)))
       (lemma-hints (if (consp simp-hints)
                        `(',(car simp-hints)
                          ,@(hint-seq-stable-under-simplification (cdr simp-hints))
                          ,@(bounds-stable-casesplit-hints cases)
                          ,@(hint-seq-stable-under-simplification post-cases-hints)
                          (acl2::rewrite-bounds nil :clause-auto-bounds t ,@theory-override))
                      `(,@(bounds-casesplit-hints cases)
                        ,@(and (consp post-cases-hints)
                               `(',(car post-cases-hints)
                                 . ,(hint-seq-stable-under-simplification (cdr post-cases-hints))))
                        (acl2::rewrite-bounds nil :clause-auto-bounds t ,@theory-override))))
       (thmname (intern-in-package-of-symbol
                 (concatenate 'string basename "-BOUNDS")
                 name))
       (thm-concl `(let ((bounds-val ,term))
                     (and ,@(if skip-lower nil `((<= ,lower-bound-name bounds-val)))
                          ,@(if skip-upper nil `((<= bounds-val ,upper-bound-name))))))
       (thm-body (if (equal hyp t) thm-concl `(implies ,hyp ,thm-concl))))
    (value
     `(encapsulate nil
        (defconst ,lower-bound-name ,(if integerp (ceiling lower-bound 1) lower-bound))
        (defconst ,upper-bound-name ,(if integerp (floor upper-bound 1) upper-bound))
        (local
         (defthm ,lemmaname
           ,lemma-body
           :hints ,lemma-hints
           :rule-classes nil))
        (defthm ,thmname
          ,thm-body
          :hints (("goal" :use ,lemmaname))
          :rule-classes ,rule-classes)
        ))))

(defmacro def-bounds (name term
                           &key
                           (cases)
                           (simp-hints)
                           (post-cases-hints)
                           (hyp 't)
                           (integerp 't)
                           (skip-lower 'nil)
                           (skip-upper 'nil)
                           (in-theory-override 'nil)
                           (rule-classes ':linear))
  `(make-event (def-bounds-fn ',name ',term ',hyp ',cases ',simp-hints ',post-cases-hints ',integerp ',skip-lower ',skip-upper ',in-theory-override ',rule-classes state)))

(defstub check-bounds-override () nil)
(defattach check-bounds-override constant-nil-function-arity-0)

(defmacro check-lower-bound (name bound)
  `(with-output :off :all :on (error comment)
     (progn (assert-event (or (check-bounds-override)
                              (>= ,name ,bound))
                          :msg (msg "~x0 bounds check failed: ~s1 < ~s2~%" ',name
                                    (str::hexify ,name)
                                    (str::hexify ,bound)))
            (value-triple (cw "Lower bound check passed: ~x0~%Value: ~s1~%" ',name (str::hexify ,name))))))

(defmacro check-upper-bound (name bound)
  `(with-output :off :all :on (error comment)
     (progn (assert-event (or (check-bounds-override)
                              (<= ,name ,bound))
                          :msg (msg "~x0 bounds check failed: ~s1 > ~s2~%" ',name
                                    (str::hexify ,name)
                                    (str::hexify ,bound)))
            (value-triple (cw "Upper bound check passed: ~x0~%Value: ~s1~%" ',name (str::hexify ,name))))))



(defxdoc def-bounds
  :parents (proof-automation)
  :short "Find and prove upper and lower bounds for an expression, following a series of simplification steps."
  :long
  "<p>Usage:</p>
@({
 (def-bounds my-bounds-theorem
    ;; Term to simplify and bound
    (* (foo x) (bar y))

    ;; Assumption (default t)
    :hyp (foo-input-p x)

    
    ;; Simplification steps, each a hint keyword-value list
    :simp-hints
     ((:in-theory (enable foo-cancel))
      (:expand ((bar y))))

    ;; Case splits, each either a list of cases or a
    ;; :ranges or :ranges-from-to-by form.
    :cases
     (((< (foo-prime x) 0))
      (:ranges (bar-quotient y) -1000 -100 0 100 1000)
      (:ranges-from-to-by (bar-remainder y)
        #x-a000 #xa000 #x1000))

    ;; Further simplification steps for after case splitting
    :post-cases-hints
    ((:in-theory (enable bar-remainder-when-foo-prime-negative)))

    ;; Choose to only bound in one direction or the other
    :skip-lower nil
    :skip-upper nil

    ;; Indicates that the term is always an integer
    :integerp t

    ;; Override rule-classes (default :linear)
    :rule-classes (:rewrite :linear)

    ;; Override theory when applying bound-rewriter (must enable REWRITE-BOUNDS)
    :in-theory-override (enable rewrite-bounds))
 })

<p>This applies the given simplification steps and case-splits, then uses @(see
rewrite-bounds) to find an upper and lower bound for the resulting expression.
Then it replicates these steps in a @('defthm') to prove the bounds, creating a
linear rule by default (but the rule-classes may be overridden).</p>")
