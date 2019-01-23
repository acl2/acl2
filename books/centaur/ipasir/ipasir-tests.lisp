; IPASIR - Link from ACL2 to IPASIR incremental sat solvers
; Copyright (C) 2017 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "IPASIR")

(include-book "ipasir-tools")
(include-book "ipasir-backend")
(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (define triv (state)
         (b* (((local-ipasir) (mv data ipasir state))
              (ipasir (ipasir-add-lit ipasir 0))
              (ipasir (ipasir-add-lit ipasir 2))
              (ipasir (ipasir-finalize-clause ipasir))
              (ipasir (ipasir-add-lit ipasir 3))
              (ipasir (ipasir-add-lit ipasir 1))
              (ipasir (ipasir-finalize-clause ipasir))
              (ipasir (ipasir-add-lit ipasir 10))
              (ipasir (ipasir-finalize-clause ipasir))
              (ipasir (ipasir-set-limit ipasir 0))
              ((mv status ipasir) (ipasir-solve ipasir))
              ((unless (eq status :sat))
               (mv status ipasir state))
              (val1 (ipasir-val ipasir 0))
              (val-1 (ipasir-val ipasir 1))
              (val2 (ipasir-val ipasir 2))
              (val-2 (ipasir-val ipasir 3))
              (val3 (ipasir-val ipasir 4))
              (val-3 (ipasir-val ipasir 5))
              (res1 (list status val1 val-1 val2 val-2 val3 val-3))
              (ipasir (ipasir-assume ipasir 3))
              (ipasir (ipasir-assume ipasir 1))
              (ipasir (ipasir-assume ipasir 4))
              ((mv status2 ipasir) (ipasir-solve ipasir))
              ((when (eq status2 :sat))
               (mv status2 ipasir state))
              ((unless (eq status2 :unsat))
               (mv status ipasir state))
              (failed1 (ipasir-failed ipasir 1))
              (failed2 (ipasir-failed ipasir 3))
              (failed3 (ipasir-failed ipasir 4))
              (res2 (list status2 failed1 failed2 failed3))
              (ipasir (ipasir-add-lit ipasir 0))
              (ipasir (ipasir-finalize-clause ipasir))
              (ipasir (ipasir-assume ipasir 2))
              (ipasir (ipasir-assume ipasir 0))
              (ipasir (ipasir-assume ipasir 4))
              ((mv status3 ipasir) (ipasir-solve ipasir))
              ((unless (eq status3 :unsat))
               (mv status3 ipasir state))
              (failed1 (ipasir-failed ipasir 0))
              (failed2 (ipasir-failed ipasir 2))
              (failed3 (ipasir-failed ipasir 4))
              (res3 (list status3 failed1 failed2 failed3)))
           (mv (list res1 res2 res3)
               ipasir state))))


(local (defthm triv-len
         (implies (not (symbolp (mv-nth 0 (triv state))))
                  (equal (len (car (mv-nth 0 (triv state)))) 7))
         :hints(("Goal" :in-theory (e/d (triv) ((triv)))))))

(make-event
 (b* (((mv val state) (triv state))
      ((unless (equal val '((:SAT 0 1 1 0 0 1)
                            (:UNSAT 1 1 0)
                            (:UNSAT 0 1 0))))
       (er soft 'triv-test "Failed!")))
   (value '(value-triple :ok))))


(local (include-book "centaur/satlink/cnf-basics" :dir :system))

(local
 (define ipasir-set-maj3 (ipasir (out litp) (a litp) (b litp) (c litp))
   :guard (and (not (eq (ipasir-get-status ipasir) :undef))
               (ipasir-empty-new-clause ipasir))
   :returns (new-ipasir)
   :parents (ipasir-formula)
   :short "Add clauses restricting @('out') to be @('(maj3 a b c)')."
   (b* ((ipasir (ipasir-add-ternary ipasir out (l- a) (l- b)))
        (ipasir (ipasir-add-ternary ipasir out (l- a) (l- c)))
        (ipasir (ipasir-add-ternary ipasir out (l- c) (l- b)))
        (ipasir (ipasir-add-ternary ipasir (l- out) a b))
        (ipasir (ipasir-add-ternary ipasir (l- out) a c))
        (ipasir (ipasir-add-ternary ipasir (l- out) c b)))
     ipasir)
   
   ///
   (defret ipasir-set-maj3-status
     (equal (ipasir$a->status new-ipasir) :input))

   (defret ipasir-set-maj3-formula
     (implies (syntaxp (not (equal ipasir ''nil)))
              (equal (ipasir$a->formula new-ipasir)
                     (append (ipasir$a->formula (ipasir-set-maj3 nil out a b c))
                             (ipasir$a->formula ipasir))))
     :hints(("Goal" :in-theory (enable ipasir-add-ternary-formula))))

   (defret ipasir-set-maj3-eval-formula
     (equal (eval-formula (ipasir$a->formula new-ipasir) env)
            (b-and (b-eqv (eval-lit out env)
                          (b-ior (b-and (eval-lit a env)
                                        (eval-lit b env))
                                 (b-ior (b-and (eval-lit a env)
                                               (eval-lit c env))
                                        (b-and (eval-lit b env)
                                               (eval-lit c env)))))
                   (eval-formula (ipasir$a->formula ipasir) env)))
     :hints ((and stable-under-simplificationp
                  '(:bdd (:vars nil) :in-theory (enable b-and b-ior b-not b-xor)))))

   (defret ipasir-set-maj3-new-clause
     (not (ipasir$a->new-clause new-ipasir)))

   (defret ipasir-set-maj3-assumption
     (equal (ipasir$a->assumption new-ipasir)
            (ipasir$a->assumption ipasir)))))

(define lit-vec-eval ((lit-vec lit-listp) env$)
  :measure (len lit-vec)
  (if (atom lit-vec)
      0
    (acl2::logcons (eval-lit (car lit-vec) env$)
                   (lit-vec-eval (cdr lit-vec) env$)))
  ///
  (defthm lit-vec-eval-of-nil
    (equal (lit-vec-eval nil assign) 0))

  (defthm lit-vec-eval-of-cons
    (equal (lit-vec-eval (cons a b) env)
           (acl2::logcons (eval-lit a env)
                          (lit-vec-eval b env))))

  (defthm lit-vec-eval-of-append
    (equal (lit-vec-eval (append a b) env)
           (acl2::logapp (len a)
                         (lit-vec-eval a env)
                         (lit-vec-eval b env)))
    :hints(("Goal" :in-theory (enable bitops::logapp**)))))

(local (define make-adder ((next natp)
                           (carry-in litp)
                           (a-inputs lit-listp)
                           (b-inputs lit-listp)
                           ipasir)
         :guard (and (eql (len a-inputs) (len b-inputs))
                     (consp a-inputs)
                     (not (eq (ipasir-get-status ipasir) :undef))
                     (ipasir-empty-new-clause ipasir))
         :returns (mv (next-out natp :rule-classes :type-prescription)
                      (sum lit-listp)
                      new-ipasir)
         :guard-debug t
         (b* ((next (lnfix next))
              (carry-in (lit-fix carry-in))
              (a (lit-fix (car a-inputs)))
              (b (lit-fix (car b-inputs)))
              ((mv hsum next) (mv (make-lit next 0) (+ 1 next)))
              ((mv sum next) (mv (make-lit next 0) (+ 1 next)))
              ((mv carry next) (mv (make-lit next 0) (+ 1 next)))
              ;; hsum is xor of a, b:
              (ipasir (ipasir-set-xor ipasir hsum a b))

              ;; sum is xor of carry-in, hsum:
              (ipasir (ipasir-set-xor ipasir sum carry-in hsum))

              ;; carry is maj of carry-in, a, b:
              (ipasir (ipasir-set-maj3 ipasir carry a b carry-in))

              ((when (mbe :logic (or (atom (cdr a-inputs))
                                     (atom (cdr b-inputs)))
                          :exec (atom (cdr a-inputs))))
               (mv next (list sum carry) ipasir))

              ((mv next sum-out ipasir) (make-adder next carry (cdr a-inputs) (cdr b-inputs) ipasir)))
           (mv next (cons sum sum-out) ipasir))
         ///
         (defret ipasir-make-adder-status
           (equal (ipasir$a->status new-ipasir) :input))
         
         (local (defthm lit-vec-eval-of-atom
                  (implies (atom x)
                           (equal (lit-vec-eval x assign) 0))
                  :hints(("Goal" :in-theory (enable lit-vec-eval)))))

         (local (include-book "arithmetic/top-with-meta" :dir :system))

         (local (defthm len-equal-0
                  (Equal (equal 0 (len x))
                         (atom x))))

         (local (include-book "std/lists/append" :dir :system))

         (local (defun-sk ipasir-make-adder-next/sum-ipasir-irrel (next carry-in a-inputs b-inputs)
                  (forall ipasir
                          (implies (syntaxp (not (equal ipasir ''nil)))
                                   (b* (((mv next-out sum new-ipasir)
                                         (make-adder next carry-in a-inputs b-inputs ipasir))
                                        ((mv next-out2 sum2 new-ipasir2)
                                         (make-adder next carry-in a-inputs b-inputs nil)))
                                     (and (equal next-out next-out2)
                                          (equal sum sum2)
                                          (equal (ipasir$a->formula new-ipasir)
                                                 (append (ipasir$a->formula new-ipasir2)
                                                         (ipasir$a->formula ipasir)))))))
                  :rewrite :direct))
         (local (in-theory (disable ipasir-make-adder-next/sum-ipasir-irrel)))

         (local (defthm ipasir-make-adder-next/sum-ipasir-irrel-lemma
                  (ipasir-make-adder-next/sum-ipasir-irrel
                   next carry-in a-inputs b-inputs)
                  :hints (("goal" :induct (make-adder next carry-in a-inputs b-inputs ipasir))
                          (and stable-under-simplificationp
                               `(:expand (,(car (last acl2::clause))))))))
                                   

         (defret ipasir-make-adder-next/sum
           (b* (((mv next-out2 sum2 &) (make-adder next carry-in a-inputs b-inputs nil)))
             (implies (syntaxp (not (equal ipasir ''nil)))
                      (and (equal next-out next-out2)
                           (equal sum sum2)))))

         
         
         (defret ipasir-make-adder-formula
           (implies (syntaxp (not (equal ipasir ''nil)))
                    (equal (ipasir$a->formula new-ipasir)
                           (append (ipasir$a->formula
                                    (mv-nth 2 (make-adder next carry-in a-inputs b-inputs nil)))
                                   (ipasir$a->formula ipasir)))))

         ;; (local (defthm equal-b-xor-0
         ;;          (implies (syntaxp (or (acl2::rewriting-negative-literal-fn
         ;;                                 `(equal (acl2::b-xor$inline ,a ,b) '0)
         ;;                                 mfc state)
         ;;                                (acl2::rewriting-negative-literal-fn
         ;;                                 `(equal '0 (acl2::b-xor$inline ,a ,b))
         ;;                                 mfc state)))
         ;;                   (equal (equal (b-xor a b) 0)
         ;;                          (equal (bfix a) (bfix b))))
         ;;          :hints(("Goal" :in-theory (enable b-xor)))))

         ;; (local (defthm logxor-of-bits
         ;;          (implies (and (bitp a) (bitp b))
         ;;                   (equal (logxor a b)
         ;;                          (b-xor a b)))
         ;;          :hints(("Goal" :in-theory (enable bitp)))))


         ;; (local (defthm sfdf
         ;;          (implies (equal a (+ b c d))
         ;;                   (iff (equal (+ b c e) a)
         ;;                        (equal (fix d) (fix e))))))

         ;; (local (defthm fdsfdsf
         ;;          (implies (and (equal a (b-ior b c))
         ;;                        (bitp b) (bitp c) (bitp d) (bitp a))
         ;;                   (iff (equal a (+ d b))
         ;;                        (if (bit->bool b)
         ;;                            (not (bit->bool d))
         ;;                          (equal c d))))
         ;;          :hints(("Goal" :in-theory (enable bitp)))))

         (defret ipasir-make-adder-eval-formula
           ;; this isn't sufficient for general reasoning but is a good sanity
           ;; check.  The real correctness stmt would have to involve all the
           ;; hsums and carry-ins as intermediate variables.  Something like:
           ;; if no literals >= next are present in the formula, then the
           ;; result formula is true under assign if:
           ;;  - the original formula is satisfied
           ;;  - the eval of the sum equals the addition of the evals of the inputs
           ;;  - the auxiliary variables are set to the right function of the
           ;;    portion of the assignment < next.
           (implies (and (bit->bool (eval-formula (ipasir$a->formula new-ipasir) assign))
                         (equal (len a-inputs) (len b-inputs))
                         (consp a-inputs))
                    (and (equal (lit-vec-eval sum assign)
                                (+ (lit-vec-eval a-inputs assign)
                                   (lit-vec-eval b-inputs assign)
                                   (eval-lit carry-in assign)))
                         (bit->bool (eval-formula (ipasir$a->formula ipasir) assign))))
           :hints (("Goal" :induct t)
                   (and stable-under-simplificationp
                        '(:in-theory (enable bitops::equal-logcons-strong
                                             b-and b-xor b-ior)
                          :expand ((lit-vec-eval a-inputs assign)
                                   (lit-vec-eval b-inputs assign)))))
           :rule-classes nil)
         
         (defret ipasir-make-adder-new-clause
           (not (ipasir$a->new-clause new-ipasir)))
         
         (defret ipasir-make-adder-assumption
           (equal (ipasir$a->assumption new-ipasir)
                  (ipasir$a->assumption ipasir)))

         (defret ipasir-sum-length
           (equal (len sum)
                  (+ 1 (max 1 (min (len a-inputs) (len b-inputs))))))))

(local (define make-equiv ((next natp)
                           (a-inputs lit-listp)
                           (b-inputs lit-listp)
                           ipasir)
         :guard (and (eql (len a-inputs) (len b-inputs))
                     (consp a-inputs)
                     (not (eq (ipasir-get-status ipasir) :undef))
                     (ipasir-empty-new-clause ipasir))
         :returns (mv (next natp :rule-classes :type-prescription)
                      (equalp litp :rule-classes :type-prescription)
                      new-ipasir)
         :Verify-guards nil
         (b* ((next (lnfix next))
              (a (lit-fix (car a-inputs)))
              (b (lit-fix (car b-inputs)))
              ((mv bitequiv next) (mv (make-lit next 0) (+ 1 next)))
              ;; bitequiv is iff of a, b:
              ;; a & b -> bitequiv   =  ~a | ~b | bitequiv
              (ipasir (ipasir-add-ternary ipasir bitequiv (l- a) (l- b)))
              ;; ~a & ~b -> bitequiv = a | b | bitequiv
              (ipasir (ipasir-add-ternary ipasir bitequiv a b))
              ;; a & ~b -> ~bitequiv = ~a | b | ~bitequiv
              (ipasir (ipasir-add-ternary ipasir (l- bitequiv) (l- a) b))
              ;; ~a & b -> ~bitequiv = ~a | b | ~bitequiv
              (ipasir (ipasir-add-ternary ipasir (l- bitequiv) a (l- b)))

              ((when (mbe :logic (or (atom (cdr a-inputs))
                                     (atom (cdr b-inputs)))
                          :exec (atom (cdr a-inputs))))
               (mv next bitequiv ipasir))

              ((mv next rest-equiv ipasir)
               (make-equiv next (cdr a-inputs) (cdr b-inputs) ipasir))

              ((mv equiv next) (mv (make-lit next 0) (+ 1 next)))
              ;; equiv is and of bitequiv, rest-equiv
              ;; ~bitequiv -> ~equiv
              (ipasir (ipasir-add-binary ipasir bitequiv (l- equiv)))
              ;; ~rest-equiv -> ~equiv
              (ipasir (ipasir-add-binary ipasir rest-equiv (l- equiv)))
              ;; bitequiv & rest-equiv -> equiv
              (ipasir (ipasir-add-ternary ipasir (l- bitequiv) (l- rest-equiv) equiv)))

           (mv next equiv ipasir))
         
         ///
         (defret ipasir-make-equiv-status
           (equal (ipasir$a->status new-ipasir) :input))
         
         (defret ipasir-make-equiv-new-clause
           (not (ipasir$a->new-clause new-ipasir)))
         
         (defret ipasir-make-equiv-assumption
           (equal (ipasir$a->assumption new-ipasir)
                  (ipasir$a->assumption ipasir)))

         (verify-guards make-equiv
           :hints (("goal" :expand ((len a-inputs) (len b-inputs)
                                    (len (cdr a-inputs))
                                    (len (cdr b-inputs))))))))

(local (include-book "centaur/misc/numlist" :dir :system))

(local (defthm lit-listp-of-numlist
         (implies (and (posp next) (posp incr))
                  (lit-listp (acl2::numlist next incr n)))
         :hints(("Goal" :in-theory (enable acl2::numlist)))))

(local (defthm consp-by-len
         (implies (posp (len x))
                  (consp x))))

(local (define ipasir-lit-list-val (ipasir (lits lit-listp))
         :guard (eq (ipasir-get-status ipasir) :sat)
         (if (atom lits)
             nil
           (cons (ipasir-val ipasir (car lits))
                 (ipasir-lit-list-val ipasir (cdr lits))))))

(local (defmacro print-lit-list-val (x)
         `(cw "~x0: ~x1~%" ',x (ipasir-lit-list-val ipasir ,x))))
              

(local (define compare-adds ((nbits posp) (limit acl2::maybe-natp) state)
         (b* (((local-ipasir) (mv ans ipasir state))
              (nbits (acl2::lposfix nbits))
              (next 1)
              ((mv false next) (mv (make-lit next 0) (+ 1 next)))
              (ipasir (ipasir-add-unary ipasir (l- false)))
              ((mv a next)
               (mv (acl2::numlist (* 2 next) 2 nbits)
                   (+ nbits next)))
              ((mv b next)
               (mv (acl2::numlist (* 2 next) 2 nbits)
                   (+ nbits next)))
              ((mv c next)
               (mv (acl2::numlist (* 2 next) 2 nbits)
                   (+ nbits next)))
              ((mv d next)
               (mv (acl2::numlist (* 2 next) 2 nbits)
                   (+ nbits next)))
              ((mv next a+b ipasir) (make-adder next false a b ipasir))
              ((mv next c+d ipasir) (make-adder next false c d ipasir))
              ((mv next a+b+c+d ipasir) (make-adder next false a+b c+d ipasir))

              ((mv next a+c ipasir) (make-adder next false a c ipasir))
              ((mv next b+d ipasir) (make-adder next false b d ipasir))
              ((mv next a+c+b+d ipasir) (make-adder next false a+c b+d ipasir))

              ((mv ?next equiv ipasir) (make-equiv next a+b+c+d a+c+b+d ipasir))

              (ipasir (ipasir-assume ipasir (l- equiv)))

              (ipasir (ipasir-set-limit ipasir limit))
              ((mv status1 ipasir) (ipasir-solve ipasir))
              (- (and (eq status1 :sat)
                      (progn$ (print-lit-list-val a)
                              (print-lit-list-val b)
                              (print-lit-list-val a+b)
                              (print-lit-list-val c)
                              (print-lit-list-val d)
                              (print-lit-list-val c+d)
                              (print-lit-list-val a+c)
                              (print-lit-list-val b+d)
                              (print-lit-list-val a+b+c+d)
                              (print-lit-list-val a+c+b+d)
                              (cw "equiv: ~x0~%" (ipasir-val ipasir equiv)))))
              (ipasir (ipasir-assume ipasir equiv))
              ((mv status2 ipasir) (ipasir-solve ipasir))
              (- (and (eq status2 :sat)
                      (progn$ (print-lit-list-val a)
                              (print-lit-list-val b)
                              (print-lit-list-val a+b)
                              (print-lit-list-val c)
                              (print-lit-list-val d)
                              (print-lit-list-val c+d)
                              (print-lit-list-val a+c)
                              (print-lit-list-val b+d)
                              (print-lit-list-val a+b+c+d)
                              (print-lit-list-val a+c+b+d)
                              (cw "equiv: ~x0~%" (ipasir-val ipasir equiv))))))
           (mv (list status1 status2) ipasir state))))


(make-event
 (b* (((mv result state) (compare-adds 5 20 state))
      ((unless (equal result '(:unsat :sat)))
       (er soft 'compare-adds-assertion
           "Assertion failed -- result was ~x0~%" result)))
   (value '(value-triple :passed))))


(local (define duplicate-lits-test (state)
         (b* (((local-ipasir) (mv ans ipasir state))
              (ipasir (ipasir-add-4ary ipasir 2 2 2 2))
              (ipasir (ipasir-add-4ary ipasir 3 3 3 3))
              ((mv status ipasir) (ipasir-solve ipasir)))
           (mv status ipasir state))))

(make-event
 (b* (((mv result state) (duplicate-lits-test state))
      ((unless (equal result :unsat))
       (er soft 'duplicate-lits-test-assertion
           "Assertion failed -- result was ~x0~%" result)))
   (value '(value-triple :passed))))

(local (define contradictory-lits-test (state)
         (b* (((local-ipasir) (mv ans ipasir state))
              (ipasir (ipasir-add-4ary ipasir 2 3 2 3))
              ((mv status ipasir) (ipasir-solve ipasir)))
           (mv status ipasir state))))

(make-event
 (b* (((mv result state) (contradictory-lits-test state))
      ((unless (equal result :sat))
       (er soft 'contradictory-lits-test-assertion
           "Assertion failed -- result was ~x0~%" result)))
   (value '(value-triple :passed))))



