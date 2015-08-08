; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2013 Centaur Technology
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

; sexpr-purebool-p.lisp
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "sfaig")
;; (include-book "sexpr-to-faig")
;; (include-book "sexpr-vars-1pass")
;; (include-book "g-sexpr-eval") ;; BOZO for varmap stuff, split this out
(include-book "centaur/aig/faig-purebool-p" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/aig/aig-vars" :dir :system))
(local (include-book "sexpr-equivs"))
(local (include-book "sexpr-advanced"))

(local (in-theory (disable* 4v-sexpr-eval
                            4v-sexpr-alist-extract
                            4v-lookup
                            4v-sexpr-apply
                            faig-eval
                            aig-eval
                            num-varmap
                            4v-sexpr-to-faig
                            4v-sexpr-to-faig-plain
                            faig-const->4v
                            4v->faig-const
                            sig-al-to-svar-al
                            4v-alist->faig-const-alist
                            f-aig-defs
                            t-aig-defs
                            aig-vars
                            )))

(local (defthm len-of-4v-sexpr-eval-list
         (equal (len (4v-sexpr-eval-list x env))
                (len x))
         :hints(("Goal" :in-theory (enable 4v-sexpr-eval-list)))))

(local (defthm nth-of-4v-list->faig-const-list-equal
         (equal (nth n (4v-list->faig-const-list x))
                (and (< (nfix n) (len x))
                     (4v->faig-const (nth n x))))
         :hints(("Goal" :in-theory (enable 4v-list->faig-const-list)))))

(local (defthm nth-of-4v-sexpr-eval-list-equal
         (equal (nth n (4v-sexpr-eval-list x env))
                (and (< (nfix n) (len x))
                     (4v-sexpr-eval (nth n x) env)))
         :hints(("Goal" :in-theory (enable 4v-sexpr-eval-list)))))

(local (defthm nth-of-faig-const-list->4v-list-equal
         (equal (nth n (faig-const-list->4v-list x))
                (and (< (nfix n) (len x))
                     (faig-const->4v (nth n x))))
         :hints(("Goal" :in-theory (enable faig-const-list->4v-list)))))

(local (defthm nth-of-faig-eval-list-equal
         (equal (nth n (faig-eval-list x env))
                (and (< (nfix n) (len x))
                     (faig-eval (nth n x) env)))))



(defsection 4v-sexpr-purebool-p
  :parents (4v-sexprs)
  :short "Does a 4v-sexpr always evaluate to a purely Boolean value, i.e., is
it never X or Z?"

  :long "<p>It is sometimes useful to know whether a 4v-sexpr is always purely
Boolean valued; see @(see faig-purebool-p) for some directly analogous
discussion about @(see faig)s.</p>

<p>@(call 4v-sexpr-purebool-p) is a logically nice, but non-executable way to
express pure Boolean-ness.  See also @(see 4v-sexpr-purebool-check), which can
be executed, and uses a SAT solver to answer the question.</p>"

  (defun-sk 4v-sexpr-purebool-p (sexpr)
    (forall (env)
            (or (equal (4v-sexpr-eval sexpr env) (4vt))
                (equal (4v-sexpr-eval sexpr env) (4vf)))))

  (verify-guards 4v-sexpr-purebool-p)

  (local
   (defthmd backward-lemma
     (implies (not (4v-sexpr-purebool-p sexpr))
              (not (faig-purebool-p (sfaig sexpr))))
     ;; This is straightforward.  Since it's not sexpr purebool, we can get a
     ;; counterexample.  We then just need to map that counterexample over into
     ;; the FAIG world.
     :hints(("Goal"
             :in-theory (e/d (4v->faig-const)
                             (faig-eval-of-sfaig-make-faigenv))
             :use ((:instance faig-eval-of-sfaig-make-faigenv
                              (sexpr sexpr)
                              (env (4V-SEXPR-PUREBOOL-P-WITNESS SEXPR)))
                   (:instance faig-purebool-p-necc
                              (x (SFAIG SEXPR))
                              (env
                               (SFAIG-MAKE-FAIGENV
                                SEXPR
                                (4V-SEXPR-PUREBOOL-P-WITNESS SEXPR)))))))))

  (local
   (defthmd forward-lemma
     (implies (not (faig-purebool-p (sfaig sexpr)))
              (not (4v-sexpr-purebool-p sexpr)))
     ;; Proof.  The obvious thing to do is consider a witness.  Since the
     ;; corresponding FAIG isn't purely Boolean, let FAIG-ENV be an environment
     ;; that drives it to X or Z.  We'll then construct a corresponding
     ;; SEXPR-ENV, and conclude that it drives the SEXPR to X or Z.
     ;;
     ;; The crux of the proof is already done in sexpr-to-faig.lisp:
     ;;
     ;; (defthm faig-eval-4v-sexpr-to-faig-plain
     ;;   (let ((4v-env (faig-const-alist->4v-alist (faig-eval-alist onoff env))))
     ;;     (equal (faig-eval (4v-sexpr-to-faig-plain x onoff) env)
     ;;            (4v->faig-const (4v-sexpr-eval x 4v-env)))))
     ;;
     ;; Reusing this result is just kind of tricky.  We need to construct the ENV
     ;; above by using the witness for faig-purebool-p:
     :hints(("Goal"
             :in-theory (e/d (faig-const->4v)
                             (4v-sexpr-purebool-p-necc
                              4v-sexpr-purebool-p))
             :use ((:instance 4v-sexpr-purebool-p-necc
                              (sexpr sexpr)
                              (env
                               (b* ((faig     (sfaig sexpr))
                                    (faig-env (faig-purebool-p-witness faig)))
                                 (sfaig-recover-4venv sexpr faig-env)))))))))

  (defthmd 4v-sexpr-purebool-p-to-faig-purebool-p
    (equal (4v-sexpr-purebool-p sexpr)
           (faig-purebool-p (sfaig sexpr)))
    :hints(("Goal"
            :in-theory (disable 4v-sexpr-purebool-p
                                faig-purebool-p)
            :use ((:instance forward-lemma)
                  (:instance backward-lemma))))))


(define 4v-sexpr-purebool-check
  :parents (4v-sexpr-purebool-p)
  :short "An executable version of @(see 4v-sexpr-purebool-p) using SAT."
  ((sexpr "The 4v-sexpr to check.")
   &key
   ((config satlink::config-p) 'satlink::*default-config*))
  :returns
  (mv (fail booleanp :rule-classes :type-prescription
            "If true, calling the SAT solver failed and the other answers are
             meaningless.")
      (purebool booleanp :rule-classes :type-prescription
                "Does the sexpr always evaluate to purely Boolean?")
      (ctrex
       "NIL when the sexpr is purely Boolean.  Otherwise, an example
        environment (an alist suitable for @(see 4v-sexpr-eval)) for which
        @('sexpr') evaluates to X or Z."))

  :long "<p>Note: if you want to check whether several sexprs are all purely
Boolean valued, @(see 4v-sexpr-purebool-list-check) will typically be far more
efficient than calling @('4v-sexpr-purebool-check') repeatedly.</p>"

  (mbe :logic
       (b* ((faig (sfaig sexpr))
            ((mv fail purebool faig-env)
             (faig-purebool-check faig :config config))
            ((when fail)
             (mv fail nil nil))
            ((when purebool)
             (mv nil t nil))
            (4v-env (sfaig-recover-4venv sexpr faig-env)))
         (mv nil nil 4v-env))

       :exec
       ;; Slight optimization to avoid redundantly computing vars and onoff.
       (b* ((vars  (4v-sexpr-vars-1pass sexpr))
            (onoff (num-varmap vars 0))
            (faig  (4v-sexpr-to-faig sexpr onoff))
            ((mv fail purebool faig-env)
             (faig-purebool-check faig :config config))
            ((when fail)
             (mv fail nil nil))
            ((when purebool)
             (mv nil t nil))
            (4v-env (faig-const-alist->4v-alist
                     (faig-eval-alist onoff faig-env))))
         (mv nil nil 4v-env)))

  :guard-hints(("Goal" :in-theory (enable sfaig
                                          sfaig-recover-4venv)))

  ///
  (defthm 4v-sexpr-purebool-check-correct
    (b* (((mv fail purebool ?alist)
          (4v-sexpr-purebool-check sexpr :config config)))
      (implies (not fail)
               (equal purebool
                      (4v-sexpr-purebool-p sexpr))))
    :hints(("Goal"
            :in-theory (e/d (sfaig)
                            (4v-sexpr-purebool-p
                             faig-purebool-p))
            :use ((:instance 4v-sexpr-purebool-p-to-faig-purebool-p)))))

  (defthm 4v-sexpr-purebool-check-counterexample-correct
    (b* (((mv fail ?purebool alist)
          (4v-sexpr-purebool-check sexpr :config config)))
      (implies (and (not fail)
                    (not (4v-sexpr-purebool-p sexpr)))
               (and (not (equal (4v-sexpr-eval sexpr alist) (4vt)))
                    (not (equal (4v-sexpr-eval sexpr alist) (4vf))))))
    :hints(("Goal"
            :in-theory (e/d (faig-const->4v)
                            (4v-sexpr-purebool-p faig-purebool-p))
            :use ((:instance 4v-sexpr-purebool-p-to-faig-purebool-p))))))


(std::deflist 4v-sexpr-purebool-list-p (x)
  (4v-sexpr-purebool-p x)
  :guard t
  :parents (4v-sexpr-purebool-p)
  :short "Do a list of @(see 4v-sexprs) always evaluate to purely Boolean
values, i.e., are they never X or Z?"

  :long "<p>This is a logically nice, but non-executable way to express pure
Boolean-ness.  See also @(see 4v-sexpr-purebool-list-check), which can be
executed; it uses a SAT solver to answer the question.</p>")


(defsection 4v-sexpr-purebool-list-p-to-faig-purebool-list-p
  :parents (4v-sexpr-purebool-p)
  :short "Main theorem showing that @(see 4v-sexpr-purebool-list-p) is
equivalent to @(see faig-purebool-list-p)."

  :long "<p>This is the main result that lets us develop an efficient,
SAT-based way to check, all at once, the Boolean-ness of a list of @(see
4v-sexprs).</p>"

  ;; Backward Direction: If it's FAIG purebool, then it's SEXPR purebool.
  ;;
  ;; Proof: suppose not.  Then there's some SEXPR that isn't purebool, and we can
  ;; show that the corresponding FAIG must also be non-purebool, which is a
  ;; contradiction.

  (local
   (define sexpr-wit (x)
     (b* (((when (atom x))
           (mv 0 nil))
          ((when (4v-sexpr-purebool-p (car x)))
           (b* (((mv idx env)
                 (sexpr-wit (cdr x))))
             (mv (+ 1 idx) env))))
       (mv 0 (4v-sexpr-purebool-p-witness (car x))))
     ///
     (defthm natp-of-sexpr-wit-index
       (natp (mv-nth 0 (sexpr-wit x)))
       :rule-classes :type-prescription)

     (defthm sexpr-wit-index-bound
       (<= (mv-nth 0 (sexpr-wit x))
           (len x))
       :rule-classes ((:rewrite) (:linear)))

     (defthm sexpr-wit-index-bound2
       (equal (< (mv-nth 0 (sexpr-wit x)) (len x))
              (not (equal (mv-nth 0 (sexpr-wit x))
                          (len x)))))

     (defthmd sexpr-wit-misses
       (b* (((mv idx ?env) (sexpr-wit sexprs)))
         (equal (equal idx (len sexprs))
                (4v-sexpr-purebool-list-p sexprs)))
       :hints(("Goal" :in-theory (enable 4v-sexpr-purebool-list-p))))

     (defthm sexpr-wit-hits
       (b* (((mv idx env) (sexpr-wit sexprs))
            (sexpr (nth idx sexprs)))
         (implies (not (equal idx (len sexprs)))
                  (and (not (equal (4v-sexpr-eval sexpr env) (4vt)))
                       (not (equal (4v-sexpr-eval sexpr env) (4vf)))))))))

  (local (defthm l0
           (implies (and (equal (faig-eval-list faigs env) rhses)
                         (< (nfix n) (len faigs)))
                    (equal (faig-eval (nth n faigs) env)
                           (nth n rhses)))))

  (local (defthm l1
           (b* (((mv idx ?env) (sexpr-wit sexprs)))
             (implies (not (equal idx (len sexprs))) ;; i.e., found a hit
                      (not (faig-purebool-p (nth idx (sfaiglist sexprs))))))
           :hints
           (("Goal"
             :in-theory (e/d (4v->faig-const)
                             (sexpr-wit-hits
                              faig-purebool-p
                              faig-purebool-p-necc
                              faig-eval-list-of-sfaiglist-make-faigenv
                              ))
             :use ((:instance sexpr-wit-hits)
                   (:instance
                    faig-purebool-p-necc
                    (x   (b* (((mv idx ?sexpr-env) (sexpr-wit sexprs)))
                           (nth idx (sfaiglist sexprs))))
                    (env (b* (((mv ?idx sexpr-env) (sexpr-wit sexprs))
                              (faig-env (sfaiglist-make-faigenv sexprs sexpr-env)))
                           faig-env)))
                   (:instance faig-eval-list-of-sfaiglist-make-faigenv
                              (sexprs sexprs)
                              (env    (mv-nth 1 (sexpr-wit sexprs))))
                   )))))

  (local (defthm l2
           (implies (and (not (faig-purebool-p (nth n x)))
                         (< (nfix n) (len x)))
                    (not (faig-purebool-list-p x)))
           :hints(("Goal" :in-theory (enable faig-purebool-list-p)))))

  (local
   (defthmd backward-lemma
     (implies (not (4v-sexpr-purebool-list-p sexprs))
              (not (faig-purebool-list-p (sfaiglist sexprs))))
     :hints(("Goal"
             :in-theory (disable faig-purebool-p
                                 sexpr-wit-hits
                                 sexpr-wit-misses
                                 l2
                                 FAIG-PUREBOOL-LIST-P-WHEN-SUBSETP-EQUAL
                                 FAIG-PUREBOOL-P-OF-NTH-WHEN-FAIG-PUREBOOL-LIST-P)
             :use (
                   (:instance sexpr-wit-hits)
                   (:instance sexpr-wit-misses)
                   (:instance l2
                              (n (mv-nth 0 (sexpr-wit sexprs)))
                              (x (sfaiglist sexprs))))))))


  ;; Forward direction.  If it's SEXPR purebool, then it's FAIG purebool.
  ;;
  ;; Proof: suppose not.  Then there's some FAIG that isn't purebool, and we can
  ;; show that the corresponding SEXPR must also be non-purebool, which is a
  ;; contradiction.

  (local
   (define faig-wit (x)
     (b* (((when (atom x))
           (mv 0 nil))
          ((when (faig-purebool-p (car x)))
           (b* (((mv idx env)
                 (faig-wit (cdr x))))
             (mv (+ 1 idx) env))))
       (mv 0 (faig-purebool-p-witness (car x))))
     ///
     (defthm natp-of-faig-wit-index
       (natp (mv-nth 0 (faig-wit x)))
       :rule-classes :type-prescription)

     (defthm faig-wit-index-bound
       (<= (mv-nth 0 (faig-wit x))
           (len x))
       :rule-classes ((:rewrite) (:linear)))

     (defthm faig-wit-index-bound2
       (equal (< (mv-nth 0 (faig-wit x)) (len x))
              (not (equal (mv-nth 0 (faig-wit x))
                          (len x)))))

     (defthmd faig-wit-misses
       (b* (((mv idx ?env) (faig-wit faigs)))
         (equal (equal idx (len faigs))
                (faig-purebool-list-p faigs)))
       :hints(("Goal" :in-theory (enable faig-purebool-list-p))))

     (defthm faig-wit-hits
       (b* (((mv idx env) (faig-wit faigs))
            (faig (nth idx faigs)))
         (implies (not (equal idx (len faigs)))
                  (and (not (equal (faig-eval faig env) (faig-t)))
                       (not (equal (faig-eval faig env) (faig-f)))))))))

  (local (defthm f0
           (implies (and (equal (4v-sexpr-eval-list sexprs env) rhses)
                         (< (nfix n) (len sexprs)))
                    (equal (4v-sexpr-eval (nth n sexprs) env)
                           (nth n rhses)))))

  (local (defthm f1
           (b* ((faigs (sfaiglist sexprs))
                ((mv idx ?env) (faig-wit faigs)))
             (implies (not (equal idx (len sexprs))) ;; i.e., found a hit
                      (not (4v-sexpr-purebool-p (nth idx sexprs)))))
           :hints
           (("Goal"
             :in-theory (e/d (faig-const->4v)
                             (4v-sexpr-eval-list-of-sfaiglist-recover-4venv
                              faig-wit-hits
                              4v-sexpr-purebool-p-necc
                              4v-sexpr-purebool-p
                              ))
             :use ((:instance faig-wit-hits
                              (faigs (sfaiglist sexprs)))
                   (:instance 4v-sexpr-purebool-p-necc
                              (sexpr
                               (b* ((faigs (sfaiglist sexprs))
                                    ((mv idx ?faig-env) (faig-wit faigs)))
                                 (nth idx sexprs)))
                              (env
                               (b* ((faigs (sfaiglist sexprs))
                                    ((mv ?idx faig-env) (faig-wit faigs)))
                                 (sfaiglist-recover-4venv sexprs faig-env))))
                   (:instance 4v-sexpr-eval-list-of-sfaiglist-recover-4venv
                              (sexprs sexprs)
                              (faig-env
                               (b* ((faigs (sfaiglist sexprs))
                                    ((mv ?idx faig-env) (faig-wit faigs)))
                                 faig-env)))
                   )))))

  (local (defthm f2
           (implies (and (not (4v-sexpr-purebool-p (nth n x)))
                         (< (nfix n) (len x)))
                    (not (4v-sexpr-purebool-list-p x)))
           :hints(("Goal" :in-theory (enable 4v-sexpr-purebool-list-p)))))

  (local
   (defthmd forward-lemma
     (implies (not (faig-purebool-list-p (sfaiglist sexprs)))
              (not (4v-sexpr-purebool-list-p sexprs)))
     :hints(("Goal"
             :in-theory (disable faig-purebool-p
                                 faig-wit-hits
                                 faig-wit-misses
                                 f2
                                 4v-sexpr-purebool-list-p-when-subsetp-equal
                                 4v-sexpr-purebool-p-of-nth-when-4v-sexpr-purebool-liST-P
                                 )
             :use ((:instance faig-wit-hits
                              (faigs (sfaiglist sexprs)))
                   (:instance faig-wit-misses
                              (faigs (sfaiglist sexprs)))
                   (:instance f2
                              (n (mv-nth 0 (faig-wit (sfaiglist sexprs))))
                              (x sexprs)))))))

  (defthmd 4v-sexpr-purebool-list-p-to-faig-purebool-list-p
    (equal (4v-sexpr-purebool-list-p sexprs)
           (faig-purebool-list-p (sfaiglist sexprs)))
    :hints(("Goal"
            :use ((:instance forward-lemma)
                  (:instance backward-lemma))))))


(define 4v-sexpr-purebool-list-check
  :parents (4v-sexpr-purebool-p)
  :short "An executable version of @(see 4v-sexpr-purebool-list-p) using SAT."
  ((x "The sexpr list to check.")
   &key
   ((config satlink::config-p) 'satlink::*default-config*))
  :returns (mv (fail booleanp
                     :rule-classes :type-prescription
                     "If true, calling the SAT solver failed and the other answers
                      are meaningless.")

               (purebool booleanp
                         :rule-classes :type-prescription
                         "Do these sexprs always evaluate to purely Boolean?")

               (alist "When these sexprs are not purely Boolean: an example
                       environment for @(see 4v-sexpr-eval-list) that drives
                       some SEXPR to X or Z."))

  (faig-purebool-list-check (sfaiglist x) :config config)

  ///
  (defthm 4v-sexpr-purebool-list-check-correct
    (b* (((mv fail purebool ?alist)
          (4v-sexpr-purebool-list-check x :config config)))
      (implies (not fail)
               (equal purebool
                      (4v-sexpr-purebool-list-p x))))
    :hints(("Goal"
            :in-theory (enable
                        4v-sexpr-purebool-list-p-to-faig-purebool-list-p))))

  ;; BOZO maybe some day prove something about the counterexample produced
  )

