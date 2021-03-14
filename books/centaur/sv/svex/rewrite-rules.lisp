; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "rewrite-base")
(include-book "seval")
(include-book "4vmask")
(include-book "centaur/bitops/trailing-0-count" :dir :system)
(include-book "rsh-concat")
(local (include-book "std/alists/alist-defuns" :dir :system))
(local (include-book "lattice"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "clause-processors/find-matching" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::ruletable-delete-tags! acl2::listp-rules (:duplicated-members)))

(local (defthm logbitp-of-logeqv
         (equal (logbitp n (logeqv a b))
                (iff (logbitp n a)
                     (logbitp n b)))
         :hints(("Goal" :in-theory (enable logeqv)))))

(local (defthm logior-of-logapp
         (equal (logior (logapp n x1 y1)
                        (logapp n x2 y2))
                (logapp n (logior x1 x2) (logior y1 y2)))
         :hints ((bitops::logbitp-reasoning))))

(local (defthm logand-of-logapp
         (equal (logand (logapp n x1 y1)
                        (logapp n x2 y2))
                (logapp n (logand x1 x2) (logand y1 y2)))
         :hints ((bitops::logbitp-reasoning))))

(local (defthm logapp-equal-neg-1
         (iff (equal (logapp n x y) -1)
              (and (equal (ifix y) -1)
                   (or (zp n)
                       (equal (logext n x) -1))))
         :hints ((bitops::logbitp-reasoning :prune-examples nil))))

(local (defthm logbitp-when-not-integerp
         (implies (not (integerp y))
                  (not (logbitp n y)))
         :hints(("Goal" :expand ((:with logbitp (logbitp n y)))))))

(local (defthm logand-equal-minus-1
         (equal (equal (logand x y) -1)
                (and (equal x -1)
                     (equal y -1)))
         :hints ((bitops::logbitp-reasoning
                  :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                                  acl2::b-and))))))

(local (defthm svexlist-eval-of-update-nth
         (equal (svexlist-eval (update-nth n v x) env)
                (4veclist-fix (update-nth n
                                          (svex-eval v env)
                                          (svexlist-eval x env))))
         :hints(("Goal" :in-theory (enable svexlist-eval)))))

(local (defthm logand-equal-logior
         (equal (equal (logand x y) (logior x y))
                (equal (ifix x) (ifix y)))
         :hints ((bitops::logbitp-reasoning
                  :add-hints (:in-theory (enable* acl2::logbitp-case-splits
                                                  acl2::bool->bit))))))

(local (defthm 2vec-of-4vec-lower
         (implies (2vec-p x)
                  (equal (2vec (4vec->lower x))
                         (4vec-fix x)))
         :hints(("Goal" :in-theory (enable 2vec)))))

(local (defthm svex-xeval-of-svex-call
         (equal (svex-xeval (svex-call fn args))
                (svex-apply
                 (case (fnsym-fix fn)
                   (=== '==)
                   (==? 'safer-==?)
                   (bit?! 'bit?)
                   (?! '?*)
                   (otherwise (fnsym-fix fn)))
                 (svexlist-xeval args)))
         :hints(("Goal" :expand ((svex-xeval (svex-call fn args)))))))

(local (defthm svex-xeval-of-svex-quote
         (equal (svex-xeval (svex-quote val))
                (4vec-fix val))
         :hints(("Goal" :in-theory (enable svex-xeval)))))


(local (defthm 4veclist-nth-safe-of-svexlist-xeval
         (equal (4veclist-nth-safe n (svexlist-xeval x))
                (svex-xeval (nth n x)))
         :hints(("Goal" :in-theory (enable svexlist-xeval 4veclist-nth-safe)))))

(local (encapsulate nil
         (local (defun ind (m x n1 n2)
                  (if (zp m)
                      (list x n1 n2)
                    (ind (1- m) (logcdr x) (1- (ifix n1)) (1- (ifix n2))))))

         (local (defthm ifix-minus
                  (equal (ifix (- x))
                         (- (ifix x)))
                  :hints(("Goal" :in-theory (enable ifix)))))

         (defthm logapp-of-shift-sums
           (implies (equal (ifix n2) (+ (nfix m) (ifix n1)))
                    (equal (logapp m (ash x (- n1)) (ash x (- n2)))
                           (ash x (- n1))))
           :hints ((acl2::equal-by-logbitp-hammer)))))

;; (def-svex-rewrite unsigned-not-less-than-0
;;   :lhs (< (concat n x 0) 0)
;;   :rhs (xdet (bitxor (concat n x 0) (concat n x 0)))
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-< 4vec-concat
;;                                     4vec-bitxor 4vec-xdet))))




(defalist svex-key-alist :key-type svex)

;; We use a somewhat odd convention for a multiref alist.  We treat it as a set
;; (that is, the value doesn't matter), if the alist is just T, then we
;; consider all svexes bound in it.  This is useful for barebones, easily
;; memoizable rewriting without any expensive linear passes to get masks or
;; multiref sets.
(define svex-get-multiref ((key svex-p)
                              (alist svex-key-alist-p))
  (b* ((alist (svex-key-alist-fix alist)))
    (if (eq alist t)
        t
      (and (hons-get (svex-fix key) alist) t))))

(define svex-set-multiref ((key svex-p)
                           (alist svex-key-alist-p))
  :returns (new-alist svex-key-alist-p)
  (b* ((alist (svex-key-alist-fix alist)))
    (if (svex-get-multiref key alist)
        alist
      (hons-acons (svex-fix key) t alist))))


(defxdoc svex-rewrite-rules
  :parents (rewriting)
  :short "Rules used by the svex @(see rewriting) functions.")

(local
 (progn


   (defun svex-gen-alist-from-calls (x)
     (b* (((when (atom x)) nil)
          (term (car x))
          ((mv ok subst) (acl2::simple-one-way-unify
                          '(svex-lookup key al) term nil))
          (key-term (cdr (assoc 'key subst)))
          ((unless (and ok
                        (quotep key-term)
                        (symbolp (acl2::unquote key-term))))
           (svex-gen-alist-from-calls (cdr x))))
       (cons (cons (car x) (acl2::unquote key-term))
             (svex-gen-alist-from-calls (cdr x)))))

   (defun svex-generalize-lookups-fn (clause)
     (b* ((calls (mergesort (acl2::find-matches-list
                             '(svex-lookup key al)
                             clause nil)))
          (alist (svex-gen-alist-from-calls calls)))
       `(:clause-processor (acl2::generalize-with-alist-cp clause ',alist))))

   (defmacro svex-generalize-lookups ()
     '(and stable-under-simplificationp
           (svex-generalize-lookups-fn clause)))))


(local (in-theory (disable set::double-containment
                           acl2::cancel_times-equal-correct
                           acl2::cancel_plus-equal-correct
                           ; acl2::logior-natp-type
                           bitops::logxor-natp-type-2
                           bitops::logior-<-0-linear-2
                           bitops::lognot-negp)))

(defun svex-rewrite-lookup-vars (vars)
  (if (atom vars)
      nil
    (cons `(,(car vars) (svex-lookup ',(car vars) subst))
          (svex-rewrite-lookup-vars (cdr vars)))))

(defun svex-rewrite-find-next-bind-form (checks)
  (b* (((when (or (atom checks)
                  (and (consp (car checks))
                       (or (eq (caar checks) 'bind)
                           (eq (caar checks) 'let)))))
        (mv nil checks))
       ((mv pre post) (svex-rewrite-find-next-bind-form (cdr checks))))
    (mv (cons (car checks) pre) post)))

(defun svex-rewrite-checks-and-bindings (checks)
  (declare (xargs :mode :program))
  (b* (((mv checks rest) (svex-rewrite-find-next-bind-form checks))
       (pre (and checks
                 `(((unless ,(if (cdr checks) `(and . ,checks) (car checks)))
                    (mv nil nil nil)))))
       ((when (atom rest)) pre)
       ((list bindsym var term) (car rest)))
    (append pre
            `((,var ,term)
              . ,(and (eq bindsym 'bind)
                      `((subst (svex-acons ',var ,var subst)))))
            (svex-rewrite-checks-and-bindings (cdr rest)))))




(defun def-svex-rewrite-fn (name lhs checks rhs hints)
  (declare (xargs :mode :program))
  (b* ((fnname (intern-in-package-of-symbol
                (concatenate 'string "SVEX-REWRITE-" (symbol-name name))
                name))
       (correct (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name fnname) "-CORRECT")
                 name))
       (subst-vars-in-args
        (intern-in-package-of-symbol
         (concatenate 'string (symbol-name fnname) "-NO-NEW-VARS")
         name))
       (rhs-vars-in-subst
        (intern-in-package-of-symbol
         (concatenate 'string (symbol-name fnname) "-RHS-VARS-BOUND")
         name)))
    `(define ,fnname ((mask 4vmask-p)
                      (args svexlist-p)
                      (multirefp)
                      (multiref-table svex-key-alist-p))
       :ignore-ok t
       :irrelevant-formals-ok t
       :returns (mv (successp booleanp)
                    (pat (iff (svex-p pat) successp))
                    (subst svex-alist-p))
       (b* ((mask (mbe :logic (4vmask-fix mask) :exec mask))
            (args (svexlist-fix args))
            (multiref-table (svex-key-alist-fix multiref-table))
            ((mv ok subst) (svexlist-unify ',(cdr lhs) args nil))
            ((unless ok) (mv nil nil nil))
            ,@(svex-rewrite-lookup-vars (svex-vars lhs))
            ,@(svex-rewrite-checks-and-bindings checks))
         (mv t ',rhs subst))
       ///
       (defthm ,correct
         (b* (((mv ok pat subst) (,fnname mask args multirefp multiref-table)))
           (implies ok
                    (equal (4vec-mask mask (svex-eval pat (svex-alist-eval subst env)))
                           (4vec-mask mask (svex-apply ',(car lhs) (svexlist-eval args env))))))
         :hints ,(or hints
                     '(("goal" :in-theory (enable svex-apply)))))

       (deffixequiv ,fnname)

       (defthm ,subst-vars-in-args
         (b* (((mv ?ok ?pat subst) (,fnname mask args multirefp multiref-table)))
           (implies (not (member v (svexlist-vars args)))
                    (not (member v (svex-alist-vars subst)))))
         :hints ((and stable-under-simplificationp
                      '(:in-theory (enable svex-vars)))))

       (defthm ,rhs-vars-in-subst
         (b* (((mv ok pat subst) (,fnname mask args multirefp multiref-table)))
           (implies ok
                    (subsetp (svex-vars pat) (svex-alist-keys subst)))))

       (table svex-rewrite ',(car lhs)
              (cons ',fnname (cdr (assoc ',(car lhs) (table-alist 'svex-rewrite world))))))))

(defmacro def-svex-rewrite (name &key lhs checks rhs hints)
  (def-svex-rewrite-fn name lhs checks rhs hints))






(define 4veclist-update-nth ((n natp) (v 4vec-p) (x 4veclist-p))
  :prepwork ((local (defthm 4veclist-fix-of-update-nth-nil
                      (equal (4veclist-fix (update-nth n v nil))
                             (append (replicate (nfix n) (4vec-x))
                                     (list (4vec-fix v))))
                      :hints(("Goal" :in-theory (e/d (4veclist-fix
                                                      update-nth
                                                      replicate)
                                                     (acl2::equal-of-append-repeat))))))
             (local (defthm 4veclist-fix-of-update-nth
                      (equal (4veclist-fix (update-nth n v x))
                             (if (<= (nfix n) (len x))
                                 (update-nth (nfix n) (4vec-fix v) (4veclist-fix x))
                               (append (4veclist-fix x)
                                       (replicate (- (nfix n) (len x)) (4vec-x))
                                       (list (4vec-fix v)))))
                      :hints(("Goal" :in-theory (enable 4veclist-fix
                                                        replicate))))))
  (mbe :logic (4veclist-fix (update-nth n v x))
       :exec (if (<= n (len x))
                 (update-nth n v x)
               (append x (replicate (- n (len x)) (4vec-x)) (list v)))))


;; (defthm 4veclist-nth-safe-of-cons-match
;;   (implies (and (syntaxp (quotep n))
;;                 (equal x (cons a b)))
;;            (equal (4veclist-nth-safe n x)
;;                   (if (zp n)
;;                       (svobj-fix a)
;;                     (4veclist-nth-safe (1- n) b))))
;;   :hints(("Goal" :in-theory (enable 4veclist-nth-safe))))



(defthm 4veclist-nth-safe-of-svexlist-eval
  (equal (4veclist-nth-safe n (svexlist-eval x env))
         (svex-eval (nth n x) env))
  :hints(("Goal" :in-theory (enable 4veclist-nth-safe svexlist-eval))))

(defthm svex-alist-eval-of-svex-acons
  (equal (svex-alist-eval (svex-acons k v al) env)
         (svex-env-acons k (svex-eval v env) (svex-alist-eval al env)))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-acons svex-env-acons))))


(defthm 4veclist-update-nth-same
  (equal (4veclist-update-nth n v (4veclist-update-nth n w x))
         (4veclist-update-nth n v x))
  :hints(("Goal" :in-theory (enable 4veclist-update-nth))))

(defthm member-svex-vars-nth
  (implies (not (member v (svexlist-vars x)))
           (not (member v (svex-vars (nth n x)))))
  :hints(("Goal" :in-theory (enable svexlist-vars))))

(defthm member-svex-vars-of-args
  (implies (and (equal (svex-kind x) :call)
                (not (member v (svex-vars x))))
           (not (member v (svexlist-vars (svex-call->args x)))))
  :hints(("Goal" :in-theory (enable svex-call->args)
          :expand ((svex-vars x)))))

(defthm member-svex-vars-of-svex-lookup
  (implies (not (member v (svex-alist-vars a)))
           (not (member v (svex-vars (svex-lookup k a))))))

(defthm svex-vars-of-svex-call
  (equal (svex-vars (svex-call fn args))
         (svexlist-vars args))
  :hints(("Goal" :expand ((svex-vars (svex-call fn args))))))

(defthm member-svexlist-vars-of-update-nth
  (implies (and (not (member v (svex-vars val)))
                (not (member v (svexlist-vars x))))
           (not (member v (svexlist-vars (update-nth n val x)))))
  :hints(("Goal" :in-theory (enable svexlist-vars))))



(def-svex-rewrite id
  :lhs (id x)
  :rhs x)



(define 3valued-syntaxp ((x (or (svex-p x) (not x))))
  :measure (svex-count x)
  :prepwork ((local (in-theory (e/d* ()
                                     (bitops::LOGAND->=-0-LINEAR-2
                                      bitops::UPPER-BOUND-OF-LOGAND
                                      bitops::LOGAND-NATP-TYPE-2
                                      bitops::LOGAND-NATP-TYPE-1
                                      bitops::LOGNOT-NEGP
                                      bitops::LOGIOR-NATP-TYPE
                                      bitops::LOGNOT-NATP
                                      double-containment
                                      default-car
                                      default-cdr
                                      (:t natp)
                                      (:t negp))))))
  (or (not x)
      (svex-case x
        :quote (3vec-p x.val)
        :var nil
        :call
        (case x.fn
          ((unfloat
            bitnot
            onp
            offp
            bitand
            bitor
            bitxor
            uand
            uor
            uxor
            +
            b-
            u-
            xdet
            countones
            onehot
            onehot0
            *
            <
            clog2
            pow
            ==
            ==?
            safer-==?
            ==??
            ===) t)
          (id (3valued-syntaxp (first x.args)))
          ((res
            resand
            resor
            override)
           (or (3valued-syntaxp (first x.args))
               (3valued-syntaxp (second x.args))))
          ((zerox
            signx
            bitsel
            rsh
            lsh)
           (3valued-syntaxp (second x.args)))
          ((concat ? ?* ?! bit? bit?!)
           (and (3valued-syntaxp (second x.args))
                (3valued-syntaxp (third x.args))))
          ((partsel)
           (3valued-syntaxp (third x.args)))
          ((partinst)
           (and (3valued-syntaxp (third x.args))
                (3valued-syntaxp (fourth x.args))))
          ((blkrev)
           (3valued-syntaxp (third x.args)))
          (otherwise t))))
  ///

  (memoize '3valued-syntaxp
           :condition '(and x
                            (eq (svex-kind x) :call)
                            (member (svex-call->fn x)
                                    '(res resand resor concat ? partinst))))

  (defthm 3vec-p-of-4vec-res
    (implies (or (3vec-p x)
                 (3vec-p y))
             (3vec-p (4vec-res x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-res))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-resand
    (implies (or (3vec-p x)
                 (3vec-p y))
             (3vec-p (4vec-resand x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-resand))
            (bitops::logbitp-reasoning)
            (and stable-under-simplificationp
                 '(:bdd (:vars nil)))))

  (defthm 3vec-p-of-4vec-resor
    (implies (or (3vec-p x)
                 (3vec-p y))
             (3vec-p (4vec-resor x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-resor))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-override
    (implies (or (3vec-p x)
                 (3vec-p y))
             (3vec-p (4vec-override x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-override))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-signx
    (implies (3vec-p y)
             (3vec-p (4vec-sign-ext x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-sign-ext))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-onset
    (3vec-p (4vec-onset x))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-onset))
           (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-offset
    (3vec-p (4vec-offset x))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-offset))
           (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-zerox
    (implies (3vec-p y)
             (3vec-p (4vec-zero-ext x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-zero-ext))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-bitsel
    (implies (3vec-p y)
             (3vec-p (4vec-bit-extract x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-bit-extract 4vec-bit-index))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-rsh
    (implies (3vec-p y)
             (3vec-p (4vec-rsh x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-rsh 4vec-shift-core))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-lsh
    (implies (3vec-p y)
             (3vec-p (4vec-lsh x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-lsh 4vec-shift-core))
            (bitops::logbitp-reasoning)))


  (defthm 3vec-p-of-4vec-?
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p (4vec-? c x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-? 3vec-? 3vec-fix))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-?*
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p (4vec-?* c x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-?* 3vec-?* 3vec-fix))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-?!
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p (4vec-?! c x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-?!))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-bit?
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p (4vec-bit? c x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-bit? 3vec-bit? 3vec-fix))
            (bitops::logbitp-reasoning)
            (and stable-under-simplificationp
                 '(:bdd (:vars nil)))))

  (defthm 3vec-p-of-4vec-bit?!
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p (4vec-bit?! c x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-bit?! 3vec-fix))
            (bitops::logbitp-reasoning)
            (and stable-under-simplificationp
                 '(:bdd (:vars nil)))))

  (defthm 3vec-p-of-4vec-concat
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p (4vec-concat n x y)))
    :hints (("goal" :in-theory (enable 3vec-p 4vec-concat))
            (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-uminus
    (3vec-p (4vec-uminus x))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-uminus))))

  (defthm 3vec-p-of-4vec-xdet
    (3vec-p (4vec-xdet x))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-xdet))))

  (defthm 3vec-p-of-4vec-countones
    (3vec-p (4vec-countones x))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-countones))))

  (defthm 3vec-p-of-4vec-onehot
    (3vec-p (4vec-onehot x))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-onehot))))

  (defthm 3vec-p-of-4vec-onehot0
    (3vec-p (4vec-onehot0 x))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-onehot0))))

  (defthm 3vec-p-of-4vec-minus
    (3vec-p (4vec-minus x y))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-minus))))

  (defthm 3vec-p-of-4vec-plus
    (3vec-p (4vec-plus x y))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-plus))))

  (defthm 3vec-p-of-4vec-times
    (3vec-p (4vec-times x y))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-times))))

  (defthm 3vec-p-of-4vec-quotient
    (3vec-p (4vec-quotient x y))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-quotient))))

  (defthm 3vec-p-of-4vec-remainder
    (3vec-p (4vec-remainder x y))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-remainder))))

  (defthm 3vec-p-of-3vec-==
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p (3vec-== x y)))
    :hints(("Goal" :in-theory (enable 3vec-==))))

  (defthm 3vec-p-of-2vec
    (3vec-p (2vec x))
    :hints(("Goal" :in-theory (enable 3vec-p))))

  (defthm 3vec-p-of-4vec-wildeq
    (3vec-p (4vec-wildeq x y))
  :hints(("Goal" :in-theory (enable 4vec-wildeq))))

  (defthm 3vec-p-of-4vec-wildeq-safe
    (3vec-p (4vec-wildeq-safe x y))
  :hints(("Goal" :in-theory (enable 4vec-wildeq-safe))))

  (defthm 3vec-p-of-4vec-symwildeq
    (3vec-p (4vec-symwildeq x y))
  :hints(("Goal" :in-theory (enable 4vec-symwildeq))))

  (defthm 3vec-p-of-4vec-==
    (3vec-p (4vec-== x y))
    :hints(("Goal" :in-theory (enable 4vec-==))))

  (defthm 3vec-p-of-4vec-===
    (3vec-p (4vec-=== x y))
    :hints(("Goal" :in-theory (enable 4vec-===))))

  (defthm 3vec-p-of-4vec-<
    (3vec-p (4vec-< x y))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-<))))

  (defthm 3vec-p-of-4vec-rev-blocks
    (implies (3vec-p x)
             (3vec-p (4vec-rev-blocks nbits bsz x)))
    :hints(("Goal" :in-theory (enable 4vec-rev-blocks 3vec-p))
           (bitops::logbitp-reasoning)))

  (defthm 3vec-p-of-4vec-clog2
    (3vec-p (4vec-clog2 x))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-clog2))))

  (defthm 3vec-p-of-4vec-pow
    (3vec-p (4vec-pow x y))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-pow))))

  (defthm 3vec-p-of-4vec-fix
    (equal (3vec-p (4vec-fix x)) (3vec-p x))
    :hints(("Goal" :in-theory (enable 3vec-p))))

  (defthm 3vec-p-of-4vec-part-select
    (implies (3vec-p in)
             (3vec-p (4vec-part-select lsb width in)))
    :hints(("Goal" :in-theory (enable 4vec-part-select))))

  (defthm 3vec-p-of-4vec-part-install
    (implies (and (3vec-p in)
                  (3vec-p val))
             (3vec-p (4vec-part-install lsb width in val)))
    :hints(("Goal" :in-theory (enable 4vec-part-install))))



  (defthm 3vec-p-of-eval-when-3valued-syntaxp
    (implies (3valued-syntaxp x)
             (3vec-p (svex-eval x env)))
    :hints (("Goal" :expand ((svex-eval x env)
                             (3valued-syntaxp x)
                             (:free (x) (svex-eval (list 'quote x) env)))
             :induct (3valued-syntaxp x)
             :in-theory (e/d (svex-apply svexlist-eval 4veclist-nth-safe)
                             ((:d 3valued-syntaxp))))))

  (deffixequiv 3valued-syntaxp :args ((x svex))))



(def-svex-rewrite unfloat-of-float-free
  :lhs (unfloat x)
  :checks ((3valued-syntaxp x))
  :rhs x)


(define 2vecx-syntaxp ((x (or (svex-p x) (not x))))
; Removed after v7-2 by Matt K. since the definition is non-recursive:
; :measure (svex-count x)
  :prepwork ((local (in-theory (e/d* ()
                                     (bitops::LOGAND->=-0-LINEAR-2
                                      bitops::UPPER-BOUND-OF-LOGAND
                                      bitops::LOGAND-NATP-TYPE-2
                                      bitops::LOGAND-NATP-TYPE-1
                                      bitops::LOGNOT-NEGP
                                      bitops::LOGIOR-NATP-TYPE
                                      bitops::LOGNOT-NATP
                                      double-containment
                                      default-car
                                      default-cdr
                                      (:t natp)
                                      (:t negp))))))
  (or (not x)
      (svex-case x
        :quote (2vecx-p x.val)
        :var nil
        :call
        (case x.fn
          ((+
            b-
            u-
            xdet
            countones
            onehot
            onehot0
            *
            <
            clog2
            pow
            /
            %
            uand
            uor
            uxor
            ==
            ==?
            safer-==?
            ==??) t)
          (otherwise nil))))
  ///

  ;; (memoize '2vecx-syntaxp
  ;;          :condition '(and x
  ;;                           (eq (svex-kind x) :call)
  ;;                           (member (svex-call->fn x)
  ;;                                   '(res resand resor concat ?))))

  (local (defthm logand-equal-neg-1
           (equal (equal (logand x y) -1)
                  (and (equal x -1)
                       (equal y -1)))
           :hints ((bitops::logbitp-reasoning))))



  (defthm 2vecx-p-of-3vec-reduction-and
    (implies (3vec-p x)
             (2vecx-p (3vec-reduction-and x)))
    :hints(("Goal" :in-theory (enable 2vecx-p 3vec-reduction-and 3vec-fix bool->vec 3vec-p))))

  (defthm 2vecx-p-of-3vec-reduction-or
    (implies (3vec-p x)
             (2vecx-p (3vec-reduction-or x)))
    :hints(("Goal" :in-theory (enable 2vecx-p 3vec-reduction-or 3vec-fix bool->vec 3vec-p))))

  (defthm 2vecx-p-of-4vec-reduction-and
    (2vecx-p (4vec-reduction-and x))
    :hints(("Goal" :in-theory (enable 4vec-reduction-and))))

  (defthm 2vecx-p-of-4vec-reduction-or
    (2vecx-p (4vec-reduction-or x))
    :hints(("Goal" :in-theory (enable 4vec-reduction-or))))

  (defthm 2vecx-p-of-4vec-parity
    (2vecx-p (4vec-parity x))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-parity 3vec-fix bool->vec))))

  (defthm 2vecx-p-of-4vec-uminus
    (2vecx-p (4vec-uminus x))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-uminus))))

  (defthm 2vecx-p-of-4vec-xdet
    (2vecx-p (4vec-xdet x))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-xdet))))

  (defthm 2vecx-p-of-4vec-countones
    (2vecx-p (4vec-countones x))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-countones))))

  (defthm 2vecx-p-of-4vec-onehot
    (2vecx-p (4vec-onehot x))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-onehot))))

  (defthm 2vecx-p-of-4vec-onehot0
    (2vecx-p (4vec-onehot0 x))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-onehot0))))

  (defthm 2vecx-p-of-4vec-minus
    (2vecx-p (4vec-minus x y))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-minus))))

  (defthm 2vecx-p-of-4vec-plus
    (2vecx-p (4vec-plus x y))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-plus))))

  (defthm 2vecx-p-of-4vec-times
    (2vecx-p (4vec-times x y))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-times))))

  (defthm 2vecx-p-of-4vec-quotient
    (2vecx-p (4vec-quotient x y))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-quotient))))

  (defthm 2vecx-p-of-4vec-remainder
    (2vecx-p (4vec-remainder x y))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-remainder))))

  (defthm 2vecx-p-of-3vec-==
    (implies (and (3vec-p x)
                  (3vec-p y))
             (2vecx-p (3vec-== x y)))
    :hints(("Goal" :in-theory (enable 3vec-==))))

  (defthm 2vecx-p-of-2vec
    (2vecx-p (2vec x))
    :hints(("Goal" :in-theory (enable 2vecx-p))))

  (defthm 2vecx-p-of-4vec-wildeq
    (2vecx-p (4vec-wildeq x y))
    :hints(("Goal" :in-theory (enable 4vec-wildeq))))

  (defthm 2vecx-p-of-4vec-wildeq-safe
    (2vecx-p (4vec-wildeq-safe x y))
    :hints(("Goal" :in-theory (enable 4vec-wildeq-safe))))

  (defthm 2vecx-p-of-4vec-symwildeq
    (2vecx-p (4vec-symwildeq x y))
    :hints(("Goal" :in-theory (enable 4vec-symwildeq))))

  (defthm 2vecx-p-of-4vec-==
    (2vecx-p (4vec-== x y))
    :hints(("Goal" :in-theory (enable 4vec-==))))

  (defthm 2vecx-p-of-4vec-<
    (2vecx-p (4vec-< x y))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-<))))

  (defthm 2vecx-p-of-4vec-clog2
    (2vecx-p (4vec-clog2 x))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-clog2))))

  (defthm 2vecx-p-of-4vec-pow
    (2vecx-p (4vec-pow x y))
    :hints(("Goal" :in-theory (enable 2vecx-p 4vec-pow))))

  (defthm 2vecx-p-of-eval-when-2vecx-syntaxp
    (implies (2vecx-syntaxp x)
             (2vecx-p (svex-eval x env)))
    :hints (("Goal" :expand ((svex-eval x env)
                             (2vecx-syntaxp x)
                             (:free (x) (svex-eval (list 'quote x) env)))
             :in-theory (e/d (svex-apply svexlist-eval 4veclist-nth-safe)
                             ((:d 2vecx-syntaxp))))))

  (deffixequiv 2vecx-syntaxp :args ((x svex))))

(defthm 4vec-xdet-of-2vecx
  (implies (2vecx-p x)
           (equal (4vec-xdet x)
                  (4vec-fix x)))
  :hints(("Goal" :in-theory (enable 2vecx-p 4vec-xdet))))

(def-svex-rewrite xdet-of-2vecx
  :lhs (xdet x)
  :checks ((2vecx-syntaxp x))
  :rhs x)

(def-svex-rewrite +-0-is-xdet-1
  :lhs (+ 0 x)
  :rhs (xdet x)
  :hints(("Goal" :in-theory (enable 4vec-plus 4vec-xdet svex-apply))))

(def-svex-rewrite +-0-is-xdet-2
  :lhs (+ x 0)
  :rhs (xdet x)
  :hints(("Goal" :in-theory (enable 4vec-plus 4vec-xdet svex-apply))))

(def-svex-rewrite *-1-is-xdet-1
  :lhs (* 1 x)
  :rhs (xdet x)
  :hints(("Goal" :in-theory (enable 4vec-times 4vec-xdet svex-apply))))

(def-svex-rewrite *-1-is-xdet-2
  :lhs (* x 1)
  :rhs (xdet x)
  :hints(("Goal" :in-theory (enable 4vec-times 4vec-xdet svex-apply))))

(def-svex-rewrite +-of-xdet-left
  :lhs (+ (xdet x) y)
  :rhs (+ x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-plus 4vec-xdet))))

(def-svex-rewrite +-of-xdet-right
  :lhs (+ y (xdet x))
  :rhs (+ y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-plus 4vec-xdet))))

(def-svex-rewrite b--of-xdet-left
  :lhs (b- (xdet x) y)
  :rhs (b- x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-minus 4vec-xdet))))

(def-svex-rewrite b--of-xdet-right
  :lhs (b- y (xdet x))
  :rhs (b- y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-minus 4vec-xdet))))

(def-svex-rewrite <-of-xdet-left
  :lhs (< (xdet x) y)
  :rhs (< x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-< 4vec-xdet))))

(def-svex-rewrite <-of-xdet-right
  :lhs (< y (xdet x))
  :rhs (< y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-< 4vec-xdet))))

(def-svex-rewrite u--of-xdet
  :lhs (u- (xdet x))
  :rhs (u- x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-uminus 4vec-xdet))))

(def-svex-rewrite *-of-xdet-left
  :lhs (* (xdet x) y)
  :rhs (* x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-times 4vec-xdet))))

(def-svex-rewrite *-of-xdet-right
  :lhs (* y (xdet x))
  :rhs (* y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-times 4vec-xdet))))

(def-svex-rewrite /-of-xdet-left
  :lhs (/ (xdet x) y)
  :rhs (/ x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-quotient 4vec-xdet))))

(def-svex-rewrite /-of-xdet-right
  :lhs (/ y (xdet x))
  :rhs (/ y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-quotient 4vec-xdet))))

(def-svex-rewrite %-of-xdet-left
  :lhs (% (xdet x) y)
  :rhs (% x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-remainder 4vec-xdet))))

(def-svex-rewrite %-of-xdet-right
  :lhs (% y (xdet x))
  :rhs (% y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-remainder 4vec-xdet))))

(def-svex-rewrite rsh-of-xdet
  :lhs (rsh (xdet n) x)
  :rhs (rsh n x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-rsh 4vec-shift-core 4vec-xdet))))

(def-svex-rewrite lsh-of-xdet
  :lhs (lsh (xdet n) x)
  :rhs (lsh n x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-lsh 4vec-shift-core 4vec-xdet))))

(def-svex-rewrite concat-of-xdet
  :lhs (concat (xdet n) x y)
  :rhs (concat n x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-xdet))))

(def-svex-rewrite partsel-of-xdet-1
  :lhs (partsel (xdet lsb) width in)
  :rhs (partsel lsb width in)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-part-select 4vec-xdet))))

(def-svex-rewrite partsel-of-xdet-2
  :lhs (partsel lsb (xdet width) in)
  :rhs (partsel lsb width in)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-part-select 4vec-xdet))))

(def-svex-rewrite partinst-of-xdet-1
  :lhs (partinst (xdet lsb) width in val)
  :rhs (partinst lsb width in val)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-part-install 4vec-xdet))))

(def-svex-rewrite partinst-of-xdet-2
  :lhs (partinst lsb (xdet width) in val)
  :rhs (partinst lsb width in val)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-part-install 4vec-xdet))))


(def-svex-rewrite bitnot-of-unfloat
  :lhs (bitnot (unfloat x))
  :rhs (bitnot x))

(def-svex-rewrite bitnot-of-bitnot
  :lhs (bitnot (bitnot x))
  :rhs (unfloat x)
  :hints(("Goal" :in-theory (enable 4vec-bitnot 3vec-bitnot 3vec-fix svex-apply svexlist-eval
                                    4vec-mask))
         (bitops::logbitp-reasoning)
         (and stable-under-simplificationp
              '(:in-theory (enable bool->bit)))))


(def-svex-rewrite bitand-of-unfloat-1
  :lhs (bitand (unfloat x) y)
  :rhs (bitand x y))

(def-svex-rewrite bitand-of-unfloat-2
  :lhs (bitand x (unfloat y))
  :rhs (bitand x y))

(def-svex-rewrite bitor-of-unfloat-1
  :lhs (bitor (unfloat x) y)
  :rhs (bitor x y))

(def-svex-rewrite bitor-of-unfloat-2
  :lhs (bitor x (unfloat y))
  :rhs (bitor x y))

(def-svex-rewrite bitxor-of-unfloat-1
  :lhs (bitxor (unfloat x) y)
  :rhs (bitxor x y))

(def-svex-rewrite bitxor-of-unfloat-2
  :lhs (bitxor x (unfloat y))
  :rhs (bitxor x y))

(def-svex-rewrite bit?-of-unfloat
  :lhs (bit? (unfloat x) y z)
  :rhs (bit? x y z)
  :hints(("Goal" :in-theory (enable 4vec-bit? svex-apply svexlist-eval))))

(def-svex-rewrite bit?!-of-unfloat
  :lhs (bit?! (unfloat x) y z)
  :rhs (bit?! x y z)
  :hints(("Goal" :in-theory (enable 4vec-bit?! svex-apply svexlist-eval 3vec-fix))))

(def-svex-rewrite uand-of-unfloat
  :lhs (uand (unfloat x))
  :rhs (uand x))

(def-svex-rewrite uor-of-unfloat
  :lhs (uor (unfloat x))
  :rhs (uor x))

(def-svex-rewrite uxor-of-unfloat
  :lhs (uxor (unfloat x))
  :rhs (uxor x))

(local (defthm 2vec-p-of-3vec-fix
         (equal (2vec-p (3vec-fix x))
                (2vec-p x))
         :hints(("Goal" :in-theory (enable 2vec-p 3vec-fix)))))

(local (defthm 3vec-fix-when-2vec-p
         (implies (2vec-p x)
                  (equal (3vec-fix x) (4vec-fix x)))
         :hints(("Goal" :in-theory (enable 2vec-p 3vec-fix)))))

(def-svex-rewrite bitsel-of-unfloat-1
  :lhs (bitsel (unfloat n) x)
  :rhs (bitsel n x)
  :hints(("Goal" :in-theory (e/d (svex-apply 4vec-bit-extract 4vec-bit-index)
                                 (2vec-p)))))

(def-svex-rewrite bitsel-of-unfloat-2
  :lhs (bitsel n (unfloat x))
  :rhs (unfloat (bitsel n x))
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bit-extract 4vec-bit-index 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit)))))

(def-svex-rewrite zerox-of-unfloat-1
  :lhs (zerox (unfloat n) x)
  :rhs (zerox n x)
  :hints(("Goal" :in-theory (e/d (svex-apply 4vec-zero-ext)
                                 (2vec-p)))))

(def-svex-rewrite zerox-of-unfloat-2
  :lhs (zerox n (unfloat x))
  :rhs (unfloat (zerox n x))
  :hints(("Goal" :in-theory (enable svex-apply 4vec-zero-ext 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit)))))


(def-svex-rewrite signx-of-unfloat-1
  :lhs (signx (unfloat n) x)
  :rhs (signx n x)
  :hints(("Goal" :in-theory (e/d (svex-apply 4vec-sign-ext)
                                 (2vec-p)))))

(def-svex-rewrite signx-of-unfloat-2
  :lhs (signx n (unfloat x))
  :rhs (unfloat (signx n x))
  :hints(("Goal" :in-theory (enable svex-apply 4vec-sign-ext 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))

(def-svex-rewrite concat-of-unfloat-1
  :lhs (concat (unfloat n) x y)
  :rhs (concat n x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))



(def-svex-rewrite partsel-of-unfloat-1
  :lhs (partsel (unfloat lsb) width in)
  :rhs (partsel lsb width in)
  :hints(("Goal" :in-theory (e/d (svex-apply 4vec-part-select)
                                 (2vec-p)))))

(def-svex-rewrite partsel-of-unfloat-2
  :lhs (partsel lsb (unfloat width) in)
  :rhs (partsel lsb width in)
  :hints(("Goal" :in-theory (e/d (svex-apply 4vec-part-select)
                                 (2vec-p)))))

(def-svex-rewrite partsel-of-unfloat-3
  :lhs (partsel lsb width (unfloat in))
  :rhs (unfloat (partsel lsb width in))
  :hints(("Goal" :in-theory (e/d (svex-apply 4vec-part-select 4vec-zero-ext
                                             4vec-concat 4vec-rsh 4vec-shift-core
                                             3vec-fix 4vec-mask)))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))

(def-svex-rewrite partinst-of-unfloat-1
  :lhs (partinst (unfloat lsb) width in val)
  :rhs (partinst lsb width in val)
  :hints(("Goal" :in-theory (e/d (svex-apply 4vec-part-install)
                                 (2vec-p)))))

(def-svex-rewrite partinst-of-unfloat-2
  :lhs (partinst lsb (unfloat width) in val)
  :rhs (partinst lsb width in val)
  :hints(("Goal" :in-theory (e/d (svex-apply 4vec-part-install)
                                 (2vec-p)))))

;; Signx 1 is special because it simply repeats the lowest bit of X forever.
;; These rules consolidate parts of concatenations that do this in more
;; complicated ways.
(def-svex-rewrite concat-1-to-signx
  :lhs (concat 1 x (concat 1 x y))
  :rhs (concat 2 (signx 1 x) y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-sign-ext 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))

(def-svex-rewrite concat-1-to-signx-2
  :lhs (concat 1 x (concat n (signx 1 x) y))
  :checks ((svex-quoted-index-p n)
           (bind n2 (svex-quote (2vec (+ 1 (2vec->val (svex-quote->val n)))))))
  :rhs (concat n2 (signx 1 x) y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-sign-ext 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))

(def-svex-rewrite concat-1-to-signx-3
  :lhs (concat 1 (unfloat x) (concat n (unfloat (signx 1 x)) y))
  :checks ((svex-quoted-index-p n)
           (bind n2 (svex-quote (2vec (+ 1 (2vec->val (svex-quote->val n)))))))
  :rhs (concat n2 (unfloat (signx 1 x)) y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-sign-ext 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))




(def-svex-rewrite rsh-of-unfloat-1
  :lhs (rsh (unfloat n) x)
  :rhs (rsh n x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-rsh 4vec-shift-core 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))

(def-svex-rewrite rsh-of-unfloat-2
  :lhs (rsh n (unfloat x))
  :rhs (unfloat (rsh n x))
  :hints(("Goal" :in-theory (enable svex-apply 4vec-rsh 4vec-shift-core 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))

(def-svex-rewrite lsh-of-unfloat-1
  :lhs (lsh (unfloat n) x)
  :rhs (lsh n x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-lsh 4vec-shift-core 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))

(def-svex-rewrite lsh-of-unfloat-2
  :lhs (lsh n (unfloat x))
  :rhs (unfloat (lsh n x))
  :hints(("Goal" :in-theory (enable svex-apply 4vec-lsh 4vec-shift-core 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::logbitp-case-splits
                                          bitops::logbitp-when-bit
                                          bitops::bool->bit))
          :prune-examples nil)))

(def-svex-rewrite +-of-unfloat-1
  :lhs (+ (unfloat x) y)
  :rhs (+ x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-plus 3vec-fix 4vec-mask))))

(def-svex-rewrite +-of-unfloat-2
  :lhs (+ y (unfloat x))
  :rhs (+ y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-plus 3vec-fix 4vec-mask))))

(def-svex-rewrite b--of-unfloat-1
  :lhs (b- (unfloat x) y)
  :rhs (b- x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-minus 3vec-fix 4vec-mask))))

(def-svex-rewrite b--of-unfloat-2
  :lhs (b- y (unfloat x))
  :rhs (b- y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-minus 3vec-fix 4vec-mask))))

(def-svex-rewrite u--of-unfloat
  :lhs (u- (unfloat x))
  :rhs (u- x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-uminus 3vec-fix 4vec-mask))))

(def-svex-rewrite *-of-unfloat-1
  :lhs (* (unfloat x) y)
  :rhs (* x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-times 3vec-fix 4vec-mask))))

(def-svex-rewrite *-of-unfloat-2
  :lhs (* y (unfloat x))
  :rhs (* y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-times 3vec-fix 4vec-mask))))

(def-svex-rewrite /-of-unfloat-1
  :lhs (/ (unfloat x) y)
  :rhs (/ x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-quotient 3vec-fix 4vec-mask))))

(def-svex-rewrite /-of-unfloat-2
  :lhs (/ y (unfloat x))
  :rhs (/ y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-quotient 3vec-fix 4vec-mask))))

(def-svex-rewrite %-of-unfloat-1
  :lhs (% (unfloat x) y)
  :rhs (% x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-remainder 3vec-fix 4vec-mask))))

(def-svex-rewrite %-of-unfloat-2
  :lhs (% y (unfloat x))
  :rhs (% y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-remainder 3vec-fix 4vec-mask))))



(def-svex-rewrite <-of-unfloat-1
  :lhs (< (unfloat x) y)
  :rhs (< x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-< 3vec-fix 4vec-mask))))

(def-svex-rewrite <-of-unfloat-2
  :lhs (< y (unfloat x))
  :rhs (< y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-< 3vec-fix 4vec-mask))))

(def-svex-rewrite ==-of-unfloat-1
  :lhs (== (unfloat x) y)
  :rhs (== x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-==))))

(def-svex-rewrite ==-of-unfloat-2
  :lhs (== y (unfloat x))
  :rhs (== y x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-==))))




;; (define concat-under-mask-meta-aux ((mask 4vmask-p)
;;                                     (xwidth natp)
;;                                     (x svex-p)
;;                                     (okp))
;;   :prepwork ((local (in-theory (disable (tau-system))))
;;              (local (defthm svex-p-compound-recognizer
;;                       (implies (svex-p x) x)
;;                       :rule-classes :compound-recognizer))
;;              (local (defthm svex-fix-type
;;                       (svex-p (svex-fix x))
;;                       :rule-classes
;;                       ((:type-prescription :typed-term (svex-fix x))))))
;;   :returns (mv (successp)
;;                (subst svex-alist-p))
;;   :measure (svex-count x)
;;   (b* ((xwidth (lnfix xwidth))
;;        (x (svex-fix x))
;;        (mask (4vmask-fix mask))
;;        ((unless (svex-case x
;;                   :call (and (eq x.fn 'concat)
;;                              (eql (len x.args) 3)
;;                              (b* ((w (car x.args)))
;;                                (svex-case w
;;                                  :quote (and (2vec-p w.val)
;;                                              (<= 0 (2vec->val w.val))
;;                                              (eql 0 (loghead (2vec->val w.val) mask)))
;;                                  :otherwise nil)))
;;                   :otherwise nil))
;;         (mv okp
;;             `((width . ,(svex-quote (2vec (lnfix xwidth))))
;;               (x . ,x))))
;;        ((svex-call x))
;;        (width (2vec->val (svex-quote->val (first x.args))))
;;        (newxwidth (+ xwidth width))
;;        (newmask (logtail width mask)))
;;     (concat-under-mask-meta-aux newmask newxwidth (third x.args)
;;                                 (or okp
;;                                     (not (equal (second x.args) ''(-1 . 0))))))
;;   ///
;;   (local (in-theory (disable (:d concat-under-mask-meta-aux)
;;                              not)))
;;   (local (in-theory (enable* bitops::ihsext-advanced-thms)))
;;   (local (in-theory (disable bitops::loghead-identity
;;                              bitops::logtail-identity
;;                              unsigned-byte-p
;;                              default-car default-cdr)))

;;   (local (defthm shift-mask-when-zero-prefix
;;            (implies (and (equal 0 (loghead width mask))
;;                          (natp width) (natp xwidth))
;;                     (equal (ash (logtail width mask) (+ xwidth width))
;;                            (ash mask xwidth)))
;;            :hints ((bitops::logbitp-reasoning))))


;;   (local (defthm unnest-logapps-under-mask
;;            (implies (and (equal 0 (loghead (+ w1 w2) mask))
;;                          (natp w1) (natp w2))
;;                     (and (equal (logior (lognot mask)
;;                                         (logapp w1 a (logapp w2 b c)))
;;                                 (logior (lognot mask)
;;                                         (logapp (+ w1 w2) -1 c)))
;;                          (equal (logand mask
;;                                         (logapp w1 a (logapp w2 b c)))
;;                                 (logand mask
;;                                         (logapp (+ w1 w2) 0 c)))))
;;            :hints ((bitops::logbitp-reasoning))))

;;   ;; (local (defthm norm-first-logapp-under-mask
;;   ;;          (implies (and (syntaxp (not (equal a ''0)))
;;   ;;                        (equal 0 (loghead w mask))
;;   ;;                        (natp w))
;;   ;;                   (equal (logior (lognot mask)
;;   ;;                                  (logapp w a b))
;;   ;;                          (logior (lognot mask)
;;   ;;                                  (logapp w 0 b))))
;;   ;;          :hints ((bitops::logbitp-reasoning))))

;;   (defthm mask-when-loghead-0
;;     (implies (and (equal 0 (loghead (+ (2vec->val w1) (2vec->val w2)) (4vmask-fix mask)))
;;                   (2vec-p w1) (2vec-p w2)
;;                   (natp (2vec->val w1)) (natp (2vec->val w2)))
;;              (equal (4vec-mask mask
;;                                (4vec-concat w1 a (4vec-concat w2 b c)))
;;                     (4vec-mask mask (4vec-concat (2vec (+ (2vec->val w1) (2vec->val w2)))
;;                                                  '(-1 . 0) c))))
;;     :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat))
;;            ;; (bitops::logbitp-reasoning
;;            ;;   ;; :add-hints (:in-theory (enable* bitops::logbitp-case-splits
;;            ;;   ;;                                 bitops::logbitp-when-bit
;;            ;;   ;;                                 bitops::bool->bit))
;;            ;;   ;; :prune-examples nil
;;            ;;   )
;;            ))



;;   (defret concat-under-mask-meta-aux-correct
;;     (equal (4vec-mask (logapp xwidth 0 (4vmask-fix mask))
;;                       (svex-eval '(concat width '(-1 . 0) x)
;;                                  (svex-alist-eval subst env)))
;;            (4vec-mask (logapp xwidth 0 (4vmask-fix mask))
;;                       (4vec-concat (2vec (nfix xwidth))
;;                                    '(-1 . 0) (svex-eval x env))))
;;     :hints (("goal" :induct (concat-under-mask-meta-aux mask xwidth x okp)
;;              :expand ((concat-under-mask-meta-aux mask xwidth x okp))
;;              :in-theory (enable svex-apply svexlist-eval svex-lookup)
;;              :do-not-induct t)
;;             ;; (and stable-under-simplificationp
;;             ;;      '(:in-theory (enable 4vec-mask 4vec-concat)))
;;             ;; (bitops::logbitp-reasoning
;;             ;;  :add-hints (:in-theory (enable* bitops::logbitp-case-splits
;;             ;;                                  bitops::logbitp-when-bit
;;             ;;                                  bitops::bool->bit)))
;;             ))

;;   (defret alist-keys-of-concat-under-mask-meta-aux
;;     (equal (svex-alist-keys subst)
;;            '(width x))
;;     :hints (("goal" :induct (concat-under-mask-meta-aux mask xwidth x okp)
;;              :expand ((concat-under-mask-meta-aux mask xwidth x okp))
;;              :in-theory (enable svex-alist-keys))))

;;   (local (in-theory (disable member-equal)))

;;   (defret no-new-vars-of-concat-under-mask-meta-aux
;;     (implies (not (member v (svex-vars x)))
;;              (not (member v (svex-alist-vars subst))))
;;     :hints (("goal" :induct (concat-under-mask-meta-aux mask xwidth x okp)
;;              :expand ((concat-under-mask-meta-aux mask xwidth x okp))
;;              :in-theory (enable svex-alist-vars))))

;;   (deffixequiv concat-under-mask-meta-aux))



;; (define svex-concat-flatten ((x svex-p)
;;                              (width natp)
;;                              (acc svex-p))
;;   :prepwork ((local (defthm nth-open-by-len
;;                       (implies (and (syntaxp (quotep n))
;;                                     (< (nfix n) (len x)))
;;                                (equal (nth n x)
;;                                       (if (zp n)
;;                                           (car x)
;;                                         (nth (1- n) (cdr x)))))))
;;              (local (defthm len-of-cdr
;;                       (implies (posp (len x))
;;                                (equal (len (cdr x))
;;                                       (1- (len x))))))
;;              (local (defthm consp-by-len
;;                       (implies (posp (len x))
;;                                (consp x))))
;;              (local (in-theory (disable nth len not))))
;;   :returns (concat svex-p)
;;   :measure (svex-count x)
;;   :verify-guards nil
;;   (b* ((width (lnfix width))
;;        ((fun (ret x width acc))
;;         (svex-call 'concat (list (svex-quote (2vec width))
;;                                  x acc)))
;;        ((when (eql width 0)) (svex-fix acc)))
;;     (svex-case x
;;       :call (b* (((unless (and (eq x.fn 'concat)
;;                                (eql (len x.args) 3)))
;;                   (ret x width acc))
;;                  (w1 (car x.args)))
;;               (svex-case w1
;;                 :quote (b* (((unless (and (2vec-p w1.val)
;;                                           (<= 0 (2vec->val w1.val))))
;;                              (ret x width acc))
;;                             (w1val (2vec->val w1.val))
;;                             ((when (eql 0 w1val))
;;                              (svex-concat-flatten (third x.args) width acc))
;;                             ((when (<= width w1val))
;;                              (svex-concat-flatten (second x.args) width acc))
;;                             (acc (svex-concat-flatten (third x.args)
;;                                                       (- width w1val)
;;                                                       acc)))
;;                          (svex-concat-flatten (second x.args)
;;                                               w1val acc))
;;                 :otherwise (ret x width acc)))
;;       :otherwise (ret x width acc)))
;;   ///
;;   (verify-guards svex-concat-flatten)
;;   (local (defthm 4vec-concat-of-0-rw
;;            (implies (and (2vec-p w)
;;                          (equal (2vec->val w) 0))
;;                     (equal (4vec-concat w x y)
;;                            (4vec-fix y)))
;;            :hints(("Goal" :in-theory (enable 4vec-concat)))))
;;   (local (defthm 4vec-concat-nest-outer-width-less
;;            (implies (and (2vec-p w1)
;;                          (2vec-p w2)
;;                          (<= 0 (2vec->val w1))
;;                          (<= (2vec->val w1) (2vec->val w2)))
;;                     (equal (4vec-concat w1 (4vec-concat w2 x y) z)
;;                            (4vec-concat w1 x z)))
;;            :hints(("Goal" :in-theory (enable 4vec-concat))
;;                   (bitops::logbitp-reasoning))))
;;   (local (defthm 4vec-concat-nest-outer-width-greater
;;            (implies (and (2vec-p w1)
;;                          (2vec-p w2)
;;                          (<= 0 (2vec->val w2))
;;                          (< (2vec->val w2) (2vec->val w1)))
;;                     (equal (4vec-concat w1 (4vec-concat w2 x y) z)
;;                            (4vec-concat w2 x (4vec-concat (2vec (- (2vec->val w1) (2vec->val w2))) y z))))
;;            :hints(("Goal" :in-theory (enable 4vec-concat))
;;                   (bitops::logbitp-reasoning))))
;;   (defthm svex-concat-flatten-correct
;;     (equal (svex-eval (svex-concat-flatten x width acc) env)
;;            (4vec-concat (2vec (nfix width )) (svex-eval x env)
;;                         (svex-eval acc env)))
;;     :hints (("goal" :induct t
;;              :expand ((svex-concat-flatten x width acc)))
;;             (and stable-under-simplificationp
;;                  '(:in-theory (enable svex-apply svexlist-eval)))))

;;   (defret svex-vars-of-svex-concat-flatten
;;     (implies (and (not (member v (svex-vars x)))
;;                   (not (member v (svex-vars acc))))
;;              (not (member v (svex-vars concat))))))

;; (def-svex-rewrite concat-flatten
;;   :lhs (concat w (concat w1 x y) z)
;;   :checks ((svex-quoted-index-p w)
;;            (svex-quoted-index-p w1)
;;            (bind res (svex-concat-flatten (svex-call 'concat (list w1 x y))
;;                                           (2vec->val (svex-quote->val w))
;;                                           z)))
;;   :rhs res)





;; (define svex-meta-concat-under-mask-1 ((mask 4vmask-p)
;;                                        (args svexlist-p)
;;                                        localp)
;;   :ignore-ok t
;;   :irrelevant-formals-ok t
;;   :returns (mv (successp booleanp)
;;                (pat (iff (svex-p pat) successp))
;;                (subst svex-alist-p))
;;   :prepwork ((local (defthm lookup-by-member-keys
;;                       (implies (member k (svex-alist-keys subst))
;;                                (svex-lookup k subst))
;;                       :hints(("Goal" :in-theory (enable svex-lookup
;;                                                         svex-alist-keys))))))

;;   (b* (((when localp) (mv nil nil nil))
;;        ((mv okp subst)
;;         (concat-under-mask-meta-aux
;;          mask 0 (svex-call 'concat args) nil))
;;        ((unless okp) (mv nil nil nil))
;;        (x (svex-lookup 'x subst))
;;        ;; ((when (and localp
;;        ;;             (not (svex-case x :quote t :otherwise nil))))
;;        ;;  (mv nil nil nil))
;;        )
;;     (mv t '(concat width '(-1 . 0) x) subst))
;;   ///

;;   (DEFTHM
;;     SVEX-META-CONCAT-UNDER-MASK-1-CORRECT
;;     (B*
;;         (((MV OK PAT SUBST)
;;           (SVEX-META-CONCAT-UNDER-MASK-1 MASK ARGS LOCALP)))
;;       (IMPLIES OK
;;                (EQUAL (4VEC-MASK MASK
;;                                  (SVEX-EVAL PAT (SVEX-ALIST-EVAL SUBST ENV)))
;;                       (4VEC-MASK MASK
;;                                  (SVEX-APPLY 'CONCAT
;;                                              (SVEXLIST-EVAL ARGS ENV))))))
;;     :HINTS (("Goal" :use ((:instance concat-under-mask-meta-aux-correct
;;                            (xwidth 0) (x (svex-call 'concat args)) (okp nil)))
;;              :in-theory (e/d (svex-apply)
;;                              (concat-under-mask-meta-aux-correct)))))
;;   (DEFFIXEQUIV SVEX-META-CONCAT-UNDER-MASK-1)
;;   (DEFTHM SVEX-META-CONCAT-UNDER-MASK-1-NO-NEW-VARS
;;     (B* (((MV ?OK ?PAT SUBST)
;;           (SVEX-META-CONCAT-UNDER-MASK-1 MASK ARGS LOCALP)))
;;       (IMPLIES (NOT (MEMBER V (SVEXLIST-VARS ARGS)))
;;                (NOT (MEMBER V (SVEX-ALIST-VARS SUBST)))))
;;     :HINTS ((AND STABLE-UNDER-SIMPLIFICATIONP
;;                  '(:IN-THEORY (ENABLE SVEX-VARS)))))
;;   (DEFTHM SVEX-META-CONCAT-UNDER-MASK-1-RHS-VARS-BOUND
;;     (B* (((MV OK PAT SUBST)
;;           (SVEX-META-CONCAT-UNDER-MASK-1 MASK ARGS LOCALP)))
;;       (IMPLIES OK
;;                (SUBSETP (SVEX-VARS PAT)
;;                         (SVEX-ALIST-KEYS SUBST)))))
;;   (TABLE SVEX-REWRITE 'CONCAT
;;          (CONS 'SVEX-META-CONCAT-UNDER-MASK-1
;;                (CDR (ASSOC 'CONCAT
;;                            (TABLE-ALIST 'SVEX-REWRITE WORLD))))))

;; (def-svex-rewrite concat-under-mask-1
;;   :lhs (concat w x y)
;;   :checks ((or (not localp)
;;                (eql (svex-kind y) :quote))
;;            (svex-quoted-index-p w)
;;            (eql 0 (loghead (2vec->val (svex-quote->val w)) mask))
;;            (not (and (equal (svex-kind x) :quote)
;;                      (equal (svex-quote->val x) (4vec-x))))
;;            (bind xx (svex-quote (4vec-x))))
;;   :rhs (concat w xx y)
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-lsh))
;;          (svex-generalize-lookups)
;;          (bitops::logbitp-reasoning :prune-examples nil))
;;   :localp t)



(def-svex-rewrite concat-under-mask-1
  :lhs (concat w x y)
  :checks ((or (not multirefp)
               (eql (svex-kind y) :quote))
           (svex-quoted-index-p w)
           (not (sparseint-test-bitand (sparseint-concatenate (2vec->val (svex-quote->val w)) -1 0) mask))
           (not (and (equal (svex-kind x) :quote)
                     (equal (svex-quote->val x) 0)))
           (bind xx (svex-quote 0)))
  :rhs (concat w xx y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-lsh 4vec-shift-core))
         (svex-generalize-lookups)
         (bitops::logbitp-reasoning :prune-examples nil)))

;; (def-svex-rewrite concat-under-mask-1-const
;;   :lhs (concat w x y)
;;   :checks ((eql (svex-kind y) :quote)
;;            (svex-quoted-index-p w)
;;            (eql 0 (loghead (2vec->val (svex-quote->val w)) mask))
;;            (bind yy (svex-quote (4vec-concat (2vec->val (svex-quote->val w))
;;                                              (4vec-x) y))))
;;   :rhs yy
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-lsh))
;;          (svex-generalize-lookups)
;;          (bitops::logbitp-reasoning :prune-examples nil))
;;   :localp t)

(def-svex-rewrite concat-under-mask-2
  :lhs (concat w x y)
  :checks ((svex-quoted-index-p w)
           (not (sparseint-test-bitand (sparseint-concatenate (2vec->val (svex-quote->val w)) 0 -1) mask)))
  :rhs x
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-lsh 4vec-shift-core))
         (bitops::logbitp-reasoning :prune-examples nil))
  ;; :localp t
  )


;; should be subsumed by concat-flatten
;; (def-svex-rewrite concat-of-concat-greater
;;   :lhs (concat w1 (concat w2 x y) z)
;;   :checks ((svex-quoted-index-p w1)
;;            (svex-quoted-index-p w2)
;;            (<= (2vec->val (svex-quote->val w1)) (2vec->val (svex-quote->val w2))))
;;   :rhs (concat w1 x z)
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-lsh))
;;          (bitops::logbitp-reasoning :prune-examples nil)))

;; (def-svex-rewrite concat-of-concat-less
;;   ;; DANGER This could add function calls and cause blowup in the number of terms.
;;   :lhs (concat w1 (concat w2 x y) z)
;;   :checks ((svex-quoted-index-p w1)
;;            (svex-quoted-index-p w2)
;;            (< (2vec->val (svex-quote->val w2)) (2vec->val (svex-quote->val w1)))
;;            (bind w3 (svex-quote (2vec (- (2vec->val (svex-quote->val w1)) (2vec->val (svex-quote->val w2)))))))
;;   :rhs (concat w2 x (concat w3 y z))
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-lsh))
;;          (bitops::logbitp-reasoning :prune-examples nil)))

(def-svex-rewrite concat-of-concat-join-consts
  :lhs (concat w1 x1 (concat w2 x2 y))
  :checks ((svex-quoted-index-p w1)
           (svex-quoted-index-p w2)
           (eq (svex-kind x1) :quote)
           (eq (svex-kind x2) :quote)
           (bind newx (svex-quote (4vec-concat (svex-quote->val w1)
                                               (svex-quote->val x1)
                                               (svex-quote->val x2))))
           (bind new-w (svex-quote (2vec (+ (2vec->val (svex-quote->val w1))
                                            (2vec->val (svex-quote->val w2)))))))
  :rhs (concat new-w newx y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-lsh 4vec-shift-core))
         (bitops::logbitp-reasoning :prune-examples nil)))

(def-svex-rewrite concat-of-concat-wider
  :lhs (concat w1 (concat w2 x y) z)
  :checks ((svex-quoted-index-p w1)
           (svex-quoted-index-p w2)
           (<= (2vec->val (svex-quote->val w1))
               (2vec->val (svex-quote->val w2))))
  :rhs (concat w1 x z)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-lsh 4vec-shift-core))
         (svex-generalize-lookups)
         (bitops::logbitp-reasoning :prune-examples nil)))

(local (defthmd equal-of-4vec-masks
         (equal (equal (4vec-mask mask x) (4vec-mask mask y))
                (or (equal x y)
                    (hide (equal (4vec-mask mask x) (4vec-mask mask y)))))
         :hints (("goal" :expand ((:free (x) (hide x)))))))

(local (Defthm sparseint-val-of-s4vec->upper
         (equal (sparseint-val (s4vec->upper x))
                (4vec->upper (s4vec->4vec x)))
         :hints(("Goal" :in-theory (enable s4vec->4vec)))))

(local (Defthm sparseint-val-of-s4vec->lower
         (equal (sparseint-val (s4vec->lower x))
                (4vec->lower (s4vec->4vec x)))
         :hints(("Goal" :in-theory (enable s4vec->4vec)))))


(local (in-theory (disable 4vec->upper-of-s4vec->4vec
                           4vec->lower-of-s4vec->4vec)))



(encapsulate nil
  (local (in-theory (disable acl2::commutativity-of-logand
                             acl2::commutativity-of-logior
                             logmask
                             bitops::logand-natp-type-2
                             bitops::logand-natp-type-1
                             acl2::loghead-identity
                             bitops::logbitp-when-bit
                             bitops::lognot-natp
                             bitops::logand->=-0-linear-2
                             bitops::upper-bound-of-logand
                             logbitp-when-not-integerp)))
  (local (defthm loghead-neg1
           (equal (loghead n -1)
                  (logmask n))
           :hints((logbitp-reasoning))))

  (local (defthm logapp-lemma1
           (implies (and (equal 0 (loghead n (lognot bl)))
                         (equal 0 (loghead n (lognot bu))))
                    (equal (logapp n (logand (logior bu bl) x) y)
                           (logapp n x y)))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm logapp-lemma2
           (implies (and (equal 0 (loghead n (lognot bl)))
                         (equal 0 (loghead n (lognot bu))))
                    (equal (logapp n (logand bu bl x) y)
                           (logapp n x y)))
           :hints ((bitops::logbitp-reasoning))))


  (local (defthm svex-xeval-lemma
           (implies (and (equal 0 (loghead n (lognot (4vec->lower x))))
                         (4vec-[= x y))
                    (and (equal (loghead n (lognot (4vec->lower y))) 0)
                         (equal (loghead n (lognot (4vec->upper y)))
                                (loghead n (lognot (4vec->upper x))))))
           :hints (("goal" :in-theory (enable 4vec-[=))
                   (logbitp-reasoning :passes 2))
           :rule-classes nil))

  (def-svex-rewrite concat-of-bitand-full-1
    :lhs (concat w (bitand bmask x) y)
    :checks ((svex-quoted-index-p w)
             (let wmask (sparseint-concatenate (2vec->val (svex-quote->val w)) -1 0))
             (let bmaskval (svex-s4xeval bmask))
             ;; want the width portion of mask to be all 1s, i.e:
             ;; (wmask & mask) == wmask
             ;; (wmask & ~mask) == 0
             (not (sparseint-test-bitandc2 wmask (s4vec->upper bmaskval)))
             (not (sparseint-test-bitandc2 wmask (s4vec->lower bmaskval))))
    :rhs (concat w (unfloat x) y)
    :hints(("Goal" :in-theory (enable equal-of-4vec-masks))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-apply ;; 4vec-bit? 3vec-bit?
                                     4vec-concat 4vec-bitand 3vec-bitand
                                     3vec-fix)))
           
           (svex-generalize-lookups)
           (and stable-under-simplificationp
                '(:use ((:instance svex-xeval-lemma
                         (n (4vec->lower (svex-quote->val w)))
                         (x (svex-xeval bmask))
                         (y (svex-eval bmask env))))))))


  (local (defthm logapp-lemma1-2
           (implies (and (equal 0 (loghead n (lognot bl)))
                         (equal 0 (loghead n (lognot bu))))
                    (equal (logapp n (logand x (logior bu bl)) y)
                           (logapp n x y)))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm logapp-lemma2-2
           (implies (and (equal 0 (loghead n (lognot bl)))
                         (equal 0 (loghead n (lognot bu))))
                    (equal (logapp n (logand x1 bu x2 bl) y)
                           (logapp n (logand x2 x1) y)))
           :hints ((bitops::logbitp-reasoning))))

  (def-svex-rewrite concat-of-bitand-full-2
    :lhs (concat w (bitand x bmask) y)
    :checks ((svex-quoted-index-p w)
             (let wmask (sparseint-concatenate (2vec->val (svex-quote->val w)) -1 0))
             (let bmaskval (svex-s4xeval bmask))
             ;; want the width portion of mask to be all 1s, i.e:
             ;; (wmask & mask) == wmask
             ;; (wmask & ~mask) == 0
             (not (sparseint-test-bitandc2 wmask (s4vec->upper bmaskval)))
             (not (sparseint-test-bitandc2 wmask (s4vec->lower bmaskval))))
    :rhs (concat w (unfloat x) y)
    :hints(("Goal" :in-theory (enable equal-of-4vec-masks))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-apply ;; 4vec-bit? 3vec-bit?
                                     4vec-concat 4vec-bitand 3vec-bitand
                                     3vec-fix)))
           (svex-generalize-lookups)
           (and stable-under-simplificationp
                '(:use ((:instance svex-xeval-lemma
                         (n (4vec->lower (svex-quote->val w)))
                         (x (svex-xeval bmask))
                         (y (svex-eval bmask env))))))))



  (local (defthm svex-xeval-lemma-2
           (implies (and (equal 0 (loghead n (4vec->upper x)))
                         (4vec-[= x y))
                    (and (equal (loghead n (4vec->upper y)) 0)
                         (equal (loghead n (4vec->lower y))
                                (loghead n (4vec->lower x)))))
           :hints (("goal" :in-theory (enable 4vec-[=))
                   (logbitp-reasoning :passes 2))
           :rule-classes nil))

  (local (defthm logapp-zero-lemma1
           (implies (and (equal 0 (loghead n bl))
                         (equal 0 (loghead n bu)))
                    (equal (logapp n (logand (logior bu bl) x) y)
                           (logapp n 0 y)))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm logapp-zero-lemma2
           (implies (and (equal 0 (loghead n bu)))
                    (equal (logapp n (logand bu x) y)
                           (logapp n 0 y)))
           :hints ((bitops::logbitp-reasoning))))

  (def-svex-rewrite concat-of-bitand-empty-1
    :lhs (concat w (bitand bmask x) y)
    :checks ((svex-quoted-index-p w)
             (let wmask (sparseint-concatenate (2vec->val (svex-quote->val w)) -1 0))
             (let bmaskval (svex-s4xeval bmask))
             ;; want the width portion of mask to be all 0s, i.e:
             ;; (wmask & mask) == 0
             (not (sparseint-test-bitand wmask (s4vec->upper bmaskval)))
             (not (sparseint-test-bitand wmask (s4vec->lower bmaskval))))
    :rhs (concat w 0 y)
    :hints(("Goal" :in-theory (enable equal-of-4vec-masks))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-apply ;; 4vec-bit? 3vec-bit?
                                     4vec-concat 4vec-bitand 3vec-bitand
                                     3vec-fix)))
           
           (svex-generalize-lookups)
           (and stable-under-simplificationp
                '(:use ((:instance svex-xeval-lemma-2
                         (n (4vec->lower (svex-quote->val w)))
                         (x (svex-xeval bmask))
                         (y (svex-eval bmask env))))))))


  (local (defthm logapp-zero-lemma1-2
           (implies (and (equal 0 (loghead n bl))
                         (equal 0 (loghead n bu)))
                    (equal (logapp n (logand x (logior bu bl)) y)
                           (logapp n 0 y)))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm logapp-zero-lemma2-2
           (implies (and (equal 0 (loghead n bu)))
                    (equal (logapp n (logand x1 bu x2) y)
                           (logapp n 0 y)))
           :hints ((bitops::logbitp-reasoning))))


  (def-svex-rewrite concat-of-bitand-empty-2
    :lhs (concat w (bitand x bmask) y)
    :checks ((svex-quoted-index-p w)
             (let wmask (sparseint-concatenate (2vec->val (svex-quote->val w)) -1 0))
             (let bmaskval (svex-s4xeval bmask))
             ;; want the width portion of mask to be all 0s, i.e:
             ;; (wmask & mask) == 0
             (not (sparseint-test-bitand wmask (s4vec->upper bmaskval)))
             (not (sparseint-test-bitand wmask (s4vec->lower bmaskval))))
    :rhs (concat w 0 y)
    :hints(("Goal" :in-theory (enable equal-of-4vec-masks))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-apply ;; 4vec-bit? 3vec-bit?
                                     4vec-concat 4vec-bitand 3vec-bitand
                                     3vec-fix)))
           (svex-generalize-lookups)
           (and stable-under-simplificationp
                '(:use ((:instance svex-xeval-lemma-2
                         (n (4vec->lower (svex-quote->val w)))
                         (x (svex-xeval bmask))
                         (y (svex-eval bmask env))))))
           )))


(def-svex-rewrite zerox-to-concat
  :lhs (zerox w x)
  :rhs (concat w x 0)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-zero-ext 4vec-concat))))

;; should be subsumed by concat-under-mask-2
(def-svex-rewrite zerox-of-concat-greater
  :lhs (zerox w1 (concat w2 x y))
  :checks ((svex-quoted-index-p w1)
           (svex-quoted-index-p w2)
           (<= (2vec->val (svex-quote->val w1)) (2vec->val (svex-quote->val w2))))
  :rhs (zerox w1 x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-zero-ext 4vec-mask 4vec-lsh 4vec-shift-core))
         (bitops::logbitp-reasoning :prune-examples nil)))


;; (define rsh-of-concat-meta-aux ((shift natp)
;;                                 (x svex-p))
;;   :measure (svex-count x)
;;   :prepwork ((local (defthm true-listp-of-svex-call->args
;;                       (true-listp (svex-call->args x))
;;                       :rule-classes :type-prescription))
;;              (local (defthmd nth-expand
;;                       (implies (syntaxp (quotep n))
;;                                (equal (nth n x)
;;                                       (if (zp n)
;;                                           (car x)
;;                                         (nth (1- n) (cdr x))))))))
;;   :returns (subst svex-alist-p)
;;   (b* ((shift (lnfix shift))
;;        ((unless (svex-case x :call (eq x.fn 'concat) :otherwise nil))
;;         `((shift . ,(svex-quote (2vec shift)))
;;           (x . ,(svex-fix x))))
;;        ((svex-call x))
;;        ((unless (eql (len x.args) 3))
;;         `((shift . ,(svex-quote (2vec shift)))
;;           (x . ,(svex-fix x))))
;;        ((list width ?first rest) x.args)
;;        (widthval (svex-case width :quote (and (2vec-p width.val)
;;                                               (2vec->val width.val)) :otherwise nil))
;;        ((unless (and widthval
;;                      (<= 0 widthval)
;;                      (< widthval shift)))
;;         `((shift . ,(svex-quote (2vec shift)))
;;           (x . ,(svex-fix x)))))
;;     (rsh-of-concat-meta-aux (- shift widthval) rest))
;;   ///
;;   (local (in-theory (disable bitops::logtail-identity nth len
;;                              (:d rsh-of-concat-meta-aux))))
;;   (defthm eval-of-rsh-of-concat-meta-aux
;;     (equal (svex-eval '(rsh shift x)
;;                       (svex-alist-eval (rsh-of-concat-meta-aux shift x) env))
;;            (4vec-rsh (2vec (nfix shift)) (svex-eval x env)))
;;     :hints(("Goal" :in-theory (enable svex-apply svexlist-eval svex-lookup)
;;             :induct (rsh-of-concat-meta-aux shift x)
;;             :expand ((rsh-of-concat-meta-aux shift x)))
;;            (and stable-under-simplificationp
;;                 '(:in-theory (enable 4vec-rsh 4vec-concat
;;                                      bitops::logtail-of-logapp-split
;;                                      nth-expand)))))

;;   (defthm rsh-of-concat-no-new-vars
;;     (implies (not (member v (svex-vars x)))
;;              (not (member v (svex-alist-vars (rsh-of-concat-meta-aux shift x)))))
;;     :hints(("Goal" :in-theory (enable svex-alist-vars)
;;             :induct (rsh-of-concat-meta-aux shift x)
;;             :expand ((rsh-of-concat-meta-aux shift x)))))

;;   (defthm svex-alist-keys-of-rsh-of-concat-meta-aux
;;     (equal (svex-alist-keys (rsh-of-concat-meta-aux shift x))
;;            '(shift x))
;;     :hints(("Goal" :in-theory (enable svex-alist-keys)
;;             :induct (rsh-of-concat-meta-aux shift x)
;;             :expand ((rsh-of-concat-meta-aux shift x))))))


;; (defalist concat-alist :key-type natp :val-type svex-p)

;; (define concat-alist-to-svex ((x concat-alist-p)
;;                               (rest svex-p))
;;   :measure (len (concat-alist-fix x))
;;   :returns (concat svex-p)
;;   (b* ((x (concat-alist-fix x)))
;;     (if (atom x)
;;         (svex-fix rest)
;;       (svex-call 'concat
;;                (list (svex-quote (2vec (caar x)))
;;                      (cdar x)
;;                      (concat-alist-to-svex (cdr x) rest))))))

;; (define svex-to-concat-alist ((x svex-p))
;;   :returns (mv (alist concat-alist-p)
;;                (rest svex-p))
;;   :measure (svex-count x)
;;   (svex-case x
;;     :call (if (and (eq x.fn 'concat)
;;                    (eql (len x.args) 3)
;;                    (b* ((w (car x.args)))
;;                      (svex-case w
;;                        :quote (and (2vec-p w.val)
;;                                    (<= 0 (2vec->val w.val)))
;;                        :otherwise nil)))
;;               (b* (((mv alist rest) (svex-to-concat-alist (third x.args))))
;;                 (mv (cons (cons (2vec->val (svex-quote->val (car x.args)))
;;                                 (second x.args))
;;                           alist)
;;                     rest))
;;             (mv nil (svex-fix x)))
;;     :otherwise (mv nil (svex-fix x)))
;;   ///
;;   (local (defthm equal-of-len
;;            (implies (syntaxp (quotep y))
;;                     (equal (equal (len x) y)
;;                            (if (zp y)
;;                                (and (equal y 0) (atom x))
;;                              (and (consp x)
;;                                   (equal (len (cdr x)) (1- y))))))))
;;   (local (in-theory (disable len)))
;;   (defret concat-alist-to-svex-of-svex-to-concat-alist
;;     (equal (svex-eval (concat-alist-to-svex alist rest) env)
;;            (svex-eval x env))
;;     :hints(("Goal" :in-theory (enable concat-alist-to-svex
;;                                       svexlist-eval)))))

;; (fty::deftagsum concat-tree
;;   (:leaf ((expr svex-p))
;;    :layout :tree)
;;   (:branch ((lwidth natp)
;;             (left concat-tree-p)
;;             (right concat-tree-p))
;;    :layout :tree))

(defalist rsh-of-concat-alist :key-type natp :val-type svex-p)

(defprod rsh-of-concat-table
  ((alist rsh-of-concat-alist-p "alist binding naturals to tails")
   (alist-width natp            "width of the alist")
   (tail svex-p                 "expression for remainder after the alist")))

(define rsh-of-concat-table-lookup ((shift natp)
                                    (x rsh-of-concat-table-p))
  :returns (rsh-expr svex-p)
  (b* (((rsh-of-concat-table x))
       (shift (lnfix shift))
       (alist-lookup (hons-get shift x.alist))
       ((when alist-lookup) (cdr alist-lookup))
       ((unless (<= x.alist-width shift))
        (raise "Error -- rsh-of-concat table should contain all indices less than alist-width")
        (svex-call 'rsh (list (svex-quote (2vec (- shift x.alist-width))) x.tail))))
    (svex-rsh (- shift x.alist-width) x.tail)))

(define svex-to-rsh-of-concat-accumulate
  ((width natp "Number of bits remaining to accumulate")
   (offset natp "Current offset from the top-level concat")
   (local-offset natp "Offset from the current tail of the concatenation")
   (concat svex-p "Current tail of the concatenation")
   (acc rsh-of-concat-alist-p "Accumulated alist"))
  :returns (acc-final rsh-of-concat-alist-p)
  :measure (nfix width)
  (b* (((when (zp width))
        (rsh-of-concat-alist-fix acc))
       (acc (hons-acons (lnfix offset)
                        (svex-rsh local-offset concat)
                        acc)))
    (svex-to-rsh-of-concat-accumulate
     (1- width) (+ 1 (lnfix offset)) (+ 1 (lnfix local-offset)) concat acc))
  ///
  (defret lookup-exists-in-svex-to-rsh-of-concat-accumulate
    (iff (hons-assoc-equal k acc-final)
         (or (and (integerp k)
                  (<= (nfix offset) k)
                  (< k (+ (nfix offset) (nfix width))))
             (hons-assoc-equal k (rsh-of-concat-alist-fix acc)))))

  (defret lookup-in-svex-to-rsh-of-concat-accumulate
    (equal (hons-assoc-equal k acc-final)
           (if (and (integerp k)
                    (<= (nfix offset) k)
                    (< k (+ (nfix offset) (nfix width))))
               (cons k (svex-rsh (+ (nfix local-offset)
                                    (- k (nfix offset)))
                                 concat))
             (hons-assoc-equal k (rsh-of-concat-alist-fix acc))))))






(define svex-to-rsh-of-concat-table-aux ((x svex-p)
                                         (offset natp)
                                         (acc rsh-of-concat-alist-p))
  :returns (rsh-table rsh-of-concat-table-p)
  :measure (svex-count x)
  :prepwork (;; (local (defthm equal-of-len
             ;;          (implies (syntaxp (quotep y))
             ;;                   (equal (equal (len x) y)
             ;;                          (if (zp y)
             ;;                              (and (equal y 0) (atom x))
             ;;                            (and (consp x)
             ;;                                 (equal (len (cdr x)) (1- y))))))))
             (local (defthm nth-expand
                      (implies (syntaxp (quotep n))
                               (equal (nth n x)
                                      (if (zp n)
                                          (car x)
                                        (nth (1- n) (cdr x)))))))
             (local (in-theory (disable nth))))

  (b* (((fun (end x offset acc))
        (make-rsh-of-concat-table
         :alist (make-fast-alist (rsh-of-concat-alist-fix acc))
         :alist-width offset :tail x)))
    (svex-case x
      :call (b* (((unless (and (eq x.fn 'concat)
                               (eql (len x.args) 3)))
                  (end x offset acc))
                 (w (first x.args)))
              (svex-case w
                :quote (b* (((unless (2vec-p w.val)) (end x offset acc))
                            (wval (2vec->val w.val))
                            ((unless (<= 0 wval)) (end x offset acc))
                            (acc (svex-to-rsh-of-concat-accumulate
                                  wval offset 0 x acc)))
                         (svex-to-rsh-of-concat-table-aux
                          (third x.args) (+ wval (lnfix offset)) acc))
                :otherwise (end x offset acc)))
      :otherwise (end x offset acc)))
  ///
  (local (defret alist-width-of-svex-to-rsh-of-concat-table-aux
           (<= (nfix offset)
               (rsh-of-concat-table->alist-width rsh-table))
           ;; :hints (("goal" :induct (svex-to-rsh-of-concat-table-aux x offset acc)
           ;;          :expand ((svex-to-rsh-of-concat-table-aux x offset acc))))
           :rule-classes :linear))
  (local (defret lookup-in-svex-to-rsh-of-concat-table-aux-alist
           (iff (hons-assoc-equal k (rsh-of-concat-table->alist rsh-table))
                (or (hons-assoc-equal k (rsh-of-concat-alist-fix acc))
                    (and (integerp k)
                         (<= (nfix offset) k)
                         (< k (rsh-of-concat-table->alist-width rsh-table)))))))
  (local (defret lookup-preserved-of-svex-to-rsh-of-concat-table-aux-alist
           (implies (not (and (integerp k)
                              (<= (nfix offset) k)
                              ;; (< k (rsh-of-concat-table->alist-width rsh-table))
                              ))
                    (equal (hons-assoc-equal k (rsh-of-concat-table->alist rsh-table))
                           (hons-assoc-equal k (rsh-of-concat-alist-fix acc))))))

  (defret lookup-in-svex-to-rsh-of-concat-table-aux
    (implies (and (integerp k)
                  (<= (nfix offset) k)
                  (not (hons-assoc-equal k (rsh-of-concat-alist-fix acc))))
             (equal (svex-eval (rsh-of-concat-table-lookup k rsh-table) env)
                    (4vec-rsh (2vec (- k (nfix offset))) (svex-eval x env))))
    :hints(("Goal" :induct t
            ;; :in-theory (enable svex-apply svexlist-eval
            ;;                    rsh-of-concat-table-lookup)
            )
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable svex-apply svexlist-eval)))
           (and stable-under-simplificationp
                '(:in-theory (enable rsh-of-concat-table-lookup
                                     svex-apply svexlist-eval)))))

  (defret svex-vars-of-lookup-in-svex-to-rsh-of-concat-table-aux
    (implies (and (not (member v (svex-vars x)))
                  (not (hons-assoc-equal (nfix k) (rsh-of-concat-alist-fix acc))))
             (not (member v (svex-vars (rsh-of-concat-table-lookup k rsh-table)))))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable rsh-of-concat-table-lookup))))))

(define svex-to-rsh-of-concat-table ((x svex-p "concat term"))
  :returns (rsh-table rsh-of-concat-table-p)
  (svex-to-rsh-of-concat-table-aux x 0 nil)
  ///
  (defret lookup-in-svex-to-rsh-of-concat-table
    (implies (natp k)
             (equal (svex-eval (rsh-of-concat-table-lookup k rsh-table) env)
                    (4vec-rsh (2vec k) (svex-eval x env)))))

  (defret svex-vars-of-lookup-in-svex-to-rsh-of-concat-table
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars (rsh-of-concat-table-lookup k rsh-table))))))

  (memoize 'svex-to-rsh-of-concat-table))


(def-svex-rewrite rsh-of-concat-less
  :lhs (rsh sh (concat w x y))
  :checks ((svex-quoted-index-p sh)
           (svex-quoted-index-p w)
           (<= (2vec->val (svex-quote->val w)) (2vec->val (svex-quote->val sh)))
           (bind res (rsh-of-concat-table-lookup
                      (- (2vec->val (svex-quote->val sh)) (2vec->val (svex-quote->val w)))
                      (svex-to-rsh-of-concat-table y))))
  :rhs res)

(def-svex-rewrite partsel-of-concat
  :lhs (partsel lsb width (concat w x y))
  :checks ((svex-quoted-index-p lsb)
           (svex-quoted-index-p w)
           (<= (2vec->val (svex-quote->val w)) (2vec->val (svex-quote->val lsb)))
           (bind res (rsh-of-concat-table-lookup
                      (- (2vec->val (svex-quote->val lsb)) (2vec->val (svex-quote->val w)))
                      (svex-to-rsh-of-concat-table y))))
  ;; Note. The rsh-of-concat-table-lookup strategy pre-computes and caches
  ;; lookups into a nest of concatenations.  The res here will be a RSH of some
  ;; tail of the concats.  Then, the partsel-of-rsh rule will ultimately turn this in to 
  ;; (partsel shamt width tail).
  :rhs (partsel 0 width res)
  :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
                                    4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
                                    4vec-index-p svex-eval-when-2vec-p-of-minval))
         (svex-generalize-lookups)
         (logbitp-reasoning)))

(def-svex-rewrite partsel-of-concat-1
  :lhs (partsel lsb width (concat w x y))
  :checks ((svex-quoted-index-p lsb)
           (svex-quoted-index-p width)
           (svex-quoted-index-p w)
           (<= (+ (2vec->val (svex-quote->val width))
                  (2vec->val (svex-quote->val lsb)))
               (2vec->val (svex-quote->val w))))
  :rhs (partsel lsb width x)
  :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
                                    4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
                                    4vec-index-p svex-eval-when-2vec-p-of-minval))
         (svex-generalize-lookups)
         (logbitp-reasoning)))


;; (def-svex-rewrite partsel-of-concat-2
;;   :lhs (partsel lsb width (concat w x y))
;;   :checks ((svex-quoted-index-p lsb)
;;            (svex-quoted-index-p width)
;;            (svex-quoted-index-p w)
;;            (<= (2vec->val (svex-quote->val w))
;;                (2vec->val (svex-quote->val lsb)))
;;            (bind new-lsb (svex-quote (2vec (- (2vec->val (svex-quote->val lsb))
;;                                               (2vec->val (svex-quote->val w)))))))
;;   :rhs (partsel new-lsb width y)
;;   :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
;;                                     4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
;;                                     4vec-index-p svex-eval-when-2vec-p-of-minval))
;;          (svex-generalize-lookups)
;;          (logbitp-reasoning)))

;; (def-svex-rewrite rsh-of-concat-less
;;   :lhs (rsh sh (concat w x y))
;;   :checks ((svex-quoted-index-p sh)
;;            (svex-quoted-index-p w)
;;            (<= (2vec->val (svex-quote->val w)) (2vec->val (svex-quote->val sh)))
;;            (bind sh1 (svex-quote (2vec (- (2vec->val (svex-quote->val sh)) (2vec->val (svex-quote->val w)))))))
;;   :rhs (rsh sh1 y)
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-rsh))
;;          (bitops::logbitp-reasoning :prune-examples nil)))





;; (define svex-meta-rsh-of-concat ((mask 4vmask-p)
;;                                  (args svexlist-p)
;;                                  localp)
;;   ;; This replaces rsh-of-concat-less, hopefully with better performance.  If
;;   ;; necessary we can compute a lookup table of some sort for concatenations.
;;   :ignore-ok t
;;   :irrelevant-formals-ok t
;;   :returns (mv (successp booleanp)
;;                (pat (iff (svex-p pat) successp))
;;                (subst svex-alist-p))
;;   (b* (((mv ok subst) (svexlist-unify '(shift (concat width first rest)) args nil))
;;        ((unless ok) (mv nil nil nil))
;;        (shift (svex-lookup 'shift subst))
;;        (width (svex-lookup 'width subst))
;;        (rest (svex-lookup 'rest subst))
;;        (shval (svex-case shift :quote (and (2vec-p shift.val)
;;                                            (2vec->val shift.val))
;;                 :otherwise nil))
;;        (wval (svex-case width :quote (and (2vec-p width.val)
;;                                           (2vec->val width.val))
;;                :otherwise nil))
;;        ((unless (and shval wval
;;                      (<= 0 shval)
;;                      (<= 0 wval)
;;                      (< wval shval)))
;;         (mv nil nil nil))
;;        (subst (rsh-of-concat-meta-aux (- shval wval) rest)))
;;     (mv t '(rsh shift x) subst))
;;   ///
;;   (DEFTHM
;;    SVEX-META-RSH-OF-CONCAT-CORRECT
;;    (B*
;;       (((MV OK PAT SUBST)
;;         (SVEX-META-RSH-OF-CONCAT MASK ARGS LOCALP)))
;;       (IMPLIES OK
;;                (EQUAL (4VEC-MASK MASK
;;                                  (SVEX-EVAL PAT (SVEX-ALIST-EVAL SUBST ENV)))
;;                       (4VEC-MASK MASK
;;                                  (SVEX-APPLY 'RSH
;;                                              (SVEXLIST-EVAL ARGS ENV))))))
;;    :HINTS (("Goal" :IN-THEORY (ENABLE 4VEC-RSH 4VEC-CONCAT SVEX-APPLY))))
;;   (DEFFIXEQUIV SVEX-META-RSH-OF-CONCAT)
;;   (DEFTHM SVEX-META-RSH-OF-CONCAT-NO-NEW-VARS
;;           (B* (((MV ?OK ?PAT SUBST)
;;                 (SVEX-META-RSH-OF-CONCAT MASK ARGS LOCALP)))
;;               (IMPLIES (NOT (MEMBER V (SVEXLIST-VARS ARGS)))
;;                        (NOT (MEMBER V (SVEX-ALIST-VARS SUBST)))))
;;           :HINTS ((AND STABLE-UNDER-SIMPLIFICATIONP
;;                        '(:IN-THEORY (ENABLE SVEX-VARS)))))
;;   (DEFTHM SVEX-META-RSH-OF-CONCAT-RHS-VARS-BOUND
;;           (B* (((MV OK PAT SUBST)
;;                 (SVEX-META-RSH-OF-CONCAT MASK ARGS LOCALP)))
;;               (IMPLIES OK
;;                        (SUBSETP (SVEX-VARS PAT)
;;                                 (SVEX-ALIST-KEYS SUBST)))))
;;   (TABLE SVEX-REWRITE 'RSH
;;          (CONS 'SVEX-META-RSH-OF-CONCAT
;;                (CDR (ASSOC 'RSH
;;                            (TABLE-ALIST 'SVEX-REWRITE WORLD))))))

;; (def-svex-rewrite rsh-of-concat-less
;;   :lhs (rsh sh (concat w x y))
;;   :checks ((svex-quoted-index-p sh)
;;            (svex-quoted-index-p w)
;;            (<= (2vec->val (svex-quote->val w)) (2vec->val (svex-quote->val sh)))
;;            (bind sh1 (svex-quote (2vec (- (2vec->val (svex-quote->val sh)) (2vec->val (svex-quote->val w)))))))
;;   :rhs (rsh sh1 y)
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-concat 4vec-mask 4vec-rsh))
;;          (bitops::logbitp-reasoning :prune-examples nil)))



(def-svex-rewrite rsh-of-rsh
  :lhs (rsh sh1 (rsh sh2 x))
  :checks ((svex-quoted-index-p sh1)
           (svex-quoted-index-p sh2)
           (bind sh3 (svex-quote (2vec (+ (2vec->val (svex-quote->val sh1)) (2vec->val (svex-quote->val sh2)))))))
  :rhs (rsh sh3 x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-mask 4vec-rsh 4vec-lsh 4vec-shift-core))
         (bitops::logbitp-reasoning :prune-examples nil)))

(def-svex-rewrite lsh-to-rsh
  :lhs (lsh sh x)
  :rhs (rsh (u- sh) x)
  :hints(("Goal" :in-theory (enable 4vec-lsh 4vec-rsh 4vec-shift-core 4vec-uminus svex-apply))))

(def-svex-rewrite rsh-to-concat
  :lhs (rsh sh x)
  :checks ((svex-quoted-int-p sh)
           (< (2vec->val (svex-quote->val sh)) 0)
           (bind w (svex-quote (2vec (- (2vec->val (svex-quote->val sh)))))))
  :rhs (concat w 0 x)
  :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-concat svex-apply))))






;; (def-svex-rewrite rsh-of-bitnot
;;   :lhs (rsh n (bitnot x))
;;   :checks ((svex-quoted-int-p n)
;;            (<= 0 (2vec->val (svex-quote->val n))))
;;   :rhs (bitnot (rsh n x))
;;   :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-bitnot 3vec-bitnot 3vec-fix svex-apply))))

(def-svex-rewrite zerox-under-mask-1
  :lhs (zerox w x)
  :checks ((svex-quoted-index-p w)
           (not (sparseint-test-bitand (sparseint-concatenate (2vec->val (svex-quote->val w)) -1 0) mask)))
  :rhs 0
  :hints(("Goal" :in-theory (enable svex-apply 4vec-zero-ext 4vec-mask))
         (bitops::logbitp-reasoning :prune-examples nil)))

(def-svex-rewrite zerox-under-mask-2
  :lhs (zerox w x)
  :checks ((svex-quoted-index-p w)
           (not (sparseint-test-bitand (sparseint-concatenate (2vec->val (svex-quote->val w)) 0 -1) mask)))
  :rhs x
  :hints(("Goal" :in-theory (enable svex-apply 4vec-zero-ext 4vec-mask))
         (bitops::logbitp-reasoning :prune-examples nil)))

(def-svex-rewrite signx-under-mask
  :lhs (signx w x)
  :checks ((svex-quoted-index-p w)
           (not (sparseint-test-bitand (sparseint-concatenate (2vec->val (svex-quote->val w)) 0 -1) mask)))
  :rhs x
  :hints(("Goal" :in-theory (enable svex-apply 4vec-sign-ext 4vec-mask))
         (bitops::logbitp-reasoning :prune-examples nil)))

(defmacro hidelet (term)
  `(hide (let () ,term)))





(defsection bit?-rewrites
  (local (in-theory (disable bitops::logand-natp-type-2
                             bitops::logior-natp-type
                             bitops::lognot-natp
                             (:t negp)
                             (:t svexlist-unify)
                             (:t svex-eval)
                             (:t svex-kind)
                             svex-eval-when-quote
                             bitops::logand-natp-type-1
                             4vec->lower-when-2vec-p
                             bitops::logbitp-nonzero-of-bit
                             3vec-p-implies-bits
                             bitops::logbitp-when-bit
                             bitops::logbitp-when-bitmaskp
                             3vec-p-of-eval-when-3valued-syntaxp
                             not)))

  (def-svex-rewrite bit?-of-1s
    :lhs (bit? c x y)
    :checks (;; c is 1 in all the care bits
             (not (sparseint-test-bitandc2 mask (s4vec->upper (svex-s4xeval c))))
             (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval c)))))
    :rhs x
    :hints(("Goal" :in-theory (enable svex-apply 4vec-bit? 3vec-bit?
                                      4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
           (bitops::logbitp-reasoning
            ;; :prune-examples nil
            :add-hints (:in-theory (enable* bitops::bool->bit
                                            ;; bitops::logbitp-case-splits
                                    logbitp-when-4vec-[=-svex-eval-strong)))))

  (def-svex-rewrite bit?-of-0s
    :lhs (bit? c x y)
    :checks (;; c is 0 in all the care bits
             (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval c))))
             (not (sparseint-test-bitand mask (s4vec->lower (svex-s4xeval c)))))
    :rhs y
    :hints(("Goal" :in-theory (enable svex-apply 4vec-bit? 3vec-bit?
                                      4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
           (bitops::logbitp-reasoning
            ;; :prune-examples nil
            :add-hints (:in-theory (enable* bitops::bool->bit
                                            bitops::logbitp-case-splits
                                            logbitp-when-4vec-[=-svex-eval-strong))))))




(defsection bit?!-rewrites
  (local (in-theory (disable bitops::logand-natp-type-2
                             bitops::logior-natp-type
                             bitops::lognot-natp
                             (:t negp)
                             (:t svexlist-unify)
                             (:t svex-eval)
                             (:t svex-kind)
                             ;; svex-eval-when-quote
                             bitops::logand-natp-type-1
                             4vec->lower-when-2vec-p
                             bitops::logbitp-nonzero-of-bit
                             3vec-p-implies-bits
                             bitops::logbitp-when-bit
                             bitops::logbitp-when-bitmaskp
                             3vec-p-of-eval-when-3valued-syntaxp
                             not)))

  (def-svex-rewrite bit?!-of-quoted-neg1
    :lhs (bit?! c x y)
    :checks ((svex-case c :quote)
             (not (sparseint-test-bitandc2 mask (int-to-sparseint (4vec->upper (svex-quote->val c)))))
             (not (sparseint-test-bitandc2 mask (int-to-sparseint (4vec->lower (svex-quote->val c))))))
    :rhs x
    :hints(("Goal" :in-theory (enable svex-apply 4vec-bit?! 4vec-mask))
           (bitops::logbitp-reasoning
            ;; :prune-examples nil
            :add-hints (:in-theory (enable* bitops::bool->bit
                                            bitops::logbitp-case-splits
                                            logbitp-when-4vec-[=-svex-eval-strong)))))

  (def-svex-rewrite bit?!-of-quoted-non1
    :lhs (bit?! c x y)
    :checks ((svex-case c :quote)
             (not (sparseint-test-bitand mask (sparseint-bitand
                                               (int-to-sparseint (4vec->upper (svex-quote->val c)))
                                               (int-to-sparseint (4vec->lower (svex-quote->val c)))))))
    :rhs y
    :hints(("Goal" :in-theory (enable svex-apply 4vec-bit?! 4vec-mask))
           (bitops::logbitp-reasoning
            ;; :prune-examples nil
            :add-hints (:in-theory (enable* bitops::bool->bit
                                            bitops::logbitp-case-splits
                                            logbitp-when-4vec-[=-svex-eval-strong)))))

  (def-svex-rewrite bit?!-of-xeval-neg1
    :lhs (bit?! c x y)
    :checks ((let cval (svex-s4xeval c))
             (not (sparseint-test-bitandc2 mask (s4vec->upper cval)))
             (not (sparseint-test-bitandc2 mask (s4vec->lower cval))))
    :rhs x
    :hints(("Goal" :in-theory (enable svex-apply 4vec-bit?! 4vec-mask))
           (bitops::logbitp-reasoning
            ;; :prune-examples nil
            :add-hints (:in-theory (enable* bitops::bool->bit
                                            bitops::logbitp-case-splits
                                            logbitp-when-4vec-[=-svex-eval-strong)))))

  (def-svex-rewrite bit?!-of-xeval-0/z
    :lhs (bit?! c x y)
    :checks ((let cval (svex-s4xeval c))
             ;; The cval bits under the mask may be (0 . 1) (z) or 0
             ;; so we just need to check that the upper under the mask is 0.
             (not (sparseint-test-bitand mask (s4vec->upper cval))))
    :rhs y
    :hints(("Goal" :in-theory (enable svex-apply 4vec-bit?! 4vec-mask))
           (bitops::logbitp-reasoning
            ;; :prune-examples nil
            :add-hints (:in-theory (enable* bitops::bool->bit
                                            bitops::logbitp-case-splits
                                            logbitp-when-4vec-[=-svex-eval-strong))))))


(def-svex-rewrite bitand-under-mask-1
  :lhs (bitand x y)
  :checks (;; x is 1 in all the care bits
           (not (sparseint-test-bitandc2 mask (s4vec->upper (svex-s4xeval x))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval x)))))
  :rhs (unfloat y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bitand 3vec-bitand
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite bitand-under-mask-2
  :lhs (bitand x y)
  :checks (;; y is 1 in all the care bits
           (not (sparseint-test-bitandc2 mask (s4vec->upper (svex-s4xeval y))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval y)))))
  :rhs (unfloat x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bitand 3vec-bitand
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite resand-under-mask-1
  :lhs (resand x y)
  :checks (;; x is z in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval x))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval x)))))
  :rhs y
  :hints(("Goal" :in-theory (enable svex-apply 4vec-resand
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite resand-under-mask-2
  :lhs (resand x y)
  :checks (;; y is z in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval y))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval y)))))
  :rhs x
  :hints(("Goal" :in-theory (enable svex-apply 4vec-resand
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite bitor-under-mask-1
  :lhs (bitor x y)
  :checks (;; x is 0 in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval x))))
           (not (sparseint-test-bitand mask (s4vec->lower (svex-s4xeval x)))))
  :rhs (unfloat y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bitor 3vec-bitor
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite bitor-under-mask-2
  :lhs (bitor x y)
  :checks (;; y is 0 in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval y))))
           (not (sparseint-test-bitand mask (s4vec->lower (svex-s4xeval y)))))
  :rhs (unfloat x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bitor 3vec-bitor
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite resor-under-mask-1
  :lhs (resor x y)
  :checks (;; x is z in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval x))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval x)))))
  :rhs y
  :hints(("Goal" :in-theory (enable svex-apply 4vec-resor
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite resor-under-mask-2
  :lhs (resor x y)
  :checks (;; y is z in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval y))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval y)))))
  :rhs x
  :hints(("Goal" :in-theory (enable svex-apply 4vec-resor
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))


(def-svex-rewrite res-under-mask-1
  :lhs (res x y)
  :checks (;; x is z in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval x))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval x)))))
  :rhs y
  :hints(("Goal" :in-theory (enable svex-apply 4vec-res
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite res-under-mask-2
  :lhs (res x y)
  :checks (;; y is z in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval y))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval y)))))
  :rhs x
  :hints(("Goal" :in-theory (enable svex-apply 4vec-res
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))



(def-svex-rewrite res-same-1
  :lhs (res x x)
  :rhs x
  :hints(("Goal" :in-theory (enable svex-apply 4vec-res))))

(def-svex-rewrite res-same-2
  :lhs (res x (res x y))
  :rhs (res x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-res 4vec-mask))
         (bitops::logbitp-reasoning
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits)))))




(define res-combine-cond ((x s4vec-p) (y s4vec-p) (mask 4vmask-p))
  (b* (((s4vec x))
       ((s4vec y)))
    ;; For all care bits. either x or y is z, or else x and y are the same and neither is x.
    ;; This is equivalent to (bitwise)
    ;;   x is z OR y is z OR (x is 1 and y is 1) OR (x is 0 and y is 0).
    ;; (~x.upper and x.lower) OR (~y.upper and y.lower)
    ;; OR (x.upper and x.lower and y.upper and y.lower)
    ;; OR (~x.upper and ~x.lower and ~y.upper and ~y.lower).
    ;; which is the same as:
    ;; (~x.upper and x.lower) OR (~y.upper and y.lower)
    ;; OR (x.lower  and y.lower)
    ;; OR (~x.upper and ~y.upper).
    ;; What order to do these in, I have no idea.
    (not (sparseint-test-bitandc2
          (4vmask-fix mask)
          (sparseint-bitor (sparseint-bitor (sparseint-bitandc1 x.upper x.lower)
                                            (sparseint-bitnor x.upper y.upper))
                           (sparseint-bitor (sparseint-bitandc1 y.upper y.lower)
                                            (sparseint-bitand x.lower y.lower))))))
  ///

  (defthm res-combine-cond-commutative
    (equal (res-combine-cond x y mask)
           (res-combine-cond y x mask))
    :rule-classes ((:rewrite :loop-stopper ((x y)))))
  (deffixequiv res-combine-cond))

(define 4vec-res-must-choose-mask ((x s4vec-p)
                                   (y s4vec-p)
                                   (mask 4vmask-p))
  :prepwork ((local (in-theory (enable logbitp-when-4vec-[=-svex-eval-strong))))
  ;; determines bits where (res x y) is known to equal x but not known to equal
  ;; y, and mask is active.  On other bits, it's ok to choose y as long as
  ;; res-combine-cond holds.
  :returns (mask sparseint-p)
  (b* (((s4vec x)) ((s4vec y)))
    (sparseint-bitand (4vmask-fix mask)
                      (sparseint-bitand
                       (sparseint-bitor (sparseint-bitxor x.upper y.upper)
                                        (sparseint-bitxor x.lower y.lower)) ;; x != y
                       (sparseint-bitorc2 x.upper x.lower))))  ;; x is not z
  ///
  (local (in-theory (disable acl2::zip-open not
                             4vec->lower-when-2vec-p
                             bitops::logior-natp-type
                             bitops::logand->=-0-linear-2
                             bitops::upper-bound-of-logand
                             bitops::logand-natp-type-2
                             bitops::lognot-natp
                             default-<-1
                             bitops::logior->=-0-linear
                             bitops::logior-<-0-linear-1)))

  (defthm 4vec-res-must-choose-mask-correct-bit-upper
    (implies (and (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                  (not (logbitp n (sparseint-val (4vec-res-must-choose-mask
                                                  (svex-s4xeval x) (svex-s4xeval y) mask))))
                  (logbitp n (sparseint-val (4vmask-fix mask))))
             (equal (logbitp n (4vec->upper (4vec-res (svex-eval x env)
                                                      (svex-eval y env))))
                    (logbitp n (4vec->upper (svex-eval y env)))))
    :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat 4vec-res-must-choose-mask
                                      4vec-rsh 4vec-shift-core 4vec-res res-combine-cond))
           (logbitp-reasoning :prune-examples nil)
           (and stable-under-simplificationp
                '(:in-theory (enable bool->bit)))))

  (defthm 4vec-res-must-choose-mask-correct-bit-lower
    (implies (and (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                  (not (logbitp n (sparseint-val (4vec-res-must-choose-mask
                                                  (svex-s4xeval x) (svex-s4xeval y) mask))))
                  (logbitp n (sparseint-val (4vmask-fix mask))))
             (equal (logbitp n (4vec->lower (4vec-res (svex-eval x env)
                                                      (svex-eval y env))))
                    (logbitp n (4vec->lower (svex-eval y env)))))
    :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat 4vec-res-must-choose-mask
                                      4vec-rsh 4vec-shift-core 4vec-res res-combine-cond))
           (logbitp-reasoning :prune-examples nil)
           (and stable-under-simplificationp
                '(:in-theory (enable bool->bit)))))


  (local (in-theory (disable 4vec-res-must-choose-mask
                             LOGBITP-WHEN-4VEC-[=-SVEX-EVAL-STRONG)))

  ;; (defthm 4vec-res-must-choose-mask-correct-range
  ;;   (implies (and (res-combine-cond (svex-xeval x) (svex-xeval y) mask)
  ;;                 (equal 0 (loghead width (logtail lsb (4vec-res-must-choose-mask
  ;;                                                       (svex-xeval x) (svex-xeval y) mask))))
  ;;                 (natp lsb) (natp width))
  ;;            (equal (4vec-mask mask (4vec-res (svex-eval x env)
  ;;                                             (svex-eval y env)))
  ;;                   (4vec-mask mask
  ;;                              (4vec-concat (2vec lsb) (4vec-res (svex-eval x env)
  ;;                                                                (svex-eval y env))
  ;;                                           (4vec-concat (2vec width)
  ;;                                                        (4vec-rsh (2vec lsb)
  ;;                                                                  (svex-eval y env))
  ;;                                                        (4vec-rsh (2vec (+ lsb width))
  ;;                                                                  (4vec-res (svex-eval x env)
  ;;                                                                            (svex-eval y env))))))))
  ;;   :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat 4vec-rsh))
  ;;          (logbitp-reasoning :prune-examples nil
  ;;                             :simp-hint (:in-theory (enable* logbitp-case-splits
  ;;                                                             logbitp-when-4vec-[=-svex-eval-strong
  ;;                                                             ;; bit-n
  ;;                                                             4vec-res-must-choose-mask)))))

  (local (defthm 4vec-res-symm
           (equal (4vec-res x y)
                  (4vec-res y x))
           :hints(("Goal" :in-theory (enable 4vec-res)))
           :rule-classes ((:rewrite :loop-stopper ((x y 4vec-res))))))

  (local (defthm loghead-of-trailing-0-count
           (equal (loghead (bitops::trailing-0-count x) x) 0)
           :hints (("goal" :cases ((zip x))
                    :in-theory (enable bitops::trailing-0-count-properties)))))

  (defthm 4vec-res-must-choose-mask-correct-range
    (implies (and (equal 0 (loghead width (logtail lsb (sparseint-val
                                                        (4vec-res-must-choose-mask
                                                         (svex-s4xeval x) (svex-s4xeval y) mask)))))
                  (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                  (natp lsb) (nat-equiv lsb1 lsb) (natp width) (4vmask-p mask))
             (equal (4vec-mask (sparseint-rightshift lsb1 mask)
                               (4vec-rsh (2vec lsb)
                                         (4vec-res (svex-eval x env)
                                                   (svex-eval y env))))
                    (4vec-mask (sparseint-rightshift lsb mask)
                               (4vec-concat (2vec width)
                                            (4vec-rsh (2vec lsb)
                                                      (svex-eval y env))
                                            (4vec-rsh (2vec (+ lsb width))
                                                      (4vec-res (svex-eval x env)
                                                                (svex-eval y env)))))))
    :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat 4vec-rsh 4vec-shift-core))
           (logbitp-reasoning :prune-examples nil
                              :simp-hint (:in-theory (enable* logbitp-case-splits
                                                              logbitp-when-4vec-[=-svex-eval-strong
                                                              ;; bit-n
                                                              4vec-res-must-choose-mask)))))

  (defthm 4vec-res-must-choose-mask-correct-range-trailing-0
    (let ((width (bitops::trailing-0-count
                  (logtail lsb1 (sparseint-val
                                 (4vec-res-must-choose-mask
                                  (svex-s4xeval x) (svex-s4xeval y) mask))))))
      (implies (and (< 0 width)
                    (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                    (natp lsb) (nat-equiv lsb1 lsb) (natp width) (4vmask-p mask))
               (equal (4vec-mask (sparseint-rightshift lsb1 mask)
                                 (4vec-rsh (2vec lsb)
                                           (4vec-res (svex-eval x env)
                                                     (svex-eval y env))))
                      (4vec-mask (sparseint-rightshift lsb mask)
                                 (4vec-concat (2vec width)
                                              (4vec-rsh (2vec lsb)
                                                        (svex-eval y env))
                                              (4vec-rsh (2vec (+ lsb width))
                                                        (4vec-res (svex-eval x env)
                                                                  (svex-eval y env))))))))
      :hints(("Goal" :use ((:instance 4vec-res-must-choose-mask-correct-range
                            (width (bitops::trailing-0-count
                                    (logtail lsb1 (sparseint-val
                                                   (4vec-res-must-choose-mask
                                                    (svex-s4xeval x) (svex-s4xeval y) mask)))))))
              :in-theory (disable 4vec-res-must-choose-mask-correct-range))))

  (defthm 4vec-res-must-choose-mask-correct-range-trailing-0-2
    (let ((width (bitops::trailing-0-count
                  (logtail lsb1 (sparseint-val
                                 (4vec-res-must-choose-mask
                                  (svex-s4xeval x) (svex-s4xeval y) mask))))))
      (implies (and (< 0 width)
                    (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                    (natp lsb) (nat-equiv lsb1 lsb) (natp width) (4vmask-p mask))
               (equal (4vec-mask (sparseint-rightshift lsb1 mask)
                                 (4vec-rsh (2vec lsb)
                                           (4vec-res (svex-eval y env)
                                                     (svex-eval x env))))
                      (4vec-mask (sparseint-rightshift lsb mask)
                                 (4vec-concat (2vec width)
                                              (4vec-rsh (2vec lsb)
                                                        (svex-eval y env))
                                              (4vec-rsh (2vec (+ lsb width))
                                                        (4vec-res (svex-eval x env)
                                                                  (svex-eval y env))))))))
      :hints(("Goal" :use ((:instance 4vec-res-must-choose-mask-correct-range
                            (width (bitops::trailing-0-count
                                    (logtail lsb1 (4vec-res-must-choose-mask
                                                  (svex-s4xeval x) (svex-s4xeval y) mask))))))
              :in-theory (disable 4vec-res-must-choose-mask-correct-range))))


  ;; (defthm 4vec-res-must-choose-mask-correct-tail
  ;;   (implies (and (res-combine-cond (svex-xeval x) (svex-xeval y) mask)
  ;;                 (equal 0 (logtail lsb (4vec-res-must-choose-mask
  ;;                                        (svex-xeval x) (svex-xeval y) mask)))
  ;;                 (natp lsb))
  ;;            (equal (4vec-mask mask (4vec-res (svex-eval x env)
  ;;                                             (svex-eval y env)))
  ;;                   (4vec-mask mask
  ;;                              (4vec-concat (2vec lsb)
  ;;                                           (4vec-res (svex-eval x env)
  ;;                                                     (svex-eval y env))
  ;;                                           (4vec-rsh (2vec lsb) (svex-eval y env))))))
  ;;   :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat 4vec-rsh))
  ;;          (logbitp-reasoning :prune-examples nil
  ;;                             :simp-hint (:in-theory (enable* logbitp-case-splits
  ;;                                                             logbitp-when-4vec-[=-svex-eval-strong
  ;;                                                             ;; bit-n
  ;;                                                             4vec-res-must-choose-mask)))))

  (defthm 4vec-res-must-choose-mask-correct-tail
    (implies (and (equal 0 (logtail lsb1
                                    (sparseint-val
                                     (4vec-res-must-choose-mask
                                      (svex-s4xeval x) (svex-s4xeval y) mask))))
                  (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                  (natp lsb) (nat-equiv lsb1 lsb)
                  (4vmask-p mask))
             (equal (4vec-mask (sparseint-rightshift lsb1 mask)
                               (4vec-rsh (2vec lsb)
                                         (4vec-res (svex-eval x env)
                                                   (svex-eval y env))))
                    (4vec-mask (sparseint-rightshift lsb mask)
                               (4vec-rsh (2vec lsb) (svex-eval y env)))))
    :hints(("Goal" :in-theory (enable 4vec-mask 4vec-rsh 4vec-shift-core))
           (logbitp-reasoning :prune-examples nil
                              :simp-hint (:in-theory (enable* logbitp-case-splits
                                                              logbitp-when-4vec-[=-svex-eval-strong
                                                              ;; bit-n
                                                              4vec-res-must-choose-mask)))))

  (defthm 4vec-res-must-choose-mask-correct-tail2
    (implies (and (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                  (equal 0 (logtail lsb1 (sparseint-val
                                          (4vec-res-must-choose-mask
                                           (svex-s4xeval x) (svex-s4xeval y) mask))))
                  (natp lsb) (nat-equiv lsb1 lsb)
                  (4vmask-p mask))
             (equal (4vec-mask (sparseint-rightshift lsb1 mask)
                               (4vec-rsh (2vec lsb)
                                         (4vec-res (svex-eval y env)
                                                   (svex-eval x env))))
                    (4vec-mask (sparseint-rightshift lsb mask)
                               (4vec-rsh (2vec lsb) (svex-eval y env)))))
    :hints (("goal" :use 4vec-res-must-choose-mask-correct-tail
             :in-theory (disable 4vec-res-must-choose-mask-correct-tail))))

  (local (in-theory (enable not)))

  (defthm res-combine-cond-implies-logand-of-must-choose
    (implies (res-combine-cond x y mask)
             (equal (logand (sparseint-val (4vec-res-must-choose-mask x y mask))
                            (sparseint-val (4vec-res-must-choose-mask y x mask)))
                    0))
    :hints (("goal" :in-theory (enable res-combine-cond 4vec-res-must-choose-mask))
            (logbitp-reasoning)))

  (deffixequiv 4vec-res-must-choose-mask))
                                              
                  




(define res-to-concat ((xmask sparseint-p) ;; z-mask-mask of x
                       (ymask sparseint-p) ;; z-mask-mask of y
                       (mask 4vmask-p)
                       (offset natp)
                       (x svex-p)
                       (y svex-p)
                       (resfn fnsym-p))
  :prepwork ((local (defthmd integer-length-0
                      (equal (equal (integer-length x) 0)
                             (or (zip x)
                                 (eql x -1)))
                      :hints(("Goal" :expand ((integer-length x))))))
             ;; (local (defthm logand-by-logbitp
             ;;          (implies (and (logbitp n x)
             ;;                        (logbitp n y))
             ;;                   (not (equal 0 (logand x y))))
             ;;          :hints (("goal" :use ((:instance bitops::logbitp-of-logand
             ;;                                 (a n)))
             ;;                   :in-theory (disable bitops::logbitp-of-logand)))))
             ;; (local (defthm trailing-0-count-is-0
             ;;          (iff (equal 0 (bitops::trailing-0-count x))
             ;;               (or (zip x)
             ;;                   (logbitp 0 x)))
             ;;          :hints(("Goal" :in-theory (enable bitops::trailing-0-count)))))
             (local (defthm zip-when-integer
                      (implies (integerp x)
                               (equal (zip x) (equal x 0)))))
             (local (defthm integer-length-when-logtail-0
                      (implies (equal (logtail n x) 0)
                               (<= (integer-length x) (nfix n)))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                                         bitops::ihsext-recursive-redefs)))
                      :rule-classes :linear))
             ;; (local (defthm logtail-when-logbitp
             ;;          (implies (logbitp n x)
             ;;                   (not (equal (logtail n x) 0)))
             ;;          :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
             ;;                                             bitops::ihsext-recursive-redefs)))))
             ;; (local (defthm trailing-0-count-of-logtail-when-logbitp
             ;;          (implies (logbitp n x)g
             ;;                   (equal (bitops::trailing-0-count (logtail n x)) 0))
             ;;          :hints(("Goal" :in-theory (enable bitops::trailing-0-count)))))
             (local (in-theory (e/d* (acl2::arith-equiv-forwarding)
                                     (bitops::logtail-identity
                                      bitops::logior-natp-type
                                      svex-eval-when-2vec-p-of-minval
                                      bitops::logbitp-when-bit
                                      4vec->lower-when-2vec-p
                                      acl2::zip-open
                                      bitops::trailing-0-count-bound
                                      bitops::trailing-0-count-properties
                                      bitops::logtail-natp
                                      acl2::natp-posp
                                      len)))))

  :verify-guards nil
  :measure (nfix (- (min (integer-length (sparseint-val xmask))
                         (integer-length (sparseint-val ymask)))
                    (nfix offset)))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable nfix integer-length-0))))
  :guard (and (equal 0 (logand (sparseint-val xmask)
                               (sparseint-val ymask)))
              (<= (bitops::trailing-0-count-from (sparseint-val xmask) offset)
                  (bitops::trailing-0-count-from (sparseint-val ymask) offset)))
  :returns (concat svex-p)
  (b* ((x (svex-fix x))
       (y (svex-fix y))
       (?mask (4vmask-fix mask))
       (offset (lnfix offset))
       (resfn (mbe :logic (fnsym-fix resfn) :exec resfn))
       ((when (<= (sparseint-length xmask) offset))
        (if (eql 1 (sparseint-bit offset xmask))
            (svex-rsh offset x)
          (svex-rsh offset y)))
       ((when (<= (sparseint-length ymask) offset))
        (if (eql 1 (sparseint-bit offset ymask))
            (svex-rsh offset y)
          (svex-rsh offset x)))
       (ycount (sparseint-trailing-0-count-from ymask offset))
       ((unless (posp ycount))
        (svex-rsh offset (svex-call resfn (list x y)))))
    (svex-concat ycount (svex-rsh offset x)
                 (res-to-concat (sparseint-fix ymask)
                                (sparseint-fix xmask)
                                mask
                                (+ offset ycount)
                                y x resfn)))
  ///

  (local (defthm trailing-0-count-is-0
           (iff (equal 0 (bitops::trailing-0-count x))
                (or (zip x)
                    (logbitp 0 x)))
           :hints(("Goal" :in-theory (enable bitops::trailing-0-count)))))

  (local (defthm logbitp-of-trailing-0-count
           (implies (not (zip x))
                    (logbitp (bitops::trailing-0-count x) x))
           :hints(("Goal" :in-theory (enable bitops::trailing-0-count)))))

  (local (defthm trailing-0-count-of-logtail-trailing-0-count
           (equal (bitops::trailing-0-count
                   (logtail (bitops::trailing-0-count x) x))
                  0)
           :hints (("goal" :cases ((zip x))))))

  (local (defthm trailing-0-count-of-logtail-trailing-0-count-offset
           (implies (natp offset)
                    (equal (bitops::trailing-0-count
                            (logtail (+ offset (bitops::trailing-0-count (logtail offset x))) x))
                           0))
           :hints (("goal" :use ((:instance trailing-0-count-of-logtail-trailing-0-count
                                  (x (logtail offset x))))
                    :in-theory (disable trailing-0-count-of-logtail-trailing-0-count)))))

  (verify-guards res-to-concat)
  
  (local (defthmd 4vec-mask-of-4vec-concat
           (implies (4vec-index-p width)
                    (equal (4vec-mask mask (4vec-concat width x y))
                           (4vec-concat width (4vec-mask mask x)
                                        (4vec-mask (sparseint-rightshift (2vec->val width)
                                                                  (4vmask-fix mask))
                                                   y))))
           :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat))
                  (logbitp-reasoning))))

  (local (defthm logbitp-past-integer-length-1
           (implies (and (<= (integer-length x) (nfix offset))
                         (acl2::rewriting-positive-literal `(logbitp ,offset ,x)))
                    (equal (logbitp offset x)
                           (not (equal 0 (logtail offset x)))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))))

  (local (defthm logbitp-past-integer-length-2
           (implies (and (<= (integer-length x) (nfix offset))
                         (acl2::rewriting-negative-literal `(logbitp ,offset ,x)))
                    (equal (logbitp offset x)
                           (equal -1 (logtail offset x))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))))

  (local (in-theory (disable res-combine-cond-implies-logand-of-must-choose)))

  (local (defthm res-must-choose-mask-neg1-when-res-combine-cond
           (implies (and (equal -1 (logtail offset (sparseint-val (4vec-res-must-choose-mask y x mask))))
                         (res-combine-cond x y mask))
                    (equal (logtail offset (sparseint-val (4vec-res-must-choose-mask x y mask))) 0))
           :hints (("goal" :use res-combine-cond-implies-logand-of-must-choose
                    :in-theory (disable res-combine-cond-implies-logand-of-must-choose))
                   (logbitp-reasoning :prune-examples nil))))

  (local (defun 4vmask-equal (x y)
           (sparseint-equal (4vmask-fix x) (4vmask-fix y))))

  (local (defequiv 4vmask-equal))

  (local (defcong 4vmask-equal equal (4vec-mask mask x) 1
           :hints(("Goal" :in-theory (enable 4vec-mask)))))

  (local (defthm sparseint-rightshift-compose-under-4vmask-equal
           (4vmask-equal (sparseint-rightshift n (sparseint-rightshift m x))
                         (sparseint-rightshift (+ (nfix n) (nfix m)) x))))

  (local (defthm sparseint-rightshift-0-under-4vmask-equal
           (4vmask-equal (sparseint-rightshift 0 x)
                         (sparseint-fix x))))

  ;; (local (defthm loghead-of-trailing-0-count-forward
  ;;          (implies (< 0 (bitops::trailing-0-count x))
  ;;                   (equal (loghead (bitops::trailing-0-count x) x) 0))
  ;;          :rule-classes :forward-chaining))

  (defthm res-to-concat-correct
    (implies (and (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                  (equal xmask (4vec-res-must-choose-mask (svex-s4xeval x) (svex-s4xeval y) mask))
                  (equal ymask (4vec-res-must-choose-mask (svex-s4xeval y) (svex-s4xeval x) mask))
                  (equal resfn 'res)
                  (4vmask-p mask))
             (equal (4vec-mask (sparseint-rightshift offset mask)
                               (svex-eval (res-to-concat xmask ymask mask offset x y resfn) env))
                    (4vec-mask (sparseint-rightshift offset mask)
                               (4vec-rsh (2vec (nfix offset))
                                         (svex-apply resfn
                                                     (list (svex-eval x env)
                                                           (svex-eval y env)))))))
    :hints (("goal" :induct (res-to-concat xmask ymask mask offset x y resfn)
             :expand ((:free (xmask ymask resfn)
                       (res-to-concat xmask ymask mask offset x y resfn)))
             :in-theory (enable svex-apply))
            (and stable-under-simplificationp
                 '(:in-theory (enable 4vec-mask-of-4vec-concat
                                      4vec-index-p)))))

  

  (deffixequiv res-to-concat
    :hints(("Goal" :induct (res-to-concat xmask ymask mask offset x y resfn))
           '(:expand ((:free (xmask ymask mask)
                       (res-to-concat xmask ymask mask offset x y resfn))
                      (:free (offset resfn)
                       (res-to-concat xmask ymask mask offset x y resfn))
                      (:free (x y)
                       (res-to-concat xmask ymask mask offset x y resfn))))))
  


  (defthm res-to-concat-correct-0-offset
    (implies (and (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
                  (equal xmask (4vec-res-must-choose-mask (svex-s4xeval x) (svex-s4xeval y) mask))
                  (equal ymask (4vec-res-must-choose-mask (svex-s4xeval y) (svex-s4xeval x) mask))
                  (equal resfn 'res))
             (equal (4vec-mask mask (svex-eval (res-to-concat xmask ymask mask 0 x y resfn) env))
                    (4vec-mask mask
                               (svex-eval (svex-call resfn (list x y)) env))))
    :hints (("goal" :use ((:instance res-to-concat-correct (offset 0) (mask (4vmask-fix mask))))
             :in-theory (disable res-to-concat-correct))))

  (defthm res-to-concat-no-new-vars
    (implies (and (not (member-equal v (svex-vars x)))
                  (not (member-equal v (svex-vars y))))
             (not (member-equal v (svex-vars (res-to-concat xmask ymask mask offset x y resfn)))))
    :hints (("goal" :induct (res-to-concat xmask ymask mask offset x y resfn)
             :expand ((:free (xmask ymask) (res-to-concat xmask ymask mask offset x y resfn)))
             :in-theory (enable svexlist-vars svex-vars)))))



(define res-to-concat-top ((x svex-p) (y svex-p) (mask 4vmask-p) (resfn fnsym-p))
  :returns (res svex-p)
  :guard (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
  (b* ((mask (4vmask-fix mask))
       (xval (svex-s4xeval x))
       (yval (svex-s4xeval y))
       (xmask (4vec-res-must-choose-mask xval yval mask))
       (ymask (4vec-res-must-choose-mask yval xval mask)))
    (if (or (sparseint-equal xmask 0)
            (< (sparseint-trailing-0-count xmask)
               (sparseint-trailing-0-count ymask)))
        (res-to-concat xmask ymask mask 0 x y resfn)
      (res-to-concat ymask xmask mask 0 y x resfn)))
  ///

  (deffixequiv res-to-concat-top)

  (local (defthm 4vec-rsh-0
           (equal (4vec-rsh 0 x)
                  (4vec-fix x))
           :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-res-symm
           (equal (4vec-res x y)
                  (4vec-res y x))
           :hints(("Goal" :in-theory (enable 4vec-res)))
           :rule-classes ((:rewrite :loop-stopper ((x y 4vec-res))))))

  ;; (local (defthm 4vec-resand-symm
  ;;          (equal (4vec-resand x y)
  ;;                 (4vec-resand y x))
  ;;          :hints(("Goal" :in-theory (enable 4vec-resand)))
  ;;          :rule-classes ((:rewrite :loop-stopper ((x y 4vec-resand))))))

  ;; (local (defthm 4vec-resor-symm
  ;;          (equal (4vec-resor x y)
  ;;                 (4vec-resor y x))
  ;;          :hints(("Goal" :in-theory (enable 4vec-resor)))
  ;;          :rule-classes ((:rewrite :loop-stopper ((x y 4vec-resor))))))

  (defthm res-to-concat-top-correct
    (implies (and (member resfn '(res))
                  (res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask))
             (equal (4vec-mask mask (svex-eval (res-to-concat-top x y mask resfn) env))
                    (4vec-mask mask (svex-eval (svex-call resfn (list x y)) env))))
    :hints(("Goal" :in-theory (enable svex-apply svexlist-eval))))

  (defthm res-to-concat-top-no-new-vars
    (implies (and (not (member v (svex-vars x)))
                  (not (member v (svex-vars y))))
             (not (member v (svex-vars (res-to-concat-top x y mask resfn)))))))



;; BOZO change this so that we can combine values whose non-z masks overlap,
;; but that are Boolean and agree on the overlap. (bitxor x y) & (not-z x) & (not-z y) = 0.
(def-svex-rewrite res-to-concat
  :lhs (res x y)
  :checks ((res-combine-cond (svex-s4xeval x) (svex-s4xeval y) mask)
           (bind v (res-to-concat-top x y mask 'res)))
  :rhs v)

;; (def-svex-rewrite resand-to-concat
;;   :lhs (resand x y)
;;   :checks ((eql (logand (4vec-non-z-mask-mask (svex-xeval x))
;;                         (4vec-non-z-mask-mask (svex-xeval y)))
;;                 0)
;;            (bind v (res-to-concat-top x y 'resand)))
;;   :rhs v)

;; (def-svex-rewrite resor-to-concat
;;   :lhs (resor x y)
;;   :checks ((eql (logand (4vec-non-z-mask-mask (svex-xeval x))
;;                         (4vec-non-z-mask-mask (svex-xeval y)))
;;                 0)
;;            (bind v (res-to-concat-top x y 'resor)))
;;   :rhs v)

(def-svex-rewrite bitxor-identity-under-mask-1
  :lhs (bitxor x y)
  :checks (;; x is 0 in all the care bits
           (not (sparseint-test-bitand mask
                                       (s4vec->upper (svex-s4xeval x))))
           (not (sparseint-test-bitand mask (s4vec->lower (svex-s4xeval x)))))
  :rhs (unfloat y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bitxor
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite bitxor-negation-under-mask-1
  :lhs (bitxor x y)
  :checks (;; x is 1 in all the care bits
           (not (sparseint-test-bitandc2 mask (s4vec->upper (svex-s4xeval x))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval x)))))
  :rhs (bitnot y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bitxor
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))


(def-svex-rewrite bitxor-identity-under-mask-2
  :lhs (bitxor x y)
  :checks (;; y is 0 in all the care bits
           (not (sparseint-test-bitand mask (s4vec->upper (svex-s4xeval y))))
           (not (sparseint-test-bitand mask (s4vec->lower (svex-s4xeval y)))))
  :rhs (unfloat x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bitxor
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))

(def-svex-rewrite bitxor-negation-under-mask-2
  :lhs (bitxor x y)
  :checks (;; y is 1 in all the care bits
           (not (sparseint-test-bitandc2 mask (s4vec->upper (svex-s4xeval y))))
           (not (sparseint-test-bitandc2 mask (s4vec->lower (svex-s4xeval y)))))
  :rhs (bitnot x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-bitxor
                                    4vec-bitnot 3vec-bitnot 3vec-fix 4vec-mask))
         (bitops::logbitp-reasoning
          :prune-examples nil
          :add-hints (:in-theory (enable* bitops::bool->bit
                                          bitops::logbitp-case-splits
                                          logbitp-when-4vec-[=-svex-eval-strong)))))



(def-svex-rewrite uand-of-bitsel
  :lhs (uand (bitsel n x))
  :rhs 0
  :hints(("Goal"
          :in-theory (enable svex-apply 4vec-reduction-and 4vec-bit-extract
                             3vec-reduction-and 4vec-bit-index 3vec-fix
                             bool->bit))))

(def-svex-rewrite uand-of-zerox
  :lhs (uand (zerox n x))
  :checks ((svex-quoted-index-p n))
  :rhs 0
  :hints(("Goal"
          :in-theory (enable svex-apply 4vec-reduction-and 4vec-zero-ext
                             3vec-reduction-and 3vec-fix))))

(defthm logand-ash-not-equal-neg-1
  (implies (< 0 (nfix n))
           (not (equal (logand (ash x n) y) -1)))
  :hints (("goal"
           :use ((:instance bitops::logbitp-of-logand
                  (acl2::a 0) (x (ash x n))))
           :in-theory (disable logand-equal-minus-1
                               bitops::logbitp-of-logand))))

(defthm logior-ash-not-equal-neg-1
  (implies (< 0 (nfix n))
           (not (equal (logior (ash x n) (ash y n)) -1)))
  :hints (("goal" :use ((:instance bitops::logbitp-of-logior
                         (acl2::a 0) (x (ash x n)) (y (ash y n))))
           :in-theory (disable bitops::logbitp-of-logior))))

(def-svex-rewrite uand-of-lsh
  :lhs (uand (lsh n x))
  :checks ((svex-quoted-index-p n)
           (< 0 (2vec->val (svex-quote->val n))))
  :rhs 0
  :hints(("Goal" :expand ((4vec-mask mask 0))
          :in-theory (enable svex-apply 4vec-reduction-and 4vec-lsh 4vec-shift-core
                             3vec-reduction-and 3vec-fix 4vec-mask
                             bool->bit))))


(def-svex-rewrite +-of-u-
  :lhs (+ x (u- y))
  :rhs (b- x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-plus 4vec-uminus 4vec-minus))))

(def-svex-rewrite +-of-u-2
  :lhs (+ (u- y) x)
  :rhs (b- x y)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-plus 4vec-uminus 4vec-minus))))

(def-svex-rewrite b--of-0-right
  :lhs (b- x 0)
  :rhs (xdet x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-minus 4vec-xdet))))

(def-svex-rewrite b--of-0-left
  :lhs (b- 0 x)
  :rhs (u- x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-minus 4vec-uminus))))

(def-svex-rewrite +-of-0-right
  :lhs (+ x 0)
  :rhs (xdet x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-plus 4vec-xdet))))

(def-svex-rewrite +-of-0-left
  :lhs (+ 0 x)
  :rhs (xdet x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-plus 4vec-xdet))))

(def-svex-rewrite uminus-of-uminus
  :lhs (u- (u- x))
  :rhs (xdet x)
  :hints(("Goal" :in-theory (enable svex-apply 4vec-uminus 4vec-xdet))))


;; (local (defthm logext-of-logand-equal-minus-1
;;          (equal (equal (logext n (logand a b)) -1)
;;                 (and (equal (logext n a) -1)
;;                      (equal (logext n b) -1))

;; (def-svex-rewrite uand-of-concat-1
;;   :lhs (uand (concat w x y))
;;   :checks ((svex-quoted-index-p w)
;;            (< 0 (2vec->val (svex-quote->val w))))
;;   :rhs (bitand (uand (signx w x))
;;                (uand y))
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-reduction-and 3vec-reduction-and
;;                                     4vec-concat 4vec-bitand 3vec-fix 3vec-bitand 4vec-sign-ext))
;;          (and stable-under-simplificationp
;;               '(:in-theory (enable bool->bit)))))

(def-svex-rewrite concat-of-0
  :lhs (concat 0 x y)
  :rhs y
  :hints(("Goal" :in-theory (enable 4vec-concat svex-apply))))

(def-svex-rewrite rsh-of-0
  :lhs (rsh 0 x)
  :rhs x
  :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core svex-apply))))

(def-svex-rewrite lsh-of-0
  :lhs (lsh 0 x)
  :rhs x
  :hints(("Goal" :in-theory (enable 4vec-lsh 4vec-shift-core svex-apply))))

(def-svex-rewrite concat-redundant
  :lhs (concat n x (rsh n x))
  :checks ((svex-quoted-index-p n))
  :rhs x
  :hints(("Goal" :in-theory (enable svex-apply
                                    4vec-concat
                                    4vec-rsh
                                    4vec-shift-core
                                    4vec-index-p
                                    4vec-mask))
         (bitops::logbitp-reasoning)
         (and stable-under-simplificationp
              '(:in-theory (enable bool->bit)))))



(def-svex-rewrite concat-redundant-rsh
  :lhs (concat m (rsh n1 x) (rsh n2 x))
  :checks ((eq (svex-kind m) :quote)
           (eq (svex-kind n1) :quote)
           (eq (svex-kind n2) :quote)
           (4vec-index-p (svex-quote->val m))
           (2vec-p (svex-quote->val n1))
           (2vec-p (svex-quote->val n2))
           (equal (2vec->val (svex-quote->val n2))
                  (+ (2vec->val (svex-quote->val m))
                     (2vec->val (svex-quote->val n1)))))
  :rhs (rsh n1 x)
  :hints(("Goal" :in-theory (enable svex-apply
                                    4vec-concat
                                    4vec-rsh
                                    4vec-shift-core
                                    4vec-index-p
                                    4vec-mask))))



(local (acl2::use-trivial-ancestors-check))

(local (defthm 4vec-mask-of-4vec-concat
         (implies (natp width)
                  (equal (4vec-mask mask (4vec-concat (2vec width) x y))
                         (4vec-concat (2vec width)
                                      (4vec-mask (sparseint-concatenate width (4vmask-fix mask) 0) x)
                                      (4vec-mask (sparseint-rightshift width (4vmask-fix mask)) y))))
         :hints(("Goal" :in-theory (enable 4vec-mask 4vec-concat))
                (logbitp-reasoning))))

(define normalize-concat-aux ((x-width natp)
                              (x svex-p)
                              (y svex-p)
                              (mask 4vmask-p))
  :measure (svex-count x)
  :returns (concat svex-p)
  :verify-guards nil
  (b* ((x-width (lnfix x-width))
       (mask (4vmask-fix mask))
       ((when (not (sparseint-test-bitand (sparseint-concatenate x-width -1 0) mask)))
        (svex-concat x-width 0 y))
       ((mv matched a-width a b) (match-concat x))
       ((unless matched) (svex-concat x-width x y))
       ((when (< a-width x-width))
        (normalize-concat-aux
         a-width
         a
         (normalize-concat-aux (- x-width a-width) b y (sparseint-rightshift a-width mask))
         mask)))
    (normalize-concat-aux x-width a y mask))
  ///
  (verify-guards normalize-concat-aux)

  
  (local (defthm logand-loghead-neg1
           (equal (logand (loghead n -1) x)
                  (loghead n x))
           :hints((logbitp-reasoning))))

  (local (defthm 4vec-mask-when-val-is-0
           (implies (equal (sparseint-val (4vmask-fix m)) 0)
                    (equal (4vec-mask m x) '(-1 . 0)))
           :hints(("Goal" :in-theory (enable 4vec-mask)))))

  (defret normalize-concat-aux-correct
    (equal (4vec-mask mask (svex-eval concat env))
           (4vec-mask mask (4vec-concat (2vec (nfix x-width))
                                        (svex-eval x env)
                                        (svex-eval y env))))
    :hints(("Goal" :in-theory (enable match-concat-correct-rewrite-svex-eval-of-x
                                      svex-apply svexlist-eval 4veclist-nth-safe)
            :induct t)))

  (defret normalize-concat-aux-vars
    (implies (and (not (member v (svex-vars x)))
                  (not (member v (svex-vars y))))
             (not (member v (svex-vars concat)))))

  (deffixequiv normalize-concat-aux))

(define normalize-concat ((x svex-p)
                          (mask 4vmask-p))
  :measure (svex-count x)
  :returns (concat svex-p)
  :verify-guards nil
  (b* ((mask (4vmask-fix mask))
       ((when (sparseint-equal mask 0)) 0)
       ((mv matched a-width a b) (match-concat x))
       ((unless matched) (svex-fix x)))
    (normalize-concat-aux a-width a (normalize-concat b (sparseint-rightshift a-width mask)) mask))
  ///
  (verify-guards normalize-concat)

  (local (defthm 4vec-mask-when-val-is-0
           (implies (equal (sparseint-val (4vmask-fix m)) 0)
                    (equal (4vec-mask m x) '(-1 . 0)))
           :hints(("Goal" :in-theory (enable 4vec-mask)))))

  (defret normalize-concat-correct
    (equal (4vec-mask mask (svex-eval concat env))
           (4vec-mask mask (svex-eval x env)))
    :hints(("Goal" :in-theory (enable match-concat-correct-rewrite-svex-eval-of-x
                                      svex-apply svexlist-eval 4veclist-nth-safe))))

  (defret normalize-concat-vars
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars concat)))))

  (deffixequiv normalize-concat))


(define merge-branches-base ((fn fnsym-p)
                             (test svex-p)
                             (x svex-p)
                             (y svex-p)
                             (x-shift natp)
                             (y-shift natp))
  :returns (res svex-p)
  (b* ((x-shift (lnfix x-shift))
       (y-shift (lnfix y-shift))
       ((mv x-match x-shift1 x-sub) (match-rsh x))
       ((mv y-match y-shift1 y-sub) (match-rsh y))
       ((mv x-core x-shift)
        (if x-match
            (mv x-sub (+ x-shift1 x-shift))
          (mv x x-shift)))
       ((mv y-core y-shift)
        (if y-match
            (mv y-sub (+ y-shift1 y-shift))
          (mv y y-shift)))
       ((when (and (svex-equiv x-core y-core)
                   (eql x-shift y-shift)))
        (svex-rsh x-shift x-core)))
    (svex-call fn (list test (svex-rsh x-shift x-core) (svex-rsh y-shift y-core))))
  ///
  (local (defthm 4vec-?*-of-same
           (equal (4vec-?* test x x)
                  (4vec-fix x))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 3vec-fix)))))

  (defret merge-branches-base-correct
    (implies (member fn '(?* ?!))
             (equal (svex-eval res env)
                    (svex-apply fn
                                (list (svex-eval test env)
                                      (4vec-rsh (2vec (nfix x-shift))
                                                (svex-eval x env))
                                      (4vec-rsh (2vec (nfix y-shift))
                                                (svex-eval y env))))))
    :hints(("Goal" :in-theory (enable svex-apply svexlist-eval 4vec-?!
                                      match-rsh-correct-rewrite-svex-eval-of-x))))

  (defret vars-of-merge-branches-base
    (implies (and (not (member v (svex-vars test)))
                  (not (member v (svex-vars x)))
                  (not (member v (svex-vars y))))
             (not (member v (svex-vars res))))))


(define merge-branches ((fn fnsym-p)
                        (test svex-p)
                        (x svex-p)
                        (y svex-p)
                        (x-shift natp)
                        (y-shift natp))
  :returns (res svex-p)
  :verify-guards nil
  :measure (+ (svex-count x) (svex-count y))
  (b* ((x-shift (lnfix x-shift))
       (y-shift (lnfix y-shift))
       ((when (and (eql x-shift y-shift)
                   (hons-equal (svex-fix x)
                               (svex-fix y))))
        (svex-rsh x-shift x))
       ((mv x-match x-width x1 x2) (match-concat x))
       ((when (and x-match (<= x-width x-shift)))
        (merge-branches fn test x2 y (- x-shift x-width) y-shift))
       ((mv y-match y-width y1 y2) (match-concat y))
       ((when (and y-match (<= y-width y-shift)))
        (merge-branches fn test x y2 x-shift (- y-shift y-width)))

       (x1 (if x-match x1 x))
       (y1 (if y-match y1 y))
       (x-width (and x-match (- x-width x-shift)))
       (y-width (and y-match (- y-width y-shift)))

       (part1 (merge-branches-base fn test x1 y1 x-shift y-shift))

       ((when (and x-match
                   (or (not y-match)
                       (< x-width y-width))))
        (svex-concat x-width part1
                     (merge-branches fn test x2 y 0 (+ x-width y-shift))))

       ((when (and y-match
                   (or (not x-match)
                       (< y-width x-width))))
        (svex-concat y-width part1
                     (merge-branches fn test x y2 (+ y-width x-shift) 0)))

       ((when (and x-match y-match))
        ;; widths equal
        (svex-concat x-width part1
                     (merge-branches fn test x2 y2 0 0))))
    ;; neither matched
    part1)
  ///
  (verify-guards merge-branches)
  

  (local (defthm 4vec-?*-of-same
           (equal (4vec-?* test x x)
                  (4vec-fix x))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 3vec-fix)))))

  (local (defthm 4vec-?!-of-same
           (equal (4vec-?! test x x)
                  (4vec-fix x))
           :hints(("Goal" :in-theory (enable 4vec-?!)))))


  (local (defthm svex-apply-of-qmark-same
           (implies (member fn '(?* ?!))
                    (equal (svex-apply fn (list test x x))
                           (4vec-fix x)))
           :hints(("Goal" :in-theory (enable svex-apply)))))

  (local (defthm 4vec-concat-of-?*-branches-1
           (implies (equal y (4vec-?* test c d))
                    (equal (4vec-concat width (4vec-?* test a b) y)
                           (4vec-?* test
                                    (4vec-concat width a c)
                                    (4vec-concat width b d))))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-?* 3vec-?* 3vec-fix))
                  (logbitp-reasoning))))

  (local (defthm 4vec-concat-of-?!-branches-1
           (implies (equal y (4vec-?! test c d))
                    (equal (4vec-concat width (4vec-?! test a b) y)
                           (4vec-?! test
                                    (4vec-concat width a c)
                                    (4vec-concat width b d))))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-?!))
                  (logbitp-reasoning))))

  (local (defthm apply-concat-of-?-branches-1
           (implies (member fn '(?* ?!))
                    (implies (equal y (svex-apply fn (list test c d)))
                             (equal (4vec-concat width (svex-apply fn (list test a b)) y)
                                    (svex-apply fn (list test
                                                         (4vec-concat width a c)
                                                         (4vec-concat width b d))))))
           :hints(("Goal" :in-theory (e/d (svex-apply)
                                          (4vec-concat-of-?*-branches-1
                                           4vec-concat-of-?!-branches-1))
                   :use (4vec-concat-of-?*-branches-1
                         4vec-concat-of-?!-branches-1)))))

  (local (defthm 4vec-concat-of-shifts-merge
           (implies (and (natp w) (natp shift)
                         (equal shift2 (+ shift w)))
                    (equal (4vec-concat (2vec w)
                                        (4vec-rsh (2vec shift) x)
                                        (4vec-rsh (2vec shift2) x))
                           (4vec-rsh (2vec shift) x)))
           :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-concat))
                  (logbitp-reasoning))))

  (local (defthm 4vec-concat-of-concat-merge
           (implies (and (natp w1) (natp w2) (natp shift)
                         (equal shift2 (+ shift w1)))
                    (equal (4vec-concat (2vec w1)
                                        (4vec-rsh (2vec shift) x)
                                        (4vec-concat (2vec w2)
                                                     (4vec-rsh (2vec shift2) x)
                                                     y))
                           (4vec-concat (2vec (+ w1 w2))
                                        (4vec-rsh (2vec shift) x)
                                        y)))
           :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-concat))
                  (logbitp-reasoning))))

  (local
   (make-event
    `(defthmd svex-apply-when-fn-quote
       (implies (syntaxp (quotep fn))
                (equal (svex-apply fn args)
                       ,(acl2::body 'svex-apply nil (w state))))
       :hints(("Goal" :by svex-apply)))))

  (defret merge-branches-correct
    (implies (member fn '(?* ?!))
             (equal (svex-eval res env)
                    (svex-apply fn (list (svex-eval test env)
                                         (4vec-rsh (2vec (nfix x-shift))
                                                   (svex-eval x env))
                                         (4vec-rsh (2vec (nfix y-shift))
                                                   (svex-eval y env))))))
    :hints(("Goal" :in-theory (e/d (svexlist-eval svex-apply-when-fn-quote
                                    match-rsh-correct-rewrite-svex-eval-of-x
                                    match-concat-correct-rewrite-svex-eval-of-x)
                                   (acl2::member-of-cons
                                    not (:d <fn>)
                                    member-equal))
            :expand ((:free (fn) <call>))
            :induct <call>)))

  (defret vars-of-merge-branches
    (implies (and (not (member v (svex-vars test)))
                  (not (member v (svex-vars x)))
                  (not (member v (svex-vars y))))
             (not (member v (svex-vars res))))))
       


(encapsulate nil
  (local (in-theory (disable 2vec-p
                             bitops::logeqv
                             bitops::logand-natp-type-2
                             bitops::logand-natp-type-1
                             bitops::logior-natp-type
                             bitops::lognot-natp
                             bitops::logand->=-0-linear-2
                             bitops::upper-bound-of-logand
                             iff not acl2::zip-open)))
  (local (defthm equal-of-b-not
           (implies (syntaxp (quotep b))
                    (equal (equal b (acl2::b-not x))
                           (and (bitp b)
                                (equal (acl2::b-not b) (bfix x)))))
           :hints(("Goal" :in-theory (enable acl2::b-not)))))

  (def-svex-rewrite qmark-nest-1
    :lhs (? a (? a b c) c)
    :rhs (? a b c)
    :hints(("Goal" :in-theory (e/d (4vec-? 3vec-? svex-apply 4vec-mask)))
           (bitops::logbitp-reasoning)))

  (def-svex-rewrite qmark*-nest-1
    :lhs (?* a (?* a b c) c)
    :rhs (?* a b c)
    :hints(("Goal" :in-theory (e/d (4vec-?* 3vec-?* svex-apply 4vec-mask)))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:in-theory (enable b-xor)))))

  (def-svex-rewrite qmark!-nest-1
    :lhs (?! a (?! a b c) c)
    :rhs (?! a b c)
    :hints(("Goal" :in-theory (e/d (4vec-?! svex-apply 4vec-mask)))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:in-theory (enable b-xor)))))

  (def-svex-rewrite qmark-nest-2
    :lhs (? a b (? a b c))
    :rhs (? a b c)
    :hints(("Goal" :in-theory (e/d (4vec-? 3vec-? svex-apply 4vec-mask)))
           (bitops::logbitp-reasoning)))

  (def-svex-rewrite qmark*-nest-2
    :lhs (?* a b (?* a b c))
    :rhs (?* a b c)
    :hints(("Goal" :in-theory (e/d (4vec-?* 3vec-?* svex-apply 4vec-mask)))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:in-theory (enable b-xor)))))

  (def-svex-rewrite qmark!-nest-2
    :lhs (?! a b (?! a b c))
    :rhs (?! a b c)
    :hints(("Goal" :in-theory (e/d (4vec-?! svex-apply 4vec-mask)))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:in-theory (enable b-xor)))))

  (local (in-theory (disable svex-eval-when-quote
                             svex-eval-when-fncall
                             svex-eval-when-2vec-p-of-minval
                             3vec-p-implies-bits
                             bitops::logbitp-when-bitmaskp
                             bitops::logbitp-nonzero-of-bit)))

  (def-svex-rewrite qmark-select-1
    :lhs (? a b c)
    :checks ((not (sparseint-equal 0 (s4vec->lower (s3vec-fix (svex-s4xeval a))))))
    :rhs b
    :hints(("Goal" :in-theory (e/d (4vec-? 3vec-? svex-apply 4vec-mask
                                           3vec-fix 4vec-[=)
                                   (svex-eval-gte-xeval))
            :use ((:instance svex-eval-gte-xeval
                   (x (svex-lookup 'a (mv-nth 1 (svexlist-unify '(a b c) args nil)))))))
           (bitops::logbitp-reasoning
            :add-hints (:in-theory (enable* bitops::logbitp-case-splits)))))

  (def-svex-rewrite qmark*-select-1
    :lhs (?* a b c)
    :checks ((not (sparseint-equal 0 (s4vec->lower (s3vec-fix (svex-s4xeval a))))))
    :rhs b
    :hints(("Goal" :in-theory (e/d (4vec-?* 3vec-?* svex-apply 4vec-mask
                                           3vec-fix 4vec-[=)
                                   (svex-eval-gte-xeval))
            :use ((:instance svex-eval-gte-xeval
                   (x (svex-lookup 'a (mv-nth 1 (svexlist-unify '(a b c) args nil)))))))
           (bitops::logbitp-reasoning
            :add-hints (:in-theory (enable* bitops::logbitp-case-splits)))))

  (def-svex-rewrite qmark!-select-1
    :lhs (?! a b c)
    :checks ((not (sparseint-equal 0 (s4vec->lower (s3vec-fix (svex-s4xeval a))))))
    :rhs b
    :hints(("Goal" :in-theory (e/d (4vec-?! svex-apply 4vec-mask
                                           3vec-fix 4vec-[=)
                                   (svex-eval-gte-xeval))
            :use ((:instance svex-eval-gte-xeval
                   (x (svex-lookup 'a (mv-nth 1 (svexlist-unify '(a b c) args nil)))))))
           (bitops::logbitp-reasoning
            :add-hints (:in-theory (enable* bitops::logbitp-case-splits)))))

  (def-svex-rewrite qmark-select-0
    :lhs (? a b c)
    :checks ((sparseint-equal 0 (s4vec->upper (s3vec-fix (svex-s4xeval a)))))
    :rhs c
    :hints(("Goal" :in-theory (e/d (4vec-? 3vec-? svex-apply 4vec-mask
                                           3vec-fix 4vec-[=)
                                   (svex-eval-gte-xeval))
            :use ((:instance svex-eval-gte-xeval
                   (x (svex-lookup 'a (mv-nth 1 (svexlist-unify '(a b c) args nil)))))))
           (bitops::logbitp-reasoning
            :add-hints (:in-theory (enable* bitops::logbitp-case-splits)))))

  (def-svex-rewrite qmark*-select-0
    :lhs (?* a b c)
    :checks ((sparseint-equal 0 (s4vec->upper (s3vec-fix (svex-s4xeval a)))))
    :rhs c
    :hints(("Goal" :in-theory (e/d (4vec-?* 3vec-?* svex-apply 4vec-mask
                                           3vec-fix 4vec-[=)
                                   (svex-eval-gte-xeval))
            :use ((:instance svex-eval-gte-xeval
                   (x (svex-lookup 'a (mv-nth 1 (svexlist-unify '(a b c) args nil)))))))
           (bitops::logbitp-reasoning
            :add-hints (:in-theory (enable* bitops::logbitp-case-splits)))))

  (def-svex-rewrite qmark!-select-0
    :lhs (?! a b c)
    :checks ((sparseint-equal 0 (s4vec->upper (s3vec-fix (svex-s4xeval a)))))
    :rhs c
    :hints(("Goal" :in-theory (e/d (4vec-?! svex-apply 4vec-mask
                                           3vec-fix 4vec-[=)
                                   (svex-eval-gte-xeval))
            :use ((:instance svex-eval-gte-xeval
                   (x (svex-lookup 'a (mv-nth 1 (svexlist-unify '(a b c) args nil)))))))
           (bitops::logbitp-reasoning
            :add-hints (:in-theory (enable* bitops::logbitp-case-splits)))))

  (def-svex-rewrite qmark*-same
    :lhs (?* a b b)
    :rhs b
    :hints(("Goal" :in-theory (e/d (4vec-?* 3vec-?* svex-apply 4vec-mask
                                           3vec-fix 4vec-[=)
                                   (svex-eval-gte-xeval))
            :use ((:instance svex-eval-gte-xeval
                   (x (svex-lookup 'a (mv-nth 1 (svexlist-unify '(a b c) args nil)))))))
           (bitops::logbitp-reasoning
            :add-hints (:in-theory (enable* bitops::logbitp-case-splits)))))

  (def-svex-rewrite qmark!-same
    :lhs (?! a b b)
    :rhs b
    :hints(("Goal" :in-theory (e/d (4vec-?! svex-apply 4vec-mask
                                           3vec-fix 4vec-[=)
                                   (svex-eval-gte-xeval))
            :use ((:instance svex-eval-gte-xeval
                   (x (svex-lookup 'a (mv-nth 1 (svexlist-unify '(a b c) args nil)))))))
           (bitops::logbitp-reasoning
            :add-hints (:in-theory (enable* bitops::logbitp-case-splits)))))

#||
  ;; NOTE: (bozo?)  These are very particular rules for ?* and they don't
  ;; follow the usual conventions that ensure that we don't blow up.  The
  ;; reason for this is that ?* is used in procedural statement processing for things like:
  ;; always_comb begin
  ;;   a = b;
  ;;   if (c)
  ;;      a[5:0] = d;
  ;;  end
  ;;  In this case the update function for a is something like:
  ;;   a = (?* c (concat 6 d (rsh 6 b)) b)
  ;;  We've run into cases where in examples like this, c depends on upper bits
  ;;  of a, so we want to make sure we can disentangle this dependency so we
  ;;  don't get hung up on a false combinational loop.
  (def-svex-rewrite qmark*-concat-same-1
    :lhs (?* a (concat w b c) (concat w d c))
    :rhs (concat w (?* a b d) c)
    :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 4vec-concat svex-apply 3vec-fix 4vec-mask))
           (logbitp-reasoning)))

  (def-svex-rewrite qmark*-concat-same-2
    :lhs (?* a (concat w b c) (concat w b d))
    :rhs (concat w b (?* a c d))
    :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 4vec-concat svex-apply 3vec-fix 4vec-mask))
           (logbitp-reasoning)))

  (def-svex-rewrite qmark*-concat-reduce1
    :lhs (?* a (concat w b c) b)
    :checks ((svex-case w :quote (4vec-index-p w.val) :otherwise nil))
    :rhs (concat w b (?* a c (rsh w b)))
    :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 4vec-concat 4vec-rsh svex-apply 3vec-fix 4vec-mask svex-eval-when-quote 4vec-index-p))
           (svex-generalize-lookups)
           (logbitp-reasoning)))

  (def-svex-rewrite qmark*-concat-reduce2
    :lhs (?* a (concat w b (rsh w c)) c)
    :checks ((svex-case w :quote (4vec-index-p w.val) :otherwise nil))
    :rhs (concat w (?* a b c) (rsh w c))
    :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 4vec-concat 4vec-rsh svex-apply 3vec-fix 4vec-mask svex-eval-when-quote 4vec-index-p))
           (svex-generalize-lookups)
           (logbitp-reasoning)))
||#

  (local (defthm 4vec-mask-of-?*
           (equal (4vec-mask mask (4vec-?* x y z))
                  (4vec-?* x (4vec-mask mask y)
                           (4vec-mask mask z)))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 3vec-fix 4vec-mask))
                  (logbitp-reasoning))))

  (def-svex-rewrite ?*-merge-branches
    :lhs (?* test x y)
    :checks ((not (s4vec-2vec-p (svex-s4xeval test)))
             (bind res (merge-branches '?* test
                                       (normalize-concat x mask)
                                       (normalize-concat y mask)
                                       0 0))
             (not (svex-case res
                    :call (and (eq res.fn '?*)
                               (hons-equal (first res.args) test)
                               (hons-equal (second res.args) x)
                               (hons-equal (third res.args) y))
                    :otherwise nil)))
    :rhs res)

  (local (defthm 4vec-mask-of-?!
           (equal (4vec-mask mask (4vec-?! x y z))
                  (4vec-?! x (4vec-mask mask y)
                           (4vec-mask mask z)))
           :hints(("Goal" :in-theory (enable 4vec-?! 3vec-fix 4vec-mask))
                  (logbitp-reasoning))))

  (def-svex-rewrite ?!-merge-branches
    :lhs (?! test x y)
    :checks ((not (s4vec-2vec-p (svex-s4xeval test)))
             (bind res (merge-branches '?! test
                                       (normalize-concat x mask)
                                       (normalize-concat y mask)
                                       0 0))
             (not (svex-case res
                    :call (and (eq res.fn '?!)
                               (hons-equal (first res.args) test)
                               (hons-equal (second res.args) x)
                               (hons-equal (third res.args) y))
                    :otherwise nil)))
    :rhs res)

  (def-svex-rewrite ?-of-uor
    :lhs (? (uor test) x y)
    :rhs (? test x y)
    :hints(("Goal" :in-theory (enable 4vec-reduction-or
                                      3vec-reduction-or
                                      4vec-?
                                      3vec-? 3vec-fix
                                      4vec-mask
                                      svex-apply))
           (svex-generalize-lookups))))


(def-svex-rewrite ==-1-of-concat-1
  :lhs (== 1 (concat 1 a 0))
  :rhs (uor (concat 1 a 0))
  :hints(("Goal" :in-theory (enable 4vec-concat 4vec-== 3vec-== 3vec-reduction-or
                                    4vec-reduction-or
                                    3vec-reduction-and
                                    4vec-reduction-and
                                    svex-apply
                                    3vec-bitxor 3vec-bitnot 4vec-mask
                                    3vec-fix))
         (svex-generalize-lookups)
         (logbitp-reasoning)))


  
;; (def-svex-rewrite push-concat-into-bitor
;;   :lhs (concat 1 (bitor a b) 0)
;;   :checks ((not (hons-get (second args) multiref-table)))
;;   :rhs (bitor (concat 1 a 0) (concat 1 b 0))
;;   :hints(("Goal" :in-theory (enable 4vec-bitor 3vec-bitor 3vec-fix
;;                                     4vec-concat
;;                                     svex-apply))
;;          (svex-generalize-lookups)))

;; (local (defthm equal-of-upper-lower-by-xeval
;;          (implies (equal (4vec->upper (svex-xeval x))
;;                          (4vec->lower (svex-xeval x)))
;;                   (equal (equal (4vec->upper (svex-eval x env))
;;                                 (4vec->lower (svex-eval x env)))
;;                          t))
;;          :hints (("goal" :use ((:instance svex-eval-gte-xeval))
;;                   :in-theory (disable svex-eval-gte-xeval)))))


(def-svex-rewrite partsel-of-partinst-same
  :lhs (partsel lsb width (partinst lsb width x val))
  :checks ((s4vec-index-p (svex-s4xeval lsb)))
  :rhs (zerox width val)
  :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-part-install 4vec-zero-ext
                                    4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
                                    s4vec-index-p svex-eval-when-2vec-p-of-minval))
         (svex-generalize-lookups)
         (logbitp-reasoning)))

(def-svex-rewrite partinst-of-partinst-same
  :lhs (partinst lsb width (partinst lsb width x val1) val2)
  :rhs (partinst lsb width x val2)
  :hints(("Goal" :in-theory (enable 4vec-part-install 4vec-zero-ext
                                    4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask))
         (svex-generalize-lookups)
         (logbitp-reasoning)))

(def-svex-rewrite partsel-of-partinst-nonoverlapping
  :lhs (partsel lsb1 width1 (partinst lsb2 width2 x val))
  :checks ((let lsb1-val (svex-s4xeval lsb1))
           (s4vec-2vec-p lsb1-val)
           (let width1-val (svex-s4xeval width1))
           (s4vec-index-p width1-val)
           (let lsb2-val (svex-s4xeval lsb2))
           (s4vec-2vec-p lsb2-val)
           (let width2-val (svex-s4xeval width2))
           (s4vec-index-p width2-val)
           (or (not (sparseint-< (s4vec->upper lsb2-val)
                                 (sparseint-plus (s4vec->upper lsb1-val) (s4vec->upper width1-val))))
               (not (sparseint-< (s4vec->upper lsb1-val)
                                 (sparseint-plus (s4vec->upper lsb2-val) (s4vec->upper width2-val))))))
  :rhs (partsel lsb1 width1 x)
  :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-part-install 4vec-zero-ext
                                    4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
                                    s4vec-index-p svex-eval-when-2vec-p-of-minval))
         (svex-generalize-lookups)
         (logbitp-reasoning)))


;; (def-svex-rewrite concat-of-partsel-same-width
;;   :lhs (concat w (partsel lsb w x) y)
;;   :checks ((not (hons-get (second args) multiref-table))
;;            (4vec-index-p (svex-xeval lsb)))
;;   :rhs (concat w (rsh lsb x) y)
;;   :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
;;                                     4vec-concat 4vec-rsh svex-apply 4vec-mask
;;                                     4vec-index-p svex-eval-when-2vec-p-of-minval))
;;          (svex-generalize-lookups)
;;          (logbitp-reasoning)))


(def-svex-rewrite partsel-of-rsh
  :lhs (partsel lsb width (rsh shift x))
  :checks ((let lsb-val (svex-s4xeval lsb))
           (s4vec-index-p lsb-val)
           (let shift-val (svex-s4xeval shift))
           (s4vec-index-p shift-val)
           (bind newlsb (svex-quote (2vec (sparseint-val
                                           (sparseint-plus (s4vec->upper lsb-val)
                                                           (s4vec->upper shift-val)))))))
  :rhs (partsel newlsb width x)
  :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
                                    4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
                                    s4vec-index-p svex-eval-when-2vec-p-of-minval))
         (svex-generalize-lookups)
         (logbitp-reasoning)))




;; (def-svex-rewrite partsel-of-concat-1
;;   :lhs (partsel lsb width (concat cwidth x y))
;;   :checks ((let lsb-val (svex-xeval lsb))
;;            (4vec-index-p lsb-val)
;;            (let width-val (svex-xeval width))
;;            (4vec-index-p width-val)
;;            (let cwidth-val (svex-xeval cwidth))
;;            (4vec-index-p cwidth-val)
;;            (<= (+ (2vec->val lsb-val)
;;                   (2vec->val width-val))
;;                (2vec->val cwidth-val)))
;;   :rhs (partsel lsb width x)
;;   :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
;;                                     4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
;;                                     4vec-index-p svex-eval-when-2vec-p-of-minval))
;;          (svex-generalize-lookups)
;;          (logbitp-reasoning)))

;; (def-svex-rewrite partsel-of-concat-2
;;   :lhs (partsel lsb width (concat cwidth x y))
;;   :checks ((let lsb-val (svex-xeval lsb))
;;            (4vec-index-p lsb-val)
;;            ;; (let width-val (svex-xeval width))
;;            ;; (4vec-index-p width-val)
;;            (let cwidth-val (svex-xeval cwidth))
;;            (4vec-index-p cwidth-val)
;;            (<= (2vec->val cwidth-val)
;;                (2vec->val lsb-val))
;;            (bind new-lsb (svex-quote (2vec (- (2vec->val lsb-val)
;;                                               (2vec->val cwidth-val))))))
;;   :rhs (partsel new-lsb width y)
;;   :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
;;                                     4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
;;                                     4vec-index-p svex-eval-when-2vec-p-of-minval))
;;          (svex-generalize-lookups)
;;          (logbitp-reasoning)))

(def-svex-rewrite partsel-of-partsel
  :lhs (partsel lsb1 width1 (partsel lsb2 width2 x))
  :checks ((let lsb1-val (svex-s4xeval lsb1))
           (s4vec-index-p lsb1-val)
           (let width1-val (svex-s4xeval width1))
           (s4vec-index-p width1-val)
           (let lsb2-val (svex-s4xeval lsb2))
           (s4vec-index-p lsb2-val)
           (let width2-val (svex-s4xeval width2))
           (s4vec-index-p width2-val)
           (bind new-lsb (svex-quote (2vec (sparseint-val (sparseint-plus (s4vec->upper lsb1-val)
                                                                          (s4vec->upper lsb2-val))))))
           (bind new-width (svex-quote (2vec (min (max 0
                                                       (sparseint-val (sparseint-binary-minus (s4vec->upper width2-val)
                                                                                              (s4vec->upper lsb1-val))))
                                                  (sparseint-val (s4vec->upper width1-val)))))))
  :rhs (partsel new-lsb new-width x)
  :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
                                    4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
                                    s4vec-index-p svex-eval-when-2vec-p-of-minval))
         (svex-generalize-lookups)
         (logbitp-reasoning)))

(local (in-theory (enable s4vec-index-p)))
(def-svex-rewrite partsel-0-under-mask
  :lhs (partsel 0 width x)
  :checks ((let width-val (svex-s4xeval width))
           (s4vec-index-p width-val)
           (not (sparseint-test-bitand (sparseint-concatenate (sparseint-val (s4vec->upper width-val)) 0 -1) mask)))
  :rhs x
  :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-zero-ext
                                    4vec-concat 4vec-rsh 4vec-shift-core svex-apply 4vec-mask
                                    s4vec-index-p svex-eval-when-2vec-p-of-minval))
         (svex-generalize-lookups)
         (logbitp-reasoning :prune-examples nil)))


(local (in-theory (disable bitops::logior-natp-type
                           bitops::logand->=-0-linear-2
                           bitops::logand->=-0-linear-1
                           bitops::upper-bound-of-logand
                           bitops::lognot-natp
                           bitops::logxor-natp-type-1)))
 
(local (defthm 4vec-?*-identity
         (equal (4vec-?* test1 then (4vec-?* test2 then else))
                (4vec-?* (4vec-bitor test1 test2) then else))
         :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 3vec-fix
                                           4vec-bitor 3vec-bitor))
                (logbitp-reasoning)
                (and stable-under-simplificationp
                     '(:in-theory (enable bool->bit))))))

(def-svex-rewrite ?*-of-?*-same-then-branches
  :lhs (?* test1 then (?* test2 then else))
  :checks ((not (hons-get (third args) multiref-table)))
  :rhs (?* (bitor test1 test2) then else)
  :hints(("Goal" :in-theory (enable svex-apply))
         (svex-generalize-lookups)))


(local (defthm 4vec-?!-identity
         (equal (4vec-?! test1 then (4vec-?! test2 then else))
                (4vec-?! (4vec-bitor test1 test2) then else))
         :hints(("Goal" :in-theory (enable 4vec-?! 3vec-fix
                                           4vec-bitor 3vec-bitor))
                (logbitp-reasoning)
                (and stable-under-simplificationp
                     '(:in-theory (enable bool->bit))))))

(def-svex-rewrite ?!-of-?!-same-then-branches
  :lhs (?! test1 then (?! test2 then else))
  :checks ((not (hons-get (third args) multiref-table)))
  :rhs (?! (bitor test1 test2) then else)
  :hints(("Goal" :in-theory (enable svex-apply))
         (svex-generalize-lookups)))


(def-svex-rewrite bitor-self
  :lhs (bitor x x)
  :rhs (unfloat x)
  :hints (("goal" :in-theory (enable 4vec-bitor 3vec-bitor 3vec-fix
                                     svex-apply))
          (svex-generalize-lookups)))

(def-svex-rewrite bitand-self
  :lhs (bitand x x)
  :rhs (unfloat x)
  :hints (("goal" :in-theory (enable 4vec-bitand 3vec-bitand 3vec-fix
                                     svex-apply))
          (svex-generalize-lookups)))

(def-svex-rewrite bitand-bitor-1
  :lhs (bitand x (bitor x y))
  :rhs (unfloat x)
  :hints (("goal" :in-theory (enable 4vec-bitand 3vec-bitand
                                     4vec-bitor 3vec-bitor 3vec-fix
                                     svex-apply 4vec-mask))
          (svex-generalize-lookups)
          (logbitp-reasoning)))

(def-svex-rewrite bitand-bitor-2
  :lhs (bitand x (bitor y x))
  :rhs (unfloat x)
  :hints (("goal" :in-theory (enable 4vec-bitand 3vec-bitand
                                     4vec-bitor 3vec-bitor 3vec-fix
                                     svex-apply 4vec-mask))
          (svex-generalize-lookups)
          (logbitp-reasoning)))

(def-svex-rewrite bitor-bitand-1
  :lhs (bitor x (bitand x y))
  :rhs (unfloat x)
  :hints (("goal" :in-theory (enable 4vec-bitand 3vec-bitand
                                     4vec-bitor 3vec-bitor 3vec-fix
                                     svex-apply 4vec-mask))
          (svex-generalize-lookups)
          (logbitp-reasoning)))

(def-svex-rewrite bitor-bitand-2
  :lhs (bitor x (bitand y x))
  :rhs (unfloat x)
  :hints (("goal" :in-theory (enable 4vec-bitand 3vec-bitand
                                     4vec-bitor 3vec-bitor 3vec-fix
                                     svex-apply 4vec-mask))
          (svex-generalize-lookups)
          (logbitp-reasoning)))


(define s4vec-mask-to-zero ((mask 4vmask-p)
                            (x s4vec-p))
  :returns (new-x s4vec-p)
  (b* ((mask (4vmask-fix mask))
       ((s4vec x)))
    (s4vec (sparseint-bitand mask x.upper)
           (sparseint-bitand mask x.lower)))
  ///
  (defret <fn>-correct
    (equal (s4vec->4vec new-x)
           (4vec-mask-to-zero mask (s4vec->4vec x)))
    :hints(("Goal" :in-theory (enable 4vec-mask-to-zero)))))

(local (defthm 4vec-mask-to-zero-preserves-[=
         (implies (4vec-[= x y)
                  (4vec-[= (4vec-mask-to-zero mask x)
                           (4vec-mask-to-zero mask y)))
         :hints(("Goal" :in-theory (e/d (4vec-[= 4vec-mask-to-zero)
                                        ((tau-system))))
                (logbitp-reasoning))))

(local (defthmd equal-of-4vec->upper
         (implies (and (equal (4vec->lower x) y)
                       (4vec-p x))
                  (equal (equal (4vec->upper x) z)
                         (and (integerp z)
                              (equal x (4vec z y)))))
         ))
                  
                  ;; (equal (equal x y)
                  ;;        (and (4vec-p y)
                  ;;             (equal (4vec->upper x) (4vec->upper y))
                  ;;             (equal (4vec->lower

(local
 (defthmd uor-under-mask-lemma
   (implies (and (equal (4vec->upper (4vec-mask-to-zero mask (svex-xeval x))) 0)
                 (equal (4vec->lower (4vec-mask-to-zero mask (svex-xeval x))) 0))
            (Equal (4vec-mask-to-zero mask (svex-eval x env)) 0))
   :hints(("Goal" :use ((:instance 4vec-mask-to-zero-preserves-[=
                         (x (svex-xeval x)) (y (svex-eval x env))))
           :in-theory (e/d (equal-of-4vec->upper)
                           (4vec-mask-to-zero-preserves-[=))
           :expand ((:free (x) (hide x)))))))

(def-svex-rewrite uor-under-mask-1
  :lhs (uor x)
  :checks ((sparseint-equal mask 1)
           (let mask-x (s4vec-mask-to-zero -2 (svex-s4xeval x)))
           (sparseint-equal (s4vec->upper mask-x) 0)
           (sparseint-equal (s4vec->lower mask-x) 0))
  :rhs (unfloat x)
  :hints (("goal" :in-theory (enable svex-apply))
           ;; :use ((:instance uor-under-mask-lemm)
          (svex-generalize-lookups)
          (and stable-under-simplificationp
               '(:use ((:instance uor-under-mask-lemma
                        (mask -2)))))
          (and stable-under-simplificationp
               '(:in-theory (enable 4vec-reduction-or 3vec-reduction-or
                                    3vec-fix svex-apply 4vec-mask 4vec-mask-to-zero)))
          (bitops::logbitp-reasoning
           :prune-examples nil
           :add-hints (:in-theory (enable* bitops::bool->bit
                                           bitops::logbitp-case-splits)))
          ))



;; BOZO if width and yval xevaluate to xfree, then they should already have
;; been reduced to constants.
(def-svex-rewrite concat-redundant-tail
  :lhs (concat width x y)
  :checks ((let width-val (svex-s4xeval width))
           (s4vec-index-p width-val)
           (let y-val (svex-s4xeval y))
           (s4vec-xfree-p y-val)
           (let x-val (svex-s4xeval x))
           (let rsh  (s4vec-rsh width-val x-val))
           (sparseint-equal (s4vec->upper rsh) (s4vec->upper y-val))
           (sparseint-equal (s4vec->lower rsh) (s4vec->lower y-val)))
  :rhs x
  :hints (("goal" :in-theory (enable 4vec-concat 4vec-xfree-p 4vec-mask 4vec-rsh 4vec-shift-core svex-apply
                                     svex-eval-when-2vec-p-of-minval
                                     svex-eval-when-4vec-xfree-of-minval))
          (svex-generalize-lookups)
          (logbitp-reasoning
           :simp-hint (:in-theory (enable* logbitp-case-splits
                                           logbitp-when-4vec-[=-svex-eval-strong))
           :add-hints (:in-theory (enable* logbitp-case-splits
                                           logbitp-when-4vec-[=-svex-eval-strong)))))



(defun svex-rewrite-fn-try-rules (rule-fns mask args multirefp multiref-table)
  (if (atom rule-fns)
      nil
    `(((mv successp rhs subst) (,(car rule-fns) ,mask ,args ,multirefp ,multiref-table))
      ((when successp)
       (svex-rewrite-trace ',(car rule-fns) mask args multirefp rhs subst)
       (mv successp rhs subst))
      . ,(svex-rewrite-fn-try-rules (cdr rule-fns) mask args multirefp multiref-table))))



(defun svex-rewrite-fn-cases (alist mask args multirefp multiref-table)
  (if (atom alist)
      '((t (mv nil nil nil)))
    (cons `(,(caar alist)
            (b* ,(svex-rewrite-fn-try-rules (cdar alist) mask args multirefp multiref-table)
              (mv nil nil nil)))
          (svex-rewrite-fn-cases (cdr alist) mask args multirefp multiref-table))))



(defconst *typical-function-frequencies*
  ;; Actual sample of frequencies of functions on a real piece of hardware.
  '((CONCAT . 8542748)
    (BITAND . 5717903)
    (BITOR . 5592371)
    (BITNOT . 3032684)
    (UOR . 3006321)
    (RSH . 2899541)
    (PARTSEL . 703941)
     ;; this one is totally made up, but we might see a lot of bit?! due to
     ;; making all signals overridable.
    (bit?! . 500000)
    (== . 341676)
    (==? . 310880)
    (?* . 307682)
    (?! . 307682) ;; made up
    (BITXOR . 154311)
    (PARTINST . 124343)
    (? . 71636)
    (SIGNX . 58707)
    (+ . 15210)
    (B- . 7361)
    (< . 2663)
    (UAND . 2074)
    (UNFLOAT . 1967)
    (=== . 1772)
    (==?? . 894)
    (U- . 345)
    (* . 301)
    (XDET . 207)
    (UXOR . 121)
    (RES . 47)
    (% . 36)
    (/ . 18)
    (BLKREV . 4)
    (BIT? . 3)))

(local
 (define reorder-svex-table ((table symbol-alistp)
                             (freqs symbol-alistp))
   :verify-guards nil
   (b* ((table-keys (alist-keys table))
        (order (alist-keys freqs))
        (full-order (append order (set-difference-eq table-keys order))))
     (acl2::fal-extract full-order table))))

(make-event
 (b* ((orig-table (table-alist 'svex-rewrite (w state)))
      (highly-optimized-table (reorder-svex-table orig-table *typical-function-frequencies*))
      ((unless (alist-equiv orig-table highly-optimized-table))
       (er hard? '*svex-rewrite-table* "Optimization has gone awry.")))
   `(defconst *svex-rewrite-table* ',highly-optimized-table)))

#||
(loop for pair in sv::*svex-rewrite-table* do
      (loop for fn in (cdr pair) do
            (unless (memoizedp-raw fn) (profile-fn fn))))
||#

(defmacro svex-rewrite-cases (mask fn args multirefp multiref-table)
  `(case ,fn
     . ,(svex-rewrite-fn-cases *svex-rewrite-table* mask args multirefp multiref-table)))


(define 4vec-xfree-under-mask ((x 4vec-p) (mask 4vmask-p))
  (b* (((4vec x) x))
    (eql -1 (logior (lognot (sparseint-val (4vmask-fix mask))) (logior (lognot x.upper) x.lower))))
  ///
  (local (defthm equal-of-4vecs
           (implies (and (4vec-p a)
                         (4vec-p b))
                    (equal (equal a b)
                           (and (equal (4vec->upper a) (4vec->upper b))
                                (equal (4vec->lower a) (4vec->lower b)))))))

  (defthmd svex-eval-when-4vec-xfree-under-mask-of-minval
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-under-mask (svex-xeval n) mask))
             (equal (4vec-mask mask (svex-eval n env))
                    (4vec-mask mask (svex-xeval n))))
    :hints (("goal" :use ((:instance svex-eval-gte-xeval (x n)))
             :in-theory (e/d ( 4vec-equiv 4vec-mask)
                             (svex-eval-gte-xeval))
             :expand ((4vec-[= (svex-xeval n) (svex-eval n env))))
            (bitops::logbitp-reasoning)))

  (deffixequiv 4vec-xfree-under-mask)

  (defthmd svex-eval-when-4vec-xfree-under-mask-of-minval-apply
    (implies (and (syntaxp (not (equal env ''nil)))
                  (not (equal (fnsym-fix fn) '===))
                  (not (equal (fnsym-fix fn) '==?))
                  (not (equal (fnsym-fix fn) 'bit?!))
                  (not (equal (fnsym-fix fn) '?!))
                  (4vec-xfree-under-mask (svex-apply fn (svexlist-xeval args)) mask))
             (equal (4vec-mask mask (svex-apply fn (svexlist-eval args env)))
                    (4vec-mask mask (svex-apply fn (svexlist-xeval args)))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-under-mask-of-minval
                           (n (svex-call fn args))))
             :in-theory (disable svex-eval-when-4vec-xfree-under-mask-of-minval
                                 equal-of-4vecs 4vec-xfree-under-mask))))

  (defthmd svex-eval-when-4vec-xfree-under-mask-of-minval-apply-===
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-under-mask (svex-apply '== (svexlist-xeval args)) mask))
             (equal (4vec-mask mask (svex-apply '=== (svexlist-eval args env)))
                    (4vec-mask mask (svex-apply '== (svexlist-xeval args)))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-under-mask-of-minval
                           (n (svex-call '=== args))))
             :in-theory (disable svex-eval-when-4vec-xfree-under-mask-of-minval
                                 equal-of-4vecs 4vec-xfree-under-mask))))

  (defthmd svex-eval-when-4vec-xfree-under-mask-of-minval-apply-==?
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-under-mask (svex-apply 'safer-==? (svexlist-xeval args)) mask))
             (equal (4vec-mask mask (svex-apply '==? (svexlist-eval args env)))
                    (4vec-mask mask (svex-apply 'safer-==? (svexlist-xeval args)))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-under-mask-of-minval
                           (n (svex-call '==? args))))
             :in-theory (disable svex-eval-when-4vec-xfree-under-mask-of-minval
                                 equal-of-4vecs 4vec-xfree-under-mask))))

  (defthmd svex-eval-when-4vec-xfree-under-mask-of-minval-apply-bit?!
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-under-mask (svex-apply 'bit? (svexlist-xeval args)) mask))
             (equal (4vec-mask mask (svex-apply 'bit?! (svexlist-eval args env)))
                    (4vec-mask mask (svex-apply 'bit? (svexlist-xeval args)))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-under-mask-of-minval
                           (n (svex-call 'bit?! args))))
             :in-theory (disable svex-eval-when-4vec-xfree-under-mask-of-minval
                                 equal-of-4vecs 4vec-xfree-under-mask))))


  (defthmd svex-eval-when-4vec-xfree-under-mask-of-minval-apply-?!
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-under-mask (svex-apply '?* (svexlist-xeval args)) mask))
             (equal (4vec-mask mask (svex-apply '?! (svexlist-eval args env)))
                    (4vec-mask mask (svex-apply '?* (svexlist-xeval args)))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-under-mask-of-minval
                           (n (svex-call '?! args))))
             :in-theory (disable svex-eval-when-4vec-xfree-under-mask-of-minval
                                 equal-of-4vecs 4vec-xfree-under-mask)))))

(define s4vec-xfree-under-mask ((x s4vec-p) (mask 4vmask-p))
  :returns (xfree)
  (b* (((s4vec x) x))
    (not (sparseint-test-bitand (4vmask-fix mask) (sparseint-bitandc2 x.upper x.lower))))
  ///
  (defret <fn>-correct
    (equal xfree
           (4vec-xfree-under-mask (s4vec->4vec x) mask))
    :hints(("Goal" :in-theory (enable 4vec-xfree-under-mask))
           (logbitp-reasoning))))

#|
(trace$
 #!sv (svex-rewrite-fncall-once
       :entry (list 'svex-rewrite-fncall-once
                    (cons fn args)
                    mask localp)
       :exit (cons 'svex-rewrite-fncall-once values)
       :evisc-tuple '(nil 6 5 nil)
       :hide nil))

|#

(define svex-rewrite-fncall-once ((mask 4vmask-p)
                                  (fn fnsym-p)
                                  (args svexlist-p)
                                  (multirefp)
                                  (multiref-table svex-key-alist-p))
  :returns (mv (successp booleanp)
               (pat (iff (svex-p pat) successp))
               (subst svex-alist-p))
  (b* ((xeval (svex-s4xeval (svex-call fn args)))
       ((when (s4vec-xfree-under-mask xeval mask))
        (mv t (svex-quote (s4vec->4vec (s4vec-mask-to-zero mask xeval))) nil)))
    nil 
    (svex-rewrite-cases mask
                        (mbe :logic (fnsym-fix fn) :exec fn)
                        args
                        multirefp multiref-table))
  ///
  (deffixequiv svex-rewrite-fncall-once)

  (local (defthm fnsym-fix-implies-fnsym-equiv
           (implies (equal (fnsym-fix x) y)
                    (fnsym-equiv x y))
           :rule-classes :forward-chaining))

  (defthm svex-rewrite-fncall-once-correct
    (b* (((mv ok pat subst) (svex-rewrite-fncall-once mask fn args multirefp multiref-table)))
      (implies ok
               (equal (4vec-mask mask (svex-eval pat (svex-alist-eval subst env)))
                      (4vec-mask mask (svex-apply fn (svexlist-eval args env))))))
    :hints(("Goal" :in-theory (enable svex-eval-when-4vec-xfree-under-mask-of-minval-apply
                                      svex-eval-when-4vec-xfree-under-mask-of-minval-apply-===
                                      svex-eval-when-4vec-xfree-under-mask-of-minval-apply-==?
                                      svex-eval-when-4vec-xfree-under-mask-of-minval-apply-bit?!
                                      svex-eval-when-4vec-xfree-under-mask-of-minval-apply-?!))))

  (defthm svex-rewrite-fncall-once-vars
    (b* (((mv ?ok ?pat subst) (svex-rewrite-fncall-once mask fn args multirefp multiref-table)))
      (implies (not (member v (svexlist-vars args)))
               (not (member v (svex-alist-vars subst)))))
    :hints (("goal" :expand ((:free (x) (hide x))))))

  (defthm svex-rewrite-fncall-once-vars-subset
    (b* (((mv ?ok ?pat subst) (svex-rewrite-fncall-once mask fn args multirefp multiref-table)))
      (subsetp (svex-alist-vars subst) (svexlist-vars args)))
    :hints (("goal" :in-theory (disable svex-rewrite-fncall-once))
            (acl2::set-reasoning)))


  (defthm svex-rewrite-fncall-once-pat-vars-in-subst
    (b* (((mv ?ok pat subst) (svex-rewrite-fncall-once mask fn args multirefp multiref-table)))
      (subsetp (svex-vars pat) (svex-alist-keys subst)))
    :hints (("goal" :expand ((:free (x) (svex-vars (svex-quote x))))))))


;; (uor (concat 1 x 0))


#||

(acl2::set-max-mem (* 40 (expt 2 30)))
(hons-resize :addr-ht 500000000
             :sbits 232541312)
(include-book
 "rewrite-trace")
(defattach svex-rewrite-trace svex-rewrite-trace-profile)
(profile 'svex-rewrite-res-to-concat)
(profile 'svex-rewrite-concat-flatten)
(profile 'svex-rewrite-concat-under-mask-2)
(profile 'svex-rewrite-zerox-under-mask-2)
(profile 'svex-rewrite-rsh-of-concat-less)

(acl2::sneaky-alist state)
(acl2::sneaky-clear)

(loop for x in sv::*svex-rewrite-table* do
      (loop for y in (cdr x) do (profile-fn y)))
(profile-fn 'sv::svex-rewrite-fncall)
(profile-fn 'sv::svex-rewrite-fncall-once)
(profile-fn 'sv::svex-rewrite-under-subst)
(profile-fn 'sv::svex-rewrite)
(profile-fn 'sv::svex-argmasks)

(profile-fn 'sv::svexlist-compute-masks)
(profile-fn 'sv::svexlist-mask-alist)
(profile-fn 'sv::svexlist-toposort)
(profile-fn 'sv::svexlist-mask-acons)
(loop for x in sv::*svex-op-table* do
      (let ((name (intern$ (str::cat "SVMASK-FOR-" (symbol-name (car x))) "SV")))
        (profile-fn (deref-macro-name name (macro-aliases (w *the-live-state*))))))

(profile-fn 'sv::svex-to-rsh-of-concat-table)
(profile-fn 'sv::rsh-of-concat-table-lookup)
(profile-fn 'sv::svex-subst)
(profile-fn 'sv::svexlist-multirefs-top)
||#
