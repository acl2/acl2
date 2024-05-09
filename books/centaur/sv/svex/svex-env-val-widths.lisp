; SV - Symbolic Vector Hardware Analysis Framework
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "eval")
(include-book "centaur/fgl/def-fgl-rewrite" :dir :System)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (disable unsigned-byte-p signed-byte-p)))

(local (std::add-default-post-define-hook :fix))

(local (defthm signed-byte-p-implies-width-type
         (implies (signed-byte-p n x)
                  (posp n))
         :hints(("Goal" :in-theory (enable signed-byte-p)))
         :rule-classes :forward-chaining))

(define 2vec-width-p ((w integerp)
                      (x 4vec-p))
  (and (2vec-p x)
       (b* ((w (lifix w)))
         (if (<= 0 w)
             (unsigned-byte-p w (2vec->val x))
           (signed-byte-p (- w) (2vec->val x)))))
  ///
  (defthmd 2vec-width-p-to-byte-p-redef
    (equal (2vec-width-p w x)
           (let ((w (ifix w))
                 (x (4vec-fix x)))
             (if (<= 0 w)
                 (unsigned-byte-p w x)
               (signed-byte-p (- w) x))))
    :hints(("Goal" :in-theory (enable 2vec-p 2vec->val 4vec-fix 4vec-p 4vec->upper 4vec->lower 4vec))))
  
  (defthmd 2vec-width-p-to-byte-p
    (implies (syntaxp (quotep w))
             (equal (2vec-width-p w x)
                    (let ((w (ifix w))
                          (x (4vec-fix x)))
                      (if (<= 0 w)
                          (unsigned-byte-p w x)
                        (signed-byte-p (- w) x)))))
    :hints(("Goal" :in-theory (enable 2vec-p 2vec->val 4vec-fix 4vec-p 4vec->upper 4vec->lower 4vec))))

  (fgl::remove-fgl-rewrite 2vec-width-p)
  
  (fgl::def-fgl-rewrite 2vec-width-p-to-byte-p-fgl
    (implies (syntaxp (integerp w))
             (equal (2vec-width-p w x)
                    (let ((w (ifix w))
                          (x (4vec-fix x)))
                      (if (<= 0 w)
                          (unsigned-byte-p w x)
                        (signed-byte-p (- w) x)))))
    :hints(("Goal" :in-theory (e/d ()
                                   (2vec-width-p))
            :use 2vec-width-p-to-byte-p))))


(encapsulate nil
  (local
   (defthmd signed-byte-p-when-unsigned-byte-p-1
     (implies (unsigned-byte-p n x)
              (signed-byte-p (+ 1 n) x))
     :hints(("Goal" :in-theory (enable signed-byte-p unsigned-byte-p)))))

  (defthm signed-byte-p-when-unsigned-byte-p
    (implies (and (unsigned-byte-p n x)
                  (integerp m)
                  (< n m))
              (signed-byte-p m x))
    :hints(("Goal" :use (signed-byte-p-when-unsigned-byte-p-1
                         (:instance bitops::signed-byte-p-monotonicity
                          (a (+ 1 n)) (b m)))
            :in-theory (disable bitops::signed-byte-p-monotonicity)
            :do-not-induct t))))
                 


(define 2vec-width-<= ((x integerp) (y integerp))
  ;; True whenever for all v, (2vec-width-p x v) implies (2vec-width-p y v).
  (b* ((x (lifix x))
       (y (lifix y)))
    (if (<= 0 x)
        (or (<= x y)
            (< y (- x)))
      (<= y x)))
  ///
  (defthm 2vec-width-<=-implies
    (implies (and (2vec-width-<= x y)
                  (2vec-width-p x v))
             (2vec-width-p y v))
    :hints(("Goal" :in-theory (enable 2vec-width-p)))
    :otf-flg t))

(defalist svar-widths :key-type svar :val-type integerp :true-listp t)

(define svex-env-val-widths-p-aux ((widths svar-widths-p)
                                   (x svex-env-p))
  (if (atom widths)
      t
    (if (mbt (consp (car widths)))
        (and (2vec-width-p (cdar widths) (svex-env-lookup (caar widths) x))
             (svex-env-val-widths-p-aux (cdr widths) x))
      (svex-env-val-widths-p-aux (cdr widths) x)))
  ///
  (local (in-theory (enable svar-widths-fix))))

(define svex-env-val-widths-p ((widths svar-widths-p)
                               (x svex-env-p))
  :verify-guards nil
  (mbe :logic (if (atom widths)
                  t
                (if (mbt (consp (car widths)))
                    (and (2vec-width-p (cdar widths) (svex-env-lookup (caar widths) x))
                         (svex-env-val-widths-p (cdr widths) x))
                  (svex-env-val-widths-p (cdr widths) x)))
       :exec (with-fast-alist x (svex-env-val-widths-p-aux widths x)))
  ///
  (local (defthm svex-env-val-widths-p-aux-elim
           (equal (svex-env-val-widths-p-aux widths x)
                  (svex-env-val-widths-p widths x))
           :hints(("Goal" :in-theory (enable svex-env-val-widths-p-aux)))))
  
  (verify-guards svex-env-val-widths-p)
  
  (defthm 2vec-width-p-lookup-when-svex-env-val-widths-p
    (implies (and (svex-env-val-widths-p widths x)
                  (equal v1 (svar-fix v))
                  (hons-assoc-equal v1 widths))
             (2vec-width-p (cdr (hons-assoc-equal v1 widths))
                           (svex-env-lookup v x))))

  (defthm svex-env-val-widths-p-of-cons
    (implies (and (syntaxp (quotep val))
                  (equal val1 (ifix val))
                  (if (<= 0 val1)
                      (unsigned-byte-p val1 (svex-env-lookup var x))
                    (signed-byte-p val1 (svex-env-lookup var x)))
                  (svex-env-val-widths-p w2 x))
             (svex-env-val-widths-p (cons (cons var val)
                                               w2)
                                         x))
    :hints(("Goal" :in-theory (enable 2vec-width-p-to-byte-p-redef
                                      svex-env-lookup
                                      svex-env-val-widths-p))))

  (defthm svex-env-val-widths-p-of-nil
    (svex-env-val-widths-p nil x))
  
  (local (in-theory (enable svar-widths-fix))))


(define svar-widths-combine ((x svar-widths-p) (y svar-widths-p))
  ;; y should be fast
  ;; makes a new svar-widths that implies x and y
  :returns (combine svar-widths-p)
  (if (atom x)
      (svar-widths-fix y)
    (if (mbt (consp (car x)))
        (b* (((cons key xval) (car x))
             (y (svar-widths-fix y))
             (ylook (hons-get (svar-fix key) y))
             ((unless (and ylook (2vec-width-<= (cdr ylook) xval)))
              (svar-widths-combine (cdr x) (hons-acons (svar-fix key)
                                                             (lifix xval)
                                                             y))))
          (svar-widths-combine (cdr x) y))
      (svar-widths-combine (cdr x) y)))

  ///
  (fty::deffixequiv svar-widths-combine
    :hints(("Goal" :in-theory (enable svar-widths-fix))))
  
  (defret svex-env-val-widths-p-of-<fn>-when-not-second
    (implies (not (svex-env-val-widths-p y env))
             (not (svex-env-val-widths-p combine env)))
    :hints (("goal" :in-theory (enable svex-env-val-widths-p)
             :induct <call>)))

  (defret svex-env-val-widths-p-of-<fn>-when-not-first
    (implies (not (svex-env-val-widths-p x env))
             (not (svex-env-val-widths-p combine env)))
    :hints (("goal" :in-theory (enable svex-env-val-widths-p)
             :induct <call>)
            (and stable-under-simplificationp
                 '(:use ((:instance svex-env-val-widths-p-of-<fn>-when-not-second
                          (x (cdr x))))
                   :in-theory (disable svex-env-val-widths-p-of-<fn>-when-not-second)))))
  
  (defret svex-env-val-widths-p-of-<fn>-when-second
    (implies (svex-env-val-widths-p y env)
             (equal (svex-env-val-widths-p combine env)
                    (svex-env-val-widths-p x env)))
    :hints(("Goal" :in-theory (enable svex-env-val-widths-p)
            :induct <call>)))

  (defret svex-env-val-widths-p-of-<fn>-when-first
    (implies (svex-env-val-widths-p x env)
             (equal (svex-env-val-widths-p combine env)
                    (svex-env-val-widths-p y env)))
    :hints(("Goal" :cases ((svex-env-val-widths-p y env))
            :do-not-induct t))))

(define svar-widths-combine-top ((x svar-widths-p) (y svar-widths-p))
  :enabled t
  (mbe :logic (svar-widths-combine x y)
       :exec
       (fast-alist-free (svar-widths-combine x (make-fast-alist y)))))


(define svar-widths-reduce ((x svar-widths-p) (y svar-widths-p))
  ;; y should be fast
  ;; makes a new svar-widths such that it and y imply x
  :returns (reduce svar-widths-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (b* (((cons key xval) (car x))
             (y (svar-widths-fix y))
             (ylook (hons-get (svar-fix key) y))
             ((unless (and ylook (2vec-width-<= (cdr ylook) xval)))
              (cons (cons (svar-fix key)
                          (lifix xval))
                    (svar-widths-reduce (cdr x) y))))
          (svar-widths-reduce (cdr x) y))
      (svar-widths-reduce (cdr x) y)))

  ///
  (fty::deffixequiv svar-widths-reduce
    :hints(("Goal" :in-theory (enable svar-widths-fix))))
  
  (defret svex-env-val-widths-p-of-<fn>-when-first
    (implies (svex-env-val-widths-p x env)
             (svex-env-val-widths-p reduce env))
    :hints(("Goal" :in-theory (enable svex-env-val-widths-p)
            :induct <call>)))

  (defret svex-env-val-widths-p-of-<fn>-when-second
    (implies (svex-env-val-widths-p y env)
             (equal (svex-env-val-widths-p reduce env)
                    (svex-env-val-widths-p x env)))
    :hints(("Goal" :in-theory (enable svex-env-val-widths-p)
            :induct <call>))))

(define svar-widths-reduce-top ((x svar-widths-p) (y svar-widths-p))
  :enabled t
  (mbe :logic (svar-widths-reduce x y)
       :exec (with-fast-alist y
               (svar-widths-reduce x y))))


(define svar-widths-implies ((y svar-widths-p) (x svar-widths-p))
  ;; y should be fast
  ;; checks whether y implies x
  :returns (implies)
  (if (atom x)
      t
    (if (mbt (consp (car x)))
        (b* (((cons key xval) (car x))
             (y (svar-widths-fix y))
             (ylook (hons-get (svar-fix key) y))
             ((unless (and ylook (2vec-width-<= (cdr ylook) xval)))
              nil))
          (svar-widths-implies y (cdr x)))
      (svar-widths-implies y (cdr x))))

  ///
  (fty::deffixequiv svar-widths-implies
    :hints(("Goal" :in-theory (enable svar-widths-fix))))
  
  (defret svex-env-val-widths-p-when-<fn>
    (implies (and implies
                  (svex-env-val-widths-p y env))
             (svex-env-val-widths-p x env))
    :hints(("Goal" :in-theory (enable svex-env-val-widths-p)
            :induct <call>))))

(define svar-widths-implies-top ((y svar-widths-p) (x svar-widths-p))
  :enabled t
  (mbe :logic (svar-widths-implies y x)
       :exec (with-fast-alist y
               (svar-widths-implies y x))))


(define svar-widths-helps ((y svar-widths-p) (x svar-widths-p))
  ;; y should be fast
  ;; checks whether y implies anything in x
  ;; this isn't symmetrical which is why I didn't call it svar-widths-intersect
  ;; This is basically just for heuristic use
  :returns (implies)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (b* (((cons key xval) (car x))
             (y (svar-widths-fix y))
             (ylook (hons-get (svar-fix key) y))
             ((unless (and ylook (2vec-width-<= (cdr ylook) xval)))
              (svar-widths-helps y (cdr x))))
          t)
      (svar-widths-helps y (cdr x))))
  ///
  (local (in-theory (enable svar-widths-fix))))

(define svar-widths-helps-top ((y svar-widths-p) (x svar-widths-p))
  :enabled t
  (mbe :logic (svar-widths-helps y x)
       :exec (with-fast-alist y
               (svar-widths-helps y x))))

;; Rewriting theory for svex-env-val-widths-p hyps/conclusions.

;; It's easy enough to relieve a svex-env-val-widths-p, unsigned-byte-p, or
;; signed-byte-p given some known svex-env-val-widths-p hyp about that env.
;; The problem is when there's more than one such hyp, or some combination of
;; svex-env-val-widths-p and unsigned-byte/signed-byte hyps.

;; Idea: we'll collect up all such known-true facts from the type-alist into a
;; list of svar-widths objects.  We then union them together into one
;; svar-widths object and use that to relieve the current problem.

;; For unsigned-byte-p and signed-byte-p calls we can instead just search the
;; known true facts for the one that implies it, rather than consing so much.

(fty::deflist svar-widthslist :elt-type svar-widths :true-listp t)

;; This function just checks a list of svar-widths objects against an env. In
;; the rewriting theory it's only used to validate the collected known-true
;; svar-widths objects.

(define svex-env-val-widths-p-list ((w svar-widthslist-p)
                                    (x svex-env-p))
  (if (atom w)
      t
    (and (svex-env-val-widths-p (car w) x)
         (svex-env-val-widths-p-list (cdr w) x)))
  ///
  (defthm svex-env-val-widths-p-list-of-nil
    (svex-env-val-widths-p-list nil x))

  (defthm svex-env-val-widths-p-list-of-cons
    (implies (and (svex-env-val-widths-p w1 x)
                  (svex-env-val-widths-p-list w2 x))
             (svex-env-val-widths-p-list (cons w1 w2) x))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm svex-env-val-widths-p-list-of-cons-singleton
    (implies (and (syntaxp (quotep val))
                  (equal val1 (ifix val))
                  (if (<= 0 val1)
                      (unsigned-byte-p val1 (svex-env-lookup var x))
                    (signed-byte-p val1 (svex-env-lookup var x)))
                  (svex-env-val-widths-p-list w2 x))
             (svex-env-val-widths-p-list (cons (list (cons var val))
                                               w2)
                                         x))
    :hints(("Goal" :in-theory (enable 2vec-width-p-to-byte-p-redef
                                      svex-env-val-widths-p)))
    :rule-classes ((:rewrite :backchain-limit-lst (nil nil 0 nil)))))

(define svar-widthslist-combine ((w svar-widthslist-p))
  :returns (widths svar-widths-p)
  (if (atom w)
      nil
    (if (atom (cdr w))
        (make-fast-alist (svar-widths-fix (car w)))
      (svar-widths-combine (car w)
                                   (svar-widthslist-combine (cdr w)))))
  ///
  (defthm svex-env-val-widths-p-of-<fn>
    (iff (svex-env-val-widths-p (svar-widthslist-combine w) x)
         (svex-env-val-widths-p-list w x))
    :hints(("Goal" :in-theory (enable svex-env-val-widths-p-list)))))




;; Collect the svar-widthslist of all the relevant svex-env-val-widths-p hyps for a given env.


(with-output :off (event)
  (define bind-collected-svar-widthlist-rec ((targetval svar-widths-p)
                                           env ;; term
                                           type-alist)
  ;; produces a constant, since it collects only constants
  :prepwork ((local (in-theory (disable default-car default-cdr (tau-system)))))
  :hooks nil
  (if (atom type-alist)
      nil
    (b* (((unless (and (consp (car type-alist))
                       (consp (cdar type-alist))))
          (bind-collected-svar-widthlist-rec targetval env (cdr type-alist)))
         ((cons term (cons ts ?ttree)) (car type-alist))
         ((unless (and (integerp ts)
                       (<= acl2::*min-type-set* ts)
                       (<= ts acl2::*max-type-set*)))
          ;; huh.
          (bind-collected-svar-widthlist-rec targetval env (cdr type-alist)))
         ((unless (acl2::ts= (acl2::ts-intersection ts acl2::*ts-nil*) 0))
          ;; Type set intersects with that of NIL, meaning we're not assuming this term to be true
          (bind-collected-svar-widthlist-rec targetval env (cdr type-alist))))
      (case-match term
        (('svex-env-val-widths-p ('quote widths) e)
         (if (and (equal e env)
                  (svar-widths-p widths)
                  (svar-widths-helps-top widths targetval))
             (cons widths (bind-collected-svar-widthlist-rec targetval env (cdr type-alist)))
           (bind-collected-svar-widthlist-rec targetval env (cdr type-alist))))
        (('unsigned-byte-p ('quote n) ('svex-env-lookup ('quote k) e))
         (if (and (equal e env)
                  (natp n)
                  (svar-p k))
             (b* ((widths `((,k . ,n))))
               (if (svar-widths-helps-top widths targetval)
                   (cons widths (bind-collected-svar-widthlist-rec targetval env (cdr type-alist)))
                 (bind-collected-svar-widthlist-rec targetval env (cdr type-alist))))
           (bind-collected-svar-widthlist-rec targetval env (cdr type-alist))))
        (('signed-byte-p ('quote n) ('svex-env-lookup ('quote k) e))
         (if (and (equal e env)
                  (posp n)
                  (svar-p k))
             (b* ((widths `((,k . ,(- n)))))
               (if (svar-widths-helps-top widths targetval)
                   (cons widths (bind-collected-svar-widthlist-rec targetval env (cdr type-alist)))
                 (bind-collected-svar-widthlist-rec targetval env (cdr type-alist))))
           (bind-collected-svar-widthlist-rec targetval env (cdr type-alist))))
        (& (bind-collected-svar-widthlist-rec targetval env (cdr type-alist))))))))
         
         
    


(define bind-collected-svar-widthlist ((target pseudo-termp)
                                       (env pseudo-termp)
                                       mfc state)
  (declare (xargs :stobjs state)
           (ignorable state))
  :hooks nil
  (b* (((unless (quotep target)) nil)
       (targetval (unquote target))
       ((unless (svar-widths-p targetval))
        (cw "bad targetval~%"))
       ((unless (consp targetval))
        ;; too trivial for this method
        nil)
       (widths (bind-collected-svar-widthlist-rec targetval env (mfc-type-alist mfc)))
       ((unless (consp widths))
        nil))
    ;; (cw "widths: ~x0~%" widths)
    `((widths . ',widths))))



(defthm svex-env-val-widths-p-by-type-alist
  (implies (and (bind-free (bind-collected-svar-widthlist target env mfc state)
                           (widths))
                (svex-env-val-widths-p-list widths env)
                (equal new-widths (svar-widths-reduce-top target (svar-widthslist-combine widths)))
                ;; (svar-widths-implies (svar-widthslist-combine widths) target)
                )
           (equal (svex-env-val-widths-p target env)
                  (svex-env-val-widths-p new-widths env))))


(with-output :off (event)
  (define bind-first-relevant-svar-widths-rec ((targetval svar-widths-p)
                                               env ;; term
                                               type-alist)
  ;; produces a substitution giving the first widths that are relevant
  :prepwork ((local (in-theory (disable default-car default-cdr (tau-system)))))
  :hooks nil
  (if (atom type-alist)
      nil
    (b* (((unless (and (consp (car type-alist))
                       (consp (cdar type-alist))))
          (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist)))
         ((cons term (cons ts ?ttree)) (car type-alist))
         ((unless (and (integerp ts)
                       (<= acl2::*min-type-set* ts)
                       (<= ts acl2::*max-type-set*)))
          ;; huh.
          (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist)))
         ((unless (acl2::ts= (acl2::ts-intersection ts acl2::*ts-nil*) 0))
          ;; Type set intersects with that of NIL, meaning we're not assuming this term to be true
          (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist))))
      (case-match term
        (('svex-env-val-widths-p ('quote widths) e)
         (if (and (equal e env)
                  (svar-widths-p widths)
                  (svar-widths-helps-top widths targetval))
             `((widths . ',widths))
           (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist))))
        (('unsigned-byte-p ('quote n) ('svex-env-lookup ('quote k) e))
         (if (and (equal e env)
                  (natp n)
                  (svar-p k))
             (b* ((widths `((,k . ,n))))
               (if (svar-widths-helps-top widths targetval)
                   `((widths . ',widths))
                 (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist))))
           (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist))))
        (('signed-byte-p ('quote n) ('svex-env-lookup ('quote k) e))
         (if (and (equal e env)
                  (posp n)
                  (svar-p k))
             (b* ((widths `((,k . ,(- n)))))
               (if (svar-widths-helps-top widths targetval)
                   `((widths . ',widths))
                 (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist))))
           (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist))))
        (& (bind-first-relevant-svar-widths-rec targetval env (cdr type-alist))))))))


(define bind-first-relevant-svar-widths ((target pseudo-termp)
                                       (env pseudo-termp)
                                       mfc state)
  (declare (xargs :stobjs state)
           (ignorable state))
  :hooks nil
  (b* (((unless (quotep target)) nil)
       (targetval (unquote target))
       ((unless (svar-widths-p targetval))
        (cw "bad targetval~%"))
       ((unless (consp targetval))
        ;; too trivial for this method
        nil)
       (widths (bind-first-relevant-svar-widths-rec targetval env (mfc-type-alist mfc))))
    ;; (cw "widths: ~x0~%" widths)
    widths))



(defthm unsigned-byte-p-by-svex-env-val-widths-from-type-alist
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (natp n)
                (svar-p k)
                (equal target `((,k . ,n)))
                (bind-free (bind-first-relevant-svar-widths target env mfc state)
                           (widths))
                (svex-env-val-widths-p-list (list widths) env)
                (svar-widths-implies-top widths target))
           (unsigned-byte-p n (svex-env-lookup k env)))
  :hints(("Goal" :in-theory (e/d (svex-env-val-widths-p-list
                                  2vec-width-p-to-byte-p-redef)
                                 (svex-env-val-widths-p-when-svar-widths-implies))
          :use ((:instance svex-env-val-widths-p-when-svar-widths-implies
                 (y widths) (x (list (cons k n)))))
          :expand ((svex-env-val-widths-p (list (cons k n)) env)))))


(defthm signed-byte-p-by-svex-env-val-widths-from-type-alist
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (posp n)
                (svar-p k)
                (equal target `((,k . ,(- n))))
                (bind-free (bind-first-relevant-svar-widths target env mfc state)
                           (widths))
                (svex-env-val-widths-p-list (list widths) env)
                (svar-widths-implies-top widths target))
           (signed-byte-p n (svex-env-lookup k env)))
  :hints(("Goal" :in-theory (e/d (svex-env-val-widths-p-list
                                  2vec-width-p-to-byte-p-redef)
                                 (svex-env-val-widths-p-when-svar-widths-implies))
          :use ((:instance svex-env-val-widths-p-when-svar-widths-implies
                 (y widths) (x (list (cons k (- n))))))
          :expand ((svex-env-val-widths-p (list (cons k (- n))) env)))))




(with-output :off (event)
  (define bind-first-integerp-relevant-svar-widths-rec (key
                                                        env ;; term
                                                        type-alist)
  ;; produces a substitution giving the first widths that are relevant
  :prepwork ((local (in-theory (disable default-car default-cdr (tau-system)))))
  :hooks nil
  (if (atom type-alist)
      nil
    (b* (((unless (and (consp (car type-alist))
                       (consp (cdar type-alist))))
          (bind-first-integerp-relevant-svar-widths-rec key env (cdr type-alist)))
         ((cons term (cons ts ?ttree)) (car type-alist))
         ((unless (and (integerp ts)
                       (<= acl2::*min-type-set* ts)
                       (<= ts acl2::*max-type-set*)))
          ;; huh.
          (bind-first-integerp-relevant-svar-widths-rec key env (cdr type-alist)))
         ((unless (acl2::ts= (acl2::ts-intersection ts acl2::*ts-nil*) 0))
          ;; Type set intersects with that of NIL, meaning we're not assuming this term to be true
          (bind-first-integerp-relevant-svar-widths-rec key env (cdr type-alist))))
      (case-match term
        (('svex-env-val-widths-p ('quote widths) e)
         (if (and (equal e env)
                  (svar-widths-p widths))
             (b* ((widths (make-fast-alist widths)))
               (if (cdr (hons-get key widths))
                   `((widths . ',widths))
                 (bind-first-integerp-relevant-svar-widths-rec key env (cdr type-alist))))
           (bind-first-integerp-relevant-svar-widths-rec key env (cdr type-alist))))
        (& (bind-first-integerp-relevant-svar-widths-rec key env (cdr type-alist))))))))

(define bind-first-integerp-relevant-svar-widths ((key pseudo-termp)
                                                  (env pseudo-termp)
                                                  mfc state)
  (declare (xargs :stobjs state)
           (ignorable state))
  :hooks nil
  (b* (((unless (quotep key)) nil)
       (keyname (unquote key))
       ((unless (svar-p keyname))
        (cw "bad key~%"))
       (widths (bind-first-integerp-relevant-svar-widths-rec keyname env (mfc-type-alist mfc))))
    widths))


(defthm integerp-by-svex-env-val-widths-from-type-alist
  (implies (and (syntaxp (quotep k))
                (svar-p k)
                (bind-free (bind-first-integerp-relevant-svar-widths k env mfc state)
                           (widths))
                (svex-env-val-widths-p-list (list widths) env)
                (hons-get k widths))
           (integerp (svex-env-lookup k env)))
  :hints(("Goal" :in-theory (e/d (svex-env-val-widths-p-list
                                  2vec-width-p-to-byte-p-redef)
                                 (2vec-width-p-lookup-when-svex-env-val-widths-p))
          :use ((:instance 2vec-width-p-lookup-when-svex-env-val-widths-p
                 (x env) (v k) (v1 k))))))


(with-output :off (event)
  (define bind-first-natp-relevant-svar-widths-rec (key
                                                    env ;; term
                                                    type-alist)
    ;; produces a substitution giving the first widths that are relevant
    :prepwork ((local (in-theory (disable default-car default-cdr (tau-system)))))
    :hooks nil
    (if (atom type-alist)
        nil
      (b* (((unless (and (consp (car type-alist))
                         (consp (cdar type-alist))))
            (bind-first-natp-relevant-svar-widths-rec key env (cdr type-alist)))
           ((cons term (cons ts ?ttree)) (car type-alist))
           ((unless (and (natp ts)
                         (<= acl2::*min-type-set* ts)
                         (<= ts acl2::*max-type-set*)))
            ;; huh.
            (bind-first-natp-relevant-svar-widths-rec key env (cdr type-alist)))
           ((unless (acl2::ts= (acl2::ts-intersection ts acl2::*ts-nil*) 0))
            ;; Type set intersects with that of NIL, meaning we're not assuming this term to be true
            (bind-first-natp-relevant-svar-widths-rec key env (cdr type-alist))))
        (case-match term
          (('svex-env-val-widths-p ('quote widths) e)
           (if (and (equal e env)
                    (svar-widths-p widths))
               (b* ((widths (make-fast-alist widths)))
                 (if (natp (cdr (hons-get key widths)))
                     `((widths . ',widths))
                   (bind-first-integerp-relevant-svar-widths-rec key env (cdr type-alist))))
             (bind-first-natp-relevant-svar-widths-rec key env (cdr type-alist))))
          (& (bind-first-natp-relevant-svar-widths-rec key env (cdr type-alist))))))))

(define bind-first-natp-relevant-svar-widths ((key pseudo-termp)
                                                  (env pseudo-termp)
                                                  mfc state)
  (declare (xargs :stobjs state)
           (ignorable state))
  :hooks nil
  (b* (((unless (quotep key)) nil)
       (keyname (unquote key))
       ((unless (svar-p keyname))
        (cw "bad key~%"))
       (widths (bind-first-natp-relevant-svar-widths-rec keyname env (mfc-type-alist mfc))))
    widths))

(defthm natp-by-svex-env-val-widths-from-type-alist
  (implies (and (syntaxp (quotep k))
                (svar-p k)
                (bind-free (bind-first-natp-relevant-svar-widths k env mfc state)
                           (widths))
                (svex-env-val-widths-p-list (list widths) env)
                (natp (cdr (hons-get k widths))))
           (natp (svex-env-lookup k env)))
  :hints(("Goal" :in-theory (e/d (svex-env-val-widths-p-list
                                  2vec-width-p-to-byte-p-redef)
                                 (2vec-width-p-lookup-when-svex-env-val-widths-p))
          :use ((:instance 2vec-width-p-lookup-when-svex-env-val-widths-p
                 (x env) (v k) (v1 k))))))




(local
 (encapsulate nil

   (defund p (x)
     (svex-env-val-widths-p '((a . 1) (b . 1) (c . -3) (d . 2)) x))

   (defthm p-when-svex-env-val-widths-p
     (implies (svex-env-val-widths-p '((a . 1) (b . 1) (c . 2) (d . 2)) x)
              (p x))
     :hints(("Goal" :in-theory (enable p))))

   (defun my-bind-free-for-proving-svex-env-val-widths-p (target env mfc state)
     (declare (xargs :stobjs state)
              (ignorable target env state))
     (cw "type-alist: ~x0~%" (mfc-type-alist mfc)))


   (defthm prove-p
     (implies (and (svex-env-val-widths-p '((b . 1) (c . 1)) x)
                   (svex-env-val-widths-p '((a . 1) (b . 1) (e . 2)) x)
                   (unsigned-byte-p 2 (svex-env-lookup 'd x)))
              (p x)))

   (defund q (x)
     (signed-byte-p 3 (svex-env-lookup 'q x)))

   (defthm q-when-signed-byte-p
     (implies (signed-byte-p 3 (svex-env-lookup 'q x))
              (q x))
     :hints(("Goal" :in-theory (enable q))))

   (defthm prove-q-1
     (implies (and (svex-env-val-widths-p '((b . 1) (c . 1)) x)
                   (svex-env-val-widths-p '((a . 1) (b . 1) (e . 2)) x)
                   (svex-env-val-widths-p '((a . 2) (b . 4) (q . -2)) x)
                   (unsigned-byte-p 2 (svex-env-lookup 'd x)))
              (q x)))

   (defund r (x)
     (integerp (svex-env-lookup 'r x)))

   (defthm r-when-integerp
     (implies (integerp (svex-env-lookup 'r x))
              (r x))
     :hints(("Goal" :in-theory (enable r))))

   (defthm prove-r
     (implies (and (svex-env-val-widths-p '((b . 1) (c . 1)) x)
                   (svex-env-val-widths-p '((a . 1) (r . -1) (e . 2)) x)
                   (svex-env-val-widths-p '((a . 2) (b . 4) (q . -2)) x)
                   (unsigned-byte-p 2 (svex-env-lookup 'd x)))
              (r x)))))

  
