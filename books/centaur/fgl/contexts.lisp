; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "FGL")

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "logicman")
(include-book "centaur/misc/starlogic" :dir :system)

(local (std::add-default-post-define-hook :fix))

(define equiv-context-p (x)
  (or (pseudo-fnsym-p x)
      (and (consp x)
           (pseudo-termp (car x))
           (equiv-context-p (cdr x))))
  ///
  (define equiv-context-fix ((x equiv-context-p))
    :Returns (new-x equiv-context-p)
    (mbe :logic (if (atom x)
                    (pseudo-fnsym-fix x)
                  (cons (pseudo-term-fix (car x))
                        (equiv-context-fix (cdr x))))
         :exec x)
    ///
    (defthm equiv-context-fix-when-equiv-context-p
      (implies (equiv-context-p x)
               (equal (equiv-context-fix x) x)))

    ;; (defthm len-of-equiv-context-fix
    ;;   (equal (len (equiv-context-fix x)) (len x)))

    (fty::deffixtype equiv-context :pred equiv-context-p :fix equiv-context-fix :equiv equiv-context-equiv
      :define t))

  (defthm pseudo-fnsym-p-of-equiv-context-when-atom
    (implies (atom x)
             (equal (equiv-context-p x)
                    (pseudo-fnsym-p x))))

  (defthm equiv-context-p-of-cdr
    (implies (equiv-context-p x)
             (equiv-context-p (cdr x)))))


(fty::deflist equiv-contexts :pred equiv-contextsp :elt-type equiv-context-p :true-listp t)

(local (defthm equal-of-equiv-context-fix
         (implies (equal (equiv-context-fix x) y)
                  (equiv-context-equiv x y))
         :rule-classes :forward-chaining))


(define fgl-ev-equiv-context-equiv-base ((context equiv-context-p) x y)
  :measure (len (equiv-context-fix context))
  (b* ((context (equiv-context-fix context)))
    (cond ((atom context)
           (and (fgl-ev (pseudo-term-fncall context (list (pseudo-term-quote x)
                                                          (pseudo-term-quote y)))
                        nil)
                t))
          (t (fgl-ev-equiv-context-equiv-base
              (cdr context)
              (fgl-ev (car context) `((x . ,x)))
              (fgl-ev (car context) `((x . ,y)))))))
  ///
  (defthm fgl-ev-equiv-context-equiv-base-of-equal
    (equal (fgl-ev-equiv-context-equiv-base 'equal x y)
           (equal x y)))

  (defthm fgl-ev-equiv-context-equiv-base-of-iff
    (equal (fgl-ev-equiv-context-equiv-base 'iff x y)
           (iff* x y)))

  (defthm fgl-ev-equiv-context-equiv-base-of-unequiv
    (equal (fgl-ev-equiv-context-equiv-base 'unequiv x y)
           t)))



(define fgl-ev-context-equiv-some ((contexts equiv-contextsp) x y)
  (if (atom contexts)
      (equal x y)
    (or (fgl-ev-equiv-context-equiv-base (car contexts) x y)
        (fgl-ev-context-equiv-some (cdr contexts) x y)))
  ///
  (defthm fgl-ev-context-equiv-some-reflective
    (fgl-ev-context-equiv-some contexts x x))
  
  (defthm fgl-ev-context-equiv-some-nil
    (equal (fgl-ev-context-equiv-some nil x y)
           (equal x y)))

  (defthm fgl-ev-context-equiv-some-iff
    (equal (fgl-ev-context-equiv-some '(iff) x y)
           (iff* x y)))

  (defthm fgl-ev-context-equiv-some-when-member-iff
    (implies (and (member 'iff (equiv-contexts-fix contexts))
                  (iff* x y))
             (equal (fgl-ev-context-equiv-some contexts x y) t))
    :hints(("Goal" :in-theory (enable equiv-contexts-fix))))

  (defthm fgl-ev-context-equiv-some-unequiv
    (equal (fgl-ev-context-equiv-some '(unequiv) x y)
           t))

  (defthm fgl-ev-context-equiv-some-member-unequiv
    (implies (member 'unequiv (equiv-contexts-fix contexts))
             (equal (fgl-ev-context-equiv-some contexts x y)
                    t))
    :hints(("Goal" :in-theory (enable equiv-contexts-fix)))))

(define fgl-ev-context-equiv-symm ((contexts equiv-contextsp) x y)
  (or (fgl-ev-context-equiv-some contexts x y)
      (fgl-ev-context-equiv-some contexts y x))
  ///
  (defthm fgl-ev-context-equiv-symm-of-equal
    (equal (fgl-ev-context-equiv-symm nil x y)
           (equal x y)))

  (defthm fgl-ev-context-equiv-symm-of-iff
    (equal (fgl-ev-context-equiv-symm '(iff) x y)
           (iff* x y)))

  (defthm fgl-ev-context-equiv-symm-when-member-iff
    (implies (and (member 'iff (equiv-contexts-fix contexts))
                  (iff* x y))
             (equal (fgl-ev-context-equiv-symm contexts x y) t)))

  (defthm fgl-ev-context-equiv-symm-of-unequiv
    (equal (fgl-ev-context-equiv-symm '(unequiv) x y)
           t))

  (defthm fgl-ev-context-equiv-symm-when-member-unequiv
    (implies (member 'unequiv (equiv-contexts-fix contexts))
             (equal (fgl-ev-context-equiv-symm contexts x y)
                    t)))

  (defthm fgl-ev-context-equiv-symm-symmetric
    (implies (fgl-ev-context-equiv-symm contexts x y)
             (fgl-ev-context-equiv-symm contexts y x))))



(local (defthm car-last-of-append
         (equal (car (last (append x y)))
                (if (consp y)
                    (car (last y))
                  (car (last x))))))

(local (defthm car-last-of-rev
         (equal (car (last (rev x)))
                (car x))
         :hints(("Goal" :in-theory (enable rev)))))

(local (defthm car-of-rev
         (equal (car (rev x))
                (car (last x)))
         :hints(("Goal" :in-theory (enable rev)))))

(define fgl-ev-context-equiv-trace ((contexts equiv-contextsp) (trace true-listp))
  (if (atom (cdr trace))
      t
    (and (fgl-ev-context-equiv-symm contexts (car trace) (cadr trace))
         (fgl-ev-context-equiv-trace contexts (cdr trace))))
  ///
  (defthm fgl-ev-context-equiv-trace-of-append
    (implies (And (fgl-ev-context-equiv-trace contexts trace1)
                  (fgl-ev-context-equiv-trace contexts trace2)
                  (implies (and (consp trace1) (consp trace2))
                           (fgl-ev-context-equiv-symm contexts (car (last trace1)) (car trace2))))
             (fgl-ev-context-equiv-trace contexts
                                               (append trace1 trace2))))

  (defthm fgl-ev-context-equiv-trace-implies-cdr
    (implies (fgl-ev-context-equiv-trace contexts trace)
             (fgl-ev-context-equiv-trace contexts (cdr trace))))

  (defthm fgl-ev-context-equiv-trace-implies-first
    (implies (and (fgl-ev-context-equiv-trace contexts trace)
                  (consp (cdr trace)))
             (fgl-ev-context-equiv-symm contexts (car trace) (cadr trace))))

  (defthm fgl-ev-context-equiv-trace-of-single
    (fgl-ev-context-equiv-trace contexts (list x)))

  (defthm fgl-ev-context-equiv-trace-of-two
    (iff (fgl-ev-context-equiv-trace contexts (list x y))
         (fgl-ev-context-equiv-symm contexts x y)))
                           
  (defthm fgl-ev-context-equiv-trace-of-rev
    (implies (fgl-ev-context-equiv-trace contexts trace)
             (fgl-ev-context-equiv-trace contexts (rev trace)))
    :hints (("goal" :induct (rev trace) :in-theory (enable rev)
             :do-not-induct t)))

  (defthm fgl-ev-context-equiv-trace-not-equal
    (implies (not (equal (car (last trace)) (car trace)))
             (not (fgl-ev-context-equiv-trace nil trace))))

  (defthm fgl-ev-context-equiv-trace-not-iff
    (implies (not (iff* (car (last trace)) (car trace)))
             (not (fgl-ev-context-equiv-trace '(iff) trace))))

  (defthm fgl-ev-context-equiv-trace-unequiv
    (equal (fgl-ev-context-equiv-trace '(unequiv) trace) t))

  (defthm fgl-ev-context-equiv-trace-when-member-unequiv
    (implies (member 'unequiv (equiv-contexts-fix contexts))
             (equal (fgl-ev-context-equiv-trace contexts trace) t))))


(defsection fgl-ev-context-equiv
  (defun-sk fgl-ev-context-equiv (contexts x y)
    (exists trace
            (and (equal (car trace) x)
                 (equal (car (last trace)) y)
                 (fgl-ev-context-equiv-trace contexts trace))))

  (in-theory (disable fgl-ev-context-equiv
                      fgl-ev-context-equiv-suff))

  (defthm fgl-ev-context-equiv-self
    (fgl-ev-context-equiv contexts x x)
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-suff
                           (trace (list x)) (y x))))))

  (defthm fgl-ev-context-equiv-symmetric
    (implies (fgl-ev-context-equiv contexts x y)
             (fgl-ev-context-equiv contexts y x))
    :hints (("goal" :expand ((fgl-ev-context-equiv contexts x y))
             :use ((:instance fgl-ev-context-equiv-suff
                    (trace (rev (fgl-ev-context-equiv-witness contexts x y)))
                    (x y) (y x))))))

  (defthm fgl-ev-context-equiv-trans
    (implies (and (fgl-ev-context-equiv contexts x y)
                  (fgl-ev-context-equiv contexts y z))
             (fgl-ev-context-equiv contexts x z))
    :hints (("goal" :expand ((fgl-ev-context-equiv contexts x y)
                             (fgl-ev-context-equiv contexts y z)
                             (fgl-ev-context-equiv-trace contexts
                                                               (fgl-ev-context-equiv-witness contexts y z)))
             :use ((:instance fgl-ev-context-equiv-suff
                    (trace (append (fgl-ev-context-equiv-witness contexts x y)
                                   (cdr (fgl-ev-context-equiv-witness contexts y z))))
                    (x x) (y z))))))

  (defthm fgl-ev-context-equiv-equal
    (equal (fgl-ev-context-equiv nil x y)
           (equal x y))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-suff
                           (trace (list x y)) (contexts nil)))
             :expand ((fgl-ev-context-equiv nil x y)))))

  (defthm fgl-ev-context-equiv-iff
    (equal (fgl-ev-context-equiv '(iff) x y)
           (iff* x y))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-suff
                           (trace (list x y)) (contexts '(iff))))
             :expand ((fgl-ev-context-equiv '(iff) x y)))))

  (defthm fgl-ev-context-equiv-when-member-iff
    (implies (and (member 'iff (equiv-contexts-fix contexts))
                  (iff* x y))
             (equal (fgl-ev-context-equiv contexts x y) t))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-suff
                           (trace (list x y))))
             :expand ((fgl-ev-context-equiv contexts x y)))))

  (defthm fgl-ev-context-equiv-unequiv
    (equal (fgl-ev-context-equiv '(unequiv) x y)
           t)
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-suff
                           (trace (list x y)) (contexts '(unequiv))))
             :expand ((fgl-ev-context-equiv '(unequiv) x y)))))

  (defthm fgl-ev-context-equiv-when-member-unequiv
    (implies (member 'unequiv (equiv-contexts-fix contexts))
             (equal (fgl-ev-context-equiv contexts x y)
                    t))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-suff
                           (trace (list x y))))
             :expand ((fgl-ev-context-equiv contexts x y)))))

  (fty::deffixequiv fgl-ev-context-equiv :args ((contexts equiv-contextsp))
    :hints (("goal" :expand ((:free (contexts) (fgl-ev-context-equiv contexts x y)))
             :use ((:instance fgl-ev-context-equiv-suff
                    (contexts contexts) (trace (fgl-ev-context-equiv-witness
                                              (equiv-contexts-fix contexts) x y)))
                   (:instance fgl-ev-context-equiv-suff
                    (contexts (equiv-contexts-fix contexts))
                    (trace (fgl-ev-context-equiv-witness
                            contexts x y))))))))




(defchoose fgl-ev-context-fix1 (y) (contexts x)
  (fgl-ev-context-equiv contexts x y)
  :strengthen t)

(define fgl-ev-context-fix ((contexts equiv-contextsp) x)
  :non-executable t
  (fgl-ev-context-fix1 (equiv-contexts-fix contexts) x)
  ///
  (in-theory (disable (fgl-ev-context-fix)))
  (defthm fgl-ev-context-fix-equiv
    (fgl-ev-context-equiv contexts x (fgl-ev-context-fix contexts x))
    :hints (("goal" :use ((:instance fgl-ev-context-fix1
                           (y x)
                           (contexts (equiv-contexts-fix contexts)))))))

  (defthm fgl-ev-context-fix-strengthen
    (implies (fgl-ev-context-equiv contexts x y)
             (equal (fgl-ev-context-fix contexts x) (fgl-ev-context-fix contexts y)))
    :hints (("goal" :use ((:instance fgl-ev-context-fix1
                           (contexts1 (equiv-contexts-fix contexts))
                           (contexts (equiv-contexts-fix contexts))
                           (x1 y))
                          (:instance fgl-ev-context-equiv-trans
                           (x (fgl-ev-context-fix contexts x))
                           (y x) (z y))
                          (:instance fgl-ev-context-equiv-trans
                           (x (fgl-ev-context-fix contexts y))
                           (y y) (z x)))
             :in-theory (disable fgl-ev-context-equiv-trans)))
    :rule-classes nil))

(defthm fgl-ev-context-fix-equiv-rev
  (fgl-ev-context-equiv contexts (fgl-ev-context-fix contexts x) x))

(defthmd equal-of-fgl-ev-context-fix
  (iff (equal (fgl-ev-context-fix contexts x) (fgl-ev-context-fix contexts y))
       (fgl-ev-context-equiv contexts x y))
  :hints (("goal"
           :use (fgl-ev-context-fix-strengthen
                 (:instance fgl-ev-context-fix-equiv)
                 (:instance fgl-ev-context-fix-equiv-rev (x y)))
           :in-theory (disable fgl-ev-context-fix-equiv-rev
                               fgl-ev-context-fix-equiv))))

(defthmd fgl-ev-context-equiv-is-equal-of-fixes
  (iff (fgl-ev-context-equiv contexts x y)
       (equal (fgl-ev-context-fix contexts x) (fgl-ev-context-fix contexts y)))
  :hints(("Goal" :in-theory (enable equal-of-fgl-ev-context-fix))))


(defthm fgl-ev-context-fix-of-fgl-ev-context-fix
  (equal (fgl-ev-context-fix contexts (fgl-ev-context-fix contexts x))
         (fgl-ev-context-fix contexts x))
  :hints (("goal" :use ((:instance fgl-ev-context-fix-strengthen
                         (y (fgl-ev-context-fix contexts x)))))))

(defthm fgl-ev-context-fix-under-fgl-ev-context-equiv-1
  (equal (fgl-ev-context-equiv contexts (fgl-ev-context-fix contexts x) y)
         (fgl-ev-context-equiv contexts x y))
  :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-is-equal-of-fixes))))

(defthm fgl-ev-context-fix-under-fgl-ev-context-equiv-2
  (equal (fgl-ev-context-equiv contexts x (fgl-ev-context-fix contexts y))
         (fgl-ev-context-equiv contexts x y))
  :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-is-equal-of-fixes))))

(defthm fgl-ev-context-fix-of-equal
  (equal (fgl-ev-context-fix nil x) x)
  :hints (("goal" :use ((:instance fgl-ev-context-fix-equiv (contexts nil)))
           :in-theory (disable fgl-ev-context-fix-equiv
                               fgl-ev-context-fix-equiv-rev
                               fgl-ev-context-fix-under-fgl-ev-context-equiv-1
                               fgl-ev-context-fix-under-fgl-ev-context-equiv-2))))

(defthm fgl-ev-context-fix-of-iff
  (iff (fgl-ev-context-fix '(iff) x) x)
  :hints (("goal" :use ((:instance fgl-ev-context-fix-equiv (contexts '(iff))))
           :in-theory (disable fgl-ev-context-fix-equiv
                               fgl-ev-context-fix-equiv-rev
                               fgl-ev-context-fix-under-fgl-ev-context-equiv-1
                               fgl-ev-context-fix-under-fgl-ev-context-equiv-2))))

(defthm fgl-ev-context-fix-iff-congruence
  (implies (iff x y)
           (equal (fgl-ev-context-fix '(iff) x)
                  (fgl-ev-context-fix '(iff) y)))
  :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes
                         (contexts '(iff))))))
  :rule-classes :congruence)

(defthm fgl-ev-context-fix-iff-of-nil
  (equal (fgl-ev-context-fix '(iff) nil) nil))



(defthm fgl-ev-context-fix-of-unequiv
  (implies (syntaxp (not (equal x ''nil)))
           (equal (fgl-ev-context-fix '(unequiv) x)
                  (fgl-ev-context-fix '(unequiv) nil)))
  :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes (contexts '(unequiv)) (y nil))))))

(defthm fgl-ev-context-fix-when-member-unequiv
  (implies (and (syntaxp (not (equal x ''nil)))
                (member 'unequiv (equiv-contexts-fix contexts)))
           (equal (fgl-ev-context-fix contexts x)
                  (fgl-ev-context-fix contexts nil)))
  :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes (y nil))))))


(defthm fgl-ev-context-fix-when-member-iff-nonnil
  (implies (and (syntaxp (not (equal x ''t)))
                (member 'iff (equiv-contexts-fix contexts))
                x)
           (equal (fgl-ev-context-fix contexts x)
                  (fgl-ev-context-fix contexts t)))
  :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes (y t))))))

(defthm fgl-ev-context-fix-when-member-iff-equiv
  (implies (and (member 'iff (equiv-contexts-fix contexts))
                (iff* x y))
           (equal (equal (fgl-ev-context-fix contexts x)
                         (fgl-ev-context-fix contexts y))
                  t))
  :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes)))))


