; Copyright (C) 2011-2017, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book supports the resolution proof checker defined, and proved sound, in
; the book zz-check.lisp.

(in-package "ACL2")

(include-book "centaur/aig/misc" :dir :system)

(defmacro zzchk-negate-lit (lit)
  `(aig-not ,lit))

(defund zzchk-resolve1 (cl1+ cl2 lit)
  (declare (xargs :guard t))
  (cond ((atom cl2) cl1+)
        ((and lit ; presumably an optimization
              (hons-equal (car cl2) lit))
         (zzchk-resolve1 cl1+ (cdr cl2) nil))
        (t
         (zzchk-resolve1 (hons-acons (car cl2) t cl1+)
                         (cdr cl2)
                         lit))))

(defund zzchk-resolve (cl1+ cl2 lit)

; Cl1+ is a fast-alist: elements associated with T are those that are viewed as
; belonging to a clause, cl1.  We return the result of updating cl1+ by
; resolving it with clause cl2, removing the negation of lit from cl1+ and lit
; from cl2.  But as in Niklas's binResolve function (file
; Centaur/Main_c_demo.c), we do not check for the presence of lit or its
; negation.

  (declare (xargs :guard t))
  (zzchk-resolve1 (hons-acons (zzchk-negate-lit lit) nil cl1+)
                  cl2
                  lit))

(defn weak-alistp (x)
  (cond ((atom x) x)
        ((consp (car x))
         (weak-alistp (cdr x)))
        (t nil)))

(defun aig-cl-eval (cl env)
  (cond ((atom cl) nil)
        ((aig-eval (car cl) env) t)
        (t (aig-cl-eval (cdr cl) env))))

; Start proof.

(defun strip-nonnil-cars (alist ans)
  (declare (xargs :guard (weak-alistp alist)))
  (cond ((atom alist) ans)
        ((cdar alist)
         (strip-nonnil-cars (cdr alist)
                            (cons (caar alist) ans)))
        (t
         (strip-nonnil-cars (cdr alist)
                            ans))))

(defun aig-cl+-eval (cl+ env)
  (aig-cl-eval (strip-nonnil-cars (hons-shrink-alist cl+ 'cl+-final-cdr)
                                  nil)
               env))

(local (defun aig-cl-eval-wit (cl env)
         (cond ((atom cl) nil)
               ((aig-eval (car cl) env)
                (car cl))
               (t (aig-cl-eval-wit (cdr cl) env)))))

(local (defthmd aig-cl-eval-necc
         (let ((wit (aig-cl-eval-wit cl env)))
           (implies (aig-cl-eval cl env)
                    (and wit
                         (member-equal wit cl)
                         (aig-eval wit env))))))

(local (defthm aig-cl-eval-suff
         (implies (and (aig-eval lit env)
                       (member-equal lit cl))
                  (aig-cl-eval cl env))))

; Start proof of aig-cl+-eval-hons-put-list-lemma.

(defthm cdr-hons-assoc-equal-implies-member-equal-strip-cars
  (implies (cdr (hons-assoc-equal key alist))
           (member-equal key (strip-cars alist))))

(defthm member-equal-strip-nonnil-cars
  (implies (no-duplicatesp-equal (strip-cars alist))
           (iff (member-equal x (strip-nonnil-cars alist acc))
                (or (cdr (hons-assoc-equal x alist))
                    (member-equal x acc)))))

(defthm member-equal-strip-cars-implies-hons-assoc-equal
  (implies (and (weak-alistp alist)
                (member-equal key (strip-cars alist)))
           (hons-assoc-equal key alist)))

(defthm no-duplicatesp-strip-cars-hons-shrink-alist
  (implies (and (weak-alistp acc)
                (no-duplicatesp-equal (strip-cars acc)))
           (no-duplicatesp-equal (strip-cars (hons-shrink-alist alist acc)))))

(defthm hons-assoc-equal-hons-shrink-alist
  (equal (hons-assoc-equal lit (hons-shrink-alist alist acc))
         (or (hons-assoc-equal lit acc)
             (hons-assoc-equal lit alist))))

(defthm hons-assoc-equal-reduction
  (implies (hons-assoc-equal key alist)
           (equal (equal (hons-assoc-equal key alist)
                         (cons key (cdr (hons-assoc-equal key alist))))
                  t)))

(defthm hons-assoc-equal-hons-put-list-equality
  (implies (and (atom x)
                (weak-alistp acc))
           (equal (hons-assoc-equal lit (hons-put-list cl x acc))
                  (if (member-equal lit cl)
                      (cons lit x)
                    (hons-assoc-equal lit acc))))
  :hints (("Goal" :induct (hons-put-list cl x acc))))

(defthm aig-cl+-eval-hons-put-list-lemma
  (implies (and (weak-alistp acc)
                (cdr (hons-assoc-equal lit acc))
                (aig-eval lit env))
           (aig-cl+-eval acc env)))

(defthm aig-cl+-eval-hons-put-list

; This lemma is needed for zzchk-run-proof-correct-chain-1-1 (file
; zz-check.lisp).

  (implies (weak-alistp acc)
           (iff (aig-cl+-eval (hons-put-list cl t acc)
                              env)
                (or (aig-cl-eval cl env)
                    (aig-cl+-eval acc env))))
  :hints (("Goal"
           :use
           (aig-cl-eval-necc
            (:instance aig-cl-eval-necc
                       (cl (strip-nonnil-cars (hons-shrink-alist acc 'cl+-final-cdr)
                                              nil)))
            (:instance
             aig-cl-eval-necc
             (cl (strip-nonnil-cars (hons-shrink-alist (hons-put-list cl t acc)
                                                       'cl+-final-cdr)
                                    nil)))
            (:instance
             aig-cl-eval-suff
             (lit (aig-cl-eval-wit (strip-nonnil-cars
                                    (hons-shrink-alist acc 'cl+-final-cdr)
                                                      nil)
                                   env))
             (cl (strip-nonnil-cars
                  (hons-shrink-alist (hons-put-list cl t acc)
                                     'cl+-final-cdr)
                  nil)))))))

#||


(local
 (defthm aig-cl-eval-zzchk-remove-lit
   (equal (aig-cl-eval (zzchk-remove-lit lit cl) env)
          (if (aig-eval lit env)
              (hide (aig-cl-eval (zzchk-remove-lit lit cl) env))
            (aig-cl-eval cl env)))
   :hints (("Goal"
            :expand ((hide (aig-cl-eval (zzchk-remove-lit lit cl) env)))))))

(defthm aig-cl-eval-zzchk-resolve
  (implies (and (aig-cl-eval cl1 env)
                (aig-cl-eval cl2 env))
           (aig-cl-eval (zzchk-resolve cl1 cl2 lit) env))
  :hints (("Goal"
           :in-theory
           (e/d (zzchk-resolve)
                (zzchk-remove-lit aig-cl-eval hons-union)))))
||#

(defun aig-cl-lst-eval (cl-lst env)
  (cond ((atom cl-lst) t)
        ((aig-cl-eval (car cl-lst) env)
         (aig-cl-lst-eval (cdr cl-lst) env))
        (t nil)))

; Start final push towards proof of aig-cl+-eval-zzchk-resolve.

(defthm aig-cl-eval-strip-nonnil-cars-hons-shrink-alist-monotonicity
  (implies
   (aig-cl-eval (strip-nonnil-cars (hons-shrink-alist cl+ 'cl+-final-cdr)
                                   cl)
                env)
   (aig-cl-eval
    (strip-nonnil-cars (hons-shrink-alist cl+
                                          (cons (cons lit t)
                                                'cl+-final-cdr))
                       cl)
    env))
  :hints (("Goal"
           :in-theory (disable aig-cl-eval-suff) ; optional hint
           :use
           ((:instance
             aig-cl-eval-necc
             (cl (strip-nonnil-cars (hons-shrink-alist cl+ 'cl+-final-cdr)
                                    cl)))
            (:instance
             aig-cl-eval-suff
             (lit (aig-cl-eval-wit
                   (strip-nonnil-cars (hons-shrink-alist cl+ 'cl+-final-cdr)
                                      cl)
                   env))
             (cl (strip-nonnil-cars
                  (hons-shrink-alist cl+ (cons (cons lit t) 'cl+-final-cdr))
                  cl)))))))

(defthm aig-cl-eval-strip-nonnil-cars-hons-shrink-alist-zzchk-resolve1-case-1-1
  (implies
   (aig-cl-eval (strip-nonnil-cars (hons-shrink-alist cl+ 'cl+-final-cdr)
                                   nil)
                env)
   (aig-cl-eval
    (strip-nonnil-cars
     (hons-shrink-alist (zzchk-resolve1 cl+ old-cl any-lit)
                        'cl+-final-cdr)
     nil)
    env))
  :hints (("Goal" :in-theory (enable zzchk-resolve1))))

(defthm aig-cl-eval-strip-nonnil-cars-hons-shrink-alist-zzchk-resolve1-case-1
  (implies
   (and (aig-eval lit env)
        (aig-cl-eval (strip-nonnil-cars (hons-shrink-alist cl+ 'cl+-final-cdr)
                                        nil)
                     env))
   (aig-cl-eval
    (strip-nonnil-cars
     (hons-shrink-alist (zzchk-resolve1 (cons (list (aig-not lit)) cl+)
                                        old-cl
                                        any-lit)
                        'cl+-final-cdr)
     nil)
    env))
  :hints (("Goal"
           :in-theory (disable aig-cl-eval-suff) ; optional hint
           :use
           ((:instance aig-cl-eval-necc
                       (cl (strip-nonnil-cars
                            (hons-shrink-alist cl+ 'cl+-final-cdr)
                            nil)))
            (:instance aig-cl-eval-suff
                       (lit (aig-cl-eval-wit
                             (strip-nonnil-cars
                              (hons-shrink-alist cl+ 'cl+-final-cdr)
                              nil)
                             env))
                       (cl (strip-nonnil-cars
                            (hons-shrink-alist cl+
                                               (cons (list (aig-not lit))
                                                     'cl+-final-cdr))
                            nil)))))))

(defthm aig-cl-eval-strip-nonnil-cars-hons-shrink-alist-zzchk-resolve1-case-2
  (implies
   (aig-cl-eval old-cl env)
   (aig-cl-eval
    (strip-nonnil-cars
     (hons-shrink-alist (zzchk-resolve1 cl+ old-cl nil)
                        'cl+-final-cdr)
     nil)
    env))
  :hints (("Goal" :in-theory (enable zzchk-resolve1))))

(defthm aig-cl-eval-strip-nonnil-cars-hons-shrink-alist-zzchk-resolve1-case-3
  (implies
   (and (not (aig-eval lit env))
        (aig-cl-eval old-cl env))
   (aig-cl-eval
    (strip-nonnil-cars
     (hons-shrink-alist (zzchk-resolve1 cl+ old-cl lit)
                        'cl+-final-cdr)
     nil)
    env))
  :hints (("Goal" :in-theory (enable zzchk-resolve1))))

(defthm aig-cl-eval-strip-nonnil-cars-hons-shrink-alist-zzchk-resolve1
  (implies
   (and (aig-cl-eval (strip-nonnil-cars (hons-shrink-alist cl+ 'cl+-final-cdr)
                                        nil)
                     env)
        (aig-cl-eval old-cl env)
        (or (equal lit2 lit)
            (equal lit2 nil)))
   (aig-cl-eval
    (strip-nonnil-cars
     (hons-shrink-alist (zzchk-resolve1 (cons (list (aig-not lit)) cl+)
                                        old-cl
                                        lit2)
                        'cl+-final-cdr)
     nil)
    env))
  :hints (("Goal" :cases ((aig-eval lit env)))))

(defthm aig-cl-lst-eval-implies-aig-cl-eval
  (implies (and (aig-cl-lst-eval (strip-cdrs cl-alist)
                                 env)
                (hons-assoc-equal id cl-alist))
           (aig-cl-eval (cdr (hons-assoc-equal id cl-alist))
                        env)))

(defthm aig-cl+-eval-zzchk-resolve
  (implies (and (hons-assoc-equal id cl-alist)
                (aig-cl+-eval cl+ env)
                (aig-cl-lst-eval (strip-cdrs cl-alist)
                                 env))
           (aig-cl+-eval (zzchk-resolve cl+
                                        (cdr (hons-assoc-equal id cl-alist))
                                        lit)
                         env))
  :hints (("Goal" :in-theory (enable zzchk-resolve))))
