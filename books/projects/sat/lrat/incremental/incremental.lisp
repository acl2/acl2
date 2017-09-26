; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

(in-package "LRAT")

(include-book "../sorted/lrat-checker")
(include-book "../stobj-based/lrat-checker")
(include-book "tools/er-soft-logic" :dir :system)

(defun incl-verify-proof$-rec (ncls ndel formula proof a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
; See the comment in verify-clause$ about perhaps eliminating the next
; conjunct (which is perhaps not necessary).
                              (= (a$ptr a$) 0)
                              (integerp ncls) ; really natp; see comment below
                              (natp ndel)
                              (formula-p$ formula a$)
                              (proofp$ proof a$))
                  :guard-hints
                  (("Goal" :use ((:guard-theorem verify-proof$-rec))))))
  (cond
   ((atom proof) (mv t formula a$))
   (t
    (let* ((entry (car proof))
           (delete-flg (proof-entry-deletion-p entry)))
      (cond
       (delete-flg
        (let* ((indices (proof-entry-deletion-indices entry))
               (new-formula (delete-clauses indices formula))
               (len (length indices))
               (ncls

; We expect that (<= len ncls).  It is tempting to assert that here (with
; assert$), but it's not necessary so we avoid the overhead (mostly in proof,
; but perhaps also a bit in execution).

                (- ncls len))
               (ndel (+ ndel len)))
          (incl-verify-proof$-rec ncls ndel new-formula (cdr proof) a$)))
       (t ; addition
        (mv-let (ncls ndel new-formula a$)
          (verify-clause$ formula entry ncls ndel a$)
          (cond (ncls ; success
                 (let* ((entry-clause (access add-step entry :clause))
                        (newest-formula
                         (add-proof-clause (access add-step entry :index)
                                           entry-clause
                                           new-formula)))
                   (cond
                    ((null entry-clause)
                     (mv :complete newest-formula a$))
                    (t
                     (incl-verify-proof$-rec
                      (1+ ncls)
                      ndel
                      newest-formula
                      (cdr proof)
                      a$)))))
                (t (mv nil formula a$))))))))))

(defun incl-verify-proof$ (formula proof a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
; See the comment in verify-clause$ about perhaps eliminating the next
; conjunct (which is perhaps not necessary).
                              (= (a$ptr a$) 0)
                              (formula-p$ formula a$)
                              (proofp$ proof a$))))
  (incl-verify-proof$-rec (fast-alist-len formula)
                          0
                          formula
                          proof
                          a$))

(defund incl-initialize-a$ (max-var a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (equal (a$ptr a$) 0)
                              (natp max-var))))
  (cond ((<= max-var (a$stk-length a$))
         a$)
        (t (let* ((new-max-var (* 2 max-var)))
             (initialize-a$ new-max-var a$)))))

(defun check-proofp (proof) ; primitive

; This variant of proofp causes an error when false, printing the offending
; entry.

  (declare (xargs :guard t))
  (if (atom proof)
      (null proof)
    (and (or (lrat-proof-entry-p (car proof))
             (er hard? 'check-proof
                 "Illegal proof entry: ~X01"
                 (car proof)
                 nil))
         (check-proofp (cdr proof)))))

(defthm a$p-incl-initialize-a$
  (implies (and (a$p a$)
                (natp max-var))
           (a$p (incl-initialize-a$ max-var a$)))
  :hints (("Goal"
           :expand ((a$p a$))
           :in-theory
           (union-theories '(a$p-weak
                             incl-initialize-a$
                             a$p-initialize-a$)
                           (theory 'ground-zero)))))

; redundant with ../stobj-based/lrat-checker
(defthm natp-proof-max-var
  (implies (and (proofp proof) (natp acc))
           (natp (proof-max-var proof acc)))
  :rule-classes :type-prescription)

(defthm check-proofp-is-lrat-proofp
  (equal (check-proofp proof)
         (lrat-proofp proof)))

(encapsulate
  ()

  (local (defthm ordered-literalsp-implies-not-member
           (implies (and (consp x)
                         (< (abs a) (abs (car x)))
                         (ordered-literalsp x))
                    (not (member a x)))))

  (local (defthm ordered-literalsp-implies-unique-literalsp
           (implies (ordered-literalsp x)
                    (unique-literalsp x))))

  (local (defthm ordered-literalsp-implies-not-member-negate
           (implies (and (consp x)
                         (< (abs a) (abs (car x)))
                         (ordered-literalsp x))
                    (not (member (negate a) x)))))

  (local (defthm ordered-literalsp-implies-not-conflicting-literalsp
           (implies (ordered-literalsp x)
                    (not (conflicting-literalsp x)))))

  (local (defthm lrat-add-step-p-implies-add-step-p
           (implies (lrat-add-step-p proof)
                    (add-step-p proof))
           :rule-classes :forward-chaining))

  (local (defthm lrat-proof-entry-p-implies-proof-entry-p
           (implies (lrat-proof-entry-p proof)
                    (proof-entry-p proof))
           :rule-classes :forward-chaining))

  (defthm lrat-proofp-implies-proofp
    (implies (lrat-proofp proof)
             (proofp proof))
    :rule-classes :forward-chaining))

; redundant with ../stobj-based/lrat-checker
(defthm natp-formula-max-var
  (implies (and (force (natp acc))
                (force (formula-p formula)))
           (natp (formula-max-var formula acc)))
  :rule-classes :type-prescription)

(local (in-theory (disable a$p)))

; redundant with ../stobj-based/lrat-checker
(defthm formula-p$-shrink-formula
  (implies (formula-p$ formula a$)
           (formula-p$ (shrink-formula formula) a$))
  :hints (("Goal" :in-theory (enable shrink-formula))))

(defthm formula-p$-initialize-a$-lemma
  (implies (and (formula-p formula)
                (natp n)
                (<= (formula-max-var-1 formula) n))
           (formula-p$ formula
                       (initialize-a$ n a$))))

(defthm literal-listp-implies-literal-listp$
  (implies (and (a$p-weak a$)
                (literal-listp cl)
                (< (clause-max-var-1 cl)
                   (len (nth *a$arri* a$))))
           (literal-listp$ cl a$))
  :hints (("Goal" :in-theory (enable literal-listp$ literalp$))))

(defthm clausep-implies-clausep$
  (implies (and (a$p-weak a$)
                (clausep cl)
                (< (clause-max-var-1 cl)
                   (len (nth *a$arri* a$))))
           (clausep$ cl a$))
  :hints (("Goal" :in-theory (enable clausep$))))

(defthm formula-p-implies-formula-p$
  (implies (and (a$p-weak a$)
                (formula-p formula)
                (< (formula-max-var formula 0)
                   (len (nth *a$arri* a$))))
           (formula-p$ formula a$))
  :hints (("Goal" :in-theory (e/d (formula-max-var-is-formula-max-var-1)
                                  (formula-max-var)))))

(defthm formula-p$-incl-initialize-a$
  (implies (and (a$p a$)
                (formula-p formula)
                (force (<= (formula-max-var formula 0) ; avoid free var
                           max-var))
                (natp max-var))
           (formula-p$ formula
                       (incl-initialize-a$ max-var a$)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable a$p initialize-a$ incl-initialize-a$))))

; Start proof of formula-max-var-shrink-formula

(defthm formula-max-var-1-remove-deleted-clauses
  (implies (and (formula-p formula)
                (formula-p acc))
           (equal (formula-max-var-1 (remove-deleted-clauses formula acc))
                  (max (formula-max-var-1 formula)
                       (formula-max-var-1 acc)))))

(defthm formula-max-var-1-fast-alist-fork
  (implies (and (formula-p formula)
                (formula-p acc))
           (<= (formula-max-var-1 (fast-alist-fork formula acc))
               (max (formula-max-var-1 formula)
                    (formula-max-var-1 acc))))
  :rule-classes nil)

(defthm formula-max-var-1-shrink-formula
  (implies (formula-p formula)
           (<= (formula-max-var-1 (shrink-formula formula))
               (formula-max-var-1 formula)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable shrink-formula)
           :use ((:instance formula-max-var-1-fast-alist-fork
                            (acc nil))))))

(defthm formula-max-var-shrink-formula
  (implies (and (formula-p formula)
                (natp var))
           (<= (formula-max-var (shrink-formula formula) var)
               (formula-max-var formula var)))
  :hints (("Goal" :in-theory (enable formula-max-var-is-formula-max-var-1))))

(defthm clause-max-var-goes-up
  (implies (and (natp var)
                (clausep clause))
           (<= var
               (clause-max-var clause var)))
  :rule-classes :linear)

(defthm proof-max-var-goes-up
  (implies (and (natp var)
                (proofp proof))
           (<= var
               (proof-max-var proof var)))
  :rule-classes :linear)

(defthm literal-listp$-monotone-in-a$arr-length
  (implies (and (literal-listp$ proof a$1)
                (a$p a$1)
                (a$p a$2)
                (<= (a$arr-length a$1)
                    (a$arr-length a$2)))
           (literal-listp$ proof a$2))
  :hints (("Goal" :in-theory (enable literal-listp$ literalp$))))

(defthm clausep$-monotone-in-a$arr-length
  (implies (and (clausep$ proof a$1)
                (a$p a$1)
                (a$p a$2)
                (<= (a$arr-length a$1)
                    (a$arr-length a$2)))
           (clausep$ proof a$2))
  :hints (("Goal" :in-theory (enable clausep$))))

(defthmd proofp$-monotone-in-a$arr-length
  (implies (and (proofp$ proof a$1)
                (a$p a$1)
                (a$p a$2)
                (<= (a$arr-length a$1)
                    (a$arr-length a$2)))
           (proofp$ proof a$2)))

(defthm proofp$-initialize-a$-implies-proofp$-incl-initialize-a$
  (implies (and (proofp$ proof (initialize-a$ var1 a$))
                (a$p a$)
                (natp var1)
                (natp var2)
                (<= var1 var2))
           (proofp$ proof (incl-initialize-a$ var2 a$)))
  :instructions
  (:promote (:rewrite proofp$-monotone-in-a$arr-length nil t)
            (:in-theory (enable a$p))
            :prove :prove
            (:in-theory (enable a$p incl-initialize-a$ initialize-a$))
            :prove))

(defthm proofp$-initialize-a$-implies-proofp$-incl-initialize-a$
  (implies (and (proofp$ proof
                         (initialize-a$ var1 a$))
                (a$p a$)
                (natp var1)
                (natp var2)
                (<= var1 var2))
           (proofp$ proof
                    (incl-initialize-a$ var2 a$)))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance proofp$-monotone-in-a$arr-length
                            (a$1 (initialize-a$ var1 a$))
                            (a$2 (incl-initialize-a$ var2 a$))))
           :in-theory (enable a$p incl-initialize-a$ initialize-a$)
           :do-not-induct t)))

(defthm clause-max-var-monotone
  (implies (and (clausep cl)
                (natp var1)
                (natp var2)
                (<= var1 var2))
           (<= (clause-max-var cl var1)
               (clause-max-var cl var2))))

(defthm proof-max-var-monotone
  (implies (and (proofp proof)
                (natp var1)
                (natp var2)
                (<= var1 var2))
           (<= (proof-max-var proof var1)
               (proof-max-var proof var2))))

(defthm proofp$-incl-initialize-a$

; Proof takes advantage of events from ../stobj-based/lrat-checker:
; proof-max-var-1, proof-max-var-is-proof-max-var-1, and
; proofp$-initialize-a$-lemma.

  (implies (and (a$p a$)
                (proofp proof)
                (natp n)
                (<= (proof-max-var proof 0) n))
           (proofp$ proof
                    (incl-initialize-a$ n a$)))
  :hints (("Goal"
           :in-theory (enable a$p proof-max-var-is-proof-max-var-1)
           :restrict ((proofp$-initialize-a$-implies-proofp$-incl-initialize-a$
                       ((var1 n)))))))

(defthm car-incl-initialize-a$
  (implies (equal (a$ptr a$) 0)
           (equal (car (incl-initialize-a$ max-var a$))
                  0))
  :hints (("Goal" :in-theory (enable incl-initialize-a$
                                     initialize-a$))))

(defun incl-valid-proofp$ (formula proof old-max-var a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (natp old-max-var)
                              (<= (formula-max-var formula 0)
                                  old-max-var))
                  :guard-hints (("Goal"
                                 :use ((:guard-theorem valid-proofp$))))))
  (let* ((formula (shrink-formula formula))
         (max-var (and (check-proofp proof)
                       (proof-max-var proof old-max-var))))
    (cond ((natp max-var)
           (let ((a$ (incl-initialize-a$ max-var a$)))
             (mv-let (v new-formula a$)
               (incl-verify-proof$ formula proof a$)
               (mv v
                   new-formula
                   max-var
                   a$))))
          (t (mv nil formula old-max-var a$)))))

(include-book "clrat-parser")

(in-theory (disable acl2::read-file-into-string2)) ; speeding things up

(defthm stringp-mv-nth-1-clrat-read-next-1
  (stringp
   (mv-nth 1
           (clrat-read-next-1 clrat-file posn chunk-size
                              old-suffix clrat-file-length state))))

(in-theory (disable clrat-read-next-1))

(defthm stringp-mv-nth-1-clrat-read-next
  (stringp
   (mv-nth 1
           (clrat-read-next clrat-file posn chunk-size
                            old-suffix clrat-file-length state))))

(defthm natp-mv-nth-2-incl-valid-proofp$
  (implies (force (natp max-var))
           (natp (mv-nth 2 (incl-valid-proofp$ formula proof max-var a$))))
  :rule-classes :type-prescription)

; Start proof of formula-p-incl-valid-proofp$

(encapsulate
  ()
  (local (include-book "../list-based/soundness"))

  (defthm formula-p-delete-clauses
    (implies (and (formula-p fal)
                  (index-listp index-list))
             (formula-p (delete-clauses index-list fal)))))

(defthm formula-p-mv-nth-2-verify-clause$
  (implies (and (formula-p formula)
                (add-step-p add-step))
           (formula-p (mv-nth 2
                              (verify-clause$ formula add-step ncls ndel a$)))))

(defthm formula-p-incl-verify-proof$-rec
  (implies (and (formula-p formula)
                (proofp proof))
           (formula-p
            (mv-nth
             1
             (incl-verify-proof$-rec ncls ndel formula proof a$))))
  :hints (("Goal" :in-theory (disable verify-clause$))))

(defthm formula-p-incl-valid-proofp$
  (implies (and (formula-p formula)
                (proofp proof))
           (formula-p
            (mv-nth
             1
             (incl-valid-proofp$ formula proof old-max-var a$)))))

(defthm formula-p-incl-valid-proofp$-alt
  (implies (and (formula-p formula)
                (car (incl-valid-proofp$ formula proof old-max-var a$)))
           (formula-p
            (mv-nth
             1
             (incl-valid-proofp$ formula proof old-max-var a$)))))

(encapsulate
  ()
  (local (include-book "../stobj-based/equiv"))

  (defthm a$p-mv-nth-3-verify-clause$
    (implies (and (a$p a$)
                  (formula-p$ formula a$)
                  (clausep$ (access add-step add-step :clause) a$))
             (a$p (mv-nth 3 (verify-clause$ formula add-step ncls ndel a$))))
    :hints (("Goal" :in-theory (enable verify-clause$))))

  (defthm formula-p$-for-verify-clause$-alt
    (implies (and (a$p a$)
                  (formula-p$ formula a$)
                  (clausep$ (access add-step add-step :clause) a$)
                  (car (verify-clause$ formula add-step ncls ndel a$)))
             (formula-p$ (mv-nth 2
                                 (verify-clause$ formula add-step ncls ndel
                                                 a$))
                         (mv-nth 3
                                 (verify-clause$ formula add-step ncls ndel
                                                 a$))))
    :hints (("Goal" :in-theory (enable verify-clause verify-clause$)))))

(local (include-book "../stobj-based/equiv"))

(defthm a$=-implies-equal-clausep$-2
  (implies (a$= a1 a2)
           (equal (clausep$ clause a1)
                  (clausep$ clause a2)))
  :hints (("Goal" :in-theory (enable clausep$)))
  :rule-classes :congruence)

(defthm incl-verify-proofp$-rec-preserves-a$p
  (implies (and (a$p a$)
                (equal (a$ptr a$) 0)
                (integerp ncls)
                (natp ndel)
                (formula-p$ formula a$)
                (proofp$ proof a$))
           (a$p (mv-nth 2
                        (incl-verify-proof$-rec ncls ndel formula proof a$))))
  :hints (("Goal"
           :in-theory (e/d (formula-p$) ((:e force) verify-clause$))
           :induct (incl-verify-proof$-rec ncls ndel formula proof a$)
           :expand ((incl-verify-proof$-rec ncls ndel formula proof a$)))))

; !! Make the original rule linear?
(defthm formula-max-var-shrink-formula-linear
  (implies (and (formula-p formula)
                (natp var))
           (<= (formula-max-var (shrink-formula formula) var)
               (formula-max-var formula var)))
  :rule-classes :linear)

(defthm incl-valid-proofp$-preserves-a$p
  (implies (and (a$p a$)
                (equal (a$ptr a$) 0)
                (formula-p formula)
                (natp old-max-var)
                (<= (formula-max-var formula 0)
                    old-max-var))
           (a$p (mv-nth 3
                        (incl-valid-proofp$ formula proof old-max-var a$)))))

; Start proof of formula-max-monotone-for-incl-valid-proofp$

(defthm formula-max-var-is-formula-max-var-1-forced
  (implies (force (and (natp acc) (formula-p formula)))
           (equal (formula-max-var formula acc)
                  (max acc (formula-max-var-1 formula))))
  :hints (("Goal" :in-theory (enable formula-max-var-is-formula-max-var-1))))

(defthmd proof-max-var-is-proof-max-var-1-forced
  (implies (force (and (natp acc) (proofp proof)))
           (equal (proof-max-var proof acc)
                  (max acc (proof-max-var-1 proof))))
  :hints (("Goal" :in-theory (enable proof-max-var-is-proof-max-var-1))))

(defthm proof-max-var-cdr
  (implies (and (natp acc)
                (proofp proof))
           (<= (proof-max-var (cdr proof) acc)
               (proof-max-var proof acc)))
  :rule-classes :linear)

(defthm formula-max-var-1-delete-clauses
  (<= (formula-max-var-1 (delete-clauses x formula))
      (formula-max-var-1 formula))
  :rule-classes :linear)

(defthm formula-max-var-1-after-verify-clause
  (implies (and (formula-p formula)
                (<= (formula-max-var-1 formula) m))
           (<= (formula-max-var-1 (mv-nth 2
                                          (verify-clause formula add-step
                                                         ncls ndel)))
               m))
  :hints (("Goal" :in-theory (enable verify-clause maybe-shrink-formula)))
  :rule-classes (:rewrite :linear))

(encapsulate
  ()
  (local (include-book "../list-based/soundness"))
  (defthm formula-p-mv-nth-2-verify-clause
    (implies (formula-p formula)
             (formula-p (mv-nth 2
                                (verify-clause formula entry ncls ndel))))))

(defthm formula-max-monotone-for-incl-verify-proofp$-rec-lemma
  (implies (and (<= (formula-max-var-1 formula)
                    max-var)
                (<= (proof-max-var-1 proof)
                    max-var)
                (integerp ncls)
                (natp ndel)
                (formula-p$ formula a$)
                (a$p a$)
                (equal (a$ptr a$) 0)
                (proofp$ proof a$))
           (<= (formula-max-var-1
                (mv-nth
                 1
                 (incl-verify-proof$-rec ncls ndel formula proof a$)))
               max-var))
  :otf-flg t
  :hints (("Goal"
           :induct (incl-verify-proof$-rec ncls ndel formula proof a$)
           :do-not-induct t ; no sub-inductions
           :in-theory (enable proof-max-var-is-proof-max-var-1-forced
                              formula-p$
                              clause-max-var-is-clause-max-var-1)))
  :rule-classes nil)

(defthm formula-max-monotone-for-incl-verify-proofp$-rec
  (implies (and (<= (formula-max-var formula 0)
                    old-max-var)
                (natp old-max-var)
                (integerp ncls)
                (natp ndel)
                (formula-p$ formula a$)
                (a$p a$)
                (equal (a$ptr a$) 0)
                (proofp$ proof a$))
           (<= (formula-max-var-1
                (mv-nth
                 1
                 (incl-verify-proof$-rec ncls ndel formula proof a$)))
               (proof-max-var proof old-max-var)))
  :hints (("Goal"
           :in-theory (enable proof-max-var-is-proof-max-var-1)
           :use ((:instance
                  formula-max-monotone-for-incl-verify-proofp$-rec-lemma
                  (max-var (max (formula-max-var-1 formula)
                                (proof-max-var-1 proof))))))))

(defthm formula-max-monotone-for-incl-valid-proofp$
  (implies (and (<= (formula-max-var formula 0)
                    old-max-var)
                (natp old-max-var)
                (formula-p formula)
                (a$p a$)
                (equal (a$ptr a$) 0)
                (car (incl-valid-proofp$ formula proof old-max-var a$)))
           (<= (formula-max-var
                (mv-nth
                 1
                 (incl-valid-proofp$ formula proof old-max-var a$))
                0)
               (mv-nth
                2
                (incl-valid-proofp$ formula proof old-max-var a$)))))

(defthm natp-clrat-read-next-1-position
  (implies (force (natp position))
           (natp (mv-nth 2
                         (clrat-read-next-1 clrat-file position
                                            chunk-size suffix
                                            file-length state))))
  :hints (("Goal" :in-theory (enable clrat-read-next-1)))
  :rule-classes :type-prescription)

(defthm natp-clrat-read-next-position
  (implies (force (natp position))
           (natp (mv-nth 2
                         (clrat-read-next clrat-file position
                                          chunk-size old-suffix
                                          file-length state))))
  :hints (("Goal" :in-theory (enable clrat-read-next)))
  :rule-classes :type-prescription)

(defthm clrat-read-next-1-position-increases
  (<= position
      (mv-nth 2
              (clrat-read-next-1 clrat-file position
                                 chunk-size suffix
                                 file-length state)))
  :hints (("Goal" :in-theory (enable clrat-read-next-1)))
  :rule-classes :linear)

(defthm clrat-read-next-position-increases
  (<= position
      (mv-nth 2
              (clrat-read-next clrat-file position
                               chunk-size suffix
                               file-length state)))
  :hints (("Goal" :in-theory (enable clrat-read-next)))
  :rule-classes :linear)

(defthm clrat-read-next-1-position-increases-strict
  (implies (car (clrat-read-next-1 clrat-file position
                                   chunk-size suffix
                                   file-length state))
           (< position
              (mv-nth 2
                      (clrat-read-next-1 clrat-file position
                                         chunk-size suffix
                                         file-length state))))
  :hints (("Goal" :in-theory (enable clrat-read-next-1)))
  :rule-classes :linear)

(defthm clrat-read-next-position-increases-strict
  (implies (car (clrat-read-next clrat-file position
                                 chunk-size suffix
                                 file-length state))
           (< position
              (mv-nth 2
                      (clrat-read-next clrat-file position
                                       chunk-size suffix
                                       file-length state))))
  :hints (("Goal" :in-theory (enable clrat-read-next)))
  :rule-classes :linear)

(defun incl-valid-proofp$-top-rec (formula clrat-file posn chunk-size
                                           clrat-file-length old-suffix debug
                                           old-max-var a$ ctx state)
  (declare (xargs :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (stringp clrat-file)
                              (natp posn)
                              (< posn *2^56*)
                              (posp chunk-size)
                              (posp clrat-file-length)
                              (stringp old-suffix)
                              (natp old-max-var)
                              (<= (formula-max-var formula 0)
                                  old-max-var))
                  :verify-guards nil
                  :ruler-extenders (:lambdas mv-list return-last) ; ugly bug work-around
                  :measure (nfix (- clrat-file-length posn))
                  :stobjs (state a$)))
  (cond
   ((and (mbt (natp posn))
         (mbt (posp clrat-file-length))
         (mbt (posp chunk-size))
         (<= posn clrat-file-length))
    (prog2$
     (and debug
          (cw "; Note: Reading from position ~x0~|" posn))
     (mv-let (proof suffix new-posn)
       (clrat-read-next clrat-file posn chunk-size old-suffix
                        clrat-file-length state)
       (cond
        ((null suffix) ; error (normally a string, possibly even "")
         (mv (er hard? ctx "Implementation error: Null suffix!")
             a$))
        ((null proof)
         (mv :incomplete a$))
        ((stringp proof) ; impossible
         (mv (er hard? ctx
                 "Implementation error: ~x0 returned a string for its proof, ~
                  which we thought was impossible!"
                 'clrat-read-next)
             a$))
        (t
         (mv-let (v new-formula new-max-var a$)
           (prog2$
            (cw "; Note: Checking next proof segment.~|")
            (incl-valid-proofp$ formula proof old-max-var a$))
           (cond
            ((>= new-posn *2^56*)
             (mv (er hard? ctx
                     "Attempted to read at position ~x0, but the maximum ~
                      legal such position is 2^56 = ~x1."
                     new-posn *2^56*)
                 a$))
            ((not v) (mv nil a$))
            ((eq v :complete)
             (mv :complete a$))
            ((> new-posn clrat-file-length)

; If new-posn is exactly clrat-file-length, then as per the discussion of the
; "truncation case" in :doc read-file-into-string, we need to iterate.  But if
; new-posn exceeds clrat-file-length, then we have a valid proof that does not
; include the empty clause.

             (mv :incomplete a$))
            (t
             (incl-valid-proofp$-top-rec new-formula clrat-file new-posn
                                         chunk-size clrat-file-length suffix
                                         debug new-max-var a$ ctx
                                         state)))))))))
   (t ; impossible
    (mv nil a$))))

; Start proof of incl-valid-proofp$-preserves-a$ptr=0-lemma

(defthm a$p-mv-nth-3-verify-clause$-forward
  (implies
   (and (a$p a$)
        (formula-p$ formula a$)
        (clausep$ (access add-step add-step :clause)
                  a$))
   (a$p
    (mv-nth 3
            (verify-clause$ formula add-step ncls ndel a$))))
  :rule-classes
  ((:forward-chaining :trigger-terms
                      ((mv-nth 3
                               (verify-clause$ formula add-step ncls ndel a$))))))

(defthm varp$-nth-stk-linear-1
  (implies (and (force (a$p a$))
                (force (natp i))
                (force (< i (nth *a$ptr* a$))))
           (< (nth i (nth *a$stki* a$))
              (len (nth *a$arri* a$))))
  :rule-classes ((:linear :trigger-terms ((nth i (nth *a$stki* a$))))))

(defthm varp$-nth-stk-linear-2
  (implies (and (force (a$p a$))
                (force (natp i))
                (< i (nth *a$ptr* a$)))
           (< (nth i (nth *a$stki* a$))
              (len (nth *a$arri* a$))))
  :rule-classes ((:linear :trigger-terms ((len (nth *a$arri* a$))))))

(in-theory (disable (:linear varp$-nth-stk)))

(defthmd incl-valid-proofp$-preserves-a$ptr=0-lemma
  (implies (and (a$p a$)
                (equal (a$ptr a$) 0)
                (integerp ncls)
                (natp ndel)
                (formula-p$ formula a$)
                (proofp$ proof a$)
                (car (incl-verify-proof$-rec ncls ndel formula proof
                                             a$)))
           (let ((rec-call (incl-verify-proof$-rec ncls ndel formula proof
                                                   a$)))
             (equal (a$ptr (mv-nth 2 rec-call))
                    0)))
  :hints (("Goal"
           :induct (incl-verify-proof$-rec ncls ndel formula proof a$)
           :in-theory (enable formula-p$))))

(defthm a$ptr-incl-initialize-a$
  (implies (and (a$p-weak a$)
                (equal (a$ptr a$) 0))
           (equal (a$ptr (incl-initialize-a$ n a$))
                  0))
  :hints (("Goal" :in-theory (enable incl-initialize-a$ initialize-a$))))

(defthm incl-valid-proofp$-preserves-a$ptr=0
  (implies (and (a$p a$)
                (formula-p formula)
                (natp old-max-var)
                (<= (formula-max-var formula 0)
                    old-max-var)
                (equal (a$ptr a$) 0)
                (car (incl-valid-proofp$ formula proof old-max-var a$)))
           (equal (a$ptr (mv-nth
                          3
                          (incl-valid-proofp$ formula proof old-max-var a$)))
                  0))
  :hints (("Goal"
           :use ((:instance incl-valid-proofp$-preserves-a$ptr=0-lemma
                            (formula (shrink-formula formula))
                            (a$ (incl-initialize-a$
                                 (proof-max-var proof old-max-var)
                                 a$))
                            (ncls (fast-alist-len (shrink-formula formula)))
                            (ndel 0)))
           :in-theory (disable a$ptr))))

(in-theory (disable formula-max-var-is-formula-max-var-1-forced))

(verify-guards incl-valid-proofp$-top-rec
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors)
           :in-theory (disable incl-valid-proofp$
                               a$ptr
                               clrat-read-next))))

(defun incl-valid-proofp$-top-aux (formula clrat-file incomplete-okp chunk-size
                                           clrat-file-length debug a$ ctx state)
  (declare (xargs :stobjs (a$ state)
                  :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (stringp clrat-file)
                              (posp chunk-size)
                              (posp clrat-file-length))))
  (mv-let (val a$)
    (incl-valid-proofp$-top-rec formula clrat-file 0 chunk-size
                                clrat-file-length "" debug
                                (formula-max-var formula 0)
                                a$ ctx state)
    (case val
      (:complete (mv t a$))
      (:incomplete (mv (or incomplete-okp
                           (er hard? ctx
                               "The proof is valid but does not contain the ~
                                empty clause."))
                       a$))
      (t

; We do not expect to reach the following case.  If nil is returned as the
; first value, it is ultimately because an error occurred.  In particular,
; verify-clause$ either succeeds or causes an error.

       (mv (er hard? ctx
               "Invalid proof!")
           a$)))))

(defun ordered-formula-p1 (formula index)
  (declare (xargs :guard (posp index)))
  (if (atom formula)
      (null formula)
    (let ((pair (car formula)))
      (and (consp pair)
           (posp (car pair))
           (clause-or-assignment-p (cdr pair))
           (< (car pair) index)
           (ordered-formula-p1 (cdr formula) (car pair))))))

(defund ordered-formula-p (formula)

; It is important that the formula produced by the cnf parser does not have
; duplicate indices, since otherwise the first call of shrink-formula will
; change its semantics.  Fortunately, the cnf parser presents the formula in
; reverse order; so we can check for duplicate-free indices in linear time.

  (declare (xargs :guard t))
  (if (atom formula)
      (null formula)
    (let ((pair (car formula)))
      (and (consp pair)
           (posp (car pair))
           (clause-or-assignment-p (cdr pair))
           (ordered-formula-p1 (cdr formula) (car pair))))))

(defthm ordered-formula-p1-implies-formula-p
  (implies (ordered-formula-p1 formula index) ; free var is OK here
           (formula-p formula))
  :hints (("Goal" :in-theory (enable formula-p ordered-formula-p1))))

(defthm ordered-formula-p-implies-formula-p
  (implies (ordered-formula-p formula)
           (formula-p formula))
  :hints (("Goal" :in-theory (enable formula-p ordered-formula-p))))

(defun incl-valid-proofp$-top (cnf-file clrat-file incomplete-okp chunk-size
                                        debug ctx state)
  (declare (xargs :guard t :stobjs state))
  (let ((formula (ec-call (cnf-read-file cnf-file state))))
    (cond
     ((not (stringp clrat-file))
      (er-soft-logic
       ctx
       "The filename argument is not a string:~|~x0"
       clrat-file))
     ((not (posp chunk-size))
      (er-soft-logic
       ctx
       "The supplied :chunk-size must be a positive integer, but ~x0 is ~
        not.~|~x0"
       clrat-file))
     ((not (ordered-formula-p formula))
      (er-soft-logic ctx
                     "An invalid formula was supplied by the parser from ~
                      input file ~x0."
                     cnf-file))
     (t
      (mv-let (clrat-file-length state)
        (file-length$ clrat-file state)
        (cond
         ((posp clrat-file-length)
          (prog2$
           (and debug
                (cw "Length of file ~x0: ~x1~|" clrat-file clrat-file-length))
           (value
            (with-fast-alist
              formula
              (with-local-stobj a$
                (mv-let
                  (val a$)
                  (let ((a$ (resize-a$arr 2 a$))) ; to get a$p to hold
                    (incl-valid-proofp$-top-aux formula
                                                clrat-file
                                                incomplete-okp chunk-size
                                                clrat-file-length debug a$
                                                ctx state))
                  (cons val formula)))))))
         ((eql clrat-file-length 0)
          (er-soft-logic
           ctx
           "Zero-length file: ~x0."
           clrat-file))
         (t (er-soft-logic
             ctx
             "Sorry, Lisp cannot determine the file-length of file ~x0."
             clrat-file))))))))

(defun incl-verify-proof-fn (cnf-file clrat-file incomplete-okp chunk-size
                                      debug state)

; This is just a little interface to incl-valid-proofp$-top.

  (declare (xargs :guard t
                  :guard-hints (("Goal"
                                 :in-theory
                                 (disable incl-valid-proofp$-top-aux
                                          cnf-read-file
                                          file-length$)))
                  :stobjs state))
  (er-let* ((val/formula
             (time$ (incl-valid-proofp$-top cnf-file clrat-file incomplete-okp
                                            chunk-size debug 'incl-verify-proof
                                            state))))
    (value (car val/formula))))

(defconst *256mb*
  (expt 2 28))

(defconst *default-chunk-size*
  *256mb*)

(defmacro incl-verify-proof (cnf-file clrat-file
                                      &key
                                      incomplete-okp
                                      chunk-size
                                      (debug 't))
  `(incl-verify-proof-fn ,cnf-file ,clrat-file ,incomplete-okp
                         ,(or chunk-size *default-chunk-size*)
                         ,debug
                         state))

