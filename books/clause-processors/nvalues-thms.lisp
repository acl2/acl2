
(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "multi-env-trick")
(include-book "join-thms")
(include-book "tools/flag" :dir :system)

;; x is a true-list of length n.
(defun n-valuesp (n x)
  (and (true-listp x)
       (equal (len x) n)))

(defun-nx list-of-mv-nths (left n x)
  (if (zp left)
      nil
    (cons (mv-nth n x)
          (list-of-mv-nths (1- left) (1+ n) x))))


(encapsulate nil
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (progn


           (defthm cdr-nthcdr
             (equal (nthcdr n (cdr x))
                    (cdr (nthcdr n x))))

           (defthm car-nthcdr
             (equal (car (nthcdr n x))
                    (mv-nth n x))
             :hints(("Goal" :in-theory (enable mv-nth))))

           (defthm cons-mv-nth-ncdr-cdr
             (implies (and (natp i)
                           (< i (len x)))
                      (equal (cons (mv-nth i x) (cdr (nthcdr i x)))
                             (nthcdr i x)))
             :hints(("Goal" :in-theory (enable mv-nth))))

           (defthm nthcdr-len-x
             (implies (true-listp x)
                      (equal (nthcdr (len x) x) nil)))

           (defthm n-valuesp-list-of-mv-nths1
             (implies (and (natp i) (natp m)
                           (n-valuesp (+ m i) x))
                      (equal (list-of-mv-nths m i x) (nthcdr i x))))))

  (defthm n-valuesp-list-of-mv-nths
    (implies (n-valuesp n x)
             (equal (list-of-mv-nths n 0 x) x))))


(defevaluator n-values-ev n-values-ev-lst
  ((true-listp x) (len x) (equal x y) (cons a b) (n-valuesp n x) (if a b c)))

;; First value returned is a list of proof obligations that should be provable
;; on their own.  Second is a term that may require induction hyps to prove.
(defun n-valuesp-rewrite1 (n clique x)
  (declare (xargs :guard (and (pseudo-termp x)
                              (symbol-listp clique)
                              (natp n))))
  (cond ((zp n) (if (equal x ''nil)
                    (mv nil ''t)
                  (mv `(((equal ,x 'nil))) ''t)))
        ((atom x) (mv `(((n-valuesp ',n ,x))) ''t))
        ((and (eq (car x) 'quote) (eql (length x) 2))
         (if (and (true-listp (cadr x))
                  (eql (length (cadr x)) n))
             (mv nil ''t)
           (mv (list nil) ''t)))
        ((and (eq (car x) 'cons) (eql (length x) 3))
         (n-valuesp-rewrite1 (1- n) clique (caddr x)))
        ((and (eq (car x) 'if) (eql (length x) 4))
         (b* (((mv nonreca reca)
               (n-valuesp-rewrite1 n clique (caddr x)))
              ((mv nonrecb recb)
               (n-valuesp-rewrite1 n clique (cadddr x))))
           (mv (append nonreca nonrecb)
               (if (and (equal reca ''t) (equal recb ''t))
                   ''t
                 `(if ,(cadr x) ,reca ,recb)))))
        ((member (car x) clique)
         (mv nil `(n-valuesp ',n ,x)))
        ((consp (car x))
         (mv-let (nonrec rec)
           (n-valuesp-rewrite1 n clique (caddar x))
           (mv nonrec `((lambda ,(cadar x) ,rec) . ,(cdr x)))))
        (t (mv `(((n-valuesp ',n ,x))) ''t))))

(defthm true-listp-n-values-ev-lst
  (implies (pseudo-term-listp x)
           (true-listp (n-values-ev-lst x a)))
  :hints(("Goal" :induct (true-listp x)
          :expand ((pseudo-term-listp x)) )))

(defun n-valuesp-rewrite1-al (n clique x a)
  (cond ((zp n) (if (equal x ''nil) nil (list (list a))))
        ((atom x) (list (list a)))
        ((and (eq (car x) 'quote) (eql (length x) 2))
         (if (and (true-listp (cadr x))
                  (eql (length (cadr x)) n))
             nil
           (list (list a))))
        ((and (eq (car x) 'cons) (eql (length x) 3))
         (n-valuesp-rewrite1-al (1- n) clique (caddr x) a))
        ((and (eq (car x) 'if) (eql (length x) 4))
         (append (n-valuesp-rewrite1-al n clique (caddr x) a)
                 (n-valuesp-rewrite1-al n clique (cadddr x) a)))
        ((member (car x) clique) nil)
        ((consp (car x))
         (n-valuesp-rewrite1-al n clique (caddar x)
                             (pairlis$ (cadar x)
                                       (n-values-ev-lst (cdr x) a))))
        (t (list (list a)))))


(acl2::def-multi-env-fns n-values-ev n-values-ev-lst)

(acl2::def-join-thms n-values-ev)

(defthm clauses-apply-alists-append
  (implies (equal (len a) (len a-al))
           (equal (clauses-apply-alists-n-values-ev
                   (append a b) (append a-al b-al))
                  (and (clauses-apply-alists-n-values-ev a a-al)
                       (clauses-apply-alists-n-values-ev b b-al)))))

(defthm len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm len-n-valuesp-rewrite1
  (equal (len (n-valuesp-rewrite1-al n clique x a))
         (len (mv-nth 0 (n-valuesp-rewrite1 n clique x)))))

(defthm clauses-apply-alists-n-values-ev-open-cons
  (equal (clauses-apply-alists-n-values-ev
          (cons clause clauses) (cons alists alist-lists))
         (and (clause-apply-alists-n-values-ev clause alists)
              (clauses-apply-alists-n-values-ev clauses alist-lists))))

(defthm clause-apply-alists-n-values-ev-open-cons
  (equal (clause-apply-alists-n-values-ev
          clause (cons alist alists))
         (and (n-values-ev (disjoin clause) alist)
              (clause-apply-alists-n-values-ev clause alists))))

(in-theory (disable clauses-apply-alists-n-values-ev
                    clause-apply-alists-n-values-ev))


(defthm n-valuesp-rewrite1-correct
  (implies (and (clauses-apply-alists-n-values-ev
                 (mv-nth 0 (n-valuesp-rewrite1 n clique x))
                 (n-valuesp-rewrite1-al n clique x a))
                (n-values-ev (mv-nth 1 (n-valuesp-rewrite1 n clique x)) a)
                (natp n))
           (n-valuesp n (n-values-ev x a)))
  :hints(("Goal" :in-theory
          (disable (:definition n-valuesp-rewrite1-al)
                   n-valuesp-rewrite1)
          :induct (n-valuesp-rewrite1-al n clique x a)
          :expand ((:free (n) (n-valuesp-rewrite1-al n clique x a))
                   (:free (n) (n-valuesp-rewrite1-al n clique nil a))
                   (:free (n) (n-valuesp-rewrite1 n clique x))
                   (:free (n) (n-valuesp-rewrite1 n clique nil))))))

;; (defthm n-valuesp-rewrite1-correct
;;   (implies (and (n-values-ev-theoremp
;;                  (conjoin-clauses
;;                   (mv-nth 0 (n-valuesp-rewrite1 n clique x))))
;;                 (n-values-ev (mv-nth 1 (n-valuesp-rewrite1 n clique x)) a)
;;                 (natp n))
;;            (n-valuesp n (n-values-ev x a)))
;;   :hints (("Goal":use
;;            ((:instance n-values-ev-theoremp-implies-clauses-apply-alists
;;                        (clause  (mv-nth 0 (n-valuesp-rewrite1 n clique x)))
;;                        (alists (n-valuesp-rewrite1-al n clique x a))))
;;            :in-theory (disable
;;                         n-values-ev-theoremp-implies-clauses-apply-alists))))



;; (defthm n-valuesp-rewrite1-correct
;;   (implies (and (natp n)
;;                 (n-values-ev (mv-nth 1 (n-valuesp-rewrite1 n clique x)) a)
;;                 (not (n-valuesp n (n-values-ev x a))))
;;            (not (clauses-apply-alists-n-values-ev
;;                  (mv-nth 0 (n-valuesp-rewrite1 n clique x))
;;                  (n-valuesp-rewrite1-al n clique x a))))
;;   :hints (("goal" :induct (n-valuesp-rewrite1-al n clique x a))))

;; (defthm n-valuesp-rewrite1-correct1
;;   (implies (and (natp n)
;;                 (clauses-apply-alists-n-values-ev
;;                  (mv-nth 0 (n-valuesp-rewrite1 n clique x))
;;                  (n-valuesp-rewrite1-al n clique x a))
;;                 (not (n-valuesp n (n-values-ev x a))))
;;            (not (n-values-ev (mv-nth 1 (n-valuesp-rewrite1 n clique x)) a))))

(in-theory (disable n-valuesp-rewrite1 n-valuesp-rewrite1-al n-valuesp))

(local
 (progn
   (defun first-n-rec (n lst)
     (if (zp n)
         nil
       (cons (car lst) (first-n-rec (1- n) (cdr lst)))))

   (defthm first-n-ac-is-first-n-rec-1
     (implies (true-listp acc)
              (equal (first-n-ac n lst acc)
                     (revappend acc (first-n-rec n lst)))))

   (defthm take-is-first-n-rec
     (equal (take n l)
            (first-n-rec n l)))

   (in-theory (disable take))))




(defun n-valuesp-rewrite (clause clique)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (let ((term (car (last clause))))
    (if (and (consp term)
             (symbol-listp clique)
             (eq (car term) 'n-valuesp)
             (eql (length term) 3)
             (quotep (cadr term))
             (natp (cadr (cadr term))))
        (mv-let (nonrec rec)
          (n-valuesp-rewrite1 (cadr (cadr term)) clique (caddr term))
          (if (equal rec ''t)
              nonrec
            (cons (append (butlast clause 1) (list rec)) nonrec)))
      (list (list term)))))

(defun n-valuesp-rewrite-al (clause clique a)
  (let ((term (car (last clause))))
    (if (and (consp term)
             (symbol-listp clique)
             (eq (car term) 'n-valuesp)
             (eql (length term) 3)
             (quotep (cadr term))
             (natp (cadr (cadr term))))
        (let ((alists (n-valuesp-rewrite1-al
                       (cadr (cadr term)) clique (caddr term) a)))
          (mv-let (nonrec rec)
            (n-valuesp-rewrite1 (cadr (cadr term)) clique (caddr term))
            (declare (ignore nonrec))
            (if (equal rec ''t)
                alists
              (cons (list a) alists))))
      (list (list a)))))

(defthm n-values-ev-disjoin-append
  (iff (n-values-ev (disjoin (append x y)) a)
       (or (n-values-ev (disjoin x) a)
           (n-values-ev (disjoin y) a)))
  :hints(("Goal" :in-theory (enable append))))

;; (local
;;  (progn
;;    (defthm ev-car-last-implies-ev-disjoin
;;      (implies (n-values-ev (car (last cl)) a)
;;               (n-values-ev (disjoin cl) a))
;;      :hints(("Goal" :in-theory (e/d (disjoin) (n-values-ev-of-disjoin-3)))))

;;    (defthm ev-disjoin-append
;;      (implies (and (not (n-values-ev (disjoin cl) a))
;;                    (not (n-values-ev (disjoin last) a)))
;;               (not (n-values-ev (disjoin (append (first-n-rec n cl)
;;                                                  last))
;;                                 a)))
;;      :hints(("Goal" :in-theory (e/d (disjoin append) (n-values-ev-of-disjoin-3)))))

;;    (in-theory (disable append first-n-rec n-values-ev-of-disjoin-3))))

(defthm n-values-ev-car-last
  (implies (n-values-ev (car (last clause)) a)
           (n-values-ev (disjoin clause) a))
  :hints(("Goal" :induct (len clause)
          :in-theory (disable n-values-ev-bad-guy-rewrite)))
  :rule-classes nil)

(local
 (defthm n-values-ev-first-n-rec
   (implies (n-values-ev (disjoin (first-n-rec n clause)) a)
            (n-values-ev (disjoin clause) a))
   :rule-classes :forward-chaining))


(defthm n-valuesp-rewrite-correct1
  (implies (clauses-apply-alists-n-values-ev
            (n-valuesp-rewrite clause clique)
            (n-valuesp-rewrite-al clause clique a))
           (n-values-ev (disjoin clause) a))
  :hints (("goal" :use (n-values-ev-car-last))))

(in-theory (disable n-valuesp-rewrite n-valuesp-rewrite-al))

(acl2::prove-multi-env-clause-proc
 n-valuesp-rewrite-correct
 :ev n-values-ev :evlst n-values-ev-lst
 :clauseproc n-valuesp-rewrite
 :alists (n-valuesp-rewrite-al clause clique a)
 :alist-name a)


(in-theory (disable n-valuesp))


(defun n-valuesp-hint (clause fn world)
  (let ((last (car (last clause)))
        (clique (getprop fn 'recursivep nil 'current-acl2-world world)))
    (and (consp last)
         (eq (car last) 'n-valuesp)
         (consp (caddr last))
         ;; (or (cw "clause:~%~x0~%" clause) t)
         (cond ((or (consp (caaddr last))
                    (member (caaddr last) '(cons quote if)))
;;                 (or ;; (cw "clause proc; clause:~%~x0~%" clause)
;;                  (cw "clause proc~%")
                `(:computed-hint-replacement
                  t
                  :clause-processor (n-valuesp-rewrite clause ',clique)))))))
