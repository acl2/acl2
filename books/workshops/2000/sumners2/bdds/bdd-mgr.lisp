(in-package "ACL2")

#|

    bdd-mgr.lisp
    ~~~~~~~~~~~~

we define a bdd node manager based on stobjs and
(later) prove that the "exported" functions:
(bmr is the bdd manager stobj)

   free-bdd (lst bmr) --> (copy bmr)
   var-bdd  (n bmr) --> (bdd bmr)
   ite-bdd  (f g h bmr) --> (bdd bmr)
   eql-bdd  (f g) --> boolean

preserve the semantics of their boolean logic
equivalent operations. The implementation uses
stobjs to maintain a unique table of nodes and
a result cache of previous ite operations. the
tables are hashed and store entries in a list
when a collision occurs. the size of the tables
can easily be varied (although it requires a
recertification -- i.e. no runtime reallocation
of stobjs).

|#

;; This book includes the executable definitions for our bdd manager
;; and as such we will verify all of the guards in this book.

(set-verify-guards-eagerness 2)

#|----------------------------------------------------------------------------|#

;;;; BEGIN utility macros and functions ;;;;

(defun symb-join (x y)
  (declare (xargs :guard (and (symbolp x) (symbolp y))))
  (intern (concatenate 'string (symbol-name x) (symbol-name y))
	  "ACL2"))

(defun symb-app-fn (symb symbs)
  (declare (xargs :guard t))
  (if (atom symbs) symb
    (list 'symb-join symb
	  (symb-app-fn (first symbs) (rest symbs)))))

(defmacro symb-app (symb &rest symbs)
  (symb-app-fn symb symbs))

(defun defpred-fn (name params body)
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp params))))
  (list `(defun ,name ,params ,body)
        `(defthm ,(symb-app name '-forward-chain)
           (implies ,(cons name params)
                    ,body)
           :rule-classes :forward-chaining)
        `(defthm ,(symb-app name '-back-chain)
           (implies ,body
                    ,(cons name params))
           :rule-classes :rewrite)
        `(in-theory (disable ,name))))

(defmacro defpred (name params body)
  (declare (xargs :guard
                  (and (symbolp name)
                       (symbol-listp params))))
  (cons 'progn (defpred-fn name params body)))

(defthm natp-compound-recognizer
  (equal (natp x) (and (integerp x) (>= x 0)))
  :rule-classes :compound-recognizer)

(in-theory (disable natp))

(defun pnatp (x)
  (and (integerp x) (> x 0)))

(defthm pnatp-compound-recognizer
  (equal (pnatp x) (and (integerp x) (> x 0)))
  :rule-classes :compound-recognizer)

(in-theory (disable pnatp))

(defun fail (msg)
  (hard-error 'general-failure
	      "~xa"
	      (list (cons #\a msg))))

(defmacro fail-with (val msg)
  `(let ((fail-dmy (fail ,msg)))
     (declare (ignore fail-dmy)) ,val))

(defun binding? (x)
  (or (null x)
      (and (consp x)
	   (true-listp (car x))
	   (or (symbolp (caar x))
               (and (symbol-listp (caar x))
                    (consp (caar x))))
	   (binding? (cdr x)))))

(defun seq-fn (bind result)
  (declare (xargs :guard (binding? bind)))
  (cond ((endp bind) result)
        ((atom (caar bind))
         `(let ((,(caar bind)
                 ,(cadar bind)))
            ,(seq-fn (cdr bind) result)))
        ((endp (cdaar bind))
         `(let ((,(caaar bind)
                 ,(cadar bind)))
            ,(seq-fn (cdr bind) result)))
        (t
         `(mv-let ,(caar bind)
              ,(cadar bind)
            ,(seq-fn (cdr bind) result)))))

(defmacro seq (bind result)
  (declare (xargs :guard (binding? bind)))
  (seq-fn bind result))

;; example translation of seq:
;;
;; (seq (((x y) (f a b))
;;       (z (g x y)))
;;      (+ x y z))
;;
;; expands to:
;;
;; (mv-let (x y) (f a b)
;;   (let ((z (g x y)))
;;      (+ x y z)))


;;;; i am impressed ACL2 can prove the following without
;;;; any help.... :)

(local
(defthm logand-is-natp
  (implies (natp y)
	   (natp (logand x y)))
  :rule-classes :type-prescription))

(local
(defthm mv-nth-0-reduce
  (equal (mv-nth 0 (list x y)) x)))

(local
(defthm mv-nth-1-reduce
  (equal (mv-nth 1 (list x y)) y)))

(in-theory (disable mv-nth))

;;;; END utility macros and functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN data structure functions ;;;;

(defmacro bdd-0 () nil)

(defmacro bdd-1 () t)

(defmacro bdd-1p (x) `(eq ,x (bdd-1)))

(defmacro bdd-0p (x) `(not ,x))

(defmacro b-id (x) `(car ,x))

(defmacro b-test (x) `(cadr ,x))

(defmacro b-then (x) `(caddr ,x))

(defmacro b-else (x) `(cdddr ,x))

(defpred quadp (x)
  (and (consp x)
       (consp (cdr x))
       (consp (cddr x))))

(defun bddp (x)
  (or (booleanp x)
      (and (quadp x)
	   (pnatp (b-id x))
	   (pnatp (b-test x))
	   (bddp (b-then x))
	   (bddp (b-else x)))))

(defpred bdd-trp (x)
  (and (quadp x)
       (pnatp (b-id x))
       (pnatp (b-test x))
       (bddp (b-then x))
       (bddp (b-else x))))

(local
(defthm bddp-forward-chain-cons
  (implies (and (bddp x)
		(consp x))
	   (bdd-trp x))
  :rule-classes :forward-chaining))

(local
(defthm bddp-forward-chain-endp
  (implies (and (bddp x) (atom x))
	   (symbolp x))
  :rule-classes :forward-chaining))

(local
(defthm bddp-back-chain
  (implies (or (bdd-trp x)
	       (bdd-0p x)
	       (bdd-1p x))
	   (bddp x))
  :rule-classes :rewrite))

(in-theory (disable bddp))

(defun bdd-listp (x)
  (or (null x)
      (and (consp x)
	   (bddp (first x))
	   (bdd-listp (rest x)))))

(local
(defthm bdd-listp-forward-chain-true-listp
  (implies (bdd-listp x) (true-listp x))
  :rule-classes :forward-chaining))

(defun bdd-tr-listp (x)
  (or (null x)
      (and (consp x)
	   (bdd-trp (first x))
	   (bdd-tr-listp (rest x)))))

(local
(defthm bdd-tr-listp-forward-chain-true-listp
  (implies (bdd-tr-listp x) (true-listp x))
  :rule-classes :forward-chaining))

(local
(defthm bdd-tr-listp-forward-chain-bdd-trp
  (implies (and (bdd-tr-listp x)
		(consp x))
	   (bdd-trp (first x)))
  :rule-classes :forward-chaining))



(defmacro ite-f (x) `(car ,x))

(defmacro ite-g (x) `(cadr ,x))

(defmacro ite-h (x) `(caddr ,x))

(defmacro ite-rslt (x) `(cdddr ,x))

(defpred ite-resultp (x)
  (and (quadp x)
       (bddp (ite-f x))
       (bddp (ite-g x))
       (bddp (ite-h x))
       (bddp (ite-rslt x))))

(defun ite-resultp? (x)
  (or (null x) (ite-resultp x)))

(local
(defthm ite-resultp?-forward-chain
  (implies (and (ite-resultp? x) x)
	   (ite-resultp x))
  :rule-classes :forward-chaining))



(defun b-node (id var then else)
  (declare (xargs :guard (and (pnatp id) (pnatp var)
                              (bddp then) (bddp else))))
  (cons id (cons var (cons then else))))

(local
(defthm b-node-is-bdd-trp
  (implies (and (pnatp id) (pnatp var)
		(bddp then) (bddp else))
	   (bdd-trp (b-node id var then else)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((b-node id var then else)))
		 (:rewrite))))

;; this should be all we need to know about b-node
(in-theory (disable b-node))


(defun rslt-entry (f g h rslt)
  (declare (xargs :guard (and (bddp f) (bddp g) (bddp h)
                              (bddp rslt))))
  (cons f (cons g (cons h rslt))))

(local
(defthm rslt-entry-is-ite-resultp
  (implies (and (bddp f) (bddp g) (bddp h)
		(bddp rslt))
	   (ite-resultp (rslt-entry f g h rslt)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((rslt-entry f g h rslt)))
		 (:rewrite))))

;; this should be all we need to know about rslt-entry
(in-theory (disable rslt-entry))

;;;; END data structure functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN hash-code functions ;;;;

;;;; "bdd-hash-code" is the hash-code we use on bdd nodes

(defun bdd-hash-code (x y z r)
  (declare (xargs :guard (and (natp x) (natp y)
                              (natp z) (natp r))))
  (let ((code (logand (logxor (logxor x (ash y 2))
                              (ash z 4))
                      (1- r))))
    (if (< code r) code 0)))

(defthm bdd-hash-code-is-in-range-forward-chain
  (implies (and (natp r) (> r 0))
	   (and (natp (bdd-hash-code x y z r))
		(< (bdd-hash-code x y z r) r)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((bdd-hash-code x y z r))))
  :hints (("Goal" :in-theory (disable logxor logand ash))))

;; the above theorem should be all we need to know about bdd-hash-code

(in-theory (disable bdd-hash-code))

(defmacro id-hash (x y z)
  `(bdd-hash-code ,x ,y ,z (table-size)))

(defmacro bdd-hash (x y z)
  `(bdd-hash-code (b-id ,x) (b-id ,y) (b-id ,z) (table-size)))

;;;; END hash-code functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN stobj definition and theorems ;;;;

;;;; we now define the stobj for our bdd manager.

(defstobj bdd-mgr   ;; "bdd-mgr" -- bdd manager stobj
  ;; hash-table used to create bdd nodes uniquely. collisions are chained
  (uniq-tbl :type (array (satisfies bdd-tr-listp) (4096))
            :initially nil)
  ;; hash-table used to cache ite results. collisions overwrite
  (rslt-tbl :type (array (satisfies ite-resultp?) (4096))
            :initially nil)
  ;; number of bdd nodes allocated
  (next-id :type (integer 1 *)
           :initially 1))

(defmacro table-size () 4096)

(defmacro bmr-tblp (x)
  `(equal (len ,x) (table-size)))

(local
(defthm nth-uniq-tblp-back-chain
  (implies (uniq-tblp x)
           (bdd-tr-listp (nth n x)))))

(local
(defthm nth-rslt-tblp-back-chain
  (implies (rslt-tblp x)
           (ite-resultp? (nth n x)))))

(local
(defthm update-nth-uniq-tblp-bdd-tr-listp
  (implies (and (uniq-tblp x)
                (bdd-tr-listp v))
           (uniq-tblp (update-nth n v x)))))

(local
(defthm update-nth-rslt-tblp-ite-resultp?
  (implies (and (rslt-tblp x)
                (ite-resultp? v))
           (rslt-tblp (update-nth n v x)))))

(local
(defthm bdd-mgrp-nth-type-correct
  (implies (bdd-mgrp x)
           (and (uniq-tblp (nth 0 x))
                (rslt-tblp (nth 1 x))
                (pnatp (nth 2 x))
                (bmr-tblp (nth 0 x))
                (bmr-tblp (nth 1 x))))
  :rule-classes (:forward-chaining :rewrite)))

(local
(defthm bdd-mgrp-update-nth-type-correct
  (implies (and (bdd-mgrp x)
                (case n (0 (and (uniq-tblp v)
                                (bmr-tblp v)))
                        (1 (and (rslt-tblp v)
                                (bmr-tblp v)))
                        (2 (pnatp v))))
           (bdd-mgrp (update-nth n v x)))))

(in-theory (disable nth update-nth bdd-mgrp))

;;;; END stobj definition and theroems ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "eql-bdd" function ;;;;

(defun eql-bdd (x y)
  (declare (xargs :guard
                  (and (bddp x) (bddp y))))
  (if (atom x)
      (and (atom y) (iff x y))
    (and (consp y)
         (eql (b-id x) (b-id y)))))

;;;; END "eql-bdd" function ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN unique-tbl functions ;;;;

(defun node-eql (var then else bdd)
  (declare (xargs :guard
                  (and (pnatp var) (bddp then) (bddp else)
                       (bdd-trp bdd))))
  (and (eql var (b-test bdd))
       (eql-bdd then (b-then bdd))
       (eql-bdd else (b-else bdd))))

(defun bdd-match (var then else chain)
  (declare (xargs :guard
                  (and (pnatp var) (bddp then) (bddp else)
                       (bdd-tr-listp chain))))
  (cond ((endp chain) nil)
        ((node-eql var then else (first chain))
         (first chain))
        (t (bdd-match var then else (rest chain)))))

(local
(defthm bdd-match-bddp
  (implies (and (bdd-tr-listp chain)
		(bdd-match var then else chain))
	   (bdd-trp (bdd-match var then else chain)))))

;;;; the function "get-unique" checks if a previous bdd node
;;;; with the same signature <var,then,else> has been created
;;;; and if so, it returns this node. otherwise, it creates a
;;;; new bdd-node and adds it to the unique-tbl.

(defun bdd-id (b)
  (declare (xargs :guard (bddp b)))
  (if (atom b) 0 (b-id b)))

(local
(defthm bdd-id-natp
  (implies (bddp b)
	   (natp (bdd-id b)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((bdd-id b))))))

(in-theory (disable eql-bdd bdd-id))

(defun get-unique (var then else bdd-mgr)
  (declare (xargs :guard (and (pnatp var)
                              (bddp then)
                              (bddp else))
                  :stobjs bdd-mgr))
  (seq ((code (id-hash var (bdd-id then) (bdd-id else)))
        (chain (uniq-tbli code bdd-mgr))
        (bdd (bdd-match var then else chain)))
       (if bdd (mv bdd bdd-mgr)
         (seq ((bdd (b-node (next-id bdd-mgr) var then else))
               (bdd-mgr (update-next-id (1+ (next-id bdd-mgr)) bdd-mgr))
               (bdd-mgr (update-uniq-tbli code (cons bdd chain) bdd-mgr)))
              (mv bdd bdd-mgr)))))

(local
(defthm get-unique-type-correct
  (implies (and (pnatp var) (bddp then) (bddp else)
		(bdd-mgrp x))
	   (and (bddp (mv-nth 0 (get-unique var then else x)))
		(bdd-mgrp (mv-nth 1 (get-unique var then else x)))))))

(in-theory (enable eql-bdd))
(in-theory (disable get-unique))

;;;; END unique-tbl functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "init-bdd" functions ;;;;

(defun init-uniq-tbl (n bdd-mgr)
  (declare (xargs :guard (and (natp n)
                              (<= n (table-size)))
                  :measure (nfix (- (table-size) n))
                  :stobjs bdd-mgr))
  (if (zp (- (table-size) n)) bdd-mgr
    (seq ((bdd-mgr (update-uniq-tbli n nil bdd-mgr)))
         (init-uniq-tbl (1+ n) bdd-mgr))))

(defthm init-uniq-tbl-type-correct
  (implies (and (bdd-mgrp x) (natp n))
           (bdd-mgrp (init-uniq-tbl n x))))

(defun init-rslt-tbl (n bdd-mgr)
  (declare (xargs :guard (and (natp n)
                              (<= n (table-size)))
                  :measure (nfix (- (table-size) n))
                  :stobjs bdd-mgr))
  (if (zp (- (table-size) n)) bdd-mgr
    (seq ((bdd-mgr (update-rslt-tbli n nil bdd-mgr)))
         (init-rslt-tbl (1+ n) bdd-mgr))))

(defthm init-rslt-tbl-type-correct
  (implies (and (bdd-mgrp x) (natp n))
           (bdd-mgrp (init-rslt-tbl n x))))

(defun init-bdd (bdd-mgr)
  (declare (xargs :stobjs bdd-mgr))
  (seq ((bdd-mgr (init-uniq-tbl 0 bdd-mgr))
        (bdd-mgr (init-rslt-tbl 0 bdd-mgr))
        (bdd-mgr (update-next-id 1 bdd-mgr)))
       bdd-mgr))

(defthm init-bdd-type-correct
  (implies (bdd-mgrp x)
	   (bdd-mgrp (init-bdd x))))

(in-theory (disable init-bdd))

;;;; END "init-bdd" functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "var-bdd" function ;;;;

(defun var-bdd (n bdd-mgr)
  (declare (xargs :guard (pnatp n)
                  :stobjs bdd-mgr))
  (get-unique n (bdd-1) (bdd-0) bdd-mgr))

(defthm var-bdd-type-correct
  (implies (and (pnatp n) (bdd-mgrp x))
	   (and (bddp (mv-nth 0 (var-bdd n x)))
                (bdd-mgrp (mv-nth 1 (var-bdd n x))))))

(in-theory (disable var-bdd))

;;;; END "var-bdd" function ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN result-tbl functions ;;;;

;; the following predicate is used to keep from saving
;; "small" results in the result cache. you can use any
;; predicate here which preserves:
;;    (implies (cacheable-resultp f g h)
;;             (and (consp f) (consp g) (consp h)))

(defmacro cacheable-size () 10)

(defun cacheable-resultp (f g h)
  (declare (xargs :guard
                  (and (bddp f) (bddp g) (bddp h))))
  (and (consp f) (consp g) (consp h)
       (> (b-id f) (cacheable-size))
       (> (b-id g) (cacheable-size))
       (> (b-id h) (cacheable-size))))

(local
(defthm cacheable-resultp-forward-chain
  (implies (and (cacheable-resultp f g h)
		(bddp f) (bddp g) (bddp h))
	   (and (bdd-trp f)
		(bdd-trp g)
		(bdd-trp h)))
  :rule-classes :forward-chaining))

(in-theory (disable eql-bdd cacheable-resultp))

(local
(defthm ite-resultp?-back-chain2
  (implies (and (ite-resultp? x) x)
           (and (consp x)
                (consp (cdr x))
                (consp (cddr x))
                (bddp (ite-f x))
                (bddp (ite-g x))
                (bddp (ite-h x))
                (bddp (ite-rslt x))))))

(defun find-result (f g h bdd-mgr)
  (declare (xargs :guard (and (bddp f) (bddp g) (bddp h))
                  :guard-hints
                  (("Goal" :in-theory (disable ite-resultp?)))
                  :stobjs bdd-mgr))
  (and (cacheable-resultp f g h)
       (let ((entry (rslt-tbli (bdd-hash f g h) bdd-mgr)))
	 (and entry
	      (eql-bdd f (ite-f entry))
	      (eql-bdd g (ite-g entry))
	      (eql-bdd h (ite-h entry))
	      entry))))

(local
(defthm find-result-type-correct
  (implies (and (bddp f) (bddp g) (bddp h)
		(bdd-mgrp x) (find-result f g h x))
	   (ite-resultp (find-result f g h x)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((find-result f g h bmr)))
                 :rewrite)))

(in-theory (disable find-result))
(in-theory (enable eql-bdd))


(defun set-result (f g h r bdd-mgr)
  (declare (xargs :guard (and (bddp f) (bddp g) (bddp h) (bddp r))
                  :stobjs bdd-mgr))
  (if (not (cacheable-resultp f g h)) bdd-mgr
    (update-rslt-tbli (bdd-hash f g h) (rslt-entry f g h r) bdd-mgr)))

(local
(defthm set-result-type-correct
  (implies (and (bddp f) (bddp g) (bddp h)
		(bddp r) (bdd-mgrp x))
	   (bdd-mgrp (set-result f g h r x)))))

(in-theory (disable set-result))

;;;; END result-tbl functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "ite-bdd" functions ;;;;

(defun then-node (f v)
  (declare (xargs :guard (and (bddp f) (pnatp v))))
  (if (and (consp f) (eql (b-test f) v)) (b-then f) f))

(local
(defthm then-node-type-correct
  (implies (bddp f) (bddp (then-node f v)))))

(defun else-node (f v)
  (declare (xargs :guard (and (bddp f) (pnatp v))))
  (if (and (consp f) (eql (b-test f) v)) (b-else f) f))

(local
(defthm else-node-type-correct
  (implies (bddp f) (bddp (else-node f v)))))

(defun top-var (f g h)
  (declare (xargs :guard
                  (and (bdd-trp f) (bddp g) (bddp h))))
  (let ((fv (b-test f))
	(not-g (atom g))
	(not-h (atom h)))
    (cond ((and not-g not-h) fv)
          (not-h
           (let ((gv (b-test g)))
             (if (<= gv fv) fv gv)))
          (not-g
           (let ((hv (b-test h)))
             (if (<= hv fv) fv hv)))
          (t
           (let ((gv (b-test g))
                 (hv (b-test h)))
             (cond ((and (<= gv fv)
                         (<= hv fv)) fv)
                   ((<= hv gv) gv)
                   (t hv)))))))

(local
(defthm top-var-type-correct
  (implies (and (bdd-trp f) (bddp g) (bddp h))
	   (pnatp (top-var f g h)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((top-var f g h)))
                 (:rewrite))))

;;;; we will help keep the case analysis for ACL2 down
;;;; by proving the following theorems and then turning
;;;; then acl2-count

(local
(defthm eql-bdd-consp-implies-consp
  (implies (and (eql-bdd f g) (consp f))
	   (consp g))
  :rule-classes :forward-chaining))

(local
(defthm acl2-count-consp->0
  (implies (consp x)
	   (< 0 (acl2-count x)))
  :rule-classes :linear))

(local
(defthm consp-<-acl2-count-bdd-else
  (implies (consp x)
	   (< (acl2-count (b-else x))
	      (acl2-count x)))
  :rule-classes :linear))

(local
(defthm consp-<-acl2-count-bdd-then
  (implies (consp x)
	   (< (acl2-count (b-then x))
	      (acl2-count x)))
  :rule-classes :linear))

(in-theory (disable acl2-count eql-bdd))

(defun yes-no? (g h) (and (bdd-1p g) (bdd-0p h)))

(defun ite-bdd (f g h bdd-mgr)
  (declare (xargs :guard (and (bddp f) (bddp g) (bddp h))
                  :stobjs bdd-mgr
                  :verify-guards nil ;;;; we verify the guard below
		  :measure (+ (acl2-count f)
			      (acl2-count g)
			      (acl2-count h))))
  (cond ((atom f) (if f (mv g bdd-mgr) (mv h bdd-mgr)))
        ((yes-no? g h) (mv f bdd-mgr))
        ((eql-bdd g h) (mv g bdd-mgr))
        ((eql-bdd f g) (ite-bdd f (bdd-1) h bdd-mgr))
        ((eql-bdd f h) (ite-bdd f g (bdd-0) bdd-mgr))
        (t (let ((entry (find-result f g h bdd-mgr)))
             (if entry (mv (ite-rslt entry) bdd-mgr)
               (seq ((var (top-var f g h))
                     ((then bdd-mgr)
                      (ite-bdd (then-node f var)
                               (then-node g var)
                               (then-node h var)
                               bdd-mgr))
                     ((else bdd-mgr)
                      (ite-bdd (else-node f var)
                               (else-node g var)
                               (else-node h var)
                               bdd-mgr))
                     ((rslt bdd-mgr)
                      (if (eql-bdd then else) (mv then bdd-mgr)
                        (get-unique var then else bdd-mgr)))
                     (bdd-mgr (set-result f g h rslt bdd-mgr)))
                    (mv rslt bdd-mgr)))))))

(in-theory (enable acl2-count))

(in-theory (disable top-var then-node else-node))

(defthm ite-bdd-is-type-correct
  (implies (and (bddp f) (bddp g) (bddp h)
                (bdd-mgrp x))
           (and (bddp (mv-nth 0 (ite-bdd f g h x)))
		(bdd-mgrp (mv-nth 1 (ite-bdd f g h x))))))

(verify-guards ite-bdd)

(in-theory (disable ite-bdd))

;;;; END "ite-bdd" functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "free-bdd" functions ;;;;

(defun rebuild-bdd (f bdd-mgr)
  (declare (xargs :guard (bddp f)
                  :stobjs bdd-mgr
                  :verify-guards nil))
  (if (atom f) (mv f bdd-mgr)
    (mv-let (then bdd-mgr)
        (rebuild-bdd (b-then f) bdd-mgr)
      (mv-let (else bdd-mgr)
          (rebuild-bdd (b-else f) bdd-mgr)
        (get-unique (b-test f) then else bdd-mgr)))))

(defthm rebuild-bdd-is-type-correct
  (implies (and (bddp f) (bdd-mgrp x))
           (and (bddp (mv-nth 0 (rebuild-bdd f x)))
                (bdd-mgrp (mv-nth 1 (rebuild-bdd f x))))))

(verify-guards rebuild-bdd)

(defun rebuild-bdds (keep bdd-mgr)
  (declare (xargs :guard (bdd-listp keep)
                  :stobjs bdd-mgr))
  (if (endp keep) (mv () bdd-mgr)
    (mv-let (copy bdd-mgr)
        (rebuild-bdd (first keep) bdd-mgr)
      (mv-let (rest bdd-mgr)
          (rebuild-bdds (rest keep) bdd-mgr)
        (mv (cons copy rest) bdd-mgr)))))

(defthm rebuild-bdds-is-type-correct
  (implies (and (bdd-listp keep)
                (bdd-mgrp x))
           (and (bdd-listp (mv-nth 0 (rebuild-bdds keep x)))
                (bdd-mgrp (mv-nth 1 (rebuild-bdds keep x))))))

(defun free-bdd (keep bdd-mgr)
  (declare (xargs :guard (bdd-listp keep)
                  :stobjs bdd-mgr))
  (let ((bdd-mgr (init-bdd bdd-mgr)))
    (rebuild-bdds keep bdd-mgr)))

(defthm free-bdd-is-type-correct
  (implies (and (bdd-listp keep)
                (bdd-mgrp x))
           (and (bdd-listp (mv-nth 0 (free-bdd keep x)))
                (bdd-mgrp (mv-nth 1 (free-bdd keep x))))))

;;;; END "free-bdd" functions ;;;;
