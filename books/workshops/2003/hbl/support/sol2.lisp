;(acl2::set-match-free-error nil)
(in-package "ACL2")
(include-book "misc/records" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)
;-------------------
;; use record book instead of using list

(defmacro make-rc (ptrs ram map)
  `(s 'ptrs ,ptrs (s 'ram ,ram (s 'map ,map nil))))


;; not this ptrs is expected to a list of 3 turples
;; (typ addr n)

(defmacro ptrs    (rc) `(g 'ptrs ,rc))
(defmacro ram     (rc) `(g 'ram ,rc))
(defmacro getmap  (rc) `(g 'map ,rc))

(defmacro set-ptrs (ptrs rc) `(s 'ptrs ,ptrs ,rc))
(defmacro set-ram  (ram rc) `(s 'ram  ,ram ,rc))
(defmacro set-map  (map rc) `(s 'map  ,map ,rc))

(defun set-equal (a b)
  (and (subsetp a b)
       (subsetp b a)))

(defthm subsetp-append
  (subsetp a (append b a)))

(defthm append-nil-x-x
  (equal (append nil a) a))

(defthm subsetp-reflexive
  (subsetp a a)
  :hints (("Goal"
           :use ((:instance subsetp-append (b nil))))))

(defthm subsetp-transitive
  (implies (and (subsetp a b)
                (subsetp b c))
           (subsetp a c)))

(defequiv set-equal)

(defun seq-int (start len)
  (if (zp len)
      nil
    (cons (+ 0 start)
        (seq-int (1+ start) (1- len)))))

(defun struct-equiv-1-aux-m (typ-or-typs  n mode)
  (cond ((equal mode 'ATOM)
         (cons (+ 1 (nfix n)) 0))
        ((equal mode 'LIST)
         (cons (+ 1 (nfix n)) (len typ-or-typs)))
        (t 0)))

(defun struct-equiv-1-aux (typ-or-typs ptr-or-ptrs n ram1 ram2 map mode)
  (declare (xargs :measure (struct-equiv-1-aux-m typ-or-typs n mode)))
  (let ((typ typ-or-typs)
        (ptr ptr-or-ptrs)
        (typs typ-or-typs)
        (ptrs ptr-or-ptrs))
    (cond ((equal mode 'ATOM)
           (let* ((desc (cdr (assoc-equal typ map)))
                  (size (len desc)))
             (if (zp n) t
               (if (zp ptr) t
                 (if (not (assoc-equal typ map)) t
                 (if (not (equal (g ptr ram1)
                                 (g ptr ram2))) nil
                   (let ((addr (g ptr ram1)))
                     (struct-equiv-1-aux  desc
                                          (seq-int addr size)
                                          (- n 1)
                                          ram1 ram2 map 'LIST))))))))
          ((equal mode 'LIST)
           (if (endp typs) t
             (if (not (assoc-equal (car typs) map))
                 (struct-equiv-1-aux
                  (cdr typs) (cdr ptrs) n ram1 ram2 map 'LIST)
               (and (struct-equiv-1-aux (car typs) (car ptrs) n ram1 ram2 map 'ATOM)
                    (struct-equiv-1-aux (cdr typs) (cdr ptrs) n ram1 ram2 map 'LIST)))))
           (t t))))

(defun struct-equiv-1 (typ addr n ram1 ram2 map)
  (struct-equiv-1-aux typ addr n ram1 ram2 map 'ATOM))

(defun struct-equiv-1-list (typs addrs n ram1 ram2 map)
  (struct-equiv-1-aux typs addrs n ram1 ram2 map 'LIST))

;--------
(defun typ  (ptrs) (car   ptrs))
(defun addr (ptrs) (cadr  ptrs))
(defun n    (ptrs) (caddr ptrs))

(defun typ-list (ptrs)
  (if (endp ptrs) nil
    (cons (typ (car ptrs)) (typ-list (cdr ptrs)))))

(defun addr-list (ptrs)
  (if (endp ptrs) nil
    (cons (addr (car ptrs)) (addr-list (cdr ptrs)))))

(defun n-list (ptrs)
  (if (endp ptrs) nil
    (cons (n (car ptrs)) (n-list (cdr ptrs)))))

(defun all-struct-equiv-1 (typs addrs ns ram1 ram2 map)
  (if (endp typs) t
    (and (struct-equiv-1 (car typs) (car addrs) (car ns) ram1 ram2 map)
         (all-struct-equiv-1 (cdr typs) (cdr addrs) (cdr ns) ram1 ram2 map))))

(defun struct-equiv (rc1 rc2)
  (and (set-equal (ptrs rc1) (ptrs rc2))
       (equal (getmap rc1) (getmap rc2))
       (all-struct-equiv-1 (typ-list  (ptrs rc1))
                           (addr-list (ptrs rc1))
                           (n-list    (ptrs rc1))
                           (ram rc1)  (ram rc2) (getmap rc1))))

;------------- prove this a equivalence relation ----

(defthm struct-equiv-1-aux-reflexive
  (struct-equiv-1-aux typ-of-typs ptr-or-ptrs n ram ram map mode))

(defthm struct-equiv-1-aux-symentric
  (implies (struct-equiv-1-aux typ-of-typs ptr-or-ptrs n ram1 ram2 map mode)
           (struct-equiv-1-aux typ-of-typs ptr-or-ptrs n ram2 ram1 map mode)))

(defthm struct-equiv-1-aux-implies-g-ptr-equal
  (implies (and (struct-equiv-1-aux typ ptr n ram1 ram2 map mode)
                (not (zp n))
                (not (zp ptr))
                (equal mode 'ATOM)
                (assoc-equal typ map))
           (equal (g ptr ram1) (g ptr ram2)))
  :rule-classes :forward-chaining)

(defthm struct-equiv-1-aux-transitive
  (implies (and (struct-equiv-1-aux typ-of-typs ptr-or-ptrs n
                                    ram1 ram2 map mode)
                (struct-equiv-1-aux typ-of-typs ptr-or-ptrs n
                                    ram2 ram3 map mode))
           (struct-equiv-1-aux typ-of-typs ptr-or-ptrs n
                               ram1 ram3 map mode)))

(defthm all-struct-equiv-1-reflexive
  (all-struct-equiv-1 typs addrs ns ram ram map))

(defthm all-struct-equiv-1-symentric
  (implies (all-struct-equiv-1 typs addrs ns ram1 ram2 map)
           (all-struct-equiv-1 typs addrs ns ram2 ram1 map)))

(defthm all-struct-equiv-1-transitive
  (implies (and (all-struct-equiv-1 typs addrs ns ram1 ram2 map)
                (all-struct-equiv-1 typs addrs ns ram2 ram3 map))
           (all-struct-equiv-1 typs addrs ns ram1 ram3 map)))


;------------

(in-theory (disable struct-equiv-1))

(defthm all-struct-equiv-1-mem
  (implies (and (member ptr ptrs)
                (not (struct-equiv-1 (typ ptr) (addr ptr) (n ptr) ram1 ram2  map)))
           (not (all-struct-equiv-1 (typ-list ptrs) (addr-list ptrs) (n-list ptrs)
                                    ram1 ram2  map))))



(defthm all-struct-equiv-1-subsetp
  (implies (and (subsetp ptrs2 ptrs1)
                (all-struct-equiv-1 (typ-list ptrs1)
                                    (addr-list ptrs1)
                                    (n-list ptrs1)
                                    ram1 ram2 map))
                (all-struct-equiv-1 (typ-list ptrs2)
                                    (addr-list ptrs2)
                                    (n-list ptrs2)
                                    ram1 ram2 map)))



(defthm struct-equiv-transitive
  (implies (and (struct-equiv rc1 rc2)
                (struct-equiv rc2 rc3))
           (struct-equiv rc1 rc3)))

;; (in-theory (disable set-equal))

(defequiv struct-equiv)


;--------------

(defun collect-link-cells-1-aux
  (typ-or-typs ptr-or-ptrs n ram map mode)
  (declare (xargs :measure (struct-equiv-1-aux-m typ-or-typs n mode)))
  (let ((typ typ-or-typs)
        (ptr ptr-or-ptrs)
        (typs typ-or-typs)
        (ptrs ptr-or-ptrs))
    (cond ((equal mode 'ATOM)
           (let* ((desc (cdr (assoc-equal typ map)))
                  (size (len desc)))
             (if (zp n) nil
               (if (zp ptr) nil
                 (if (not (assoc-equal typ map))
                     nil
                 (let ((addr (g ptr ram)))
                   (cons ptr (collect-link-cells-1-aux desc
                                                       (seq-int addr size)
                                                       (- n 1)
                                                       ram map 'LIST))))))))

          ((equal mode 'LIST)
           (if (endp typs) nil
             (if (not (assoc-equal (car typs)  map)) ;; skip non pointer
                 (collect-link-cells-1-aux (cdr typs) (cdr ptrs) n ram map 'LIST)
               (append (collect-link-cells-1-aux (car typs)
                                                 (car ptrs)
                                                 n
                                                 ram map 'ATOM)
                       (collect-link-cells-1-aux (cdr typs)
                                                 (cdr ptrs)
                                                 n
                                                 ram map 'LIST)))))
          (t nil))))


;---------------
(defun collect-link-cells-1 (typ addr n ram map)
  (collect-link-cells-1-aux typ addr n ram map 'ATOM))

(defun collect-link-cells-1-list (typs addrs n ram map)
  (collect-link-cells-1-aux typs addrs n ram map 'LIST))


(defun all-collect-link-cells-1 (typs addrs ns ram map)
  (if (endp typs)
      nil
    (append (collect-link-cells-1 (car typs) (car addrs) (car ns) ram map)
            (all-collect-link-cells-1 (cdr typs) (cdr addrs) (cdr ns) ram  map))))

;---------------

(defun collect-link-cells (rc)
  (all-collect-link-cells-1 (typ-list  (ptrs rc))
                            (addr-list (ptrs rc))
                            (n-list    (ptrs rc))
                            (ram rc)   (getmap rc)))


;; next task (defcong struct-equiv

(defthm member-append-1
  (implies (member x b)
           (member x (append a b))))

(defthm member-append-2
  (implies (member x a)
           (member x (append a b))))

(defthm subsetp-append-x-1
  (implies (subsetp a b)
           (subsetp (append a c)
                    (append b c))))

(defthm subsetp-append-x-2
  (implies (subsetp a b)
           (subsetp (append c a)
                    (append c b))))



(defcong set-equal set-equal (append a b) 1)
(defcong set-equal set-equal (append a b) 2)

(defthm subsetp-append-b
  (subsetp a (append a b)))

(defthm subsetp-collect-link-cells-1-subsetp
  (implies (member  ptr ptrs)
           (subsetp (collect-link-cells-1 (typ  ptr)
                                          (addr ptr)
                                          (n    ptr)
                                          ram map)
                    (all-collect-link-cells-1 (typ-list ptrs)
                                              (addr-list ptrs)
                                              (n-list ptrs)
                                              ram map)))
  :hints (("Goal" :in-theory (disable collect-link-cells-1)
           :do-not '(generalize))))

(in-theory (disable typ addr n))

(defthm subsetp-merged-still-subsetp
  (implies (and (subsetp a b)
                (subsetp c b))
           (subsetp (append a c) b)))


(defthm subsetp-all-collect-link-cells-1-subsetp
  (implies (subsetp ptrs1 ptrs2)
           (subsetp (all-collect-link-cells-1 (typ-list ptrs1)
                                                (addr-list ptrs1)
                                                (n-list ptrs1)
                                                ram map)
                    (all-collect-link-cells-1 (typ-list ptrs2)
                                                (addr-list ptrs2)
                                                (n-list ptrs2)
                                                ram map)))
  :hints (("Goal" :in-theory (disable collect-link-cells-1))))



(defthm set-equal-collect-link-cells-1-set-equal
  (implies (and (set-equal ptrs1 ptrs2)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context:
                (syntaxp (not (term-order ptrs1 ptrs2))))
           (set-equal (all-collect-link-cells-1 (typ-list ptrs1)
                                                (addr-list ptrs1)
                                                (n-list ptrs1)
                                                ram map)
                      (all-collect-link-cells-1 (typ-list ptrs2)
                                                (addr-list ptrs2)
                                                (n-list ptrs2)
                                                ram map))))


(defthm struct-equiv-1-aux-implies-collect-link-cells-aux-equal
  (implies (struct-equiv-1-aux typ-or-typs ptr-or-ptrs n ram1 ram2 map mode)
           (equal (collect-link-cells-1-aux typ-or-typs ptr-or-ptrs n
                                            ram1 map mode)
                  (collect-link-cells-1-aux typ-or-typs ptr-or-ptrs n
                                            ram2 map mode))))


(defthm struct-equiv-1-equal-collect-link-cells-1-equal
  (implies (all-struct-equiv-1 typs addrs ns ram1 ram2 map)
           (equal  (all-collect-link-cells-1 typs
                                             addrs
                                             ns
                                             ram1 map)
                   (all-collect-link-cells-1 typs
                                             addrs
                                             ns
                                             ram2 map)))
  :hints (("Goal" :in-theory (enable struct-equiv-1))))


;--------------
(in-theory (disable set-equal))


(defcong struct-equiv set-equal (collect-link-cells rc) 1)

;-- need to prove update to the non link cell keep the struct-equiv

(defthm not-member-append-f-1
  (implies (not (member x (append a b)))
           (not (member x a)))
  :rule-classes :forward-chaining)

(defthm not-member-append-f-2
  (implies (not (member x (append a b)))
           (not (member x b)))
  :rule-classes :forward-chaining)


(defun struct-equiv-1-induct (addrx typ-or-typs ptr-or-ptrs n ram map mode)
  (declare (xargs :measure (struct-equiv-1-aux-m typ-or-typs n mode)))
  (let ((typ typ-or-typs)
        (ptr ptr-or-ptrs)
        (typs typ-or-typs)
        (ptrs ptr-or-ptrs))
    (cond ((equal mode 'ATOM)
           (let* ((desc (cdr (assoc-equal typ map)))
                  (size (len desc)))
             (if (zp n) t
               (if (zp ptr) t
                 (if (not (assoc-equal typ map)) t
                   (if (equal addrx ptr) t
                     (let ((addr (g ptr ram)))
                       (struct-equiv-1-induct  addrx  desc  (seq-int addr size)
                                               (- n 1)  ram  map 'LIST))))))))
          ((equal mode 'LIST)
           (if (endp typs) t
             (if (not (assoc-equal (car typs) map))
                 (struct-equiv-1-induct addrx (cdr typs) (cdr ptrs) n  ram map 'LIST)
               (list (struct-equiv-1-induct addrx (car typs) (car ptrs) n ram map 'ATOM)
                     (struct-equiv-1-induct addrx (cdr typs) (cdr ptrs) n ram map 'LIST)))))
           (t (list addrx typ-or-typs ptr-or-ptrs n ram map mode)))))


(defthm struct-equiv-1-aux-atom-implies-member
  (implies (AND
            (NOT (ZP N))
            (NOT (ZP ADDR))
            (ASSOC-EQUAL TYP MAP))
           (MEMBER ADDR
                   (COLLECT-LINK-CELLS-1-AUX TYP ADDR N RAM MAP
                                             'ATOM)))
  :hints (("Goal" :expand  (COLLECT-LINK-CELLS-1-AUX TYP ADDR N RAM MAP 'ATOM))))

(defthm struct-equiv-1-aux-s-add-v-struct-equiv-1-aux
  (implies (not (member addr (collect-link-cells-1-aux
                              typ-or-typs ptr-or-ptrs n ram map mode)))
           (struct-equiv-1-aux typ-or-typs ptr-or-ptrs n
                               (s addr any ram) ram map mode))
  :hints (("Goal" :induct (struct-equiv-1-induct addr typ-or-typs ptr-or-ptrs n ram
                                                 map mode)
           :do-not '(generalize))))

;-----------------------

(defthm all-struct-equiv-1-s-add-v-all-struct-equiv-1
  (implies (not (member addr (all-collect-link-cells-1
                              typs ptrs ns ram map)))
           (all-struct-equiv-1 typs  ptrs ns
                               (s addr any ram) ram map))
  :hints (("Goal" :in-theory (enable struct-equiv-1))))


(defthm struct-equiv-preserved-if-update-non-link-cell
  (implies (not (member addr (collect-link-cells rc)))
           (struct-equiv (set-ram (s addr v (ram rc)) rc)
                         rc)))

;-----------------------

;;
;; done with the proof that (s addr v ram) preserve struct-equiv
;; so far, we have
;;
;;    (defcong struct-equiv set-equal (collect-link-cells rc) 1)
;;
;; and
;;
;;     struct-equiv-preserved-if-update-non-link-cell
;;


;
;--- define the generic mark algorithm, that only change data cells
;

;;
;; we need to be able to tell that data cell value only depend on data cells
;;


(defun collect-data-cells-1-aux (typ-or-typs ptr-or-ptrs n ram map mode)
  (declare (xargs :measure (struct-equiv-1-aux-m typ-or-typs n mode)))
  (let ((typ typ-or-typs)
        (ptr ptr-or-ptrs)
        (typs typ-or-typs)
        (ptrs ptr-or-ptrs))
    (cond ((equal mode 'ATOM)
           (let* ((desc (cdr (assoc-equal typ map)))
                  (size (len desc)))
             (if (zp n) nil
               (if (zp ptr) nil
                 (if (not (assoc-equal typ map))
                     nil
                   ;;  maybe I should modify it so that it matches with
                   ;;  collect-updates. i.e. collect data cells here in one
                   ;;  batch. Still want a try with the other proof.
                   (let ((addr (g ptr ram)))
                     (collect-data-cells-1-aux desc
                                               (seq-int addr size)
                                               (- n 1)
                                               ram map 'LIST)))))))
          ((equal mode 'LIST)
           (if (endp typs) nil
             (if (not (assoc-equal (car typs)  map))
                 ;; this is a data cell, recorded it.
                 (cons (car ptrs)
                       (collect-data-cells-1-aux (cdr typs) (cdr ptrs)
                                                 n ram map 'LIST))
               (append (collect-data-cells-1-aux (car typs)
                                                 (car ptrs)
                                                 n
                                                 ram map 'ATOM)
                       (collect-data-cells-1-aux (cdr typs)
                                                 (cdr ptrs)
                                                 n
                                                 ram map 'LIST)))))
          (t nil))))


;-----------

(defun collect-data-cells-1 (typ addr n ram map)
  (collect-data-cells-1-aux typ addr n ram map 'ATOM))

(defun collect-data-cells-1-list (typs addrs n ram map)
  (collect-link-cells-1-aux typs addrs n ram map 'LIST))


(defun all-collect-data-cells-1 (typs addrs ns ram map)
  (if (endp typs)
      nil
    (append (collect-data-cells-1 (car typs) (car addrs) (car ns) ram map)
            (all-collect-data-cells-1 (cdr typs) (cdr addrs) (cdr ns) ram  map))))

;------------

(defun collect-data-cells (rc)
  (all-collect-data-cells-1 (typ-list  (ptrs rc))
                            (addr-list (ptrs rc))
                            (n-list    (ptrs rc))
                            (ram rc)   (getmap rc)))

;; prove (defcong .... )

(defthm subsetp-collect-data-cells-1-subsetp
  (implies (member  ptr ptrs)
           (subsetp (collect-data-cells-1 (typ  ptr)
                                          (addr ptr)
                                          (n    ptr)
                                          ram map)
                    (all-collect-data-cells-1 (typ-list ptrs)
                                              (addr-list ptrs)
                                              (n-list ptrs)
                                              ram map)))
  :hints (("Goal" :in-theory (disable collect-data-cells-1)
           :do-not '(generalize))))


(defthm subsetp-all-collect-data-cells-1-subsetp
  (implies (subsetp ptrs1 ptrs2)
           (subsetp (all-collect-data-cells-1 (typ-list ptrs1)
                                                (addr-list ptrs1)
                                                (n-list ptrs1)
                                                ram map)
                    (all-collect-data-cells-1 (typ-list ptrs2)
                                                (addr-list ptrs2)
                                                (n-list ptrs2)
                                                ram map)))
  :hints (("Goal" :in-theory (disable collect-data-cells-1))))


(defthm set-equal-collect-data-cells-1-set-equal
  (implies (and (set-equal ptrs1 ptrs2)
                ;; Added for mod to ACL2 v2-8 that does better matching for
                ;; calls of equivalence relations against the current context:
                (syntaxp (not (term-order ptrs1 ptrs2))))
           (set-equal (all-collect-data-cells-1 (typ-list ptrs1)
                                                (addr-list ptrs1)
                                                (n-list ptrs1)
                                                ram map)
                      (all-collect-data-cells-1 (typ-list ptrs2)
                                                (addr-list ptrs2)
                                                (n-list ptrs2)
                                                ram map)))
  :hints (("Goal" :in-theory (enable set-equal))))


(defthm struct-equiv-1-aux-implies-collect-data-cells-aux-equal
  (implies (struct-equiv-1-aux typ-or-typs ptr-or-ptrs n ram1 ram2 map mode)
           (equal (collect-data-cells-1-aux typ-or-typs ptr-or-ptrs n
                                            ram1 map mode)
                  (collect-data-cells-1-aux typ-or-typs ptr-or-ptrs n
                                            ram2 map mode))))


(defthm struct-equiv-1-equal-collect-data-cells-1-equal
  (implies (all-struct-equiv-1 typs addrs ns ram1 ram2 map)
           (equal  (all-collect-data-cells-1 typs
                                             addrs
                                             ns
                                             ram1 map)
                   (all-collect-data-cells-1 typs
                                             addrs
                                             ns
                                             ram2 map)))
  :hints (("Goal" :in-theory (enable struct-equiv-1))))

(defcong struct-equiv set-equal (collect-data-cells rc) 1)

;----------------
;;
;; the problem here is how to characterize all possible updates?
;;
;; A constraint function is good. However to argue it can model all possible
;; computation need some efforts.
;;
;; Because in this mark function, we update in the pre-order, once we reach
;; some node, we update, then we continue, etc.
;;
;; It is hard to argue that we could implement all kinds of update order,
;; because it is possible that the data value depends on the order we do them.
;;
;; In J's model, the value of new data fills only depends on the old data
;; within the same node.
;;
;; In my model, I want to extend that to all possible data fields reachable.
;;
;; Then I have to face this problem.
;;



;; say only change up

(encapsulate
 ((new-field-value (typ ptr i n ram map) t))
 (local (defun new-field-value (typ ptr i n ram map)
          (declare (ignore typ ptr i n ram map))
          0))
 (defthm new-field-value-s-commutes
   (implies (not (member addr (append (collect-data-cells-1 typ ptr n ram map)
                                      (collect-link-cells-1 typ ptr n ram map))))
            (equal (new-field-value typ ptr i n (s addr val ram) map)
                   (new-field-value typ ptr i n ram              map)))))

;;
;; This is to say, any write outside the reachable data+link fields,
;; doesn't matter to the new-field-value
;;

(defun single-update1 (typ ptr i n ram map)
  (declare (xargs :measure (nfix (- (len (cdr (assoc-equal typ map)))
                                    (nfix i)))))
  (let* ((descriptor (cdr (assoc-equal typ map)))
         (i (nfix i))
         (slot-typ (nth i descriptor))
         (addr (g ptr ram)))
    (if (zp ptr) ram
      (if (< i (len  descriptor))
          (if (assoc-equal slot-typ map)
              ;; a struct type, meaning a ptr in the (car addrs)
              ;; don't touch link cells
              (single-update1 typ ptr  (+ i 1) n ram map)
            ;; else not a struct type, update the value
            (let ((ram  (s (+ addr i) (new-field-value typ ptr i n ram map) ram)))
              ;; let the new value depends on the changes to the previous slos
              (single-update1 typ ptr (+ i 1) n ram map)))
        ram))))

;; (defstub single-update2 (types addr size ram map)  ram) ;; update in inorder
;; (defstub single-update3 (type ptr size ram map)  ram) ;; update in postorder

;;
;; chose not to deal with those now.
;;
;;
;; assume our constainted new-value is so powerful that it can emulates all
;; possible changes with in-order and post-order updates, arbitary updates.
;;
;; not so sure. this is possible,
;;
;; I could find a particular way of updating memory that cause the program
;; enter into a loop, however oracle in the single-updates have to garantee to
;; provide us an initial ram to result in the same loop....
;; it is possible, because oracle can detect if the initial ram config is ...
;;
;;

(defun mark-1-aux (typ-or-typs ptr-or-ptrs n ram map mode)
  (declare (xargs :measure (struct-equiv-1-aux-m typ-or-typs n mode)))
  (let ((typ typ-or-typs)
        (ptr ptr-or-ptrs)
        (typs typ-or-typs)
        (ptrs ptr-or-ptrs))
    (cond ((equal mode 'ATOM)
           (let* ((desc (cdr (assoc-equal typ map)))
                  (size (len desc)))
             (if (zp n) ram
               (if (zp ptr) ram
                 (if (not (assoc-equal typ map)) ;; not bound
                     ram
                   (let* ((addr (g ptr ram))
                          (new-ram (single-update1 typ ptr 0 n ram map)))
                     (mark-1-aux desc
                                 (seq-int addr size)
                                 (- n 1)
                                 new-ram map 'LIST)))))))
          ((equal mode 'LIST)
           (if (endp typs)
               ram
             (if (not (assoc-equal (car typs)  map))
                 (mark-1-aux (cdr typs) (cdr ptrs) n ram map 'LIST)
               (let ((new-ram (mark-1-aux (car typs)
                                          (car ptrs)
                                          n
                                          ram map 'ATOM)))
                 (mark-1-aux (cdr typs)
                             (cdr ptrs)
                             n
                             new-ram map 'LIST)))))
          (t ram))))


;--- mark-1
(defun mark-1 (typ addr n ram map)
  (mark-1-aux typ addr n ram map 'ATOM))

(defun mark-1-list (typs addrs n ram map)
  (mark-1-aux typs addrs n ram map 'LIST))

;-------------

(defun all-mark-1 (typs addrs ns ram map)
  (if (endp typs)
      ram
    (all-mark-1 (cdr typs) (cdr addrs) (cdr ns)
                (mark-1 (car typs) (car addrs) (car ns) ram map)
                map)))

;-------------

(defun mark (rc)
  (all-mark-1 (typ-list (ptrs rc))
              (addr-list (ptrs rc))
              (n-list    (ptrs rc))
              (ram rc)
              (getmap rc)))

;------------
;;
;; update is of this format (type ptr i n),
;; new-value depends on these
;;

;; relevence analysis problem.

(defun m-collect-updates (typ map i ram)
  (declare (ignore ram))
  (nfix (- (len (cdr (assoc-equal typ map)))
           (nfix i))))


(defun  make-update (typ ptr i n)
  (list typ ptr i n))

(defun  gtyp (update)  (car update))
(defun  gptr (update)  (cadr  update))
(defun  gi   (update) (caddr update))
(defun  gn   (update) (caddr (cdr update)))

(defthm make-update-accessor
  (and   (equal (gtyp (make-update typ ptr i n)) typ)
         (equal (gptr (make-update typ ptr i n)) ptr)
         (equal (gi (make-update typ ptr i n)) i)
         (equal (gn (make-update typ ptr i n)) n)))

(in-theory (disable make-update gtyp gptr gi gn))


(defun collect-updates-from-single-update1 (typ ptr i n ram map)
  (declare (xargs :measure (m-collect-updates typ map i ram)))
  (let* ((descriptor (cdr (assoc-equal typ map)))
         (i (nfix i))
         (slot-typ (nth i descriptor))
         (addr (g ptr ram)))
    (if (zp ptr) nil
      (if (< i (len  descriptor))
          (if (assoc-equal slot-typ map)
              ;; a struct type, meaning a ptr in the (car addrs)
              ;; don't touch link cells
              (collect-updates-from-single-update1 typ ptr (+ i 1) n ram map)
            ;; else not a struct type, update the value
            (let ((new-ram  (s (+ addr i) (new-field-value typ ptr i n ram map) ram)))
              ;; let the new value depends on the changes to the previous slos
              (cons (make-update typ ptr i n)
                    (collect-updates-from-single-update1 typ ptr (+ i 1) n
                                                         new-ram map))))
        nil))))


(defun collect-updates-zdynamic-1-aux (typ-or-typs ptr-or-ptrs n ram map mode)
  (declare (xargs :measure (struct-equiv-1-aux-m typ-or-typs n mode)))
  (let ((typ typ-or-typs)
        (ptr ptr-or-ptrs)
        (typs typ-or-typs)
        (ptrs ptr-or-ptrs))
    (cond ((equal mode 'ATOM)
           (let* ((desc (cdr (assoc-equal typ map)))
                  (size (len desc)))
             (if (zp n) nil
               (if (zp ptr) nil
                 (if (not (assoc-equal typ map)) ;; not bound
                     nil
                   (let* ((addr (g ptr ram))
                          (new-ram (single-update1 typ ptr 0 n ram map)))
                     (append (collect-updates-from-single-update1
                              typ ptr 0 n ram map)
                             (collect-updates-zdynamic-1-aux
                              desc
                              (seq-int addr size)
                              (- n 1)
                              new-ram map 'LIST))))))))
          ((equal mode 'LIST)
           (if (endp typs)
               nil
             (if (not (assoc-equal (car typs)  map))
                 (collect-updates-zdynamic-1-aux
                     (cdr typs) (cdr ptrs) n ram map 'LIST)
               (let ((new-ram (mark-1-aux (car typs)
                                          (car ptrs)
                                          n
                                          ram map 'ATOM)))
                 (append (collect-updates-zdynamic-1-aux
                           (car typs) (car ptrs) n ram map 'ATOM)
                         (collect-updates-zdynamic-1-aux (cdr typs)
                                                        (cdr ptrs)
                                                        n
                                                        new-ram map 'LIST))))))
          (t nil))))


;---------- prove apply-dynamic update equal to mark on the fly
;
; update is a (typ ptr i n)
;
;

(defun apply-update (update ram map)
  (let ((typ (gtyp update))
        (ptr (gptr update))
        (i   (gi   update))
        (n   (gn   update)))
    (let ((addr (g ptr ram)))
      (s (+ addr i) (new-field-value typ ptr i n ram map) ram))))


(defun apply-updates (updates ram map)
  (if (endp updates) ram
    (apply-updates (cdr updates) (apply-update (car updates) ram map) map)))


(defthm apply-updates-collect-updates-from-single-update1-is-single-update1
  (equal (single-update1 typ ptr i n ram map)
         (apply-updates (collect-updates-from-single-update1
                         typ ptr i n ram map)
                        ram map)))


(defthm apply-updates-append
  (equal (apply-updates (append updates1 updates2) ram map)
         (apply-updates updates2
                        (apply-updates updates1 ram map) map)))

(in-theory (disable apply-update))

(defthm apply-updates-collect-dynamic-is-mark
  (equal (mark-1-aux typ-or-typs ptr-or-ptrs n ram map mode)
         (apply-updates (collect-updates-zdynamic-1-aux
                        typ-or-typs ptr-or-ptrs n ram map mode)
                       ram map))
  :hints (("Goal" :do-not '(generalize))))

;
;--------------------
;

(defun collect-updates-dynamic-1 (typ ptr n ram map)
  (collect-updates-zdynamic-1-aux typ  ptr n ram map 'ATOM))

(defun collect-updates-dynamic-1-list (typs ptrs n ram map)
  (collect-updates-zdynamic-1-aux typs  ptrs n ram map 'LIST))


;--------------------

(defun all-collect-updates-dynamic-1 (typs ptrs ns ram map)
  (if (endp typs)
      nil
    (append (collect-updates-dynamic-1 (car typs) (car ptrs) (car ns)
                                       ram map)
          (all-collect-updates-dynamic-1
                   (cdr typs) (cdr ptrs) (cdr ns)
                   (mark-1 (car typs) (car ptrs) (car ns) ram map)
                   map))))

;--------------

(defun collect-updates-dynamic (rc)
  (all-collect-updates-dynamic-1 (typ-list  (ptrs rc))
                                 (addr-list (ptrs rc))
                                 (n-list    (ptrs rc))
                                 (ram rc)
                                 (getmap rc)))

;--------------

(defthm all-mark-1-is-apply-update-1
  (equal (all-mark-1 typs addrs ns ram map)
         (apply-updates (all-collect-updates-dynamic-1 typs addrs ns ram map)
                        ram map)))


(defthm apply-equal-mark
  (equal (mark rc)
         (apply-updates (collect-updates-dynamic rc)
                        (ram rc) (getmap rc))))

;--------------
;;
;; next is to prove struct-equiv,
;; is if data cell doesn't overlap with link cell,
;; then collect-dyanmic is collect-static
;;


(defun overlap (a b)
  (if (endp a) nil
    (or (member (car a) b)
        (overlap (cdr a) b))))

(defun update-2-w (update ram)
  (let ((ptr (gptr update))
        (i   (gi   update)))
    (+ i (g ptr ram))))

(defun updates-2-ws (updates ram map)
  (if (endp updates)
      nil
    (cons (update-2-w (car updates) ram)
          (updates-2-ws (cdr updates) (apply-update (car updates) ram map)
                        map))))

(defthm member-append
  (implies (member x a)
           (member x (append a b))))

(defthm inrange-seen
  (implies (and (not (zp l))
                (integerp x)
                (integerp y)
                (integerp l)
                (<  y (+ x l))
                (<= x y))
           (member y (seq-int x l)))
  :hints (("Goal" :do-not '(generalize))))

(defthm consp-car-append
  (implies (consp l)
           (equal (car (append l x))
                  (car l))))


(defthm consp-implies-consp
  (implies (and (consp (append a b))
                (not (consp b)))
           (consp a))
  :rule-classes :forward-chaining)


;----------------------------------
;
; very awkward, because our collect-data-cell doesn't match our collect-updates.
;
;  collect-data-cell, record the data cell, in collect-data-cell-1-list
;  while  collect-updates-dymanic collect data-cell in collect-data-cell-1
;

(defthm first-update-must-be-a-data-field
  (implies (consp (collect-updates-from-single-update1 TYP PTR I N RAM MAP))
           (not (assoc-equal (nth (gi (car (collect-updates-from-single-update1 TYP PTR i N RAM MAP)))
                                  (cdr (assoc-equal typ map)))
                             map)))
  :hints (("Goal" :do-not '(generalize))))

;
; proved that first update must be a data cell, we can't claim more,
; because the second update would be a data cell in a modified ram.
; we can't show that data cell is a data cell in the original ram.
;
; unless we have already shown that there is no overlap between data cell and
; link cell.
;

;--------------

(defun pos (x l)
  (if (endp l) 0
    (if (equal (car l) x) 0
      (+ 1 (pos x (cdr l))))))


(defun not-assoc-equal-induct (typx typs ptrs)
  (if (endp typs)
      (list typx typs)
    (if (equal (car typs) typx)
        (list typx typs ptrs)
      (not-assoc-equal-induct typx (cdr typs) (cdr ptrs)))))

(defthm not-assoc-equal-must-be-in-collect-data-cell-list
  (implies (and (member typx typs)
                (not (assoc-equal typx map)))
           (member (nth (pos typx typs) ptrs)
                   (collect-data-cells-1-aux typs
                                             ptrs
                                             n
                                             ram map 'LIST)))
  :hints (("Goal" :induct (not-assoc-equal-induct typx typs ptrs))))


;;
;; we need to prove (nth (gi ....)) is such a typx
;; we probably don't have to prove the general case with i in the theorem.
;;

;--- First: prove member (gi ..)

(defthm update-typ-i-is-in-range-1
  (implies (consp (collect-updates-from-single-update1
                   TYP PTR I N RAM MAP))
           (<= (nfix i) (gi (car (collect-updates-from-single-update1 typ ptr i n ram
                                                                      map)))))
  :hints (("Goal" :do-not '(generalize)))
  :rule-classes :linear)

(defthm update-typ-i-is-in-range-2
  (implies (consp (collect-updates-from-single-update1
                   TYP PTR I N RAM MAP))
           (< (gi (car (collect-updates-from-single-update1 typ ptr i n ram
                                                            map)))
              (len (cdr (assoc-equal typ map)))))
  :hints (("Goal" :do-not '(generalize)))
  :rule-classes :linear)


(defthm nth-member
  (implies (and (<= 0 i)
                (< i (len l)))
           (member (nth i l) l)))

(defun mycdrn (i l)
  (if (zp i)
      l
    (mycdrn (- i 1) (cdr l))))


(defthm member-nth-cdrn-2
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= i j)
                (< j (len l)))
           (member (nth j l)
                   (mycdrn i l))))


(defthm integerp-gi-g-ptr-car-collect-update-from-single-update1
  (implies (consp (collect-updates-from-single-update1 typ ptr i n ram map))
           (integerp (gi (car (collect-updates-from-single-update1
                               typ ptr i n ram map)))))
  :rule-classes :forward-chaining)

(defthm first-update-typ-is-member-of-sig
  (implies (consp (collect-updates-from-single-update1 typ ptr i n ram map))
           (member (nth (gi (car (collect-updates-from-single-update1
                                  typ ptr i n ram map)))
                        (cdr (assoc-equal typ map)))
                   (mycdrn i (cdr (assoc-equal typ map)))))
  :hints (("Goal" :do-not '(generalize)))
  :rule-classes :forward-chaining)


;------------------
;
; Because we already have (member (nth (pos typx) ...) in data cells
;
; next we need to prove (nth (pos (nth (gi ...))  is (nth (gi ...))
;
;------------------

(defthm pos-mycdrn
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len l)))
           (equal (pos (nth i l)
                       (mycdrn i l)) 0)))


(defthm assoc-equal-not-equal-nth-gi
  (implies (and (consp (collect-updates-from-single-update1 typ ptr i n ram map))
                (assoc-equal typx map))
           (not (equal (nth (gi (car (collect-updates-from-single-update1
                                      typ ptr i n ram map)))
                            (cdr (assoc-equal typ map)))
                       typx))))


(defthm pos-mycdrn-2
  (implies (and (integerp i)
                (<= 0 i)
                (< i (len l))
                (not (equal x (nth i l))))
           (equal (+ 1 (pos x (mycdrn i (cdr l))))
                  (pos x
                       (mycdrn i l)))))




(defthm pos-is-gi
   (implies (and (consp (collect-updates-from-single-update1 typ ptr i n ram map))
                 (integerp i)
                 (<= 0 i))
            (equal (+ i (pos (nth (gi (car
                                       (collect-updates-from-single-update1
                                        typ ptr i n ram map)))
                                  (cdr (assoc-equal typ map)))
                             (mycdrn i (cdr (assoc-equal typ map)))))
                   (gi (car (collect-updates-from-single-update1
                             typ ptr i n ram map))))))


(defthm nth-pos-mycdrn
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= 0 j))
           (equal (nth i (mycdrn j l))
                  (nth (+ j i) l))))



(defthm nth-pos-is-nth-gi
  (implies (and (consp (collect-updates-from-single-update1 typ ptr i n ram map))
                (integerp i)
                (<= 0 i))
           (equal (nth (pos (nth (gi (car (collect-updates-from-single-update1
                                           typ ptr i n ram map)))
                                 (cdr (assoc-equal typ map)))
                            (mycdrn i (cdr (assoc-equal typ map))))
                       (mycdrn i ptrs))
                  (nth (gi (car (collect-updates-from-single-update1
                                 typ ptr i n ram map)))
                       ptrs))))






(defthm member-x-collect-data-cells-1-aux
  (implies (member x (collect-data-cells-1-aux (mycdrn i typs)
                                               (mycdrn i ptrs)
                                               n
                                               ram map 'LIST))
           (member x (collect-data-cells-1-aux typs ptrs n ram map
                                               'LIST))))



(defthm first-update-is-in-data-cells-colllect-lemma
   (implies (and (consp (collect-updates-from-single-update1 TYP PTR I N RAM MAP))
                 (<= 0 i)
                 (integerp i))
            (member
             (nth (gi (car (collect-updates-from-single-update1
                            typ ptr i n ram map))) ptrs)
             (collect-data-cells-1-aux
                              (cdr (assoc-equal typ map))
                              ptrs
                              (- n 1)
                              ram map 'LIST)))
   :hints (("Goal" :in-theory (disable  not-assoc-equal-must-be-in-collect-data-cell-list)
            :use ((:instance
                          not-assoc-equal-must-be-in-collect-data-cell-list
                          (typx (nth (gi (car (collect-updates-from-single-update1
                                               typ ptr i n ram map)))
                                     (cdr (assoc-equal typ map))))
                          (typs (mycdrn i (cdr (assoc-equal typ map))))
                          (ptrs (mycdrn i ptrs))
                          (n  (- n 1))))
            :do-not-induct t)))


(defun nth-i-seq-int-induct (i addr l)
  (if (zp i)
      (list i addr l)
    (if (zp l)
       (list i addr l)
      (nth-i-seq-int-induct (- i 1)
                            (+ addr 1)
                            (- l 1)))))


(defthm seq-int-1-equal
  (equal (seq-int x 1)
         (list (+ 0 x)))
  :hints (("Goal" :expand (seq-int x 1))))


(defthm  nth-i-seq-int
  (implies (and (<= 0 i)
                (< i  l)
                (integerp l)
                (integerp i))
           (equal (nth i (seq-int addr l))
                  (+ addr i)))
  :hints (("Goal" :do-not '(generalize)
           :induct (nth-i-seq-int-induct i addr l))))

(defthm gptr-is-g-ptr-car-collect-update-from-single-update1
  (implies (consp (collect-updates-from-single-update1 typ ptr i n ram map))
           (equal (gptr (car (collect-updates-from-single-update1
                              typ ptr i n ram map)))
                  ptr)))


(defthm first-update-is-in-data-cells-colllect
   (implies (and (consp (collect-updates-from-single-update1 TYP PTR I N RAM MAP))
                 (integerp i)
                 (<= 0 i))
            (member
             (update-2-w
              (car (collect-updates-from-single-update1 typ ptr i n ram map)) ram)
             (collect-data-cells-1-aux
                              (cdr (assoc-equal typ map))
                              (seq-int (g ptr ram) (len (cdr (assoc-equal typ
                                                                          map))))
                              (- n 1)
                              ram map 'LIST)))
   :hints (("Goal" :in-theory (disable first-update-is-in-data-cells-colllect-lemma)
            :use ((:instance
                          first-update-is-in-data-cells-colllect-lemma
                          (ptrs (seq-int (g ptr ram)
                                         (len (cdr (assoc-equal typ map))))))
                  (:instance nth-i-seq-int
                             (i (gi (car (collect-updates-from-single-update1
                                          typ ptr i n ram map))))
                             (l (len (cdr (assoc-equal typ map))))))
            :do-not-induct t)))



(in-theory (disable collect-updates-from-single-update1 update-2-w))


(defthm first-update-is-in-data-cells
  (implies (consp (collect-updates-zdynamic-1-aux typs ptrs n ram map mode))
           (member
            (update-2-w
             (car (collect-updates-zdynamic-1-aux typs ptrs n ram map mode)) ram)
            (collect-data-cells-1-aux typs ptrs n ram map mode)))
  :hints (("Goal" :do-not '(generalize))
          ("Subgoal *1/12.1" :cases
           ((consp
             (collect-updates-zdynamic-1-aux
              (CAR TYPS) PTRS1 N RAM MAP 'ATOM))))
          ("Subgoal *1/10.1" :cases
           ((consp
             (collect-updates-zdynamic-1-aux
              (CAR TYPS) PTRS1 N RAM MAP 'ATOM))))
          ("Subgoal *1/5"
           :expand  (COLLECT-UPDATES-ZDYNAMIC-1-AUX TYPS PTRS N RAM MAP 'ATOM)
           :cases ((consp (COLLECT-UPDATES-FROM-SINGLE-UPDATE1 TYPS PTRS 0 N RAM MAP))))
          ("Subgoal *1/4"
           :expand  (COLLECT-UPDATES-ZDYNAMIC-1-AUX TYPS PTRS N RAM MAP 'ATOM)
           :cases ((consp (COLLECT-UPDATES-FROM-SINGLE-UPDATE1 TYPS PTRS 0 N RAM MAP))))))


(defthm member-implies-not-member
  (implies (and (not (overlap a b))
                (member x a))
           (not (member x b))))

(defthm not-overlap-data-link-implies-first-step-does-not-update-link-cell
  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n ram map mode)
                              (collect-link-cells-1-aux typs ptrs n ram map mode)))
                (consp (collect-updates-zdynamic-1-aux typs ptrs n ram map mode)))
           (not (member
                 (update-2-w (car (collect-updates-zdynamic-1-aux typs ptrs n
                                                                 ram map mode)) ram)
                 (collect-link-cells-1-aux typs ptrs n ram map mode)))))


;------------ proved that if data, link doesn't overlap,
;------------ apply updates perserve the consistent state.

(defthm first-update-1-in-collect-data-cell-1
  (implies (consp (collect-updates-dynamic-1 typ ptr n ram map))
           (member (update-2-w
                    (car (collect-updates-dynamic-1 typ ptr n ram map)) ram)
                   (collect-data-cells-1 typ ptr n ram map))))


(defthm not-consp-collect-updates-dynamic-1-mark-1-is-no-op
  (implies (not (consp (collect-updates-dynamic-1 typ ptr n ram map)))
           (equal (mark-1 typ ptr n ram map)
                  ram)))

(defthm all-collect-updates-dynamic-1-opener
  (implies (consp typs)
           (equal (all-collect-updates-dynamic-1 typs ptrs ns ram map)
                  (append (collect-updates-dynamic-1
                           (car typs) (car ptrs) (car ns) ram map)
                          (all-collect-updates-dynamic-1 (cdr typs) (cdr ptrs)
                                                         (cdr ns)
                                                         (mark-1 (car typs)
                                                                 (car ptrs)
                                                                 (car ns)
                                                                 ram map)
                                                         map))))
  :hints (("Goal" :in-theory (disable collect-updates-dynamic-1 mark-1))))

(in-theory (disable all-collect-updates-dynamic-1-opener))

(defthm first-update-1-in-all-collect-data-cell-1
  (implies (consp (all-collect-updates-dynamic-1 typs ptrs ns ram map))
           (member (update-2-w
                    (car (all-collect-updates-dynamic-1 typs ptrs ns ram map)) ram)
                   (all-collect-data-cells-1 typs ptrs ns ram map)))
  :hints (("Goal" :in-theory (cons 'all-collect-updates-dynamic-1-opener
                                   (disable collect-updates-dynamic-1
                                            update-2-w mark-1
                                            collect-data-cells-1))
           :do-not '(generalize))
          ("Subgoal *1/3" :cases ((consp (collect-updates-dynamic-1
                                          (car typs) (car ptrs) (car ns) ram
                                          map))))
          ("Subgoal *1/2" :cases ((consp (collect-updates-dynamic-1
                                          (car typs) (car ptrs) (car ns) ram
                                          map))))))


(defthm first-update-in-collect-data-cell
  (implies (consp (collect-updates-dynamic rc))
           (member (update-2-w
                    (car (collect-updates-dynamic rc)) (ram rc))
                   (collect-data-cells rc))))

;----------------

(defthm first-update-not-in-collect-link-cell
  (implies (and (consp (collect-updates-dynamic rc))
                (not (overlap (collect-data-cells rc)
                              (collect-link-cells rc))))
           (not (member (update-2-w
                         (car (collect-updates-dynamic rc)) (ram rc))
                        (collect-link-cells rc)))))


;------------------

(defthm struct-equiv-preserved-if-update-non-link-cell
  (implies (not (member addr (collect-link-cells rc)))
           (struct-equiv (set-ram (s addr v (ram rc)) rc)
                         rc)))

(defthm struct-equiv-preserved-if-apply-update-non-link-cell
  (implies (not (member (update-2-w update (ram rc))
                        (collect-link-cells rc)))
           (struct-equiv (set-ram (apply-update update (ram rc) (getmap rc))
                                  rc)
                         rc))
  :hints (("Goal" :in-theory (list* 'apply-update
                                    'update-2-w
                                   (disable struct-equiv
                                      collect-link-cells)))))



;;
;; this can't be proved, easily.
;;

;
;(defthm struct-equiv-apply-updates
;  (implies (not (overlap (collect-data-cells rc)
;                         (collect-link-cells rc)))
;           (struct-equiv
;            (apply-updates (collect-updates-dynamic rc)
;                           (ram rc) (getmap rc))
;            rc))
;  :hints (("Goal" :in-theory (disable collect-updates-dynamic
;                                      collect-link-cells
;                                      collect-data-cells
;                                      struct-equiv))))
;


;;
;; because, we can't prove a (defcong equal collect-update-dynamic ...)
;; unless we know no-overlap
;;

;; we set out to prove
;
; (defthm not-overlap-and-collect-dynamic-is-collect-static
;  (implies (not (overlap (collect-data-cells rc)
;                         (collect-link-cells rc)))
;           (equal (collect-update-dynamic rc)
;                  (collect-update-static  rc))))
;

(defun collect-updates-from-single-update1-static (typ ptr i n ram map)
  (declare (xargs :measure (m-collect-updates typ map i ram)))
  (let* ((descriptor (cdr (assoc-equal typ map)))
         (i (nfix i))
         (slot-typ (nth i descriptor)))
    (if (zp ptr) nil
      (if (< i (len  descriptor))
          (if (assoc-equal slot-typ map)
              ;; a struct type, meaning a ptr in the (car addrs)
              ;; don't touch link cells
              (collect-updates-from-single-update1-static typ ptr (+ i 1) n ram map)
            ;; else not a struct type, update the value
            ;; let the new value depends on the changes to the previous slos
            (cons (make-update typ ptr i n)
                  (collect-updates-from-single-update1-static
                   typ ptr (+ i 1) n ram map)))
        nil))))

(defun collect-updates-static-1-aux (typ-or-typs ptr-or-ptrs n ram map mode)
  (declare (xargs :measure (struct-equiv-1-aux-m typ-or-typs n mode)))
  (let ((typ typ-or-typs)
        (ptr ptr-or-ptrs)
        (typs typ-or-typs)
        (ptrs ptr-or-ptrs))
    (cond ((equal mode 'ATOM)
           (let* ((desc (cdr (assoc-equal typ map)))
                  (size (len desc)))
             (if (zp n) nil
               (if (zp ptr) nil
                 (if (not (assoc-equal typ map)) ;; not bound
                     nil
                   (let* ((addr (g ptr ram)))
                     (append (collect-updates-from-single-update1-static
                              typ ptr 0 n ram map)
                             (collect-updates-static-1-aux
                              desc
                              (seq-int addr size)
                              (- n 1)
                              ram map 'LIST))))))))
          ((equal mode 'LIST)
           (if (endp typs)
               nil
             (if (not (assoc-equal (car typs)  map))
                 (collect-updates-static-1-aux
                     (cdr typs) (cdr ptrs) n ram map 'LIST)
               (append (collect-updates-static-1-aux
                        (car typs) (car ptrs) n ram map 'ATOM)
                       (collect-updates-static-1-aux (cdr typs)
                                                     (cdr ptrs)
                                                     n
                                                     ram map 'LIST)))))
          (t nil))))


;--------------------
(defthm collect-updates-from-single-update1-static-is-independent-of-ram
  (equal (collect-updates-from-single-update1-static
          typ ptr i n AnyRam map)
         (collect-updates-from-single-update1-static
          typ ptr i n ram map))
  :hints (("Goal" :do-not '(generalize)))
  :rule-classes nil)



(defthm struct-equiv-1-aux-implies-collect-static-updates-1-aux-equal
  (implies (struct-equiv-1-aux typ-or-typs ptr-or-ptrs n ram1 ram2 map mode)
           (equal (collect-updates-static-1-aux typ-or-typs ptr-or-ptrs n
                                                ram1 map mode)
                   (collect-updates-static-1-aux typ-or-typs ptr-or-ptrs n
                                                ram2 map mode)))
  :hints (("Subgoal *1/6"
           :use ((:instance
                  collect-updates-from-single-update1-static-is-independent-of-ram
                  (i 0) (typ typ-or-typs) (ptr ptr-or-ptrs) (anyRam ram1) (ram ram2))))))

;; i need a strong theorem that establish equal after an update to the non-link
;; cell


(defthm not-change-link-collect-updates-from-single-update1-static-not-changed
  (equal (collect-updates-from-single-update1-static
          typ ptr i n (s addr v ram) map)
         (collect-updates-from-single-update1-static
          typ ptr i n ram map)))


(defthm not-change-link-cell-collect-update-static-1-aux-not-changed
  (implies (not (member addr (collect-link-cells-1-aux typ-or-typs  ptr-or-ptrs
                                                       n ram map mode)))
           (equal (collect-updates-static-1-aux typ-or-typs ptr-or-ptrs
                                                n (s addr v ram) map mode)
                  (collect-updates-static-1-aux typ-or-typs ptr-or-ptrs
                                                n ram map mode)))
  :hints (("Goal" :in-theory (disable
                              collect-updates-from-single-update1-static))))

;--------------------
;; ready to prove the most important theorem
;; collect-dynamic is  collect-static
;; when data cell and link cell doesn't overlap


(defun not-change-induct (typ ptr i n AnyRam ram map)
  (declare (xargs :measure (m-collect-updates typ map i ram)))
  (let* ((descriptor (cdr (assoc-equal typ map)))
         (i (nfix i))
         (slot-typ (nth i descriptor))
         (addr (g ptr AnyRam)))
    (if (zp ptr) (list typ ptr i n anyRam ram map)
      (if (< i (len  descriptor))
          (if (assoc-equal slot-typ map)
              ;; a struct type, meaning a ptr in the (car addrs)
              ;; don't touch link cells
              (not-change-induct  typ ptr (+ i 1) n AnyRam ram map)
            ;; else not a struct type, update the value
            (let ((new-ram  (s (+ addr i) (new-field-value typ ptr i n AnyRam map) AnyRam)))
              ;; let the new value depends on the changes to the previous slos
              (not-change-induct typ ptr (+ i 1)  n new-ram ram map)))
        (list typ ptr i n anyRam ram map)))))



(defthm not-change-link-collect-updates-from-single-update1-is-statick-not-changed
  (equal (collect-updates-from-single-update1
          typ ptr i n AnyRam map)
         (collect-updates-from-single-update1-static
          typ ptr i n ram map))
  :hints (("Goal" :do-not '(generalize)
           :induct (not-change-induct typ ptr i n AnyRam ram map))
          ("Subgoal *1/3" :expand (collect-updates-from-single-update1
                                   typ ptr i n AnyRam map))
          ("Subgoal *1/2" :expand (collect-updates-from-single-update1
                                   typ ptr i n AnyRam map))
          ("Subgoal *1/1" :expand (collect-updates-from-single-update1
                                   typ ptr i n AnyRam map))))

(in-theory (disable collect-updates-from-single-update1
                    collect-updates-from-single-update1-static))


(defthm not-overlap-append
  (implies (not (overlap (append a b)
                         (append c d)))
           (not (overlap a c))))


(defthm not-overlap-append-2
  (implies (not (overlap (append a b)
                         (append c d)))
           (not (overlap b d))))


;------------------

;; We proved the following
;(thm
;  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n ram map mode)
;                              (collect-link-cells-1-aux typs ptrs n ram map mode)))
;                (consp (collect-updates-zdynamic-1-aux typs ptrs n ram map mode)))
;           (not (member
;                 (update-2-w (car (collect-updates-zdynamic-1-aux typs ptrs n
;                                                                 ram map mode)) ram)
;                 (collect-link-cells-1-aux typs ptrs n ram map mode)))))

;--- prove more general theorem using the above

;; 1/4.1

(defthm overlap-lemma
  (implies (overlap a b)
           (overlap a (cons x b))))

;-------------------

;; why the following skip-proofs are true.
;
; because we can show
;
; (apply-updates (collect-updates-static-1-aux ...) gives struct-equiv state
;   by showing applying first update, give you a struct-equiv state
;   and the collect-updates-static-1-aux from that state is not changed.
;   thus apply the second update
;
;
; current approach is to prove if no overlap then, collect-updates-static-1-aux
; is a subset of data links.
;

(defun subset-induct (typ-or-typs ptr-or-ptrs n ram map mode)
  (declare (xargs :measure (struct-equiv-1-aux-m typ-or-typs n mode)))
  (let ((typ typ-or-typs)
        (ptr ptr-or-ptrs)
        (typs typ-or-typs)
        (ptrs ptr-or-ptrs))
    (cond ((equal mode 'ATOM)
           (let* ((desc (cdr (assoc-equal typ map)))
                  (size (len desc)))
             (if (zp n) nil
               (if (zp ptr) nil
                 (if (not (assoc-equal typ map)) ;; not bound
                     nil
                   (let* ((addr (g ptr ram)))
                     (subset-induct
                       desc (seq-int addr size)
                       (- n 1)
                       (apply-updates
                        (collect-updates-from-single-update1-static
                         typ ptr 0 n ram map) ram map)
                       map 'LIST)))))))

          ((equal mode 'LIST)
           (if (endp typs)
               nil
             (if (not (assoc-equal (car typs)  map))
                 (subset-induct  (cdr typs) (cdr ptrs) n ram map 'LIST)
               (list (subset-induct (car typs) (car ptrs) n ram map 'ATOM)
                     (subset-induct (cdr typs) (cdr ptrs)
                                    n (apply-updates
                                       (collect-updates-static-1-aux
                                        (car typs) (car ptrs) n ram map 'ATOM)
                                       ram map)
                                    map 'LIST)))))
          (t (list typs ptrs n ram map mode)))))


(defthm subsetp-cons
  (implies (subsetp x l)
           (subsetp x (cons y l))))


;--------------------------

(defthm  struct-equiv-1-aux-preserved-if-apply-update-non-link-cell
  (implies (not (member (update-2-w update ram)
                        (collect-link-cells-1-aux typs ptrs n ram map mode)))
           (struct-equiv-1-aux
                         typs ptrs n (apply-update update ram map) ram map
                         mode))
  :hints (("Goal" :in-theory (enable apply-update update-2-w))))


(defthm subsetp-update-2-ws
  (implies (and (subsetp (updates-2-ws updates ram map) l)
                (consp updates))
           (member (update-2-w (car updates) ram) l))
  :rule-classes :forward-chaining)

(defthm member-overlap-2
  (implies (and (not (overlap a b))
                (member x a))
           (not (member x b)))
  :rule-classes :forward-chaining)


(defthm subsetp-not-member-link-instance
  (implies (and (not (overlap (collect-data-cells-1-aux
                               typ-or-typs ptr-or-ptrs n ram map mode)
                              (collect-link-cells-1-aux
                               typ-or-typs ptr-or-ptrs n ram map mode)))
                (consp updates)
                (subsetp (updates-2-ws updates ram map)
                         (collect-data-cells-1-aux
                          typ-or-typs ptr-or-ptrs n ram map mode)))
           (not (member (update-2-w (car updates) ram)
                        (collect-link-cells-1-aux
                         typ-or-typs ptr-or-ptrs n ram map mode))))
  :hints (("Goal"  :in-theory (disable collect-data-cells-1-aux
                                       collect-link-cells-1-aux
                                       subsetp overlap))))


(defthm apply-updates-nil-is-not-changed
  (implies (not (consp updates))
           (equal (apply-updates updates ram map) ram)))


(defthm  struct-equiv-1-aux-preserved-if-apply-update-non-link-cell-instance
  (implies (and (not (overlap (collect-data-cells-1-aux
                               typ-or-typs ptr-or-ptrs n ram map mode)
                              (collect-link-cells-1-aux
                               typ-or-typs ptr-or-ptrs n ram map mode)))
                (consp updates)
                (subsetp (updates-2-ws updates ram map)
                         (collect-data-cells-1-aux
                          typ-or-typs ptr-or-ptrs n ram map mode)))
           (struct-equiv-1-aux
                         typ-or-typs ptr-or-ptrs n (apply-update (car updates) ram map) ram map
                         mode))
  :hints (("Goal" :cases ((not (consp updates))))))


(defthm collect-link-cells-1-aux-apply-updates-collect-links-updates-instance
  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n
                                                        ram map mode)
                              (collect-link-cells-1-aux typs ptrs n
                                                        ram map mode)))
                (consp updates)
                (subsetp (updates-2-ws updates ram map)
                         (collect-data-cells-1-aux
                          typs ptrs n ram map mode)))
           (equal (collect-link-cells-1-aux typs ptrs n
                                            (apply-update (car updates) ram
                                                          map)
                                            map
                                            mode)
                  (collect-link-cells-1-aux typs ptrs n
                                            ram map mode)))
  :hints (("Goal" :use ((:instance
                         struct-equiv-1-aux-implies-collect-link-cells-aux-equal
                         (ram1 (apply-update (car updates) ram map))
                         (ram2 ram)
                         (typ-or-typs typs) (ptr-or-ptrs ptrs))))))





(defthm collect-link-cells-1-aux-apply-updates-collect-data-updates-instance
  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n
                                                        ram map mode)
                              (collect-link-cells-1-aux typs ptrs n
                                                        ram map mode)))
                (consp updates)
                (subsetp (updates-2-ws updates ram map)
                         (collect-data-cells-1-aux
                          typs ptrs n ram map mode)))
           (equal (collect-data-cells-1-aux typs ptrs n
                                            (apply-update (car updates) ram
                                                          map)
                                            map
                                            mode)
                  (collect-data-cells-1-aux typs ptrs n
                                            ram map mode)))
  :hints (("Goal" :use ((:instance
                         struct-equiv-1-aux-implies-collect-data-cells-aux-equal
                         (ram1 (apply-update (car updates) ram map))
                         (ram2 ram)
                         (typ-or-typs typs) (ptr-or-ptrs ptrs))))))



(defthm apply-updates-struct-equiv-1-aux
  (implies (and (not (overlap (collect-data-cells-1-aux typ-or-typs ptr-or-ptrs n ram map mode)
                              (collect-link-cells-1-aux typ-or-typs ptr-or-ptrs n ram map mode)))
                (consp updates)
                (subsetp (updates-2-ws updates ram map)
                         (collect-data-cells-1-aux
                          typ-or-typs ptr-or-ptrs n ram map mode)))
           (struct-equiv-1-aux
            typ-or-typs ptr-or-ptrs n
            (apply-updates updates ram map)
            ram map
            mode))
  :hints (("Goal" :do-not '(generalize))))


; shared

;-------------------------

(defthm subsetp-collect-data-cells-1-collect-data-cells-1
  (implies (consp typs)
           (subsetp (collect-data-cells-1-aux
                     (car typs) (car ptrs) n ram map 'ATOM)
                    (collect-data-cells-1-aux
                     typs ptrs n ram map 'LIST))))


(defthm apply-updates-struct-equiv-1-aux-instance
  (implies (and (not (overlap (collect-data-cells-1-aux
                               typs ptrs n ram map 'LIST)
                              (collect-link-cells-1-aux
                               typs ptrs n ram map 'LIST)))
                (consp updates)
                (subsetp (updates-2-ws updates ram map)
                         (collect-data-cells-1-aux
                          (car typs) (car ptrs) n ram map 'ATOM)))
           (struct-equiv-1-aux
            typs ptrs n
            (apply-updates updates ram map)
            ram map
            'LIST)))

(defthm apply-updates-struct-equiv-1-aux-instance-1-instance
  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n ram map 'LIST)
                              (collect-link-cells-1-aux typs ptrs n ram map
                                                        'LIST)))
                (not (endp typs))
                (assoc-equal (car typs) map)
                (subsetp (updates-2-ws updates ram map)
                         (collect-data-cells-1-aux
                          (car typs) (car ptrs) n ram map 'ATOM)))
           (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates updates
                                              ram map)
                               ram map 'LIST))
  :hints (("Goal" :in-theory (disable apply-updates-struct-equiv-1-aux-instance)
           :use apply-updates-struct-equiv-1-aux-instance)))



(defthm struct-equiv-1-aux-implies-collect-data-equal-instance
  (implies (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates (collect-updates-static-1-aux
                                               (car typs) (car ptrs) n ram map
                                               'ATOM)
                                              ram map)
                               ram map 'LIST)
           (equal (collect-data-cells-1-aux
                   (cdr typs) (cdr ptrs) n
                   (apply-updates (collect-updates-static-1-aux
                                   (car typs) (car ptrs) n ram map
                                   'ATOM) ram map) map 'LIST)
                  (collect-data-cells-1-aux
                   (cdr typs) (cdr ptrs) n ram map 'LIST))))


(defthm struct-equiv-1-aux-implies-collect-link-equal-instance
  (implies (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates (collect-updates-static-1-aux
                                               (car typs) (car ptrs) n ram map
                                               'ATOM)
                                              ram map)
                               ram map 'LIST)
           (equal (collect-link-cells-1-aux
                   (cdr typs) (cdr ptrs) n
                   (apply-updates (collect-updates-static-1-aux
                                   (car typs) (car ptrs) n ram map
                                   'ATOM) ram map) map 'LIST)
                  (collect-link-cells-1-aux
                   (cdr typs) (cdr ptrs) n ram map 'LIST))))


(defthm struct-equiv-1-aux-implies-collect-static-equal-instance
  (implies (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates (collect-updates-static-1-aux
                                               (car typs) (car ptrs) n ram map
                                               'ATOM)
                                              ram map)
                               ram map 'LIST)
           (equal (collect-updates-static-1-aux
                   (cdr typs) (cdr ptrs) n
                   (apply-updates (collect-updates-static-1-aux
                                   (car typs) (car ptrs) n ram map
                                   'ATOM) ram map) map 'LIST)
                  (collect-updates-static-1-aux
                   (cdr typs) (cdr ptrs) n ram map 'LIST))))


;; solved 1-7-2-1

(defthm updates-2-ws-append
  (equal (updates-2-ws (append updates1 updates2)
                                  ram map)
         (append (updates-2-ws updates1 ram map)
                 (updates-2-ws updates2
                               (apply-updates updates1 ram map) map))))


;; solved 1-7-1-1




;; because our induction in collect-data-cells and collect-updates doesn't
;; match well. This proof is complicated.

(defun collect-data-cells-from-single-node (typ ptr i ram map)
  (declare (xargs :measure (m-collect-updates typ map i ram)))
  (let* ((descriptor (cdr (assoc-equal typ map)))
         (i (nfix i))
         (slot-typ (nth i descriptor))
         (addr (g ptr ram)))
    (if (zp ptr) nil
      (if (< i (len  descriptor))
          (if (assoc-equal slot-typ map)
              ;; a struct type, meaning a ptr in the (car addrs)
              ;; don't touch link cells
              (collect-data-cells-from-single-node typ ptr (+ i 1) ram map)
            ;; else not a struct type, update the value
            (cons (+ i addr)
                  (collect-data-cells-from-single-node
                   typ ptr (+ i 1) ram map)))
        nil))))



;; prove a more general one than
;; subsetp-collect-data-cells-from-single-node-collect-data-cells

(defthm nth-i-equal-car-mycdrn-i
  (implies (and (< i (len l))
                (<= 0 i))
           (equal (nth i l)
                  (car (mycdrn i l)))))


(defthm member-collect-data-cells-1-aux
  (implies (and (not (assoc-equal (car (mycdrn i typs)) map))
                (< i (len typs))
                (<= 0 i))
           (member (+ i addr)
                   (collect-data-cells-1-aux
                    (mycdrn i typs)
                    (seq-int  (+ i addr)
                              (len (mycdrn i typs)))
                    n
                    ram map 'LIST))))


(defthm subsetp-collect-data-1-aux-mycdrn
  (implies (and (consp typs)
                (integerp i)
                (<= 0 i))
           (subsetp (collect-data-cells-1-aux
                     (cdr typs)
                     (seq-int (+ 1 addr)
                              (len (cdr typs)))
                     n
                     ram map 'LIST)
                    (collect-data-cells-1-aux
                     typs
                     (seq-int addr
                              (len typs))
                     n
                     ram map 'LIST)))
  :hints (("Goal" :do-not '(generalize))))


(defthm mycdrn-i-cdr
  (equal (mycdrn i (cddr typs))
         (cdr (mycdrn i (cdr typs)))))


(defthm subsetp-collect-data-1-aux-mycdrn-2
  (implies (and (consp typs)
                (integerp i)
                (<= 0 i)
                (assoc-equal (car typs) map))
           (subsetp (collect-data-cells-1-aux
                     (cdr typs)
                     (seq-int (+ 1 addr)
                              (len (cdr typs)))
                     n
                     ram map 'LIST)
                    (collect-data-cells-1-aux
                     typs
                     (cons any
                           (seq-int (+ 1 addr)
                                    (len (cdr typs))))
                     n
                     ram map 'LIST)))
  :hints (("Goal" :do-not '(generalize))))

(defthm subsetp-collect-data-cells-from-single-node-collect-data-cells-lemma
  (implies (and (integerp i)
                (<= 0 i))
           (subsetp (collect-data-cells-from-single-node
                     typ ptr i ram map)
                    (collect-data-cells-1-aux
                     (mycdrn i (cdr (assoc-equal typ map)))
                     (seq-int (+ i (g ptr ram)) (len (mycdrn i (cdr (assoc-equal typ map)))))
                     (- n 1)
                     ram map 'LIST)))
  :hints (("Goal" :do-not '(generalize))))


(defthm seq-int-fix
  (equal (seq-int (fix addr) len)
         (seq-int addr len)))

(defthm subsetp-collect-data-cells-from-single-node-collect-data-cells
  (subsetp (collect-data-cells-from-single-node
            typ ptr 0 ram map)
           (collect-data-cells-1-aux
            (cdr (assoc-equal typ map))
            (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
            (- n 1)
            ram map 'LIST))
  :hints (("Goal"
           :in-theory (disable subsetp-collect-data-cells-from-single-node-collect-data-cells-lemma)
           :use ((:instance
                  subsetp-collect-data-cells-from-single-node-collect-data-cells-lemma
                  (i 0))))))

;-----------
(defun induct-collect-updates (typ ptr i n ram map)
  (declare (xargs :measure (m-collect-updates typ map i ram)))
  (let* ((descriptor (cdr (assoc-equal typ map)))
         (i (nfix i))
         (slot-typ (nth i descriptor))
         (addr (g ptr ram)))
    (if (zp ptr) nil
      (if (< i (len  descriptor))
          (if (assoc-equal slot-typ map)
              ;; a struct type, meaning a ptr in the (car addrs)
              ;; don't touch link cells
              (induct-collect-updates typ ptr (+ i 1) n ram map)
            ;; else not a struct type, update the value
            (let ((new-ram  (s (+ addr i) (new-field-value typ ptr i n ram map) ram)))
              ;; let the new value depends on the changes to the previous slos
              (induct-collect-updates typ ptr (+ i 1) n
                                      new-ram map)))
        nil))))

#|
;; a general statement. easy to prove but not so good.
(defthm collect-data-cells-from-single-node-not-affected-by-lemma
  (implies (equal (g ptr ram2) (g ptr ram1))
           (equal (collect-data-cells-from-single-node
                    typ ptr i ram2 map)
                  (collect-data-cells-from-single-node
                    typ ptr i ram1 map))))
;; free variables. not good. so write a more specific one.
|#


(defthm collect-data-cells-from-single-node-not-affected-by-lemma-2
  (implies (not (equal addr ptr))
           (equal (collect-data-cells-from-single-node
                    typ ptr i (s addr anyValue ram) map)
                  (collect-data-cells-from-single-node
                    typ ptr i ram map))))


(defthm member-not-member-implies-not-equal-f
  (implies (and (not (member x l))
                (member y l))
           (not (equal x y)))
  :rule-classes :forward-chaining)



;; not a very good one.
(defthm collect-data-cells-from-single-node-not-affected-by
  (implies (and (not (member ptr (collect-data-cells-from-single-node
                                  typ ptr i ram map)))
                (member addr (collect-data-cells-from-single-node
                                  typ ptr i ram map)))
           (equal (collect-data-cells-from-single-node
                    typ ptr i (s addr anyValue ram)  map)
                  (collect-data-cells-from-single-node
                    typ ptr i ram map))))

(defthm collect-updates-from-single-update1-static-opener
  (implies (zp ptr)
           (equal (collect-updates-from-single-update1-static
                     typ ptr i n ram map) nil))
  :hints (("Goal" :expand
           (collect-updates-from-single-update1-static
            typ ptr i n ram map))))

(defthm collect-updates-from-single-update1-static-opener-2
  (implies (and (<= (LEN (CDR (ASSOC-EQUAL TYP MAP))) I)
                (integerp i))
           (equal (collect-updates-from-single-update1-static
                     typ ptr i n ram map) nil))
  :hints (("Goal" :expand
           (collect-updates-from-single-update1-static
            typ ptr i n ram map))))
#|
(defthm collect-updates-from-single-update1-static-opener-3
  (implies (zp n)
           (equal (collect-updates-from-single-update1-static
                     typ ptr i n ram map) nil))
  :hints (("Goal" :expand
           (collect-updates-from-single-update1-static
            typ ptr i n ram map))))
|#


(defthm equal-collect-data-cells-from-single-node-equal-updates-2-ws
  (implies (and (not (member ptr (collect-data-cells-from-single-node
                                  typ ptr i ram map)))
                (integerp i)
                (<= 0 i))
           (equal (updates-2-ws (collect-updates-from-single-update1-static
                                 typ ptr i n ram map) ram map)
                  (collect-data-cells-from-single-node
                   typ ptr i ram map)))
  :hints (("Goal" :induct (induct-collect-updates typ ptr i n ram map)
           :in-theory (enable update-2-w make-update apply-update gptr gi gn gtyp)
           :do-not '(generalize fertilize)
           :expand (collect-updates-from-single-update1-static
                     typ ptr i n ram map))))


(defthm not-member-forward-chaining
  (implies (and (subsetp a b)
                (not (member x b)))
           (not (member x a)))
  :rule-classes :forward-chaining)


(defthm subsetp-collect-updates-from-single-update-1-static
  (implies (not (member ptr (collect-data-cells-1-aux
                             (cdr (assoc-equal typ map))
                             (seq-int (g ptr ram) (len (cdr (assoc-equal typ
                                                                         map))))
                             (- n 1) ram map 'LIST)))
           (subsetp (updates-2-ws (collect-updates-from-single-update1-static
                                   typ ptr 0 n ram map) ram map)
                    (collect-data-cells-1-aux
                     (cdr (assoc-equal typ map))
                     (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                     (- n 1)
                     ram map 'LIST)))
  :hints (("Goal" :in-theory (disable subsetp-collect-data-cells-from-single-node-collect-data-cells)
           :use subsetp-collect-data-cells-from-single-node-collect-data-cells)))



(defthm not-overlap-not-member-x
  (implies (not (overlap a (cons x b)))
           (not (member x a)))
  :rule-classes :forward-chaining)


(defthm not-overlap-implies-not-member
  (implies (not (overlap (collect-data-cells-1-aux typ ptr n ram map 'ATOM)
                         (collect-link-cells-1-aux typ ptr n ram map 'ATOM)))
           (not (member ptr (collect-data-cells-1-aux
                               typ ptr n ram map 'ATOM))))
  :hints (("Goal" :expand (collect-link-cells-1-aux typ ptr n ram map 'ATOM)))
  :rule-classes :forward-chaining)


;; I should modify the definition of collect-updates-from-single-update1-static
;; to return nil when n is zero

(defthm subsetp-collect-updates-from-single-update-collect-data-1-aux
  (implies (and (not (overlap (collect-data-cells-1-aux typ ptr n ram map 'ATOM)
                              (collect-link-cells-1-aux typ ptr n ram map
                                                        'ATOM)))
                (not (zp n)))
           (subsetp (updates-2-ws (collect-updates-from-single-update1-static
                                   typ ptr 0 n ram map) ram map)
                    (collect-data-cells-1-aux typ ptr n ram map 'ATOM)))
  :hints (("Goal" :expand (collect-data-cells-1-aux typ ptr n ram map 'ATOM))))


(defthm apply-updates-struct-equiv-1-aux-instance-2
  (implies (not (overlap (collect-data-cells-1-aux
                          typ ptr n ram map 'ATOM)
                         (collect-link-cells-1-aux
                          typ ptr n ram map 'ATOM)))
           (struct-equiv-1-aux
            typ ptr n
            (apply-updates (collect-updates-from-single-update1-static
                                     typ ptr 0 n ram map) ram map)
            ram map
            'ATOM))
  :hints (("Goal" :cases ((not (zp n))))
          ("Subgoal 1" :cases ((consp (collect-updates-from-single-update1-static
                                       typ ptr 0 n ram map))))))



(defthm apply-updates-struct-equiv-1-aux-instance-2-instance
  (implies (and (not (overlap (collect-data-cells-1-aux typ ptr n ram map 'ATOM)
                              (collect-link-cells-1-aux typ ptr n ram map 'ATOM)))
                (assoc-equal typ map)
                (not (zp n))
                (not (zp ptr)))
           (struct-equiv-1-aux
             (cdr (assoc-equal typ map))
             (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
             (- n 1)
             (apply-updates (collect-updates-from-single-update1-static
                             typ ptr 0 n ram map) ram map)
             ram
             map 'LIST))
  :hints (("Goal" :in-theory (disable apply-updates-struct-equiv-1-aux-instance-2)
           :use apply-updates-struct-equiv-1-aux-instance-2)))

;----------------------- concrete instantiations

(defthm struct-equiv-1-aux-implies-collect-data-equal-instance-2
  (implies (struct-equiv-1-aux
             (cdr (assoc-equal typ map))
             (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
             (- n 1)
             (apply-updates (collect-updates-from-single-update1-static
                             typ ptr 0 n ram map) ram map)
             ram
             map 'LIST)
           (equal (collect-data-cells-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                (apply-updates (collect-updates-from-single-update1-static
                                                typ ptr 0 n ram map) ram map)
                                map 'LIST)
                  (collect-data-cells-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                ram map 'LIST))))


(defthm struct-equiv-1-aux-implies-collect-link-equal-instance-2
  (implies (struct-equiv-1-aux
             (cdr (assoc-equal typ map))
             (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
             (- n 1)
             (apply-updates (collect-updates-from-single-update1-static
                             typ ptr 0 n ram map) ram map)
             ram
             map 'LIST)
           (equal (collect-link-cells-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                (apply-updates (collect-updates-from-single-update1-static
                                                typ ptr 0 n ram map) ram map)
                                map 'LIST)
                  (collect-link-cells-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                ram map 'LIST))))



(defthm struct-equiv-1-aux-implies-collect-update-static-equal-instance-2
  (implies (struct-equiv-1-aux
             (cdr (assoc-equal typ map))
             (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
             (- n 1)
             (apply-updates (collect-updates-from-single-update1-static
                             typ ptr 0 n ram map) ram map)
             ram
             map 'LIST)
           (equal (collect-updates-static-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                (apply-updates (collect-updates-from-single-update1-static
                                                typ ptr 0 n ram map) ram map)
                                map 'LIST)
                  (collect-updates-static-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                ram map 'LIST))))




;-------------------------

;; because our induction in collect-data-cells and collect-updates doesn't
;; match well. This proof is complicated.

(defun collect-data-cells-from-single-node (typ ptr i ram map)
  (declare (xargs :measure (m-collect-updates typ map i ram)))
  (let* ((descriptor (cdr (assoc-equal typ map)))
         (i (nfix i))
         (slot-typ (nth i descriptor))
         (addr (g ptr ram)))
    (if (zp ptr) nil
      (if (< i (len  descriptor))
          (if (assoc-equal slot-typ map)
              ;; a struct type, meaning a ptr in the (car addrs)
              ;; don't touch link cells
              (collect-data-cells-from-single-node typ ptr (+ i 1) ram map)
            ;; else not a struct type, update the value
            (cons (+ i addr)
                  (collect-data-cells-from-single-node
                   typ ptr (+ i 1) ram map)))
        nil))))



;; prove a more general one than
;; subsetp-collect-data-cells-from-single-node-collect-data-cells

(defthm nth-i-equal-car-mycdrn-i
  (implies (and (< i (len l))
                (<= 0 i))
           (equal (nth i l)
                  (car (mycdrn i l)))))


(defthm member-collect-data-cells-1-aux
  (implies (and (not (assoc-equal (car (mycdrn i typs)) map))
                (< i (len typs))
                (<= 0 i))
           (member (+ i addr)
                   (collect-data-cells-1-aux
                    (mycdrn i typs)
                    (seq-int  (+ i addr)
                              (len (mycdrn i typs)))
                    n
                    ram map 'LIST))))


(defthm subsetp-collect-data-1-aux-mycdrn
  (implies (and (consp typs)
                (integerp i)
                (<= 0 i))
           (subsetp (collect-data-cells-1-aux
                     (cdr typs)
                     (seq-int (+ 1 addr)
                              (len (cdr typs)))
                     n
                     ram map 'LIST)
                    (collect-data-cells-1-aux
                     typs
                     (seq-int addr
                              (len typs))
                     n
                     ram map 'LIST)))
  :hints (("Goal" :do-not '(generalize))))


(defthm mycdrn-i-cdr
  (equal (mycdrn i (cddr typs))
         (cdr (mycdrn i (cdr typs)))))


(defthm subsetp-collect-data-1-aux-mycdrn-2
  (implies (and (consp typs)
                (integerp i)
                (<= 0 i)
                (assoc-equal (car typs) map))
           (subsetp (collect-data-cells-1-aux
                     (cdr typs)
                     (seq-int (+ 1 addr)
                              (len (cdr typs)))
                     n
                     ram map 'LIST)
                    (collect-data-cells-1-aux
                     typs
                     (cons any
                           (seq-int (+ 1 addr)
                                    (len (cdr typs))))
                     n
                     ram map 'LIST)))
  :hints (("Goal" :do-not '(generalize))))

(defthm subsetp-collect-data-cells-from-single-node-collect-data-cells-lemma
  (implies (and (integerp i)
                (<= 0 i))
           (subsetp (collect-data-cells-from-single-node
                     typ ptr i ram map)
                    (collect-data-cells-1-aux
                     (mycdrn i (cdr (assoc-equal typ map)))
                     (seq-int (+ i (g ptr ram)) (len (mycdrn i (cdr (assoc-equal typ map)))))
                     (- n 1)
                     ram map 'LIST)))
  :hints (("Goal" :do-not '(generalize))))


(defthm seq-int-fix
  (equal (seq-int (fix addr) len)
         (seq-int addr len)))

(defthm subsetp-collect-data-cells-from-single-node-collect-data-cells
  (subsetp (collect-data-cells-from-single-node
            typ ptr 0 ram map)
           (collect-data-cells-1-aux
            (cdr (assoc-equal typ map))
            (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
            (- n 1)
            ram map 'LIST))
  :hints (("Goal"
           :in-theory (disable subsetp-collect-data-cells-from-single-node-collect-data-cells-lemma)
           :use ((:instance
                  subsetp-collect-data-cells-from-single-node-collect-data-cells-lemma
                  (i 0))))))

;-----------
(defun induct-collect-updates (typ ptr i n ram map)
  (declare (xargs :measure (m-collect-updates typ map i ram)))
  (let* ((descriptor (cdr (assoc-equal typ map)))
         (i (nfix i))
         (slot-typ (nth i descriptor))
         (addr (g ptr ram)))
    (if (zp ptr) nil
      (if (< i (len  descriptor))
          (if (assoc-equal slot-typ map)
              ;; a struct type, meaning a ptr in the (car addrs)
              ;; don't touch link cells
              (induct-collect-updates typ ptr (+ i 1) n ram map)
            ;; else not a struct type, update the value
            (let ((new-ram  (s (+ addr i) (new-field-value typ ptr i n ram map) ram)))
              ;; let the new value depends on the changes to the previous slos
              (induct-collect-updates typ ptr (+ i 1) n
                                      new-ram map)))
        nil))))

#|
;; a general statement. easy to prove but not so good.
(defthm collect-data-cells-from-single-node-not-affected-by-lemma
  (implies (equal (g ptr ram2) (g ptr ram1))
           (equal (collect-data-cells-from-single-node
                    typ ptr i ram2 map)
                  (collect-data-cells-from-single-node
                    typ ptr i ram1 map))))
;; free variables. not good. so write a more specific one.
|#


(defthm collect-data-cells-from-single-node-not-affected-by-lemma-2
  (implies (not (equal addr ptr))
           (equal (collect-data-cells-from-single-node
                    typ ptr i (s addr anyValue ram) map)
                  (collect-data-cells-from-single-node
                    typ ptr i ram map))))


(defthm member-not-member-implies-not-equal-f
  (implies (and (not (member x l))
                (member y l))
           (not (equal x y)))
  :rule-classes :forward-chaining)



;; not a very good one.
(defthm collect-data-cells-from-single-node-not-affected-by
  (implies (and (not (member ptr (collect-data-cells-from-single-node
                                  typ ptr i ram map)))
                (member addr (collect-data-cells-from-single-node
                                  typ ptr i ram map)))
           (equal (collect-data-cells-from-single-node
                    typ ptr i (s addr anyValue ram)  map)
                  (collect-data-cells-from-single-node
                    typ ptr i ram map))))

(defthm collect-updates-from-single-update1-static-opener
  (implies (zp ptr)
           (equal (collect-updates-from-single-update1-static
                     typ ptr i n ram map) nil))
  :hints (("Goal" :expand
           (collect-updates-from-single-update1-static
            typ ptr i n ram map))))

(defthm collect-updates-from-single-update1-static-opener-2
  (implies (and (<= (LEN (CDR (ASSOC-EQUAL TYP MAP))) I)
                (integerp i))
           (equal (collect-updates-from-single-update1-static
                     typ ptr i n ram map) nil))
  :hints (("Goal" :expand
           (collect-updates-from-single-update1-static
            typ ptr i n ram map))))



(defthm equal-collect-data-cells-from-single-node-equal-updates-2-ws
  (implies (and (not (member ptr (collect-data-cells-from-single-node
                                  typ ptr i ram map)))
                (integerp i)
                (<= 0 i))
           (equal (updates-2-ws (collect-updates-from-single-update1-static
                                 typ ptr i n ram map) ram map)
                  (collect-data-cells-from-single-node
                   typ ptr i ram map)))
  :hints (("Goal" :induct (induct-collect-updates typ ptr i n ram map)
           :in-theory (enable update-2-w make-update apply-update gptr gi gn gtyp)
           :do-not '(generalize fertilize)
           :expand (collect-updates-from-single-update1-static
                     typ ptr i n ram map))))


(defthm not-member-forward-chaining
  (implies (and (subsetp a b)
                (not (member x b)))
           (not (member x a)))
  :rule-classes :forward-chaining)


(defthm subsetp-collect-updates-from-single-update-1-static
  (implies (not (member ptr (collect-data-cells-1-aux
                             (cdr (assoc-equal typ map))
                             (seq-int (g ptr ram) (len (cdr (assoc-equal typ
                                                                         map))))
                             (- n 1) ram map 'LIST)))
           (subsetp (updates-2-ws (collect-updates-from-single-update1-static
                                   typ ptr 0 n ram map) ram map)
                    (collect-data-cells-1-aux
                     (cdr (assoc-equal typ map))
                     (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                     (- n 1)
                     ram map 'LIST)))
  :hints (("Goal" :in-theory (disable subsetp-collect-data-cells-from-single-node-collect-data-cells)
           :use subsetp-collect-data-cells-from-single-node-collect-data-cells)))



(defthm not-overlap-not-member-x
  (implies (not (overlap a (cons x b)))
           (not (member x a)))
  :rule-classes :forward-chaining)



(defthm subsetp-collect-updates-static-1-aux-data-cells
  (implies (not (overlap (collect-data-cells-1-aux typ-or-typs
                                                   ptr-or-ptrs n ram map mode)
                         (collect-link-cells-1-aux typ-or-typs
                                                   ptr-or-ptrs n ram map mode)))
           (subsetp (updates-2-ws (collect-updates-static-1-aux typ-or-typs
                                                                ptr-or-ptrs
                                                                n ram map mode) ram map)
                    (collect-data-cells-1-aux typ-or-typs ptr-or-ptrs
                                               n ram map mode)))
  :hints (("Goal" :induct (subset-induct
                           typ-or-typs ptr-or-ptrs n ram map mode)
           :do-not '(generalize))))

;; this is important result



;--- this above the important result we want to show ---
(defun prefix (a b)
  (if (endp a) t
    (if (endp b) nil
      (and (equal (car a) (car b))
           (prefix (cdr a) (cdr b))))))

(defthm prefix-subsetp
  (implies (prefix updates2 updates1)
           (subsetp (updates-2-ws updates2 ram map)
                    (updates-2-ws updates1 ram map))))

(defthm prefix-append
  (prefix a (append a b)))

(defthm subsetp-collect-updates-static-1-aux
  (implies (and (not (endp typs))
                (assoc-equal (car typs) map))
           (subsetp (updates-2-ws (collect-updates-static-1-aux
                                   (car typs) (car ptrs) n ram map 'ATOM) ram map)
                    (updates-2-ws (collect-updates-static-1-aux
                                   typs ptrs n ram map 'LIST) ram map))))


(defthm apply-updates-struct-equiv-1-aux-instance-1
  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n ram map 'LIST)
                              (collect-link-cells-1-aux typs ptrs n ram map
                                                        'LIST)))
                (not (endp typs))
                (assoc-equal (car typs) map))
           (struct-equiv-1-aux typs ptrs n
                               (apply-updates (collect-updates-static-1-aux
                                                (car typs) (car ptrs) n ram map
                                                'ATOM)
                                              ram map)
                               ram map 'LIST))
  :hints (("Goal" :do-not '(generalize)
           :cases ((consp (collect-updates-static-1-aux
                           (car typs) (car ptrs) n ram map 'ATOM))))
          ("Subgoal 1" :use ((:instance subsetp-transitive
                                        (a (updates-2-ws
                                            (collect-updates-static-1-aux
                                                (car typs) (car ptrs) n ram map
                                                'ATOM) ram map))
                                        (b (updates-2-ws
                                            (collect-updates-static-1-aux
                                             typs ptrs n ram map 'LIST) ram
                                             map))
                                        (c (collect-data-cells-1-aux
                                            typs ptrs n ram map 'LIST)))))))


;-----------------
;
; need to instantiate it again to get the version I wanted.
;
#|
(defthm apply-updates-struct-equiv-1-aux-instance-1-instance
  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n ram map 'LIST)
                              (collect-link-cells-1-aux typs ptrs n ram map
                                                        'LIST)))
                (not (endp typs))
                (assoc-equal (car typs) map))
           (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates (collect-updates-static-1-aux
                                                (car typs) (car ptrs) n ram map
                                                'ATOM)
                                              ram map)
                               ram map 'LIST))
  :hints (("Goal" :in-theory (disable apply-updates-struct-equiv-1-aux-instance-1)
           :use apply-updates-struct-equiv-1-aux-instance-1)))

;; now I have what I want.

;; instantiate some of struct-equiv-1-aux-implies-collect-XXX-equal

(defthm struct-equiv-1-aux-implies-collect-data-equal-instance
  (implies (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates (collect-updates-static-1-aux
                                               (car typs) (car ptrs) n ram map
                                               'ATOM)
                                              ram map)
                               ram map 'LIST)
           (equal (collect-data-cells-1-aux
                   (cdr typs) (cdr ptrs) n
                   (apply-updates (collect-updates-static-1-aux
                                   (car typs) (car ptrs) n ram map
                                   'ATOM) ram map) map 'LIST)
                  (collect-data-cells-1-aux
                   (cdr typs) (cdr ptrs) n ram map 'LIST))))

(defthm struct-equiv-1-aux-implies-collect-link-equal-instance
  (implies (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates (collect-updates-static-1-aux
                                               (car typs) (car ptrs) n ram map
                                               'ATOM)
                                              ram map)
                               ram map 'LIST)
           (equal (collect-link-cells-1-aux
                   (cdr typs) (cdr ptrs) n
                   (apply-updates (collect-updates-static-1-aux
                                   (car typs) (car ptrs) n ram map
                                   'ATOM) ram map) map 'LIST)
                  (collect-link-cells-1-aux
                   (cdr typs) (cdr ptrs) n ram map 'LIST))))
|#

(defthm struct-equiv-1-aux-implies-collect-update-static-1-aux-equal-instance
  (implies (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates (collect-updates-static-1-aux
                                               (car typs) (car ptrs) n ram map
                                               'ATOM)
                                              ram map)
                               ram map 'LIST)
           (equal (collect-updates-static-1-aux
                   (cdr typs) (cdr ptrs) n
                   (apply-updates (collect-updates-static-1-aux
                                   (car typs) (car ptrs) n ram map
                                   'ATOM) ram map) map 'LIST)
                  (collect-updates-static-1-aux
                   (cdr typs) (cdr ptrs) n ram map 'LIST))))



(defthm mark-1-aux-equal-is-if-dynamic-equal-static
  (implies (equal (collect-updates-zdynamic-1-aux typ ptr n ram map 'ATOM)
                  (collect-updates-static-1-aux  typ ptr n ram map 'ATOM))
           (equal (mark-1-aux typ ptr n ram map 'ATOM)
                  (apply-updates (collect-updates-static-1-aux
                                   typ ptr n ram map 'ATOM) ram map))))

;-------------------------------




(defthm lemma-1-7-2-1
  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n ram map 'list)
                              (collect-link-cells-1-aux typs ptrs n ram map 'list)))
                (equal (collect-updates-zdynamic-1-aux (car typs)
                                                       (car ptrs) n ram map
                                                       'ATOM)
                       (collect-updates-static-1-aux (car typs)
                                                      (car ptrs) n ram map
                                                      'ATOM))
                 (not (endp typs))
                 (assoc-equal (car typs) map))
            (not (overlap (collect-data-cells-1-aux
                           (cdr typs) (cdr ptrs) n
                           (mark-1-aux (car typs) (car ptrs) n ram map 'ATOM)
                           map 'LIST)
                          (collect-link-cells-1-aux
                           (cdr typs) (cdr ptrs) n
                           (mark-1-aux (car typs) (car ptrs) n ram map 'ATOM)
                           map 'LIST))))
  :hints (("Goal" :in-theory (disable apply-updates-collect-dynamic-is-mark))))




;; (in-theory (disable mark-1-aux-equal-is-if-dynamic-equal-static))

#|
(defthm struct-equiv-1-aux-implies-collect-update-static-1-aux-equal-instance
  (implies (struct-equiv-1-aux (cdr typs) (cdr ptrs) n
                               (apply-updates (collect-updates-static-1-aux
                                               (car typs) (car ptrs) n ram map
                                               'ATOM)
                                              ram map)
                               ram map 'LIST)
           (equal (collect-updates-static-1-aux
                   (cdr typs) (cdr ptrs) n
                   (apply-updates (collect-updates-static-1-aux
                                   (car typs) (car ptrs) n ram map
                                   'ATOM) ram map) map 'LIST)
                  (collect-updates-static-1-aux
                   (cdr typs) (cdr ptrs) n ram map 'LIST))))
|#

(defthm lemma-1-7-1-1
  (implies (and (not (overlap (collect-data-cells-1-aux typs ptrs n ram map 'list)
                              (collect-link-cells-1-aux typs ptrs n ram map
                                                        'list)))
                (not (endp typs))
                (assoc-equal (car typs) map)
                (equal (collect-updates-zdynamic-1-aux (car typs)
                                                        (car ptrs) n ram map
                                                        'ATOM)
                         (collect-updates-static-1-aux (car typs)
                                                       (car ptrs) n ram map
                                                       'ATOM))
                  (equal (collect-updates-zdynamic-1-aux (cdr typs)
                                                        (cdr ptrs) n
                                                        (mark-1-aux (car typs)
                                                                    (car ptrs)
                                                                    n
                                                                    ram map
                                                                    'ATOM)
                                                        map 'LIST)
                         (collect-updates-static-1-aux (cdr typs)
                                                       (cdr ptrs) n
                                                       (mark-1-aux (car typs)
                                                                   (car ptrs)
                                                                   n
                                                                   ram map
                                                                   'ATOM)
                                                       map 'LIST)))
                  (equal (collect-updates-zdynamic-1-aux (cdr typs)
                                                        (cdr ptrs) n
                                                        (mark-1-aux (car typs)
                                                                    (car ptrs)
                                                                    n
                                                                    ram map
                                                                    'ATOM)
                                                        map 'LIST)
                         (collect-updates-static-1-aux (cdr typs)
                                                        (cdr ptrs) n
                                                        ram
                                                        map 'LIST)))
  :hints (("Goal" :in-theory (disable
                              apply-updates-collect-dynamic-is-mark))))



;--------------- prove the two lemmas that deal with recursion
;--------------- mode = LIST.

;--------------- mode = ATOM
#|
(skip-proofs
 (defthm subsetp-collect-updates-from-single-update-collect-data-1-aux
   (implies (not (overlap (collect-data-cells-1-aux typ ptr n ram map 'ATOM)
                          (collect-link-cells-1-aux typ ptr n ram map 'ATOM)))
            (subsetp (updates-2-ws (collect-updates-from-single-update1-static
                                     typ ptr 0 n ram map) ram map)
                     (collect-data-cells-1-aux typ ptr n ram map 'ATOM)))))
|#


(defthm subsetp-collect-updates-from-single-update-collect-updates-static-1-aux
  (implies (and (assoc-equal typ map)
                (not (zp n))
                (not (zp ptr)))
           (subsetp (updates-2-ws (collect-updates-from-single-update1-static
                                   typ ptr 0 n ram map) ram map)
                    (updates-2-ws (collect-updates-static-1-aux
                                   typ ptr n ram map 'ATOM) ram map)))
  :hints (("Goal" :expand (collect-updates-static-1-aux typ ptr n ram map
                                                        'ATOM))))

;---------------
#|
(defthm apply-updates-struct-equiv-1-aux-instance-2
  (implies (and (not (overlap (collect-data-cells-1-aux typ ptr n ram map 'ATOM)
                              (collect-link-cells-1-aux typ ptr n ram map 'ATOM)))
                (assoc-equal typ map)
                (not (zp ptr)))
           (struct-equiv-1-aux typ ptr n
                               (apply-updates (collect-updates-from-single-update1-static
                                               typ ptr 0 n ram map)
                                              ram map)
                               ram map 'ATOM))
  :hints (("Goal"
           :cases ((consp (collect-updates-from-single-update1-static
                                               typ ptr 0 n ram map))))
          ("Subgoal 1"
           :use ((:instance subsetp-transitive
                                   (a (updates-2-ws
                                       (collect-updates-from-single-update1-static
                                        typ ptr 0 n ram map) ram map))
                                   (b (updates-2-ws
                                       (collect-updates-static-1-aux
                                        typ ptr n ram map 'ATOM) ram ram))
                                   (c (collect-data-cells-1-aux
                                       typ ptr n ram map 'ATOM)))))))

|#
#|
; instantiate the about again


(defthm apply-updates-struct-equiv-1-aux-instance-2-instance
  (implies (and (not (overlap (collect-data-cells-1-aux typ ptr n ram map 'ATOM)
                              (collect-link-cells-1-aux typ ptr n ram map 'ATOM)))
                (assoc-equal typ map)
                (not (zp n))
                (not (zp ptr)))
           (struct-equiv-1-aux
             (cdr (assoc-equal typ map))
             (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
             (- n 1)
             (apply-updates (collect-updates-from-single-update1-static
                             typ ptr 0 n ram map) ram map)
             ram
             map 'LIST))
  :hints (("Goal" :in-theory (disable apply-updates-struct-equiv-1-aux-instance-2)
           :use apply-updates-struct-equiv-1-aux-instance-2)))

;----------------------- concrete instantiations

(defthm struct-equiv-1-aux-implies-collect-data-equal-instance-2
  (implies (struct-equiv-1-aux
             (cdr (assoc-equal typ map))
             (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
             (- n 1)
             (apply-updates (collect-updates-from-single-update1-static
                             typ ptr 0 n ram map) ram map)
             ram
             map 'LIST)
           (equal (collect-data-cells-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                (apply-updates (collect-updates-from-single-update1-static
                                                typ ptr 0 n ram map) ram map)
                                map 'LIST)
                  (collect-data-cells-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                ram map 'LIST))))


(defthm struct-equiv-1-aux-implies-collect-link-equal-instance-2
  (implies (struct-equiv-1-aux
             (cdr (assoc-equal typ map))
             (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
             (- n 1)
             (apply-updates (collect-updates-from-single-update1-static
                             typ ptr 0 n ram map) ram map)
             ram
             map 'LIST)
           (equal (collect-link-cells-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                (apply-updates (collect-updates-from-single-update1-static
                                                typ ptr 0 n ram map) ram map)
                                map 'LIST)
                  (collect-link-cells-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                ram map 'LIST))))


(defthm struct-equiv-1-aux-implies-collect-update-static-equal-instance-2
  (implies (struct-equiv-1-aux
             (cdr (assoc-equal typ map))
             (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
             (- n 1)
             (apply-updates (collect-updates-from-single-update1-static
                             typ ptr 0 n ram map) ram map)
             ram
             map 'LIST)
           (equal (collect-updates-static-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                (apply-updates (collect-updates-from-single-update1-static
                                                typ ptr 0 n ram map) ram map)
                                map 'LIST)
                  (collect-updates-static-1-aux
                                (cdr (assoc-equal typ map))
                                (seq-int (g ptr ram) (len (cdr (assoc-equal typ map))))
                                (- n 1)
                                ram map 'LIST))))

|#
;---------------------------------------


(defthm collect-updates-zdynamic-1-aux-is-collect-updates-static-1-aux
  (implies (not (overlap (collect-data-cells-1-aux typ-or-typs ptr-or-ptrs
                                                   n ram map mode)
                         (collect-link-cells-1-aux typ-or-typs ptr-or-ptrs
                                                   n ram map mode)))
           (equal (collect-updates-zdynamic-1-aux typ-or-typs ptr-or-ptrs
                                                 n ram map mode)
                  (collect-updates-static-1-aux typ-or-typs ptr-or-ptrs
                                                n ram map mode)))
  :hints (("Goal" :induct (collect-updates-zdynamic-1-aux typ-or-typs
                                                         ptr-or-ptrs
                                                         n ram map mode)
           :in-theory (disable
                       APPLY-UPDATES-COLLECT-DYNAMIC-IS-MARK)
           :do-not '(generalize))))



;------------------ done at last !!! -------
;
; we now have this result and a theorem that
; (updates-2-ws (collect-updates-static-1-aux ..) is a subset of
; (collect-static-data ..)
;


(defthm g-over-apply-update-lemma
  (implies (not (equal addr (update-2-w update ram)))
           (equal (g addr (apply-update update ram map))
                  (g addr ram)))
  :hints (("Goal" :in-theory (enable apply-update
                                     update-2-w
                                     gtyp gptr gi gn))))

(defthm g-over-apply-updates-lemma
  (implies (not (member addr (updates-2-ws updates ram map)))
           (equal (g addr (apply-updates updates ram map))
                  (g addr ram))))


(defthm g-over-mark-1-aux-lemma
  (implies (and (not (overlap (collect-data-cells-1-aux typ-or-typs ptr-or-ptrs
                                                        n ram map mode)
                              (collect-link-cells-1-aux typ-or-typs ptr-or-ptrs
                                                        n ram map mode)))
                (not (member addr
                             (updates-2-ws (collect-updates-static-1-aux
                                            typ-or-typs ptr-or-ptrs
                                                        n ram map mode) ram map))))
           (equal (g addr (mark-1-aux typ-or-typs ptr-or-ptrs
                                      n ram map mode))
                  (g addr ram))))



(defthm g-over-mark-1-aux
  (implies (and (not (overlap (collect-data-cells-1-aux typ-or-typs ptr-or-ptrs
                                                        n ram map mode)
                              (collect-link-cells-1-aux typ-or-typs ptr-or-ptrs
                                                        n ram map mode)))
                (not (member addr
                             (collect-data-cells-1-aux typ-or-typs ptr-or-ptrs
                                                       n ram map mode))))
           (equal (g addr (mark-1-aux typ-or-typs ptr-or-ptrs
                                      n ram map mode))
                  (g addr ram)))
  :hints (("Goal" :in-theory (disable subsetp-collect-updates-static-1-aux-data-cells)
           :use subsetp-collect-updates-static-1-aux-data-cells)))


;------------ done! -------------
(defun collect-updates-static-1 (typ ptr n ram map)
  (collect-updates-static-1-aux typ ptr n ram map 'ATOM))


(defun collect-updates-static-1-list (typs ptrs n ram map)
  (collect-updates-static-1-aux typs ptrs n ram map 'LIST))


(defun all-collect-updates-static-1 (typs ptrs ns ram map)
  (if (endp typs)
      nil
    (append (collect-updates-static-1 (car typs) (car ptrs) (car ns) ram map)
            (all-collect-updates-static-1
             (cdr typs) (cdr ptrs) (cdr ns) ram map))))


(defun collect-updates-static (rc)
  (all-collect-updates-static-1 (typ-list (ptrs rc))
                                (addr-list (ptrs rc))
                                (n-list   (ptrs rc))
                                (ram rc)
                                (getmap rc)))




;----------------------------------

; (defthm g-over-mark
;   (implies (and (not (overlap (collect-data-cells rc)
;                               (collect-link-cells rc)))
;                 (not (member addr (updates-2-ws (collect-updates-static rc)))))
;            (equal (g addr (mark rc))
;                   (g addr (ram rc)))))

















