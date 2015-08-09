; A Solution to the Rockwell challenge
; Hanbing Liu (version for submission to ACL2 workshop)
; March 26th, 2003


; Abstract
; Rockwell challenge is about reasoning effectively about updates to dynamic
; data structures in a linear address space.
;
;             Dynamic Datastructures in ACL2: A Challenge
;
;                  David Greve and Matt Wilding
;                          Nov. 2002
; http://hokiepokie.org/docs/festival02.txt
; a local copy is in http://melton.csres.utexas.edu

; The key is to
;   (1) recover the notion of objects being independent entities and
;   (2) reduce update-on-the fly operations to simpler operations that apply a
;       corresponding sequence of updates.

; START OF THE SCRIPT
;
; This file contains the proofs of the concrete problem. 3 properties as
; described below

; We assume that two books have been loaded, part of the ACL2
; distribution:


; 1.  Problem Set Up
; *****************************
; (acl2::set-match-free-error nil) ;
(in-package "ACL2")
(include-book "misc/records" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)

(defun seq-int (start len)
  (if (zp len)
      nil
    (cons start
        (seq-int (1+ start) (1- len)))))

(defun unique (list)
  (if (consp list)
      (and (not (member (car list) (cdr list)))
         (unique (cdr list)))
    t))

;; We introduce two data structures.
;; "A" nodes have 4 words.
;; Words 0 and 3 are scalars and words 1 and 2 are A node pointers.

;; Collect addresses in the first n nodes of an a structure
(defun a-collect (ptr n ram)
  (declare (xargs :measure (nfix n)))

  ;    +---+
  ; 0: |   |
  ;    +---+
  ; 1: | o-+--> a-node
  ;    +---+
  ; 2: | o-+--> a-node
  ;    +---+
  ; 3: |   |
  ;    +---+

  (if (zp n)
      nil
    (if (zp ptr)
      nil
      (append
       (seq-int ptr 4)
       (a-collect (g (+ 1 ptr) ram) (1- n) ram)
       (a-collect (g (+ 2 ptr) ram) (1- n) ram)
       ))))

;; "B" nodes have 3 words.  Word 2 is an integer, words 0 and 1 are
;; B-node pointers.  "0" is a null pointer

;; Collect addresses from the first n nodes of a b structure
(defun b-collect (ptr n ram)
  (declare (xargs :measure (nfix n)))

  ;    +---+
  ; 0: | o-+--> b-node
  ;    +---+
  ; 1: | o-+--> b-node
  ;    +---+
  ; 2: |   |
  ;    +---+

  (if (zp n)
      nil
    (if (zp ptr)
      nil
      (append
       (seq-int ptr 3)
       (b-collect (g ptr ram) (1- n) ram)
       (b-collect (g (+ 1 ptr) ram) (1- n) ram)
       ))))

;; Crawl through at most n nodes in an "a" structure along the second
;; pointer.  Modify word 0 of each node by adding word 2 to it.
(defun a-mark-objects (addr n ram)
  (declare (xargs :measure (nfix n)))
  (if (zp n) ram
    (if (zp addr) ram
      (let ((ram (s addr (+ (g addr ram) (g (+ 2 addr) ram)) ram)))
      (a-mark-objects (g (+ addr 2) ram) (1- n) ram)))))

;; Crawl through at most n nodes in an "b" structure along the pointer
;; in the first field

(defun b-mark-objects (addr n ram)
  (declare (xargs :measure (nfix n)))
  (if (zp n) ram
    (if (zp addr) ram
      (let ((ram (s (+ 2 addr) 0 ram)))
      (b-mark-objects (g addr ram) (1- n) ram)))))


(defun compose-bab (ptr1 n1 ptr2 n2 ptr3 n3 ram)
  (let ((ram (b-mark-objects ptr1 n1 ram)))
    (let ((ram (a-mark-objects ptr2 n2 ram)))
      (let ((ram (b-mark-objects ptr3 n3 ram)))
      ram))))



; 2.  Proof of property I
; *****************************
;
; 2.1 Problem Analysis
; *****************************
; Difficulty:
;   Data structures in linear addressed space.
;   Abtraction at high level language hides many important assumption.
;   (1) Independent entity.
;   (2) Well-formness

(defun make-ram-config (addr n ram)
  (list addr n ram))

(defun addr (rm-config)
  (car rm-config))
(defun n (rm-config)
  (cadr rm-config))
(defun ram (rm-config)
  (caddr rm-config))

;; Comment: Introduce RAM-configuration to rephrase the problem in
;; RAM-configuration. The structural equivalence on RCs is used to capture
;; the "shape" of the object at addr being the same.

(defun rc-s (x v rc)
  (let ((addr (addr rc))
        (n    (n rc))
        (ram  (ram rc)))
    (make-ram-config addr n (s x v ram))))


; Strategy:
;   To prove (g addr (s addrx v mem)) = (g addr mem)
;   The only way we know is to prove
;              addr!=addrx
;
;   Update on the fly is hard. Thus let's reduce it to
;   apply a sequnce of updates.
;
;   If we can prove addr not member of updated cells, then we prove the final
;   result

(defun collect-A-updates-dynamic (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (let* ((rc1 (rc-s addr (+ (g addr ram) (g (+ 2 addr) ram)) rc))
               (ram (ram rc1))
               (addr (addr rc1))
               (n    (n    rc1)))
          (append
           (list addr)
           (collect-A-updates-dynamic (make-ram-config (g (+ 2 addr) ram) (1- n)
                                                       ram))))))))

(defun apply-A-update (addr ram)
  (s addr (+ (g addr ram) (g (+ 2 addr) ram)) ram))


(defun apply-A-updates (seq ram)
  (if (endp seq) ram
    (apply-A-updates (cdr seq) (apply-A-update (car seq) ram))))


(defthm a-mark-objects-alt-definition
  (equal (a-mark-objects addr n ram)
         (apply-a-updates (collect-a-updates-dynamic
                           (make-ram-config addr n ram))
                          ram))
  :rule-classes :definition)

; The above theorem ''a-mark-objects-alt-definition''
; Reduce the a-mark-objects to apply  dynamic



; And we know:
(defun a-updates-w (l)
   (if (endp l) nil
      (cons (car l) (a-updates-w (cdr l)))))

(defthm apply-a-updates-equal
   (implies (not (member x (a-updates-w updates)))
            (equal (g x (apply-a-updates updates ram))
                   (g x ram))))


; Thus to prove the final goal
;
;     (defthm rd-read-over-a-mark-objects
;       (implies
;        (let ((list (a-collect ptr n ram)))
;             (and (not (member addr list))
;                  (unique list)))
;         (equal (g addr (a-mark-objects ptr n ram))
;                (g addr ram)))
;
; We need to show the following: *P1*
;      (implies (not (member addr (a-collect-1 rc)))
;               (not (member addr
;                        (a-updates-w
;                          (collect-a-udpate-dynamic rc)))))
;
; where a-collect-1 is

(defun a-collect-1 (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (append
         (seq-int addr 4)
         (a-collect-1 (make-ram-config (g (+ 1 addr) ram) (1- n) ram))
         (a-collect-1 (make-ram-config (g (+ 2 addr) ram) (1- n) ram)))))))


(defthm a-collect-1-alt-definition
  (equal (a-collect addr n ram)
         (a-collect-1 (make-ram-config addr n ram)))
  :rule-classes :definition)

; However *P1* is not true.
; We can only a similar *P1* style lemma for

(defun collect-a-updates-static (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (append
         (list addr)
         (collect-A-updates-static
          (make-ram-config (g (+ 2 addr) ram) (1- n)
                           ram)))))))




; Now the Major Task is to show
;   (collect-a-updates-dynamic rc) == (collect-A-updates-static rc)
;  under the condition of (uniqueness (a-collect-1 rc))

; We have the observation that "uniqueness" is not the fundamental reason.
; We need to characterize the "shape" of object does not change, in order to
; prove
;   (collect-a-updates-dynamic rc) == (collect-A-updates-static rc)

; Define structural Equivalent.
;
; Basically, if two objects are structural equivalent, they occupied the same
; range of memory and their components are structural equivalent to each other.
;
(defun struct-equiv-A-ram-config1 (addr1 n1 ram1 addr2 n2 ram2)
  (declare (xargs :measure (nfix n1)))
  (and (equal addr1 addr2)
       (equal n1 n2)
       (cond ((zp n1) t)
             ((zp addr1) t)
             (t (and
                 (struct-equiv-A-ram-config1
                  (g (+ addr1 1) ram1)
                  (- n1 1)
                  ram1
                  (g (+ addr2 1) ram2)
                  (- n2 1)
                  ram2)
                 (struct-equiv-A-ram-config1
                  (g (+ addr1 2) ram1)
                  (- n1 1)
                  ram1
                  (g (+ addr2 2) ram2)
                  (- n2 1)
                  ram2))))))

(defun struct-equiv-A-ram-config (rc1 rc2)
  (struct-equiv-A-ram-config1 (addr rc1) (n rc1) (ram rc1)
                              (addr rc2) (n rc2) (ram rc2)))


(defthm struct-equiv-A-ram-config1-reflexive
  (struct-equiv-A-ram-config1 x1 x2 x3 x1 x2 x3))

(defthm struct-equiv-A-ram-config1-symentric
  (iff (struct-equiv-A-ram-config1 x12 x22 x32 x11 x21 x31)
       (struct-equiv-A-ram-config1 x11 x21 x31 x12 x22 x32)))

(defthm struct-equiv-A-ram-config1-transitive
  (implies  (and (struct-equiv-A-ram-config1 x11 x21 x31 x12 x22 x32)
                 (struct-equiv-A-ram-config1 x12 x22 x32 x13 x23 x33))
            (struct-equiv-A-ram-config1 x11 x21 x31 x13 x23 x33)))

(defequiv struct-equiv-A-ram-config)

; For "shape" not change, we need to introduce the concept of link cell and
; data cells. and show structural equivalent state, these two set do not
; change.

(defun A-collect-link-cells-static (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (append (list (+ addr 1)
                      (+ addr 2))
                (A-collect-link-cells-static
                 (make-ram-config (g (+ 1 addr) ram)
                                  (1- n)
                                  ram))
                (A-collect-link-cells-static
                 (make-ram-config (g (+ 2 addr) ram)
                                  (1- n)
                                  ram)))))))

(defthm rc-config-accessor
  (and (equal (addr (make-ram-config addr n ram)) addr)
       (equal (n (make-ram-config addr n ram)) n)
       (equal (ram (make-ram-config addr n ram)) ram)))

(in-theory (disable make-ram-config ram n addr))

(defcong struct-equiv-A-ram-config equal (n rc) 1)
(defcong struct-equiv-A-ram-config equal (addr rc) 1)

(defun cong-induct (rc rc-equiv)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) (list rc rc-equiv)
      (if (zp addr) (list rc rc-equiv)
        (list (cong-induct (make-ram-config (g (+ 1 addr) ram)
                                            (1- n)
                                            ram)
                           (make-ram-config (g (+ 1 (addr rc-equiv)) (ram
                                                                      rc-equiv))
                                            (1- (n rc-equiv))
                                            (ram rc-equiv)))
              (cong-induct (make-ram-config (g (+ 2 addr) ram)
                                            (1- n)
                                            ram)
                           (make-ram-config (g (+ 2 (addr rc-equiv)) (ram
                                                                      rc-equiv))
                                            (1- (n rc-equiv))
                                            (ram rc-equiv))))))))


(defthm member-append-1
  (implies (not (member x a))
           (iff (member x (append a b))
                (member x b))))

(defthm member-append-2
  (implies (not (member x b))
           (iff (member x (append a b))
                (member x a))))

(defthm member-append-3
  (implies (member x b)
           (member x (append a b))))

(defthm member-append-4
  (implies (member x a)
           (member x (append a b))))



(defcong struct-equiv-A-ram-config equal (A-collect-link-cells-static rc) 1
  :hints (("Goal" :induct (cong-induct rc rc-equiv))))

; Now we can state the condition under which the "shape" does not change after
; an update.

(defthm set-non-link-cells-collect-equal
  (implies (not (member x (a-collect-link-cells-static rc)))
           (struct-equiv-A-ram-config (rc-s x v rc) rc))
  :hints (("Goal" :induct (a-collect-link-cells-static rc))))


(defun A-collect-data-cells-static (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (append (list addr
                      (+ addr 3))
                (A-collect-data-cells-static
                 (make-ram-config (g (+ 1 addr) ram)
                                  (1- n)
                                  ram))
                (A-collect-data-cells-static
                 (make-ram-config (g (+ 2 addr) ram)
                                  (1- n)
                                  ram)))))))


(defcong struct-equiv-A-ram-config equal (A-collect-data-cells-static rc) 1
  :hints (("Goal" :induct (cong-induct rc rc-equiv))))


; We can prove
;  under the condition that link cells and data cells do not overlap
;  collect-dynamic == collect-static
;

(defthm addr-member-a-collect-data-cells-static
  (let ((n (n rc))
        (addr (addr rc)))
    (implies (and (not (zp n))
                  (not (zp addr)))
             (member addr (a-collect-data-cells-static rc)))))


(defthm accessor-rc-s
  (and (equal (addr (rc-s x v rc)) (addr rc))
       (equal (n    (rc-s x v rc)) (n    rc))))



(defun overlap (a b)
  (if (endp a) nil
    (or (member (car a) b)
        (overlap (cdr a) b))))


(defthm addr-not-a-member-a-collect-link-cells-static
  (let ((n (n rc))
        (addr (addr rc)))
    (implies (and (not (zp n))
                  (not (zp addr))
                  (not (overlap (a-collect-data-cells-static rc)
                                (a-collect-link-cells-static rc))))
             (not (member addr (a-collect-link-cells-static rc))))))


(defthm struct-equiv-A-ram-config1-implies-struct-equiv-A-ram-config1
  (and (implies (and (struct-equiv-A-ram-config1 addr1 n1 ram1 addr2 n2 ram2)
                     (not (zp n1))
                     (not (zp addr1)))
                (struct-equiv-A-ram-config
                 (make-ram-config (g (+ 2 addr1) ram1) (1- n1) ram1)
                 (make-ram-config (g (+ 2 addr2) ram2) (1- n2) ram2)))
       (implies (and (struct-equiv-A-ram-config1 addr1 n1 ram1 addr2 n2 ram2)
                     (not (zp addr1))
                     (not (zp n1)))
                (struct-equiv-A-ram-config
                 (make-ram-config (g (+ 1 addr1) ram1) (1- n1) ram1)
                 (make-ram-config (g (+ 1 addr2) ram2) (1- n2) ram2)))))

;; Comment: this is saying if structural equivalent, then branches are
;; structural equivalent.

(defthm struct-equiv-A-ram-config-implies-struct-equiv-A-ram-config-1
  (let ((addr1 (addr rc1))
        (n1    (n rc1))
        (ram1  (ram rc1))
        (addr2 (addr rc2))
        (n2    (n rc2))
        (ram2  (ram rc2)))
    (and (implies (and (struct-equiv-A-ram-config rc1 rc2)
                       (not (zp (addr rc1)))
                       (not (zp (n    rc1))))
                  (struct-equiv-A-ram-config
                   (make-ram-config (g (+ 2 addr1) ram1) (1- n1) ram1)
                   (make-ram-config (g (+ 2 addr2) ram2) (1- n2) ram2)))
         (implies (and (struct-equiv-A-ram-config rc1 rc2)
                       (not (zp (addr rc1)))
                       (not (zp (n    rc1))))
                  (struct-equiv-A-ram-config
                   (make-ram-config (g (+ 1 addr1) ram1) (1- n1) ram1)
                   (make-ram-config (g (+ 1 addr2) ram2) (1- n2) ram2))))))

(defthm struct-equiv-A-ram-config-implies-struct-equiv-A-ram-config-1-instance
  (let* ((rc1 (rc-s (addr rc) (+ (g (addr rc) (ram rc))
                                 (g (+ 2 (addr rc)) (ram rc))) rc))
         (rc2 rc)
         (addr1 (addr rc1))
         (n1    (n rc1))
         (ram1  (ram rc1))
         (addr2 (addr rc2))
         (n2    (n rc2))
         (ram2  (ram rc2)))
    (and (implies (and (struct-equiv-A-ram-config rc1 rc2)
                       (not (zp (addr rc1)))
                       (not (zp (n    rc1))))
                  (struct-equiv-A-ram-config
                   (make-ram-config (g (+ 2 addr1) ram1) (1- n1) ram1)
                   (make-ram-config (g (+ 2 addr2) ram2) (1- n2) ram2)))
         (implies (and (struct-equiv-A-ram-config rc1 rc2)
                       (not (zp (addr rc1)))
                       (not (zp (n    rc1))))
                  (struct-equiv-A-ram-config
                   (make-ram-config (g (+ 1 addr1) ram1) (1- n1) ram1)
                   (make-ram-config (g (+ 1 addr2) ram2) (1- n2) ram2))))))

;; Comments: this is bad. that I need to explicitly instantiate the lemma

(defthm struct-equiv-A-ram-config-implies-struct-equiv-A-ram-config-1-instance-2
  (implies (and (not (overlap (a-collect-data-cells-static rc)
                              (a-collect-link-cells-static rc)))
                (not (zp (addr rc)))
                (not (zp (n    rc))))
           (struct-equiv-A-ram-config
            (MAKE-RAM-CONFIG (G (+ 2 (ADDR RC))
                                (RAM (RC-S (ADDR RC)
                                           (+ (G (ADDR RC) (RAM RC))
                                              (G (+ 2 (ADDR RC)) (RAM RC)))
                                           RC)))
                             (+ -1 (N RC))
                             (RAM (RC-S (ADDR RC)
                                        (+ (G (ADDR RC) (RAM RC))
                                           (G (+ 2 (ADDR RC)) (RAM RC)))
                                        RC)))
            (MAKE-RAM-CONFIG (G (+ 2 (ADDR RC))
                                (RAM RC))
                             (+ -1 (N RC))
                             (RAM RC))))
  :hints (("Goal" :in-theory (disable struct-equiv-A-ram-config rc-s)
           :use
           struct-equiv-A-ram-config-implies-struct-equiv-A-ram-config-1-instance)))


(defthm overlap-append-1
  (implies (overlap a b)
           (overlap (append c a) b)))

(defthm overlap-append-2
  (implies (overlap a b)
           (overlap a (append d b))))


(defthm overlap-append-3-cons
  (implies (overlap a b)
           (overlap a (cons x b))))



(defthm not-overlap-not-overlap-branch
  (implies (and (not (overlap (a-collect-data-cells-static rc)
                              (a-collect-link-cells-static rc)))
                (not (zp (n rc)))
                (not (zp (addr rc))))
           (not (overlap (a-collect-data-cells-static
                          (make-ram-config (G (+ 2 (ADDR RC)) (RAM RC))
                                           (+ -1 (N RC))
                                           (RAM RC)))
                         (a-collect-link-cells-static
                          (make-ram-config (G (+ 2 (ADDR RC)) (RAM RC))
                                           (+ -1 (N RC))
                                           (RAM RC))))))
  :hints (("Goal" :do-not '(generalize))))


(defcong struct-equiv-A-ram-config equal (collect-A-updates-static rc) 1
  :hints (("Goal" :induct (cong-induct rc rc-equiv))))


(defthm not-overlap-implies-collect-a-update-dynamic-equal-static
  (implies (not (overlap (a-collect-data-cells-static rc)
                         (a-collect-link-cells-static rc)))
           (equal (collect-a-updates-dynamic rc)
                  (collect-a-updates-static rc)))
  :hints (("Goal" :induct (collect-a-updates-dynamic rc)
           :do-not '(generalize)
           :in-theory (disable rc-s struct-equiv-A-ram-config))))

; After we proved the above
;           (equal (collect-a-updates-dynamic rc)
;                  (collect-a-updates-static rc))
;
; We need to show (unique (a-collect-1 rc) implies not overlap link + data



; But let us prove the following fact before we move on to show UNIQUE implies NOT OVERLAP
; That is a *P1* style property for collect-a-updates-static
(defthm inrange-seen
  (implies (and (not (zp l))
                (integerp x)
                (integerp y)
                (integerp l)
                (<  y (+ x l))
                (<= x y))
           (member y (seq-int x l)))
  :hints (("Goal" :do-not '(generalize))))

(defthm mem-collect-a-updates-static-mem-a-collect-1
  (implies (member x (a-updates-w (collect-a-updates-static rc)))
           (member x (a-collect-1 rc)))
  :rule-classes ((:rewrite :corollary
                           (implies (not (member x (a-collect-1 rc)))
                                    (not (member x (a-updates-w (collect-a-updates-static rc))))))))

; and this fact

(defthm not-overlap-g-a-mark
  (let ((rc (make-ram-config addr n ram)))
    (implies (and (not (overlap (a-collect-data-cells-static rc)
                                (a-collect-link-cells-static rc)))
                  (not (member x (a-updates-w (collect-a-updates-static rc)))))
             (equal (g x (a-mark-objects addr n ram))
                    (g x ram)))))


; TO SHOW UNIQUE implies not overlap
(defthm seq-int-1-equal
    (equal (seq-int x 1)
           (list x))
    :hints (("Goal" :expand (seq-int x 1))))


#| ;; just to show as not closely related  result.
(defthm mem-a-collect-mem-link-or-data
  (implies (and (member x (a-collect-1 rc))
                (not (member x (a-collect-data-cells-static rc))))
           (member x (a-collect-link-cells-static rc))))
; either be link or data, possibly being both
|#

(defthm subset-append-1
  (implies (and (subsetp a b)
                (subsetp c b))
           (subsetp (append a c) b)))

(defthm subset-append-2
  (implies (subsetp a b)
           (subsetp a (append c b))))

(defthm subset-append-3
  (implies (and (subsetp a b)
                (subsetp c d))
           (subsetp (append a c)
                    (append b d))))

(defthm subsetp-link-all
  (subsetp (a-collect-link-cells-static rc)
           (a-collect-1 rc)))


(defthm subsetp-data-all
  (subsetp (a-collect-data-cells-static rc)
           (a-collect-1 rc)))


(defthm member-subsetp
  (implies (and (member x a)
                (subsetp a b))
           (member x b)))

(defthm shared-member-not-unique
  (implies (and (member x a)
                (member x b))
           (not (unique (append a b)))))

(defthm mem-link-mem-all
  (implies (member x (a-collect-link-cells-static rc))
           (member x (a-collect-1 rc)))
  :rule-classes :forward-chaining)

(defthm mem-data-mem-all
  (implies (member x (a-collect-data-cells-static rc))
           (member x (a-collect-1 rc)))
  :rule-classes :forward-chaining)



(defthm member-link-data-not-unique-lemma
  (implies (and (member x (a-collect-data-cells-static rc1))
                (member x (a-collect-link-cells-static rc2)))
           (not (unique (append (a-collect-1 rc1)
                                (a-collect-1 rc2))))))


(defthm not-unique-append
  (implies (not (unique a))
           (not (unique (append a b)))))

(defthm not-unique-append-2
  (implies (not (unique b))
           (not (unique (append a b)))))

(defthm member-link-data-not-unique
  (implies (and (member x (a-collect-data-cells-static rc))
                (member x (a-collect-link-cells-static rc)))
           (not (unique (a-collect-1 rc)))))


(defun overlap-witness (a b)
  (if (endp a)
      nil
    (if (member (car a) b)
        (car a)
      (overlap-witness (cdr a) b))))

(defthm overlap-witness-mem-a
  (implies (overlap a b)
           (member (overlap-witness a b) a))
  :rule-classes :forward-chaining)

(defthm overlap-witness-mem-b
  (implies (overlap a b)
           (member (overlap-witness a b) b))
  :rule-classes :forward-chaining)


(defthm unique-implies-no-overlap
  (implies (overlap (a-collect-data-cells-static rc)
                    (a-collect-link-cells-static rc))
           (not (unique (a-collect-1 rc))))
  :hints (("Goal" :do-not '(generalize)))
  :rule-classes ((:rewrite :corollary
                           (implies (unique (a-collect-1 rc))
                                    (not (overlap (a-collect-data-cells-static rc)
                                                  (a-collect-link-cells-static rc)))))))
;; Finally w proved
;;  (implies (overlap (a-collect-data-cells-static rc)
;;                    (a-collect-link-cells-static rc))
;;           (not (unique (a-collect-1 rc))))

(defthm a-collect-unique-implies-not-changed
    (implies (and (unique (a-collect addr n ram))
                  (not (member x (a-collect addr n ram))))
             (equal (g x (a-mark-objects addr n ram))
                    (g x ram))))


;----------------------------------------------------
; Finally we have the first proof for A

; Very similar for B data structure. Comment skipped

(defun collect-B-updates-dynamic (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (let* ((rc1 (rc-s (+ 2 addr) 0  rc))
               (ram (ram rc1))
               (addr (addr rc1))
               (n    (n    rc1)))
          (append
           (list addr)
           (collect-B-updates-dynamic (make-ram-config (g addr ram) (1- n)
                                                       ram))))))))

(defun apply-B-update (addr ram)
  (s (+ 2 addr) 0 ram))

(defun apply-B-updates (seq ram)
  (if (endp seq) ram
    (apply-B-updates (cdr seq) (apply-B-update (car seq) ram))))


(defthm B-mark-object-alt-definition
  (equal (B-mark-objects addr n ram)
         (apply-B-updates (collect-B-updates-dynamic
                           (make-ram-config addr n ram)) ram))
  :rule-classes :definition)


(defun collect-B-updates-static (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (append
         (list addr)
         (collect-B-updates-static (make-ram-config (g addr ram) (1- n)
                                                    ram)))))))



(defun struct-equiv-B-ram-config1 (addr1 n1 ram1 addr2 n2 ram2)
  (declare (xargs :measure (nfix n1)))
  (and (equal addr1 addr2)
       (equal n1 n2)
  (cond ((zp n1) t)
        ((zp addr1) t)
        (t (and
            (struct-equiv-B-ram-config1
             (g addr1 ram1)
             (- n1 1)
             ram1
             (g addr2 ram2)
             (- n2 1)
             ram2)
            (struct-equiv-B-ram-config1
             (g (+ addr1 1) ram1)
             (- n1 1)
             ram1
             (g (+ addr2 1) ram2)
             (- n2 1)
             ram2))))))

(defun struct-equiv-B-ram-config (rc1 rc2)
  (struct-equiv-B-ram-config1 (addr rc1) (n rc1) (ram rc1)
                              (addr rc2) (n rc2) (ram rc2)))


(defthm struct-equiv-B-ram-config1-reflexive
  (struct-equiv-B-ram-config1 x1 x2 x3 x1 x2 x3))

(defthm struct-equiv-B-ram-config1-symentric
  (iff (struct-equiv-B-ram-config1 x12 x22 x32 x11 x21 x31)
       (struct-equiv-B-ram-config1 x11 x21 x31 x12 x22 x32)))

(defthm struct-equiv-B-ram-config1-transitive
  (implies  (and (struct-equiv-B-ram-config1 x11 x21 x31 x12 x22 x32)
                 (struct-equiv-B-ram-config1 x12 x22 x32 x13 x23 x33))
            (struct-equiv-B-ram-config1 x11 x21 x31 x13 x23 x33)))

(defequiv struct-equiv-B-ram-config)


(defun B-collect-link-cells-static (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (append (list addr
                      (+ addr 1))
                (B-collect-link-cells-static
                 (make-ram-config (g addr ram)
                                  (1- n)
                                  ram))
                (B-collect-link-cells-static
                 (make-ram-config (g (+ 1 addr) ram)
                                  (1- n)
                                  ram)))))))




(defcong struct-equiv-B-ram-config equal (n rc) 1)
(defcong struct-equiv-B-ram-config equal (addr rc) 1)


(defun cong-induct-B (rc rc-equiv)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) (list rc rc-equiv)
      (if (zp addr) (list rc rc-equiv)
        (list (cong-induct-B (make-ram-config (g addr ram)
                                            (1- n)
                                            ram)
                             (make-ram-config (g (addr rc-equiv)
                                                 (ram rc-equiv))
                                            (1- (n rc-equiv))
                                            (ram rc-equiv)))
              (cong-induct-B (make-ram-config (g (+ 1 addr) ram)
                                            (1- n)
                                            ram)
                             (make-ram-config (g (+ 1 (addr rc-equiv)) (ram
                                                                      rc-equiv))
                                            (1- (n rc-equiv))
                                            (ram rc-equiv))))))))

(defcong struct-equiv-B-ram-config equal (B-collect-link-cells-static rc) 1
  :hints (("Goal" :induct (cong-induct-B rc rc-equiv))))



(defthm B-set-non-link-cells-collect-equal
  (implies (not (member x (B-collect-link-cells-static rc)))
           (struct-equiv-B-ram-config (rc-s x v rc) rc))
  :hints (("Goal" :induct (B-collect-link-cells-static rc))))





(defun B-collect-data-cells-static (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (append (list (+ addr 2))
                (B-collect-data-cells-static
                 (make-ram-config (g addr ram)
                                  (1- n)
                                  ram))
                (B-collect-data-cells-static
                 (make-ram-config (g (+ 1 addr) ram)
                                  (1- n)
                                  ram)))))))



(defcong struct-equiv-B-ram-config equal (B-collect-data-cells-static rc) 1
  :hints (("Goal" :induct (cong-induct-B rc rc-equiv))))

;-----------------------------




(defthm addr-member-B-collect-data-cells-static
  (let ((n (n rc))
        (addr (addr rc)))
    (implies (and (not (zp n))
                  (not (zp addr)))
             (member (+ 2 addr) (B-collect-data-cells-static rc)))))

(defthm addr-not-B-member-a-collect-link-cells-static
  (let ((n (n rc))
        (addr (addr rc)))
    (implies (and (not (zp n))
                  (not (zp addr))
                  (not (overlap (b-collect-data-cells-static rc)
                                (b-collect-link-cells-static rc))))
             (not (member (+ 2 addr) (B-collect-link-cells-static rc))))))

(defthm unique-B-collect-1-struct-equiv-B-ram-config
  (implies (and (not (overlap (b-collect-data-cells-static rc)
                              (b-collect-link-cells-static rc)))
                (not (zp (n    rc)))
                (not (zp (addr rc))))
           (struct-equiv-B-ram-config (rc-s (+ 2 (addr rc)) any rc) rc))
  :hints (("Goal" :do-not '(generalize))))




(defthm struct-equiv-B-ram-config1-implies-struct-equiv-B-ram-config1
  (and (implies (and (struct-equiv-B-ram-config1 addr1 n1 ram1 addr2 n2 ram2)
                     (not (zp n1))
                     (not (zp addr1)))
                (struct-equiv-B-ram-config
                 (make-ram-config (g addr1 ram1) (1- n1) ram1)
                 (make-ram-config (g addr2 ram2) (1- n2) ram2)))
       (implies (and (struct-equiv-B-ram-config1 addr1 n1 ram1 addr2 n2 ram2)
                     (not (zp addr1))
                     (not (zp n1)))
                (struct-equiv-B-ram-config
                 (make-ram-config (g (+ 1 addr1) ram1) (1- n1) ram1)
                 (make-ram-config (g (+ 1 addr2) ram2) (1- n2) ram2)))))


(defthm struct-equiv-B-ram-config-implies-struct-equiv-B-ram-config-1
  (let ((addr1 (addr rc1))
        (n1    (n rc1))
        (ram1  (ram rc1))
        (addr2 (addr rc2))
        (n2    (n rc2))
        (ram2  (ram rc2)))
    (and (implies (and (struct-equiv-B-ram-config rc1 rc2)
                       (not (zp (addr rc1)))
                       (not (zp (n    rc1))))
                  (struct-equiv-B-ram-config
                   (make-ram-config (g  addr1 ram1) (1- n1) ram1)
                   (make-ram-config (g  addr2 ram2) (1- n2) ram2)))
         (implies (and (struct-equiv-B-ram-config rc1 rc2)
                       (not (zp (addr rc1)))
                       (not (zp (n    rc1))))
                  (struct-equiv-B-ram-config
                   (make-ram-config (g (+ 1 addr1) ram1) (1- n1) ram1)
                   (make-ram-config (g (+ 1 addr2) ram2) (1- n2) ram2))))))


(defthm struct-equiv-B-ram-config-implies-struct-equiv-B-ram-config-1-instance
  (let* ((rc1 (rc-s (+ 2 (addr rc)) 0 rc))
         (rc2 rc)
        (addr1 (addr rc1))
        (n1    (n rc1))
        (ram1  (ram rc1))
        (addr2 (addr rc2))
        (n2    (n rc2))
        (ram2  (ram rc2)))
    (and (implies (and (struct-equiv-B-ram-config rc1 rc2)
                       (not (zp (addr rc1)))
                       (not (zp (n    rc1))))
                  (struct-equiv-B-ram-config
                   (make-ram-config (g addr1 ram1) (1- n1) ram1)
                   (make-ram-config (g addr2 ram2) (1- n2) ram2)))
         (implies (and (struct-equiv-B-ram-config rc1 rc2)
                       (not (zp (addr rc1)))
                       (not (zp (n    rc1))))
                  (struct-equiv-B-ram-config
                   (make-ram-config (g (+ 1 addr1) ram1) (1- n1) ram1)
                   (make-ram-config (g (+ 1 addr2) ram2) (1- n2) ram2))))))


(defthm struct-equiv-B-ram-config-implies-struct-equiv-B-ram-config-1-instance-2
  (implies (and (not (overlap (b-collect-data-cells-static rc)
                              (b-collect-link-cells-static rc)))
                (not (zp (addr rc)))
                (not (zp (n    rc))))
           (struct-equiv-B-ram-config
            (MAKE-RAM-CONFIG (G (ADDR RC)
                                (RAM (RC-S (+ 2 (addr RC)) 0  RC)))
                             (+ -1 (N RC))
                             (RAM (RC-S (+ 2 (ADDR RC)) 0 RC)))
            (MAKE-RAM-CONFIG (G (ADDR RC)
                                (RAM RC))
                             (+ -1 (N RC))
                             (RAM RC))))
  :hints (("Goal" :in-theory (disable struct-equiv-B-ram-config rc-s)
           :use
           struct-equiv-B-ram-config-implies-struct-equiv-B-ram-config-1-instance)))

;----------------------------------------------------

(defthm overlap-cons
  (iff (overlap c (cons x d))
       (or (member x c)
           (overlap c d))))

(defthm overlap-app-app
  (implies (overlap a b)
           (overlap (append a c) (append b d))))


(defthm not-overlap-not-overlap-branch-B
  (implies (and (not (overlap (b-collect-data-cells-static rc)
                              (b-collect-link-cells-static rc)))
                (not (zp (n rc)))
                (not (zp (addr rc))))
           (not (overlap (b-collect-data-cells-static
                          (make-ram-config (G (ADDR RC) (RAM RC))
                                           (+ -1 (N RC))
                                           (RAM RC)))
                         (b-collect-link-cells-static
                          (make-ram-config (G (ADDR RC) (RAM RC))
                                           (+ -1 (N RC))
                                           (RAM RC))))))
  :hints (("Goal" :do-not '(generalize))))


(defcong struct-equiv-B-ram-config equal (collect-B-updates-static rc) 1
  :hints (("Goal" :induct (cong-induct-B rc rc-equiv))))



(defthm not-overlap-implies-collect-B-update-dynamic-equal-static
  (implies (not (overlap (B-collect-data-cells-static rc)
                         (B-collect-link-cells-static rc)))
           (equal (collect-B-updates-dynamic rc)
                  (collect-B-updates-static rc)))
  :hints (("Goal" :induct (collect-B-updates-dynamic rc)
           :do-not '(generalize)
           :in-theory (disable rc-s struct-equiv-B-ram-config))))


(defun b-updates-w (updates)
  (if (endp updates)
      nil
    (cons (+ 2 (car updates))
          (b-updates-w (cdr updates)))))

(defthm apply-B-updates-equal
  (implies (not (member x (b-updates-w updates)))
           (equal (g x (apply-B-updates updates ram))
                  (g x ram))))


(defthm not-overlap-g-B-mark
  (let ((rc (make-ram-config addr n ram)))
    (implies (and (not (overlap (B-collect-data-cells-static rc)
                                (B-collect-link-cells-static rc)))
                  (not (member x (b-updates-w (collect-B-updates-static rc)))))
             (equal (g x (B-mark-objects addr n ram))
                    (g x ram)))))


;---------------------------------------------------
(defun B-collect-1 (rc)
  (declare (xargs :measure (nfix (n rc))))
  (let ((n (n rc))
        (addr (addr rc))
        (ram  (ram rc)))
    (if (zp n) nil
      (if (zp addr) nil
        (append
         (seq-int addr 3)
         (B-collect-1 (make-ram-config (g addr ram) (1- n) ram))
         (B-collect-1 (make-ram-config (g (+ 1 addr) ram) (1- n) ram)))))))


(defthm B-collect-1-alt-definition
  (equal (B-collect addr n ram)
         (B-collect-1 (make-ram-config addr n ram)))
  :rule-classes :definition)

;----------------------------------------------------

(defthm mem-collect-B-updates-static-mem-B-collect-1
  (implies (member x (b-updates-w (collect-B-updates-static rc)))
           (member x (B-collect-1 rc)))
  :rule-classes ((:rewrite :corollary
                           (implies (not (member x (b-collect-1 rc)))
                                    (not (member x (b-updates-w (collect-b-updates-static rc))))))))

;---------------------------------------------------

(defthm subsetp-link-all-b
  (subsetp (b-collect-link-cells-static rc)
           (b-collect-1 rc)))


(defthm subsetp-data-all-b
  (subsetp (b-collect-data-cells-static rc)
           (b-collect-1 rc)))



(defthm mem-link-mem-all-b
  (implies (member x (b-collect-link-cells-static rc))
           (member x (b-collect-1 rc)))
  :rule-classes :forward-chaining)

(defthm mem-data-mem-all-b
  (implies (member x (b-collect-data-cells-static rc))
           (member x (b-collect-1 rc)))
  :rule-classes :forward-chaining)



(defthm member-link-data-not-unique-lemma-b
  (implies (and (member x (b-collect-data-cells-static rc1))
                (member x (b-collect-link-cells-static rc2)))
           (not (unique (append (b-collect-1 rc1)
                                (b-collect-1 rc2))))))


(defthm member-link-data-not-unique-b
  (implies (and (member x (b-collect-data-cells-static rc))
                (member x (b-collect-link-cells-static rc)))
           (not (unique (b-collect-1 rc)))))


(defthm unique-implies-no-overlap-b
  (implies (overlap (b-collect-data-cells-static rc)
                    (b-collect-link-cells-static rc))
           (not (unique (b-collect-1 rc))))
  :hints (("Goal" :do-not '(generalize)))
  :rule-classes ((:rewrite :corollary
                           (implies (unique (b-collect-1 rc))
                                    (not (overlap (b-collect-data-cells-static rc)
                                                  (b-collect-link-cells-static rc)))))))


(defthm b-collect-unique-implies-not-changed
  (implies (and (unique (b-collect addr n ram))
                (not (member x (b-collect addr n ram))))
           (equal (g x (b-mark-objects addr n ram))
                  (g x ram))))


; 3.  Proof of property II
; *****************************
;
; 3.1 Proof Analysis
; The key point is to prove that update one objects maintain the structural
; equivalent with respect to another object.
;
; Successively reduce composition of X-mark to a composition of apply-X-updates

; 3.2 Proof Scipts

; Similarly introduce
(defun collect-bab-updates-dynamic (addr1 n1 addr2 n2 addr3 n3 ram)
  (let* ((rc1 (make-ram-config addr1 n1 ram))
         (rc2 (make-ram-config addr2 n2 (apply-B-updates
                                         (collect-B-updates-dynamic rc1)
                                         (ram rc1))))
         (rc3 (make-ram-config addr3 n3 (apply-A-updates
                                         (collect-A-updates-dynamic rc2)
                                         (ram rc2)))))
  (list   (collect-B-updates-dynamic rc1)
          (collect-A-updates-dynamic rc2)
          (collect-B-updates-dynamic rc3))))



(defun apply-bab-updates (l ram)
  (apply-B-updates (caddr l)
                   (apply-a-updates (cadr l)
                                    (apply-B-updates (car l) ram))))

(defthm equal-compose-bab-apply-bab
  (equal (compose-bab addr1 n1 addr2 n2 addr3 n3 ram)
         (apply-bab-updates (collect-bab-updates-dynamic
                             addr1 n1 addr2 n2 addr3 n3 ram) ram)))

; Now we need to prove
;
; (defthm unique-equal-collect-dynamic-to-static
;   (implies (unique (append (b-collect-1 (make-ram-config addr1 n1 ram))
;                            (a-collect-1 (make-ram-config addr2 n2 ram))
;                            (b-collect-1 (make-ram-config addr3 n3 ram))))
;            (equal (collect-bab-updates-dynamic addr1 n1 addr2 n2 addr3 n3 ram)
;                   (collect-bab-updates-static  addr1 n1 addr2 n2 addr3 n3 ram)))
;

; The idea is to successively reduce collect-X-updates-dynamic to
; collect-X-updates-static
; We need to show perservation of structural equivalence with respect to one
; object after updates to other objects
;


(defthm make-ram-config-is-struct-equiv-a-ram-config
  (STRUCT-EQUIV-A-RAM-CONFIG (MAKE-RAM-CONFIG (ADDR RC)
                                              (N RC)
                                              (RAM RC))
                             RC))

(defthm make-ram-config-is-struct-equiv-b-ram-config
  (STRUCT-EQUIV-B-RAM-CONFIG (MAKE-RAM-CONFIG (ADDR RC)
                                              (N RC)
                                              (RAM RC))
                             RC))


(defthm struct-equiv-a-ram-config-apply-B-update
  (implies (not (member (+ 2 x) (a-collect-link-cells-static rc)))
           (struct-equiv-a-ram-config
            (make-ram-config (addr rc)
                             (n    rc)
                             (apply-B-update x (ram rc)))
            rc)))

(defun no-overlap-induct-A (l rc)
  (if (endp l)
      (list l rc)
    (no-overlap-induct-A (cdr l)
                         (make-ram-config (addr rc)
                                          (n rc)
                                          (apply-B-update (car l) (ram rc))))))



(defthm no-overlap-implies-A-struct-equiv-lemma
  (implies (not (overlap (b-updates-w l)
                         (a-collect-link-cells-static rc)))
           (struct-equiv-A-ram-config
                   (make-ram-config (addr rc)
                                    (n    rc)
                                    (apply-B-updates l (ram rc)))
                   rc))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable apply-B-update struct-equiv-A-ram-config)
           :induct (no-overlap-induct-A l rc))))

; above is about structure equivalent with respect to A after unrelated B updates
; Similarly for B after A, B after B, (and A after A)


(defthm struct-equiv-B-ram-config-apply-A-update
  (implies (not (member x (B-collect-link-cells-static rc)))
           (struct-equiv-B-ram-config
            (make-ram-config (addr rc)
                             (n    rc)
                             (apply-A-update x (ram rc)))
            rc)))

(defun no-overlap-induct-B (l rc)
  (if (endp l)
      (list l rc)
    (no-overlap-induct-B (cdr l)
                         (make-ram-config (addr rc)
                                          (n rc)
                                          (apply-A-update (car l) (ram rc))))))


(defthm no-overlap-implies-B-struct-equiv-lemma
  (implies (not (overlap (a-updates-w l)
                         (B-collect-link-cells-static rc)))
           (struct-equiv-B-ram-config
                   (make-ram-config (addr rc)
                                    (n    rc)
                                    (apply-A-updates l (ram rc)))
                   rc))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable apply-A-update struct-equiv-B-ram-config)
           :induct (no-overlap-induct-B l rc))))

;----------
; A after A
(defthm struct-equiv-a-ram-config-apply-A-update
  (implies (not (member x (a-collect-link-cells-static rc)))
           (struct-equiv-a-ram-config
            (make-ram-config (addr rc)
                             (n    rc)
                             (apply-A-update x (ram rc)))
            rc)))


(defthm no-overlap-implies-A-struct-equiv-2-lemma
  (implies (not (overlap (a-updates-w l)
                         (a-collect-link-cells-static rc)))
           (struct-equiv-A-ram-config
                   (make-ram-config (addr rc)
                                    (n    rc)
                                    (apply-A-updates l (ram rc)))
                   rc))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable apply-A-update struct-equiv-A-ram-config)
           :induct (no-overlap-induct-B l rc))))


(defthm no-overlap-implies-A-struct-equiv-2
  (implies (not (overlap (a-updates-w l)
                         (a-collect-link-cells-static (make-ram-config addr n ram))))
           (struct-equiv-A-ram-config
                   (make-ram-config addr
                                    n
                                    (apply-A-updates l ram))
                   (make-ram-config addr n ram)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance no-overlap-implies-A-struct-equiv-2-lemma
                            (rc (make-ram-config addr n ram))))
           :in-theory (disable struct-equiv-A-ram-config))))


;---
; B after B

(defthm struct-equiv-B-ram-config-apply-B-update
  (implies (not (member (+ 2 x) (B-collect-link-cells-static rc)))
           (struct-equiv-B-ram-config
            (make-ram-config (addr rc)
                             (n    rc)
                             (apply-B-update x (ram rc)))
            rc)))


(defthm no-overlap-implies-B-struct-equiv-2-lemma
  (implies (not (overlap (b-updates-w l)
                         (B-collect-link-cells-static rc)))
           (struct-equiv-B-ram-config
                   (make-ram-config (addr rc) ;; (addr rc) doesn't match
                                    (n    rc)
                                    (apply-B-updates l (ram rc)))
                   rc))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable apply-B-update struct-equiv-B-ram-config)
           :induct (no-overlap-induct-A l rc))))


; Colloray from the result of property 1
(defthm collect-dynamic-equal-static-A-1
  (implies (unique (a-collect-1 rc1))
           (equal (collect-A-updates-dynamic rc1)
                  (collect-A-updates-static rc1))))


(in-theory (disable struct-equiv-A-ram-config apply-A-update))

(defthm collect-dynamic-equal-static-A-2
  (implies (and (unique (a-collect-1 rc1))
                (struct-equiv-A-ram-config rc2 rc1))
           (equal (collect-A-updates-dynamic rc2)
                  (collect-A-updates-static rc1)))
  :hints (("Goal" :use ((:instance collect-dynamic-equal-static-A-1
                                   (rc1 rc2)))
           :do-not-induct t)))


(defthm collect-dynamic-equal-static-B-1
  (implies (unique  (b-collect-1 rc))
           (equal (collect-B-updates-dynamic rc)
                  (collect-B-updates-static rc))))

(in-theory (disable struct-equiv-B-ram-config apply-B-update))


(defthm collect-dynamic-equal-static-B-2
  (implies (and (unique (b-collect-1 rc1))
                (struct-equiv-B-ram-config rc2 rc1))
           (equal (collect-B-updates-dynamic rc2)
                  (collect-B-updates-static rc1)))
  :hints (("Goal" :use ((:instance collect-dynamic-equal-static-B-1
                                   (rc rc2)))
           :do-not-induct t)))

;----
(defthm unique-append-f-1
  (implies (unique (append a b))
           (unique a))
  :rule-classes :forward-chaining)

(defthm unique-append-f-2
  (implies (unique (append a b))
           (unique b))
  :rule-classes :forward-chaining)

(defthm subset-b-updates-w-all
  (subsetp (b-updates-w (collect-B-updates-static rc))
           (b-collect-1 rc)))


(defthm overlap-subset
  (implies (and (overlap a c)
                (subsetp a b)
                (subsetp c d))
           (overlap b d)))


(defthm unique-implies-no-overlap-B-data-A-link
  (implies (unique (append (b-collect-1 rc2)
                           (a-collect-1 rc1)))
           (not (overlap  (b-updates-w (collect-B-updates-static rc2))
                          (a-collect-link-cells-static rc1))))
  :hints (("Goal" :in-theory (disable
                              overlap-subset
                              a-collect-1 b-collect-1)
           :do-not-induct t
           :use ((:instance overlap-subset
                            (a (b-updates-w
                                (collect-B-updates-static rc2)))
                            (b (b-collect-1 rc2))
                            (c (a-collect-link-cells-static rc1))
                            (d (a-collect-1 rc1))))))
  :rule-classes :forward-chaining)



(defthm collect-dynamic-equal-static-A-2-instance
  (implies (unique (append (b-collect-1 (make-ram-config addr1 n1 ram))
                           (a-collect-1 (make-ram-config addr2 n2 ram))))
           (equal (collect-A-updates-dynamic
                   (make-ram-config addr2 n2
                                    (apply-b-updates (collect-B-updates-static
                                                      (make-ram-config addr1 n1 ram))
                                                     ram)))
                  (collect-A-updates-static
                   (make-ram-config addr2 n2 ram))))
  :hints (("Goal"  :use ((:instance no-overlap-implies-A-struct-equiv-lemma
                                    (l (collect-B-updates-static
                                        (make-ram-config addr1 n1 ram)))
                                    (rc (make-ram-config addr2 n2 ram)))))))

;
; This above is an important step towards,
;            (equal (collect-bab-updates-dynamic addr1 n1 addr2 n2 addr3 n3 ram)
;                   (collect-bab-updates-static  addr1 n1 addr2 n2 addr3 n3 ram)))
;

; next we need to prove
;             (equal (collect-B-updates-dynamic
;                     (make-ram-config addr3 n3
;                                      (apply-A-updates
;                                       (collect-A-updates-static
;                                        (make-ram-config addr2 n2 ram))
;                                       (apply-b-updates
;                                        (collect-B-updates-static
;                                         (make-ram-config addr1 n1 ram)) ram))))
;                    (collect-B-updates-static
;                     (make-ram-config addr3 n3 ram))))
; We prove this by establishing reducing inner most of apply-X-updates to
; structural-equivalence to original state

(defthm unique-implies-no-overlap-B-data-B-link
  (implies (unique (append (B-collect-1 rc1)
                           (B-collect-1 rc2)))
           (not (overlap  (b-updates-w (collect-B-updates-static rc1))
                          (B-collect-link-cells-static rc2))))
  :hints (("Goal" :in-theory (disable
                              overlap-subset
                              a-collect-1 b-collect-1)
           :do-not-induct t
           :use ((:instance overlap-subset
                            (A (b-updates-w
                                (collect-B-updates-static rc1)))
                            (c (B-collect-link-cells-static rc2))
                            (b (B-collect-1 rc1))
                            (d (B-collect-1 rc2))))))
  :rule-classes :forward-chaining)



(defthm collect-dynamic-equal-static-B-3-instance-lemma-1
  (implies (unique (append (b-collect-1 (make-ram-config addr1 n1 ram))
                           (b-collect-1 (make-ram-config addr3 n3 ram))))
           (struct-equiv-B-ram-config
                   (make-ram-config addr3 n3
                                    (apply-b-updates (collect-B-updates-static
                                                      (make-ram-config addr1 n1 ram))
                                                     ram))
                   (make-ram-config addr3 n3 ram)))
  :hints (("Goal"  :use ((:instance no-overlap-implies-B-struct-equiv-2-lemma
                                    (l (collect-B-updates-static
                                        (make-ram-config addr1 n1 ram)))
                                    (rc (make-ram-config addr3 n3 ram))))))
  :rule-classes :forward-chaining)




(defthm subset-a-updates-w-all
  (subsetp (a-updates-w (collect-a-updates-static rc))
           (a-collect-1 rc)))


(defthm unique-implies-no-overlap-A-data-B-link
  (implies (unique (append (a-collect-1 rc1)
                           (b-collect-1 rc2)))
           (not (overlap  (a-updates-w (collect-A-updates-static rc1))
                          (B-collect-link-cells-static rc2))))
  :hints (("Goal" :in-theory (disable
                              overlap-subset
                              a-collect-1 b-collect-1)
           :do-not-induct t
           :use ((:instance overlap-subset
                            (A (a-updates-w
                                (collect-A-updates-static rc1)))
                            (b (a-collect-1 rc1))
                            (c (b-collect-link-cells-static rc2))
                            (d (b-collect-1 rc2))))))
  :rule-classes :forward-chaining)


(defthm collect-dynamic-equal-static-B-3-instance-lemma-2
  (implies (unique (append (a-collect-1 (make-ram-config addr2 n2 ram))
                           (b-collect-1 (make-ram-config addr3 n3 ram))))
           (struct-equiv-B-ram-config
                   (make-ram-config addr3 n3
                                    (apply-a-updates (collect-A-updates-static
                                                      (make-ram-config addr2 n2 ram))
                                                     ram))
                   (make-ram-config addr3 n3 ram)))
  :hints (("Goal"  :use ((:instance no-overlap-implies-B-struct-equiv-lemma
                                    (l (collect-A-updates-static
                                        (make-ram-config addr2 n2 ram)))
                                    (rc (make-ram-config addr3 n3 ram))))))
  :rule-classes :forward-chaining)


(defthm collect-dynamic-equal-static-B-3-instance-lemma-3
  (implies (unique (append (b-collect-1 (make-ram-config addr1 n1 ram))
                           (a-collect-1 (make-ram-config addr2 n2 ram))))
           (struct-equiv-A-ram-config
                   (make-ram-config addr2 n2
                                    (apply-b-updates (collect-B-updates-static
                                                      (make-ram-config addr1 n1 ram))
                                                     ram))
                   (make-ram-config addr2 n2 ram)))
  :hints (("Goal"  :use ((:instance no-overlap-implies-A-struct-equiv-lemma
                                    (l (collect-B-updates-static
                                        (make-ram-config addr1 n1 ram)))
                                    (rc (make-ram-config addr2 n2 ram))))))
  :rule-classes :forward-chaining)



(defthm unique-append
   (implies (unique (append a b c))
            (unique (append a c)))
 :hints (("Goal" :do-not '(generalize)))
 :rule-classes :forward-chaining)

(defthm subsetp-append-x
  (subsetp x (append x l)))

(defthm unique-append-f-3
  (implies (unique (append a b c))
           (unique (append a b)))
  :rule-classes :forward-chaining)

(defcong struct-equiv-B-ram-config equal (b-collect-1 rc) 1
  :hints (("Goal" :induct (cong-induct-B rc rc-equiv)
           :in-theory (enable struct-equiv-B-ram-config))))


(defcong struct-equiv-A-ram-config equal (a-collect-1 rc) 1
  :hints (("Goal" :induct (cong-induct rc rc-equiv)
           :in-theory (enable struct-equiv-A-ram-config))))

(defthm collect-dynamic-equal-static-B-3-instance-lemma
  (implies (unique (append (b-collect-1 (make-ram-config addr1 n1 ram))
                           (a-collect-1 (make-ram-config addr2 n2 ram))
                           (b-collect-1 (make-ram-config addr3 n3 ram))))
            (struct-equiv-B-ram-config
             (make-ram-config addr3 n3
                              (apply-A-updates
                               (collect-A-updates-static
                                (make-ram-config addr2 n2 ram))
                               (apply-b-updates (collect-B-updates-static
                                                 (make-ram-config addr1
                                                                  n1
                                                                  ram)) ram)))
             (make-ram-config addr3 n3 ram)))
  :hints (("Goal" :in-theory (disable
                              collect-dynamic-equal-static-B-3-instance-lemma-2)
           :use ((:instance collect-dynamic-equal-static-B-3-instance-lemma-2
                            (ram  (apply-b-updates (collect-B-updates-static
                                                    (make-ram-config addr1 n1
                                                                     ram)) ram)))))))


;----------------------
(defthm collect-dynamic-equal-static-B-3-instance
   (implies (unique (append (b-collect-1 (make-ram-config addr1 n1 ram))
                            (a-collect-1 (make-ram-config addr2 n2 ram))
                            (b-collect-1 (make-ram-config addr3 n3 ram))))
            (equal (collect-B-updates-dynamic
                    (make-ram-config addr3 n3
                                     (apply-A-updates
                                      (collect-A-updates-static
                                       (make-ram-config addr2 n2 ram))
                                      (apply-b-updates
                                       (collect-B-updates-static
                                        (make-ram-config addr1 n1 ram)) ram))))
                   (collect-B-updates-static
                    (make-ram-config addr3 n3 ram))))
   :hints (("Goal" :use ((:instance collect-dynamic-equal-static-B-2
                                    (rc2
                                     (make-ram-config addr3 n3
                                     (apply-A-updates
                                      (collect-A-updates-static
                                       (make-ram-config addr2 n2 ram))
                                      (apply-b-updates
                                       (collect-B-updates-static
                                        (make-ram-config addr1 n1 ram)) ram))))
                                    (rc1 (make-ram-config addr3 n3 ram))))))
   :rule-classes :forward-chaining)

;------
(defun collect-bab-updates-static (addr1 n1 addr2 n2 addr3 n3 ram)
  (let* ((rc1 (make-ram-config addr1 n1 ram))
         (rc2 (make-ram-config addr2 n2 ram))
         (rc3 (make-ram-config addr3 n3 ram)))
  (list   (collect-B-updates-static rc1)
          (collect-A-updates-static rc2)
          (collect-B-updates-static rc3))))



(defthm unique-equal-collect-dynamic-to-static
  (implies (unique (append (b-collect-1 (make-ram-config addr1 n1 ram))
                           (a-collect-1 (make-ram-config addr2 n2 ram))
                           (b-collect-1 (make-ram-config addr3 n3 ram))))
           (equal (collect-bab-updates-dynamic addr1 n1 addr2 n2 addr3 n3 ram)
                  (collect-bab-updates-static  addr1 n1 addr2 n2 addr3 n3 ram)))
  :hints (("Goal" :in-theory (disable
                              apply-B-updates
                              apply-B-update
                              apply-A-updates
                              apply-A-update
                              struct-equiv-A-ram-config
                              struct-equiv-B-ram-config))))


(defthm not-mem-append-f-1
  (implies (not (member x (append a b)))
           (not (member x a)))
  :rule-classes :forward-chaining)

(defthm not-mem-append-f-2
  (implies (not (member x (append a b)))
           (not (member x b)))
  :rule-classes :forward-chaining)


(defthm read-over-bab
  (implies
   (let ((list (append (b-collect ptr1 n1 ram)
                       (a-collect ptr2 n2 ram)
                       (b-collect ptr3 n3 ram)
                       )))
     (and
      (not (member addr list))
      (unique list)))
   (equal
    (g addr (compose-bab ptr1 n1 ptr2 n2 ptr3 n3 ram))
    (g addr ram))))


; 4.  Proof of property III
; *****************************
;
(in-theory (enable apply-A-update apply-B-update))
(defun a-data-cell-w-r (l)
  (if (endp l) nil
    (append (list (car l) (+ 2 (car l)))
            (a-data-cell-w-r (cdr l)))))

(defun b-data-cell-w-r (l)
  (if (endp l) nil
    (append (list (car l) (+ 2 (car l)))
            (b-data-cell-w-r (cdr l)))))

;; Introduce the concept of cells that will be used.


(defthm g-after-apply-Bs
  (implies (not (member x (b-data-cell-w-r l2)))
           (equal (g x (apply-B-updates l2 ram))
                  (g x ram)))
  :hints (("Goal" :do-not '(generalize))))


(defthm s-after-apply-Bs
  (implies (not (member x (b-data-cell-w-r l2)))
           (equal (s x any (apply-B-updates l2 ram))
                  (apply-B-updates l2 (s x any ram))))
  :hints (("Goal" :do-not '(generalize))))


(defthm apply-A-after-apply-Bs
  (implies (and (not (member a1 (b-data-cell-w-r l2)))
                (not (member (+ 2 a1) (b-data-cell-w-r l2))))
           (equal (apply-A-update  a1 (apply-B-updates l2 ram))
                  (apply-B-updates l2 (apply-A-update a1 ram))))
  :hints (("Goal" :do-not '(generalize))))


(defthm apply-update-ram
  (implies (not (overlap (a-data-cell-w-r l1) (b-data-cell-w-r l2)))
           (equal (apply-B-updates l2 (apply-A-updates l1 ram))
                  (apply-A-updates l1 (apply-B-updates l2 ram))))
  :hints (("Goal" :in-theory (disable apply-A-update)
           :do-not '(generalize))))


(defthm subsetp-a-data-cell-w-r
  (subsetp (a-data-cell-w-r (collect-a-updates-static rc1))
           (a-collect-1 rc1)))

(defthm subsetp-b-data-cell-w-r
  (subsetp (b-data-cell-w-r (collect-b-updates-static rc1))
           (b-collect-1 rc1)))


(defthm unqiue-app-implies-w-r-w-r-no-overlap
  (implies (unique (append (a-collect-1 rc1)
                           (b-collect-1 rc2)))
           (not (overlap (a-data-cell-w-r (collect-A-updates-static rc1))
                         (b-data-cell-w-r (collect-B-updates-static rc2)))))
  :hints (("Goal" :in-theory (disable overlap-subset)
           :use ((:instance overlap-subset
                                   (a (a-data-cell-w-r
                                       (collect-A-updates-static rc1)))
                                   (b (a-collect-1 rc1))
                                   (c (b-data-cell-w-r
                                       (collect-B-updates-static rc2)))
                                   (d (b-collect-1 rc2)))))))


(defthm |Subgoal *1/3'4'|
  (IMPLIES (not (member x (append l2 l1)))
           (equal (UNIQUE (APPEND l1 (CONS x l2)))
                  (unique (append l1 l2))))
  :hints (("Goal" :do-not '(generalize))))

(defthm unique-append-rev
  (implies (unique (append a b))
           (unique (append b a))))


(defthm a-mark-over-b-mark
  (implies
   (let ((list (append (a-collect ptr1 n1 ram)
                       (b-collect ptr2 n2 ram))))
     (unique list))
   (equal
    (a-mark-objects ptr1 n1 (b-mark-objects ptr2 n2 ram))
    (b-mark-objects ptr2 n2 (a-mark-objects ptr1 n1 ram)))))

; 5.  Generalization
; *****************************
; In sol2.lisp
