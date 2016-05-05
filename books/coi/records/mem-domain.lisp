; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "ACL2")

;; What we want to do is export the primary theories here into
;; theories expressed in terms of list::sets.  I think we want to do
;; this via list::2set and set::2list.  Perhaps as early as the
;; first occurrence of rkeys (?)

(include-book "memory")
(include-book "domain")
(include-book "../osets/conversions")
(include-book "../osets/extras")
(include-book "../osets/map")
(include-book "../osets/listsets-base")
(include-book "../bags/basic") ;bzo is this okay - can records depend on bags?

(local (include-book "../util/iff"))

(local (include-book "../osets/set-processor"))

(local (include-book "data-structures/memories/log2" :dir :system))

(local (in-theory (disable SET::IN))) ;for efficiency
(local (in-theory (disable SET::SUBSET)))

(local (in-theory (disable mod floor))) ;bzo make non-local?


;; [Jared] Previously this book did its own (set::quantify-predice (true-listp
;; set)).  But that was incompatible with coi/osets/listsets.lisp because, it
;; turns out, set::quantify-predicate forms can't be redundant due to the use
;; of deftheory forms.  What a pain.  Anyway, moved the quantify-predicate form
;; to coi/osets/listsets-base, leaving only these (unfortunately non-local)
;; disables...

(in-theory (disable SET::ALL<NOT-TRUE-LISTP>))
(in-theory (disable SET::ALL<TRUE-LISTP>))
(in-theory (disable SET::ALL-IN-2-NOT<TRUE-LISTP>))
(in-theory (disable SET::ALL-IN-2<TRUE-LISTP>))




;bzo make a bunch of the stuff in this file local?

;; ((200 . 2) 1 . 3)

;; (defun cons-onto-all (item lst)
;;   (if (endp lst)
;;       nil
;;     (cons (cons item (car lst))
;;           (cons-onto-all item (cdr lst)))))

(include-book "set-domain")

;bzo can we make this a set processor?
(defun cons-onto-all (item set)
  (if (set::empty set)
      (set::emptyset)
    (set::insert (cons item (set::head set))
                 (cons-onto-all item (set::tail set)))))

;bzo do we get this for a set processor?
(defthm cons-onto-all-iff
  (iff (cons-onto-all a set)
       (not (set::empty set))))


;if this didn't take a depth, how would we know to stop if an "element" of the tree happened to be another tree
(defund mem::domain-aux (mem-tree depth)
  (if (zp depth)
      (if mem-tree ;if it's not nil it's an element, so its location will become part of the domain
          (set::insert nil nil)
        nil)
    (if (not (consp mem-tree))
        (if mem-tree ;if it's not nil it's an element, so its location will become part of the domain
            (set::insert nil nil)
          nil)
      (set::union (cons-onto-all '0 (mem::domain-aux (car mem-tree) (+ -1 depth)))
                  (cons-onto-all '1 (mem::domain-aux (cdr mem-tree) (+ -1 depth)))))))


;this bits are in reverse order (least significant bit comes first in the list)
(defun convert-reversed-bit-list-to-integer (bit-list)
  (if (endp bit-list)
      0
    (+ (car bit-list)
       (* 2 (convert-reversed-bit-list-to-integer (cdr bit-list))))))

;; (defmacro def-set-processor (&key (processor-name 'unsupplied)
;;                                   (element-processor 'unsupplied)  ;can this be a term?
;;                                   (predicate 'unsupplied))
;;   `(defun ,processor-name (set) ;can this take more than one arg?
;;      (if (set::empty set)
;;          (set::emptyset)
;;        (if (,predicate (set::head set))
;;            (set::insert (,element-processor (set::head set))
;;                         (,processor-name (set::tail set)))
;;          (,processor-name (set::tail set))))))


;bzo use a set processor?
(defun convert-reversed-bit-lists-to-integers (bit-lists)
  (if (set::empty bit-lists)
      (set::emptyset)
    (set::insert (convert-reversed-bit-list-to-integer (set::head bit-lists))
                 (convert-reversed-bit-lists-to-integers (set::tail bit-lists)))))

(defthm convert-reversed-bit-lists-to-integers-iff
  (iff (convert-reversed-bit-lists-to-integers bit-lists)
       (not (set::empty bit-lists))))

(defthm convert-reversed-bit-lists-to-integers-of-insert
  (equal (convert-reversed-bit-lists-to-integers (set::insert lst lst-of-lsts))
         (set::insert (convert-reversed-bit-list-to-integer lst) (convert-reversed-bit-lists-to-integers lst-of-lsts)))
  :hints (("Goal" :use (:instance
                        (:functional-instance
                         goal-both-better
                         (generic-pred (lambda (a) t))
                         (process (lambda (a) (convert-reversed-bit-list-to-integer a)))
                         (process-set
                          (lambda (x) (convert-reversed-bit-lists-to-integers x))))
                        (a lst)
                        (x lst-of-lsts)

                        ))))

(defun mem::mem-tree-domain (mem-tree depth)
  (convert-reversed-bit-lists-to-integers (mem::domain-aux mem-tree depth)))

(defun natp-less-than-size (n size)
  (declare (xargs :guard t))
  (and (natp n)
       (< n (rfix size))))

(set::quantify-predicate (natp-less-than-size n size))

(in-theory (disable SET::FILTER<NOT-NATP-LESS-THAN-SIZE>))

(defun mem::domain (mem)
  (let* ((mem-tree-part (caar mem))
         (record-part (cdddr mem))
         (depth (caddr mem))
         (size (cadr mem))
         )
    (set::union (SET::FILTER<NATP-LESS-THAN-SIZE> (mem::mem-tree-domain mem-tree-part depth) size)
                ;;Why can't we skip the filter above?  Doesn't mem-tree-domain
                ;;always return nats less than size?  Not necessarily.  There
                ;;may be nats less than 2^depth but greater than size.  We
                ;;have to filter them out.

                (SET::FILTER<not-NATP-LESS-THAN-SIZE> (set::rkeys record-part) size)
                )))

(local (table theory-invariant-table nil nil :clear)) ;grrr

;dup in graph.lisp
;bzo rename
;; (defthm in-2list
;;   (equal (set::in a (list::2set list))
;;          (bag::memberp a list))
;;   :hints (("goal" :in-theory (enable set::2list bag::memberp)
;;            :induct (bag::memberp a list)
;;            )))

(defthm memory-p-means-not-_BAD-MEMORY-P
 (implies (mem::memory-p mem)
          (not (mem::|_BAD-MEMORY-P| mem)))
 :hints (("Goal" :expand ((MEM::|_BAD-MEMORY-P| MEM))
          :in-theory (enable mem::memory-p))))

(defthm _TO-MEM-does-nothing
 (implies (mem::memory-p mem)
          (equal (MEM::|_TO-MEM| mem)
                 mem))
 :hints (("Goal" :in-theory (enable MEM::|_TO-MEM|))))

(encapsulate
 ()
 (local (include-book "data-structures/memories/memory-impl" :dir :system))

 ;;dup
 (defthm mem::_store-memory
   (mem::_memory-p (mem::_store mem::addr mem::elem mem::mem))
   :hints(("Goal" :in-theory (enable mem::_memory-p))))

 (defthm mem::_store-memory-main
   (equal (mem::memory-p (mem::_store mem::addr mem::elem mem::mem))
          (mem::memory-p mem::mem)))

 (defthm mem::_memtree-store-memtree-2
   (mem::_memtree-p (mem::_memtree-store-nil mem::addr mem::mtree mem::depth) mem::depth)
   :hints(("Goal")))

 )

(defthm _FROM-MEM-does-nothing
  (implies (mem::memory-p mem)
           (equal (MEM::|_FROM-MEM| mem)
                  mem))
  :hints (("Goal" :in-theory (enable MEM::|_FROM-MEM|))))

;(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(encapsulate
 ()
; (Matt K., 10/2013: Changed rel8 to rel9.)
 (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

 (defthm _ADDRESS-P-of-floor
   (implies (MEM::|_ADDRESS-P| ADDR DEPTH)
            (MEM::|_ADDRESS-P| (FLOOR ADDR 2)
                  (+ -1 DEPTH)))
   :hints (("Goal" :in-theory (enable MEM::|_ADDRESS-P| EXPT-SPLIT))))

    ;what should we do with 0?
    ;we could also represent 0 with the bit-list nil, but consider (mem::domain (mem::store 0 4 (mem::new 4))) = '(0)
    ;len is the lenght of the bit list.  we need it. consider whether 0 should be '(0) or '(0 0) of '(0 0 0), etc.
 (defun convert-integer-to-reversed-bit-list (n len)
   (if (zp len)
       nil ;the empty bit list
     (cons (mod n 2)
           (convert-integer-to-reversed-bit-list (floor n 2) (+ -1 len)))))

 (defthm mod-by-2-cases
   (implies (and (not (EQUAL 0 (MOD ADDR 2)))
                 (integerp addr))
            (EQUAL (MOD ADDR 2)
                   1))
   :hints (("Goal" :cases ((integerp addr))
            :in-theory (enable mod-by-2))))

 (defthm floor-non-negative-hack
   (implies (<= 0 x)
            (not (< (FLOOR x 2) 0))))

 (defthm floor-hack
   (implies (< ADDR (* 2 (EXPT 2 (+ -1 DEPTH))))
            (< (FLOOR ADDR 2)
               (EXPT 2 (+ -1 DEPTH)))))
    ;proveable in aamp world - maybe provable from super-ihs
 (defthm a-recollapse
   (implies (natp a)
            (EQUAL (+ (MOD A 2) (* 2 (FLOOR A 2)))
                   A))
   :hints (("Goal" :use (:instance mod-fl-2 (x a) (y 2)))))



 )


(defthm cons-onto-all-of-insert
  (equal (cons-onto-all item (set::insert lst lst-of-lsts))
         (set::insert (cons item lst) (cons-onto-all item lst-of-lsts)))
  :hints (("Goal" :use (:instance
                        (:functional-instance
                         goal-both-better
                         (generic-pred (lambda (a) t))
                         (process (lambda (a) (cons item a)))
                         (process-set
                          (lambda (x) (cons-onto-all item x))))
                        (a lst)
                        (x lst-of-lsts)

                        ))))


;bzo may ben expensive?
(defthm consp-iff-when-memtree
  (implies (and (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
                (not (zp depth))
                )
           (iff (CONSP MEM-TREE)
                mem-tree))
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-P|))))

(defthm _MEMTREE-P-of-cdr
  (implies (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
           (MEM::|_MEMTREE-P| (CDR MEM-TREE)
                 (+ -1 DEPTH)))
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-P|))))

(defthm _MEMTREE-P-of-car
  (implies (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
           (MEM::|_MEMTREE-P| (CaR MEM-TREE)
                 (+ -1 DEPTH)))
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-P|))))

(in-theory (disable SET::PICK-A-POINT-SUBSET-STRATEGY))

;bzo could declare CONS-ONTO-ALL to be a set processor (add such a facility to set-processor.lisp) and get this for free
(defthm cons-onto-all-of-singleton
  (equal (cons-onto-all item (list x))
         (list (cons item x)))
  :hints (("Goal" :in-theory (enable set::head
                                     set::empty
                                     set::tail)
           :expand ((set::setp (list x))
                    (set::insert (cons item x) nil)
                    (cons-onto-all item (list x))))))


;drop?
;bzo rename
(defthm helper34324324
 (implies (and (MEM::|_ADDRESS-P| ADDR DEPTH) ;(not (zp depth))
               elem)
          (EQUAL (MEM::DOMAIN-AUX (MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH) DEPTH)
                 (list (CONVERT-INTEGER-TO-REVERSED-BIT-LIST ADDR DEPTH))))
 :HINTS (("GOAL" :in-theory (enable mem::domain-aux
                                    MEM::|_MEMTREE-STORE|
                                    MEM::|_ADDRESS-P|
                                    MEM::|_MEMTREE-FIX|
;MEM::|_MEMTREE-P|
                                    MEM::|_ADDRESS-FIX|)
          :do-not '(generalize eliminate-destructors)
          :EXPAND ((MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH)))))





;bzo rename
(defthm helper285767657
  (implies (and elem
                (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
                (MEM::|_ADDRESS-P| ADDR DEPTH))
           (equal (MEM::DOMAIN-AUX (MEM::|_MEMTREE-STORE| addr elem mem-tree depth) depth)
                  (set::insert (convert-integer-to-reversed-bit-list addr depth)
                               (MEM::DOMAIN-AUX mem-tree depth))
                  ))
  :otf-flg t
  :hints (("Subgoal *1/4'''" :expand ( ;(MEM::|_MEMTREE-STORE| (FLOOR ADDR 2)
    ;             ELEM NIL (+ -1 DEPTH))
    ;(MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH)
                                      ))
          ("Goal" :expand ((MEM::|_MEMTREE-STORE| (FLOOR ADDR 2)
                                 ELEM NIL (+ -1 DEPTH))
    ;(MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH)
                           (MEM::DOMAIN-AUX MEM-TREE depth))
           :do-not '(generalize eliminate-destructors)
           :induct t ;minor speedup
           :do-not-induct t
           :in-theory (e/d (mem::domain-aux
                              MEM::|_MEMTREE-STORE|
                              MEM::|_ADDRESS-P|
                              MEM::|_MEMTREE-FIX|
    ;MEM::|_MEMTREE-P|
                              MEM::|_ADDRESS-FIX|)
                           (;LIST::EQUAL-CONS-CASES ;bzo why?
                            )))))


(defthm _MEMTREE-STORE-iff
  (implies v
           (iff (MEM::|_MEMTREE-STORE| addr V mem-tree depth)
                t))
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-STORE|))))

(defthm _MEMTREE-P-of-_MEMTREE-STORE-nil
  (implies (and (MEM::|_ADDRESS-P| A depth)
                v)
           (MEM::|_MEMTREE-P| (MEM::|_MEMTREE-STORE| A V nil depth) depth))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((MEM::|_MEMTREE-STORE| A V NIL DEPTH))
           :in-theory (enable MEM::|_MEMTREE-P|
                              MEM::|_MEMTREE-FIX|
                              MEM::|_ADDRESS-FIX|))))

(defthm _MEMTREE-P-of-_MEMTREE-STORE
  (implies (and (MEM::|_ADDRESS-P| A depth)
                (MEM::|_MEMTREE-P| memtree depth)
                v)
           (MEM::|_MEMTREE-P| (MEM::|_MEMTREE-STORE| A V memtree depth) depth))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((MEM::|_MEMTREE-STORE| A V MEMTREE DEPTH)
                    (MEM::|_MEMTREE-STORE| A V NIL DEPTH))
           :in-theory (enable MEM::|_MEMTREE-P|
                              MEM::|_MEMTREE-FIX|
                              MEM::|_ADDRESS-FIX|))))



(defthm CONVERT-REVERSED-BIT-LIST-TO-INTEGER-of-CONVERT-INTEGER-TO-REVERSED-BIT-LIST
  (implies (and (natp a)
                (< a (expt 2 len))
                (natp len))
           (EQUAL (CONVERT-REVERSED-BIT-LIST-TO-INTEGER
                   (CONVERT-INTEGER-TO-REVERSED-BIT-LIST A len))
                  A))
  )

(defund good-memoryp (mem)
  (and (mem::memory-p mem)
;       (wfr (cdddr mem))
       (set::all<natp-less-than-size> (mem::mem-tree-domain (caar mem) (caddr mem)) (cadr mem))
       (set::all<not-natp-less-than-size> (set::rkeys (cdddr mem)) (cadr mem))

       (equal (signed-byte-p 29 (caddr mem))
              (cdar mem))

;bzo drop?
       (if (equal 1 (cadr mem)) ;log2 on 0 is weird, so we handle this case specially
           (equal 1 (caddr mem))
         (equal (mem::|_LOG2| (+ -1 (cadr mem)))
                (caddr mem)))))


;bzo the macro should do this...
(defthm FILTER<NOT-NATP-LESS-THAN-SIZE>-of-insert
  (equal (SET::FILTER<NOT-NATP-LESS-THAN-SIZE> (set::insert a x) size)
         (if (not (and (natp a)
                       (< a (rfix size))))
             (set::insert a (SET::FILTER<NOT-NATP-LESS-THAN-SIZE> x size))
           (SET::FILTER<NOT-NATP-LESS-THAN-SIZE> x size)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable SET::FILTER<NOT-NATP-LESS-THAN-SIZE>)
           :use (:instance
                 (:functional-instance
                  goal-both-better
                  (generic-pred (lambda (a)  (not (and (natp a)
                                                       (< a (rfix size))))))
                  (process (lambda (a) a))
                  (process-set
                   (lambda (x) (SET::FILTER<NOT-NATP-LESS-THAN-SIZE> x size))))
                 (a a)
                 (x x)

                 ))))

(defthm FILTER<NATP-LESS-THAN-SIZE>-of-insert
  (equal (SET::FILTER<NATP-LESS-THAN-SIZE> (set::insert a x) size)
         (if (and (natp a)
                       (< a (rfix size)))
             (set::insert a (SET::FILTER<NATP-LESS-THAN-SIZE> x size))
           (SET::FILTER<NATP-LESS-THAN-SIZE> x size)))
  :otf-flg t
  :hints (("Goal" :use (:instance
                        (:functional-instance
                         goal-both-better
                         (generic-pred (lambda (a)  (and (natp a)
                                                              (< a (rfix size)))))
                         (process (lambda (a) a))
                         (process-set
                          (lambda (x) (SET::FILTER<NATP-LESS-THAN-SIZE> x size))))
                        (a a)
                        (x x)

                        ))))

(defthm domain-of-store-v-non-nil
  (implies (and ;(MEM::MEMORY-P mem)
;(WFR (CDDDR MEM))
            (good-memoryp mem)
            v ;is not nil (maybe that's all we need?)
            )
           (equal (mem::domain (mem::store a v mem))
                  (set::insert a (mem::domain mem))))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (good-memoryp
                              MEM::|_ADDRESS-P|
                              MEM::SIZE
                              MEM::STORE MEM::|_STORE|
                              MEM::|_FROM-MEM|
                              MEM::|_BAD-MEMORY-P|
                              MEM::|_MEMORY-P|
                              MEM::|_MEMORY-MTREE|
                              MEM::|_MEMORY-FIX|
                              MEM::MEMORY-P
                              MEM::|_MEMORY-DEPTH|
                              MEM::|_MEMORY-FAST|
                              MEM::|_MEMORY-SIZE|
                              MEM::|_MEMORY-RECORD|

                              )
                           (SET::DOUBLE-CONTAINMENT-expensive
                            )))))

;show how s affects this...

;for typed records gotta unwrap the domain...

(in-theory (disable mem::domain)) ;move back

;bzo add to sets library
(defthm delete-of-insert-diff
  (implies (not (equal a b))
           (equal (set::delete a (set::insert b x))
                  (set::insert b (set::delete a x))))
  :hints (("Goal" :in-theory (enable SET::PICK-A-POINT-SUBSET-STRATEGY)
           :do-not '(generalize eliminate-destructors))))

(defthm not-in-cons-and-cons-onto-all
  (implies (not (set::in x y))
           (not (set::in (cons a x)
                         (cons-onto-all a y)))))

(defthm sfix-does-nothing-rewrite
  (equal (EQUAL (SET::SFIX x) x)
         (set::setp x)))

(defthm setp-of-cons-onto-all
  (set::setp (cons-onto-all a x)))

(defthm delete-of-cons-onto-all
  (equal (set::delete (cons a x)
                      (cons-onto-all a y))
         (cons-onto-all a (set::delete x y)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm not-in-cons-and-cons-onto-all-2
  (implies (not (equal a b))
           (not (set::in (cons a x)
                         (cons-onto-all b y)))))

(local (in-theory (disable SET::UNION-DELETE-Y)))
(local (in-theory (disable SET::UNION-DELETE-x)))

(defthm delete-of-union-irrel-1
 (implies (not (set::in a x))
          (equal (set::delete a (set::union x y))
                 (set::union x (set::delete a y))))
 :hints (("Goal" :in-theory (enable SET::UNION-DELETE-Y))))

(defthm delete-of-union-irrel-2
  (implies (not (set::in a y))
           (equal (set::delete a (set::union x y))
                  (set::union y (set::delete a x))))
  :hints (("Goal" :in-theory (enable SET::UNION-DELETE-x))))

(theory-invariant (incompatible (:rewrite SET::UNION-DELETE-Y) (:rewrite delete-of-union-irrel-1)))
(theory-invariant (incompatible (:rewrite SET::UNION-DELETE-x) (:rewrite delete-of-union-irrel-2)))

(defthm helper285767657-nil-version
  (implies (and (MEM::|_MEMTREE-P| MEM-TREE DEPTH)
                (MEM::|_ADDRESS-P| ADDR DEPTH))
           (equal (MEM::DOMAIN-AUX (MEM::|_MEMTREE-STORE-NIL| addr mem-tree depth) depth)
                  (set::delete (convert-integer-to-reversed-bit-list addr depth)
                               (MEM::DOMAIN-AUX mem-tree depth))
                  ))
  :otf-flg t
  :hints (
          ("Goal" :expand (
    ;(MEM::|_MEMTREE-STORE| ADDR ELEM NIL DEPTH)
                           (MEM::DOMAIN-AUX MEM-TREE depth))
           :do-not '(generalize eliminate-destructors)
           :induct t ;minor speedup
           :do-not-induct t
           :in-theory (enable MEM::DOMAIN-AUX
                              MEM::|_MEMTREE-STORE-NIL|
                              MEM::|_ADDRESS-P|
                              MEM::|_MEMTREE-FIX|
    ;MEM::|_MEMTREE-P|
                              MEM::|_ADDRESS-FIX|))))


(in-theory (disable delete-of-union-irrel-1
                    delete-of-union-irrel-2))

(in-theory (enable SET::UNION-DELETE-x
                   SET::UNION-DELETE-y))

(defthm subset-delete-self
  (equal (set::subset x (set::delete a x))
         (not (set::in a x))))

;; (defun all-have-len (len x)
;;   (if (set::empty x)
;;       t
;;     (and (equal len (len (set::head x)))
;;          (all-have-len len (set::tail x)))))

(defun len-equal (a len)
  (declare (xargs :guard t))
  (equal (len a) (rfix len)))

(set::quantify-predicate (len-equal a len))


(defthm all-len-equal-of-union
  (equal (set::all<len-equal> (set::union x y) depth)
         (and (set::all<len-equal> x depth)
              (set::all<len-equal> y depth))))

(defthm all-len-equal-of-cons-onto-all
  (implies (not (zp depth))
           (equal (SET::ALL<LEN-EQUAL> (CONS-ONTO-ALL a x) DEPTH)
                  (SET::ALL<LEN-EQUAL> x (+ -1 DEPTH)))))

(defthm all-len-equal-of-domain-aux
  (implies (and (natp depth)
                (mem::_memtree-p tree depth))
           (set::all<len-equal> (MEM::DOMAIN-AUX tree depth) depth))
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX)
           :do-not '(generalize eliminate-destructors))))

; The definition of bitp here was deleted April 2016 by Matt K. now that
; bitp is defined in ACL2.

(defun bit-listp (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (and (bitp (car lst))
           (bit-listp (cdr lst)))
    t))

(defthm integerp-of-CONVERT-REVERSED-BIT-LIST-TO-INTEGER
  (implies (bit-listp rbl)
           (natp (CONVERT-REVERSED-BIT-LIST-TO-INTEGER rbl)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable CONVERT-REVERSED-BIT-LIST-TO-INTEGER))))

(encapsulate
 ()
; (Matt K., 10/2013: Changed rel8 to rel9.)
 (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

 (defthm test
  (implies (and (force (bit-listp rbl))
                (force (true-listp rbl))
                )
           (equal (convert-integer-to-reversed-bit-list (convert-reversed-bit-list-to-integer rbl) (len rbl))
                  rbl))

  :hints (("Goal" :expand ((CONVERT-INTEGER-TO-REVERSED-BIT-LIST
                            (* 2
                               (CONVERT-REVERSED-BIT-LIST-TO-INTEGER (CDR RBL)))
                            (+ 1 (LEN (CDR RBL))))
                           (CONVERT-INTEGER-TO-REVERSED-BIT-LIST
                            (+ (CAR RBL)
                               (* 2
                                  (CONVERT-REVERSED-BIT-LIST-TO-INTEGER (CDR RBL))))
                            (+ 1 (LEN (CDR RBL)))))
           :do-not '(generalize eliminate-destructors)))))

;nested inductions
;kill the other
(defthm convert-reversed-bit-list-to-integer-of-convert-integer-to-reversed-bit-list-2
 (implies (and (force (natp n))
               (force (< n (expt 2 len)))
               )
          (equal (convert-reversed-bit-list-to-integer (convert-integer-to-reversed-bit-list n len))
                 n)))

(set::quantify-predicate (bit-listp set))

(in-theory (disable SET::ALL<BIT-LISTP>))
(in-theory (disable SET::ALL<not-BIT-LISTP>))
(in-theory (disable SET::ALL-IN-2-NOT<BIT-LISTP>))

;(in-theory (disable SET::FILTER-IN-NOT<NATP-LESS-THAN-SIZE>))


(defthm len-of-CONVERT-INTEGER-TO-REVERSED-BIT-LIST
  (equal (LEN (CONVERT-INTEGER-TO-REVERSED-BIT-LIST A len))
         (nfix len)))

(defthm convert-integer-to-reversed-bit-list-equal-rewrite
  (implies (and (true-listp x)
                (bit-listp x)
                (natp a)
                (< a (expt 2 (len x)))
                )
           (equal (equal (convert-integer-to-reversed-bit-list a (len x)) x)
                  (equal a (convert-reversed-bit-list-to-integer x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm in-of-convert-reversed-bit-lists-to-integers
  (implies (and (force (set::all<len-equal> bit-lists len))
                (force (set::all<bit-listp> bit-lists))
                (force (set::all<true-listp> bit-lists))
                (force (natp a))
                (force (< a (expt 2 len)))
                (not (zp len)))
           (equal (set::in a (convert-reversed-bit-lists-to-integers bit-lists))
                  (set::in (convert-integer-to-reversed-bit-list a len) bit-lists)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm not-in-of-convert-reversed-bit-lists-to-integers
  (implies (and (not (natp a))
                (force (set::all<bit-listp> bit-lists)))
           (not (set::in a (convert-reversed-bit-lists-to-integers bit-lists))))
  :hints (("Goal" :in-theory (enable SET::ALL<BIT-LISTP>
                                     )
           :do-not '(generalize eliminate-destructors))))

;(local (in-theory (disable LIST::EQUAL-OF-BOOLEANS-REWRITE)))
(local (in-theory (disable acl2::equal-booleans-reducton)))

(defthm in-of-convert-reversed-bit-lists-to-integers-better
  (implies (and (force (set::all<len-equal> bit-lists len))
                (force (set::all<bit-listp> bit-lists))
                (force (set::all<true-listp> bit-lists))
;                (force (natp a))
                (force (< a (expt 2 len)))
                (not (zp len)))
           (equal (set::in a (convert-reversed-bit-lists-to-integers bit-lists))
                  (and (natp a)
                       (set::in (convert-integer-to-reversed-bit-list a len) bit-lists))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm in-of-convert-reversed-bit-lists-to-integers-better2
  (implies (and (force (set::all<len-equal> bit-lists (len (set::head bit-lists))))
                (force (set::all<bit-listp> bit-lists))
                (force (set::all<true-listp> bit-lists))
;                (force (natp a))
                (force (< a (expt 2 (len (set::head bit-lists)))))
                (not (zp (len (set::head bit-lists)))))
           (equal (set::in a (convert-reversed-bit-lists-to-integers bit-lists))
                  (and (natp a)
                       (set::in (convert-integer-to-reversed-bit-list a (len (set::head bit-lists))) bit-lists))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;need to know the extra fact that the record doesn't have any usb32s (or whatevers) among its keys
;perhaps remove the usb32s from the rkeys of the record?

;show the stronger version of good-memoryp is preserved by stores?

;; (defthm consp-len-hack
;;   (implies (< 0 (len x)) (consp x)))

;bzo should the quantify macro generate this too?
(defthm delete-of-filter<not-natp-less-than-size>
  (equal (set::delete a (set::filter<not-natp-less-than-size> set size))
         (if (not (and (natp a)
                       (< a (rfix size))))
             (set::filter<not-natp-less-than-size> (set::delete a set) size)
           (set::filter<not-natp-less-than-size> set size)))
  :hints (("Goal" :in-theory (enable SET::FILTER<NOT-NATP-LESS-THAN-SIZE>))))

(defthm delete-of-filter<natp-less-than-size>
  (equal (set::delete a (set::filter<natp-less-than-size> set size))
         (if (and (natp a)
                  (< a (rfix size)))
             (set::filter<natp-less-than-size> (set::delete a set) size)
           (set::filter<natp-less-than-size> set size))))

(defthm setp-of-convert-reversed-bit-lists-to-integers
  (set::setp (convert-reversed-bit-lists-to-integers bit-lists)))

(local
 (defun double-cdr-induct (x y)
   (if (endp x)
       (list x y)
     (double-cdr-induct (cdr x) (cdr y)))))

(defthm two-calls-to-CONVERT-REVERSED-BIT-LIST-TO-INTEGER-must-differ
  (implies (and (not (equal a b))
                (bit-listp a)
                (bit-listp b)
                (true-listp a)
                (true-listp b)
                (equal (len a) (len b)))
           (NOT (EQUAL (CONVERT-REVERSED-BIT-LIST-TO-INTEGER A)
                       (CONVERT-REVERSED-BIT-LIST-TO-INTEGER b))))
  :hints (("Goal" :induct (double-cdr-induct a b)
           :do-not '(generalize eliminate-destructors))))

(defthm not-in-CONVERT-REVERSED-BIT-LIST-TO-INTEGER-CONVERT-REVERSED-BIT-LIST-TO-INTEGERs
  (IMPLIES
   (AND (not (set::in a x))
        (SET::ALL<LEN-EQUAL> x len)
        (SET::ALL<TRUE-LISTP> x)
    ;       (BIT-LISTP (SET::HEAD x))
        (SET::ALL<BIT-LISTP> x)
        (natp len)
        (bit-listp a)
        (true-listp a)
        (equal (len a) len)
        )
   (NOT
    (SET::IN (CONVERT-REVERSED-BIT-LIST-TO-INTEGER a)
             (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS x))))
  :hints (("Goal" :in-theory (enable set::in
                                     )
           :do-not '(generalize eliminate-destructors))))

(defthm not-in-CONVERT-REVERSED-BIT-LIST-TO-INTEGER-CONVERT-REVERSED-BIT-LIST-TO-INTEGERs-better
  (IMPLIES
   (AND (not (set::in a x))
        (SET::ALL<LEN-EQUAL> x (len (set::head x)))
        (SET::ALL<TRUE-LISTP> x)
    ;       (BIT-LISTP (SET::HEAD x))
        (SET::ALL<BIT-LISTP> x)
        (natp (len (set::head x)))
        (bit-listp a)
        (true-listp a)
        (equal (len a) (len (set::head x)))
        )
   (NOT
    (SET::IN (CONVERT-REVERSED-BIT-LIST-TO-INTEGER a)
             (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm use-all-len-equal
  (implies (and (set::all<len-equal> x len)
                (rationalp len)
                )
           (equal (len (set::head x))
                  (if (not (set::empty x))
                      len
                  0)))
  :hints (("Goal" :expand ((set::all<len-equal> x len)))))

(defthm true-listp-of-head
 (implies (set::all<true-listp> lists)
          (true-listp (set::head lists)))
 :hints (("Goal" :in-theory (enable set::all<true-listp>))))

(defthm delete-of-CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS
  (implies (and (set::all<len-equal> bit-lists len)
                (SET::ALL<TRUE-LISTP> BIT-LISTS)
                (SET::ALL<bit-LISTP> BIT-LISTS)
                (natp a)
                (rationalp len)
    ;               (< a len)
                (natp len)
                (< A (EXPT 2 len))
                )
           (equal (SET::DELETE A (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS bit-lists))
                  (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS
                   (SET::DELETE (CONVERT-INTEGER-TO-REVERSED-BIT-LIST A len)
                                bit-lists))))
  :hints (("Subgoal *1/2" :cases ((SET::EMPTY (SET::TAIL BIT-LISTS))))
          ("Goal" :in-theory (disable ;test
                              (:type-prescription CONVERT-INTEGER-TO-REVERSED-BIT-LIST) ;had to disable this
                              )
           :do-not '(generalize eliminate-destructors))))

(defthm delete-of-CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS2
  (implies (and (set::all<len-equal> bit-lists (len (set::head bit-lists)))
                (SET::ALL<TRUE-LISTP> BIT-LISTS)
                (SET::ALL<bit-LISTP> BIT-LISTS)
                (natp a)
                (rationalp (len (set::head bit-lists)))
    ;               (< a len)
                (natp (len (set::head bit-lists)))
                (< A (EXPT 2 (len (set::head bit-lists))))
                )
           (equal (SET::DELETE A (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS bit-lists))
                  (CONVERT-REVERSED-BIT-LISTS-TO-INTEGERS
                   (SET::DELETE (CONVERT-INTEGER-TO-REVERSED-BIT-LIST
                                 A (len (set::head bit-lists)))
                                bit-lists))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm len-of-head-of-domain-aux
  (implies (and (natp depth)
                (mem::_memtree-p mem depth))
           (equal (len (set::head (mem::domain-aux mem depth)))
                  (if (set::empty (mem::domain-aux mem depth))
                      0
                    (nfix depth))))
  :hints (("Goal" :use (:instance all-len-equal-of-domain-aux (tree mem))
           :in-theory (disable mem::domain-aux all-len-equal-of-domain-aux MEM::|_MEMTREE-P|)
           :do-not '(generalize eliminate-destructors))))

(defthm all-true-listp-of-DOMAIN-AUX
  (SET::ALL<TRUE-LISTP> (MEM::DOMAIN-AUX tree depth))
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX SET::ALL<TRUE-LISTP>))))

;bzo - is this a general theorem that quantify should give us?
;the need for it arose when i disabled SET::ALL<BIT-LISTP>, since the definition rule was high on accumulated persistence
(defthm not-all-BIT-LISTP-when-not-head
  (IMPLIES (AND (NOT (BIT-LISTP (SET::HEAD SET::SET-FOR-ALL-REDUCTION)))
                (NOT (SET::EMPTY SET::SET-FOR-ALL-REDUCTION)))
           (NOT (SET::ALL<BIT-LISTP> SET::SET-FOR-ALL-REDUCTION)))
  :hints (("Goal" :in-theory (enable SET::ALL<BIT-LISTP>))))

(defthm all-bit-listp-of-domain-aux
  (set::all<bit-listp> (mem::domain-aux tree depth))
    :hints (("Goal" :in-theory (enable mem::domain-aux acl2::equal-booleans-reducton))))
;; LIST::EQUAL-OF-BOOLEANS-REWRITE

(defthm setp-of-domain-aux
  (set::setp (mem::domain-aux tree depth))
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX))))

;should this be generated by the filter macro?
(defthm use-all<not-natp-less-than-size>
  (implies (and (set::all<not-natp-less-than-size> x sz)
                (natp-less-than-size a sz)
                (set::setp x)
                )
           (equal (set::delete a x)
                  x)))

(defthm use-all<natp-less-than-size>
  (implies (and (set::all<natp-less-than-size> x sz)
                (not (natp-less-than-size a sz))
                (set::setp x)
                )
           (equal (set::delete a x)
                  x)))

;auto-generate this?
(defthm convert-reversed-bit-lists-to-integers-of-delete-subset
  (set::subset (convert-reversed-bit-lists-to-integers (set::delete bl bls))
               (convert-reversed-bit-lists-to-integers bls)))

(local
 (defthm 2set-remove
   (equal (list::2set (list::remove a list))
          (set::delete a (list::2set list))))
 )

(local (in-theory (disable set::delete-2set)))

(local (theory-invariant (incompatible (:rewrite 2set-remove)
                                       (:rewrite set::delete-2set))))

;bzo now combine the cases..
(defthm domain-of-store-v-nil
  (implies (and (good-memoryp mem)
                (not v)
                )
           (equal (mem::domain (mem::store a v mem))
                  (set::delete a (mem::domain mem))))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :cases ((SET::EMPTY (MEM::DOMAIN-AUX (CAR (CAR MEM))
                                                (CAR (CDR (CDR MEM))))))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (set::delete-of-union-push-into-both

                            good-memoryp
                            MEM::DOMAIN
                            MEM::|_ADDRESS-P|
                            MEM::SIZE
                            MEM::STORE MEM::|_STORE|
                            MEM::|_FROM-MEM|
                            MEM::|_BAD-MEMORY-P|
                            MEM::|_MEMORY-P|
                            MEM::|_MEMORY-MTREE|
                            MEM::|_MEMORY-FIX|
                            MEM::MEMORY-P
                            MEM::|_MEMORY-DEPTH|
                            MEM::|_MEMORY-FAST|
                            MEM::|_MEMORY-SIZE|
                            MEM::|_MEMORY-RECORD|
                            )
                           (SET::DOUBLE-CONTAINMENT-expensive
                            SET::UNION-DELETE-y
                            SET::UNION-DELETE-x)))))

(defthm domain-of-store
  (implies (good-memoryp mem)
           (equal (mem::domain (mem::store a v mem))
                  (if v
                      (set::insert a (mem::domain mem))
                    (set::delete a (mem::domain mem))))))

;bzo  make DOMAIN-OF-STORE-V-NON-NIL etc. local

(in-theory (disable DOMAIN-OF-STORE-V-NON-NIL DOMAIN-OF-STORE-V-nil))

;prove setp of domain
(defthm setp-of-domain
  (set::setp (mem::domain mem))
  :hints (("Goal" :in-theory (enable mem::domain))))

;bzo move!
(defthm domain-of-new
  (equal (mem::domain (mem::new size))
         nil)
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX
                                     mem::new
                                     mem::domain
                                     mem::mem-tree-domain))))

(defthm mem::mem-tree-domain-of-nil
  (equal (mem::mem-tree-domain nil depth)
         nil)
  :hints (("Goal" :in-theory (enable MEM::DOMAIN-AUX
                                     mem::mem-tree-domain
                                     ))))

(defthm natp-of-_LOG2
  (natp (MEM::|_LOG2| n))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable MEM::|_LOG2|))))

(defthm _memtree-p-of-nil
  (mem::|_MEMTREE-P| nil depth)
  :hints (("Goal" :in-theory (enable MEM::|_MEMTREE-P|))))

(defthm log2-equal-0-rewrite
  (implies (natp size)
           (equal (EQUAL (MEM::|_LOG2| size) 0)
                  (equal 0 size)))
  :hints (("Goal" :expand ((MEM::|_LOG2| SIZE)))))

(defthm good-memoryp-of-new
  (implies (posp size)
           (good-memoryp (mem::new size)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable mem::new
                                     good-memoryp
                                     MEM::|_MEMORY-DEPTH|
                                     MEM::|_MEMORY-FIX|
                                     MEM::|_MEMORY-SIZE|
                                     MEM::|_MEMORY-P|
                                     MEM::MEMORY-P
                                     ))))
;bzo provide a macro for disabling a function's executable counterpart but allowing it to run on small values?
;(local (in-theory (disable (:executable-counterpart expt))))

;; (local
;;  (defthm good-memoryp-of-store-1
;;    (implies (and (good-memoryp mem)
;;                  a)
;;             (wfr (cdddr (mem::store a v mem) )))
;;    :otf-flg t
;;    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;             :cases (a)
;;             :in-theory (enable WFKEY
;;                                MEM::MEMORY-P
;;                                MEM::|_MEMORY-FAST|
;;                                MEM::|_MEMORY-SIZE|
;;                                MEM::|_MEMORY-DEPTH|
;;                                MEM::|_MEMORY-P|
;;                                MEM::|_BAD-MEMORY-P|
;;                                MEM::|_MEMORY-MTREE|
;;                                MEM::STORE
;;                                MEM::|_TO-MEM|
;;                                MEM::|_STORE|
;;                                MEM::|_FROM-MEM|
;;                                GOOD-MEMORYP
;;                                MEM::|_MEMORY-RECORD|
;;                                MEM::|_MEMORY-FIX|
;;                                )))))


(local
 (defthm rkeys-of-cdddr-of-store
   (implies (good-memoryp mem)
            (equal (SET::RKEYS (CDDDR (MEM::STORE A V MEM)))
                   (if (not (natp-less-than-size a (CADR MEM)))
                       (if v
                           (set::insert a (set::rkeys (CDDDR MEM)))
                         (set::delete a (set::rkeys (CDDDR MEM))))
                     (SET::RKEYS (CDDDR MEM)))))
   :otf-flg t
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::STORE
                               MEM::MEMORY-P
                               MEM::SIZE
                               MEM::|_ADDRESS-P|
                               MEM::|_MEMORY-P|
                               MEM::|_MEMORY-SIZE|
                               MEM::|_MEMORY-DEPTH|
                               MEM::|_MEMORY-FAST|
                               MEM::|_TO-MEM|
                               MEM::|_FROM-MEM|
                               MEM::|_STORE|
                               MEM::|_MEMORY-MTREE|
                               MEM::|_MEMORY-FIX|
                               GOOD-MEMORYP
                               MEM::|_MEMORY-RECORD|
                               )))))

(local
 (defthm cadr-of-_store
   (implies (good-memoryp mem)
            (equal (CADR (MEM::_STORE A V MEM))
                   (CADR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable ;MEM::STORE
;MEM::|_FROM-MEM|
;MEM::|_TO-MEM|
                        MEM::|_STORE|
                        GOOD-MEMORYP
                        MEM::MEMORY-P
;MEM::|_MEMORY-P|
                        MEM::|_MEMORY-SIZE|
                        MEM::|_MEMORY-FIX|
                        )))))

(local
 (defthm cdar-of-_store
   (implies (good-memoryp mem)
            (equal (CDaR (MEM::_STORE A V MEM))
                   (CDaR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::|_MEMORY-FAST|
;MEM::STORE
;MEM::|_FROM-MEM|
;MEM::|_TO-MEM|
                               MEM::|_STORE|
                               GOOD-MEMORYP
                               MEM::MEMORY-P
;MEM::|_MEMORY-P|
                               MEM::|_MEMORY-SIZE|
                               MEM::|_MEMORY-FIX|
                               )))))

(local
 (defthm caddr-of-_store
   (implies (good-memoryp mem)
            (equal (CAdDR (MEM::_STORE A V MEM))
                   (CAdDR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable ;MEM::STORE
;MEM::|_FROM-MEM|
;MEM::|_TO-MEM|
                        MEM::|_STORE|
                        GOOD-MEMORYP
                        MEM::MEMORY-P
;MEM::|_MEMORY-P|
                        MEM::|_MEMORY-SIZE|
                        MEM::|_MEMORY-FIX|
                        MEM::|_MEMORY-DEPTH|
                        )))))

(local
 (defthm cadr-of-store
   (implies (good-memoryp mem)
            (equal (CADR (MEM::STORE A V MEM))
                   (CADR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::STORE
                               MEM::|_FROM-MEM|
                               MEM::|_TO-MEM|
;                             MEM::|_STORE|
                               GOOD-MEMORYP
                               MEM::MEMORY-P
                               MEM::|_MEMORY-P|
                               )))))

(local
 (defthm cdar-of-store
   (implies (good-memoryp mem)
            (equal (CDaR (MEM::STORE A V MEM))
                   (CDaR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::STORE
                               MEM::|_FROM-MEM|
                               MEM::|_TO-MEM|
;                             MEM::|_STORE|
                               GOOD-MEMORYP
                               MEM::MEMORY-P
                               MEM::|_MEMORY-P|
                               )))))

(local
 (defthm caddr-of-store
   (implies (good-memoryp mem)
            (equal (CADdR (MEM::STORE A V MEM))
                   (CADdR MEM)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable MEM::STORE
                               MEM::|_FROM-MEM|
                               MEM::|_TO-MEM|
;                             MEM::|_STORE|
                               GOOD-MEMORYP
                               MEM::MEMORY-P
                               MEM::|_MEMORY-P|
                               )))))

(in-theory (disable MEM::MEM-TREE-DOMAIN))

(defthm mem-tree-domain-after-store
  (implies (good-memoryp mem)
           (equal (MEM::MEM-TREE-DOMAIN (CAAR (MEM::STORE A V MEM))
                                        (CADDR ;(MEM::STORE A V
                                         MEM
                                         ;)
                                         ))
                  (if (natp-less-than-size a (CADR MEM))
                      (if v
                          (set::insert a (MEM::MEM-TREE-DOMAIN (CAAR MEM)
                                                               (CADDR MEM)))
                        (set::delete a (MEM::MEM-TREE-DOMAIN (CAAR MEM)
                                                             (CADDR MEM))))
                    (MEM::MEM-TREE-DOMAIN (CAAR MEM)
                                          (CADDR MEM)))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;           :use (:instance domain-of-store) ;gross way to prove this...
           :cases ((SET::EMPTY (MEM::DOMAIN-AUX (CAR (CAR MEM))
                                                      (CAR (CDR (CDR MEM))))))

           :in-theory (e/d (MEM::DOMAIN

                            MEM::MEM-TREE-DOMAIN
                            MEM::STORE
                            MEM::MEMORY-P
                            MEM::SIZE
                            MEM::|_ADDRESS-P|
                            MEM::|_MEMORY-P|
                            MEM::|_MEMORY-SIZE|
                            MEM::|_MEMORY-DEPTH|
                            MEM::|_MEMORY-FAST|
                            MEM::|_TO-MEM|
                            MEM::|_FROM-MEM|
                            MEM::|_STORE|
                            MEM::|_MEMORY-MTREE|
                            MEM::|_MEMORY-FIX|
                            GOOD-MEMORYP
                            MEM::|_MEMORY-RECORD|
                            )
                           (domain-of-store)))))


(local (in-theory (disable SIGNED-BYTE-P)))

;bzo speed this up..
(defthm good-memoryp-of-store
  (implies (and (good-memoryp mem)
                ;a
                )
           (good-memoryp (mem::store a v mem)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance rkeys-of-cdddr-of-store)
                 (:instance mem-tree-domain-after-store))
           :in-theory (e/d (good-memoryp
                            ;MEM::MEM-TREE-DOMAIN
                            )
                           (SET::ALL-STRATEGY<NOT-NATP-LESS-THAN-SIZE>
                            mem-tree-domain-after-store
                            SET::ALL-STRATEGY<NATP-LESS-THAN-SIZE>)))))

(defthm _memtree-p-of-list-nil
  (implies (not (zp depth))
           (not (mem::|_MEMTREE-P| '(nil) depth)))
  :hints (("Goal" :in-theory (enable mem::|_MEMTREE-P|))))

(defthm mem::domain-aux-iff
  (implies (mem::|_MEMTREE-P| mem-tree depth)
           (iff (mem::domain-aux mem-tree depth)
                mem-tree))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable MEM::DOMAIN-AUX
                              mem::|_MEMTREE-P|))))

(defthm domain-of-clear
  (implies (good-memoryp m)
           (equal (mem::domain (mem::clear p m))
                  (set::delete p (mem::domain m))))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm good-memoryp-of-clear
  (implies (acl2::good-memoryp mem)
           (acl2::good-memoryp (mem::clear addr mem)))
  :hints (("Goal" :in-theory (enable mem::clear))))
