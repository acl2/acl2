; Mixed rules 2
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;TODO Move the things in this file into other files according to topic.  Start
;by splitting the list stuff from the bv stuff.

;;  This file was called hacks6.lisp.

(include-book "list-rules")
(include-book "kestrel/bv-lists/bvnth" :dir :system)
;(include-book "kestrel/arrays-2d/bv-arrays-2d" :dir :system)
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/lists-light/finalcdr" :dir :system)
(include-book "kestrel/lists-light/update-subrange" :dir :system)
(include-book "kestrel/bv-lists/getbit-list" :dir :system)
(include-book "kestrel/bv-lists/all-signed-byte-p" :dir :system)
;(include-book "ihs/logops-lemmas" :dir :system) ;todo
;fixme move these up
(include-book "lenconsmeta") ;BOZO did this speed things up?  try with and without...
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "kestrel/bv/logext" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvif" :dir :system)
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/subrange" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/library-wrappers/arithmetic-top-with-meta" :dir :system))

(local (in-theory (disable ;unsigned-byte-p-of-+-when-<-of-logtail-and-expt
                           ;usb-plus-from-bounds
                           ;;unsigned-byte-p-plus
                           ))) ;bad?

(local (in-theory (disable expt
                           )))

(in-theory (disable ;logapp-0 ;bad forcing
                    ;logtail-equal-0
                    ))

;(in-theory (disable MV-NTH-TO-VAL)) ;bad rule
;(in-theory (disable SYN::LEN-IMPLIES-ACL2-LEN)) ;weird rule

;(in-theory (disable LIST::LEN-OF-NON-CONSP)) ;TODO: push back

;(in-theory (disable SYN::LEN-IMPLIES-ACL2-LEN)) ;BOZO

;(local (in-theory (enable BAG::UNIQUE-OF-CONS)))

;(local (in-theory (disable LIST::2SET))) ;move

;(local (in-theory (disable FLOOR-MINUS-ERIC-BETTER)))

;; ;what about lambdas?
;; ;dup?
;; ;move to utilities?
;; ;guards?
;; ;generalize to apply an alist?
;; (mutual-recursion
;;  (defun substitute-sexp (new old exp)
;;    (if (equal exp old)
;;        new
;;      (if (consp exp)
;;          (if (equal 'quote (car exp))
;;              exp
;;            (cons (car exp)
;;                  (substitute-sexp-list new old (cdr exp))))
;;        exp)))

;;  (defun substitute-sexp-list (new old exp-list)
;;    (if (endp exp-list)
;;        nil
;;      (cons (substitute-sexp new old (car exp-list))
;;            (substitute-sexp-list new old (cdr exp-list))))))

;fixme are these the same?
;(in-theory (disable BAG::UNIQUE-SUBBAGP-UNIQUE-FREE)) ;bozo?
;(in-theory (disable BAG::SUBBAGP-UNIQUENESS))

;; ;mixes sets and bags...
;; ;do we need this?
;; (skip -proofs
;;  (defthmd new-ad-not-memberp ;disabled Tue May 25 03:44:18 2010
;;    (implies (bag::subbagp lst rkeys)
;;             (not (bag::memberp (new-ad rkeys) lst)))))

;enable when stable?
;(in-theory (disable LIST::UPDATE-NTH-EQUAL-REWRITE))
;(in-theory (disable LIST::EQUAL-CONS-CASES))

;these caused problems.  investigate why
;(in-theory (enable LIST::UPDATE-NTH-EQUAL-REWRITE))
;(in-theory (enable LIST::EQUAL-CONS-CASES))


;; (thm
;;  (implies (natp n)
;;           (equal (list::finalcdr (list::update-nth n v x))
;;                  (if (equal n (len x))
;;                      nil
;;                  (list::finalcdr x))))
;;  :hints (("Goal" :in-theory (enable list::update-nth))))


;; ;bozo gen this hack!
;; (defthmd update-nth-4-elems-smash-all
;;   (implies (and (equal 4 (len x))
;;                 (true-listp x))
;;            (equal (update-nth 0 v0 (update-nth 1 v1 (update-nth 2 v2 (update-nth 3 v3 x))))
;;                   (list v0 v1 v2 v3)))
;;   :hints (("Goal" :in-theory (enable list::update-nth-equal-rewrite))))

;; (defun induct-sub1-cdr (n l)
;;   (if (endp l)
;;       (list n l)
;;     (induct-sub1-cdr (+ -1 n) (cdr l))))

(defthm integerp-of-nth-free-len
  (implies (and (equal (len l) k) ;k is a free variable
                (< n k)
                (integerp n)
                (<= 0 n)
                (integer-listp l))
           (INTEGERP (NTH n l)))
  :hints (("Goal" ; :induct (induct-sub1-cdr n l)
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (integer-listp nth) (nth-of-cdr)))))

;; (defun ind-hint (m n dom)
;;   (if (zp m)
;;       (list m n dom)
;;     (ind-hint (+ -1 m) (+ 1 n) dom ;(set::insert (NEW-AD (SET::UNION DOM (N-NEW-ADS N DOM))) dom)
;;               )))

;;aha.  the final theorem doesn't say that the new ads really do get bound, which i guess we need?

;; (defun contains-a-consp (lst)
;;   (if (endp lst)
;;       nil
;;     (or (consp (car lst))
;;         (contains-a-consp (cdr lst)))))

;; (defun all-nil (lst)
;;   (declare (xargs :guard (true-listp lst)))
;;   (if (endp lst)
;;       t
;;     (and (not (car lst))
;;          (all-nil (cdr lst)))))

;; (defun find-a-key-with-non-nil-binding (pairs)
;;   (if (endp pairs)
;;       nil
;;     (if (cdar pairs)
;;         (caar pairs)
;;       (find-a-key-with-non-nil-binding (cdr pairs)))))



;; (defthm memberp-of-FIND-A-KEY-WITH-NON-NIL-BINDING-and-STRIP-CARS
;;   (implies (FIND-A-KEY-WITH-NON-NIL-BINDING PAIRS)
;;            (memberp (FIND-A-KEY-WITH-NON-NIL-BINDING PAIRS) (STRIP-CARS PAIRS)))
;;   :hints (("Goal" :in-theory (enable FIND-A-KEY-WITH-NON-NIL-BINDING STRIP-CARS))))

;; (thm
;;  (implies (and (not (all-nil (strip-cdrs pairs)))
;;                (bag::unique (strip-cars pairs)))
;;           (get-field ad (find-a-key-with-non-nil-binding pairs) (set-fields ad pairs heap)))
;;  :hints (("Subgoal *1/3.2" :use (:instance memberp-of-FIND-A-KEY-WITH-NON-NIL-BINDING-and-STRIP-CARS
;;                                            (pairs (cdr pairs)))
;;           :in-theory (disable memberp-of-FIND-A-KEY-WITH-NON-NIL-BINDING-and-STRIP-CARS))
;;          ("Goal" :expand (;(LOOKUP-EQUAL (FIND-A-KEY-WITH-NON-NIL-BINDING (CDR PAIRS)) PAIRS)
;;                           (STRIP-CARS PAIRS))
;;           :do-not '(generalize eliminate-destructors))))

;; (defthm rkeys-of-set-fields-1
;;   (implies (bag::unique (strip-cars bindings))
;;            (equal (rkeys (set-fields ad bindings heap))
;;                   (if (and (not (g ad heap)) ;too extreme?
;;                            (all-equal$ nil (strip-cdrs bindings)))
;;                       (set::delete ad (rkeys heap))
;;                     (set::insert ad (rkeys heap)))))
;;   :hints (("Goal" :induct t
;;            :in-theory (e/d (set-fields) (SET::DOUBLE-CONTAINMENT))))))

;; (skip -proofs
;; (defthm rkeys-of-set-fields
;;    (implies (and (not (all-equal$ nil (strip-cdrs pairs)))
;;                  (bag::unique (strip-cars pairs)))
;;             (equal (rkeys (set-fields ad pairs heap))
;;                    (set::insert ad (rkeys heap))))
;;    :hints (("Subgoal *1/2.4" :use (
;;                                    (:instance rkeys-of-set-fields-cases (pairs (cdr pairs)))

;;                                    )
;; ;          :expand (SET-FIELDS AD PAIRS HEAP)
;;             :in-theory (e/d (set-fields BAG::UNIQUE-OF-CONS)
;;                             ( ;rkeys-of-set-fields-subset
;;                              SET::DOUBLE-CONTAINMENT
;;                              SET::PICK-A-POINT-SUBSET-STRATEGY)))

;;            ("Subgoal *1/2.3" :use (
;;          ;                          (:instance rkeys-of-set-field-cases (pair (CAAR PAIRS)) (value (CDAR PAIRS)))

;;                                    )
;; ;          :expand (SET-FIELDS AD PAIRS HEAP)
;;             :in-theory (e/d (set-fields BAG::UNIQUE-OF-CONS)
;;                             ( ;rkeys-of-set-fields-subset
;;                              SET::DOUBLE-CONTAINMENT
;;                              SET::PICK-A-POINT-SUBSET-STRATEGY)))
;;            ("subgoal *1/2" :use ( ;(:instance rkeys-of-set-fields-cases (pairs (CDR PAIRS)))
;; ;(:instance rkeys-of-set-field-cases (pair (CAAR PAIRS)) (value (CDAR PAIRS)))
;; ;(:instance rkeys-of-set-field-cases (pair (CAAR PAIRS)) (value (CDAR PAIRS)) (heap (SET-FIELDS AD (CDR PAIRS) HEAP)))
;;                                  ;(:instance rkeys-of-set-fields-cases (pairs (CDR PAIRS)) (heap (SET-FIELD AD (CAAR PAIRS) (CDAR PAIRS) HEAP)))
;;                                  )
;; ;          :expand (SET-FIELDS AD PAIRS HEAP)
;;             :in-theory (e/d (set-fields
;;                              BAG::UNIQUE-OF-CONS)
;;                             ( ;rkeys-of-set-fields-subset
;;                              ;rkeys-of-set-field-both
;;                              SET::DOUBLE-CONTAINMENT
;;                              SET::PICK-A-POINT-SUBSET-STRATEGY)))
;;            ("Goal" :induct t
;;             :do-not '(generalize eliminate-destructors)
;;             :in-theory (e/d (set-fields) (SET::PICK-A-POINT-SUBSET-STRATEGY SET::DOUBLE-CONTAINMENT))))))




;just recode ithbit to not call new
;but when almost all of the state is inside a HIDE, why is acl2 so slow?  try in allegro?
;add in fresh vars for wormhole abstraction??  when the wormhole abstracte result is used and we get a big term for the wormhole quantity - generalize that term to a fresh var and try to prove for that fresh var

;general facility to do this for (hide some-huge-term) ??

;(in-theory (disable UPDATE-NTH-4-ELEMS-SMASH-ALL)) ;for loade
;(in-theory (disable LIST::UPDATE-NTH-EQUAL-UPDATE-NTH-REWRITE))

;(in-theory (disable LIST::LEN-UPDATE-NTH-BETTER))
(in-theory (disable TRUE-LISTP-UPDATE-NTH)) ;TRUE-LISTP-OF-UPDATE-NTH-2 is stronger

;loade
;(in-theory (disable UPDATE-NTH-OF-CONS)) ;why necessary?
;(in-theory (disable LIST::LEN-CONS)) ;why necessary?

;bbozo temporary
;(in-theory (disable LIST::UPDATE-NTH-UPDATE-NTH-DIFF))

;combine update-nth calls into update-subrange

;; (thm
;;  (implies (and (equal (+ 1 end (- start)) (len lst))
;;                (true-listp vals)
;;                (equal (len vals) (len lst)))
;;           (equal (update-subrange start end vals lst)
;;                  (firstn (len lst) vals)))
;;  :hints (("Goal" :in-theory (enable update-subrange))))

;; ;for testing
;; (defthmd signed-byte-p-5-cases
;;   (equal (signed-byte-p 5 x)
;;          (memberp x '(-16 -15 -14 -13 -12 -11 -10 -9 -8 -7 -6 -5 -4 -3 -2 -1 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)))
;;   :hints (("Goal" :in-theory (enable signed-byte-p))))

;; (thm
;;  (equal (equal (logxor a b) (logxor a c))
;;         (equal a c)))

;(in-theory (enable update-nth-of-cons))

;; (defthm rkeys-of-initialize-one-dim-arrays
;;   (implies type
;;            (equal (rkeys (jvm::initialize-one-dim-arrays addrs type contents heap))
;;                   (set::union (list::2set addrs) (rkeys heap))))
;;   :hints (("Goal"
;;            :in-theory (e/d (;LIST::2SET
;;                             ) (set::double-containment)))))


;; ;mixes theories?
;; (defthm nthcdr-of-push
;;   (implies (and (integerp n)
;;                 (< 0 n))
;;            (equal (nthcdr n (jvm::push a x))
;;                   (nthcdr (+ -1 n) x)))
;;   :hints (("Goal" :in-theory (enable jvm::push))))

;; (NOT (SET::IN (NTH '0
;;                    (GET-FIELD (LOCALVAR '1 S0)
;;                               (array-contents-pair)
;;                               (JVM::HEAP S0)))
;;               (N-NEW-ADS '4
;;                          (SET::INSERT (NEW-AD (RKEYS (JVM::HEAP S0)))
;;                                       (RKEYS (JVM::HEAP S0)))))).
;; 2)

;(in-theory (enable JVM::INITIALIZE-ONE-DIM-ARRAY)) ;why?

;;with wormhole abstraction, what if we copy over a nil object?  that messes up the domain?

;; ;use defmap?
;; (defun bvchop-list-list (n x)
;;   (if (endp x)
;;       nil
;;     (cons (bvchop-list n (car x))
;;           (bvchop-list-list n (cdr x)))))

;; (defthm array-contents-list-of-store-array-list
;;   (implies (and (equal (len ref-list) (len contents))
;; ;                (true-listp contents)
;;                 (bag::unique ref-list)
;; ;                (integerp len)
;;                 )
;;            (equal (array-contents-list ref-list (store-array-list ref-list contents len ':byte  ;gen?
;;                                                                   heap))
;;                   (bvchop-list-list 8 (take-list len contents)) ;(byte-fix-list-list (take-list len contents))
;;                   ))
;;   :hints (("Goal" :in-theory (enable array-contents-list store-array-list))))

;; (defthm array-contents2-of-store-array-2d
;;   (implies (and (not (memberp ref (array-contents ref heap)))
;;                 (equal (len (array-contents ref heap)) (len contents))
;;                 (equal numrows (len contents))
;;                 (integerp rowsize)
;;                 (bag::unique (array-contents ref heap)))
;;            (equal (array-contents2 ref (store-array-2d ref contents numrows rowsize ':byte  ;gen?
;;                                                        heap))
;;                   ;(byte-fix-list-list (take-list rowsize contents))
;;                   (bvchop-list-list 8 (take-list rowsize contents))
;;                   ))
;;   :hints (("Goal" :in-theory (enable store-array-2d))))


;; (defthmd store-array-recollapse
;;   (implies (equal (len val) (GET-FIELD REF '("ARRAY" . "length") heap))
;;            (equal (SET-FIELD ref
;;                              (array-contents-pair)
;;                              val
;;                              heap)
;;                  (store-array ref val heap)))
;;   :hints (("Goal" :in-theory (enable store-array))))

;; (theory-invariant (incompatible (:definition store-array ) (:rewrite store-array-recollapse)))

;; (defthm len-of-update-nth-equal-rewrite
;;   (implies (and (natp n)
;;                 (natp k)
;;                 (< n k)
;;                 (< n (len lst)) ;is this hyp ok?
;;                 )
;;            (equal (equal (len (update-nth n v lst)) k)
;;                   (and (equal (len lst) k))))
;;   :hints (("Goal" :in-theory (enable ;list::len-update-nth-better
;;                               ))))

;; ;hope the backchain-limit is okay...
;; (defthm len-of-update-nth-rewrite-2-semi-cheap
;;   (implies (and (< n (len lst)) ;is this hyp ok?
;;                 (natp n))
;;            (equal (len (update-nth n v lst))
;;                   (len lst)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (2 nil)))
;;   :hints (("Goal" :in-theory (enable ;list::len-update-nth-better
;;                               ))))



;; (defthm get-length-field-of-store-array
;;   (equal (get-field ref '("ARRAY" . "length") (store-array ref contents len type heap))
;;          (len contents))
;;   :hints (("Goal" :in-theory (e/d (store-array) (;store-array-recollapse
;;                                                  )))))

;; (defthm get-contents-field-of-store-array
;;   (equal (get-field ref (array-contents-pair) (store-array ref contents len ':byte heap))
;;          contents
;;          )
;;   :hints (("Goal" :in-theory (e/d (store-array) (;store-array-recollapse
;;                                                  )))))

;; (defthm get-field-of-store-array-irrel2
;;   (implies (not (memberp pair (list (array-contents-pair) ;("ARRAY". "length")
;;                                       )))
;;            (equal (get-field ref pair (store-array ref2 contents len type heap))
;;                   (get-field ref pair heap)))
;;   :hints (("Goal" :in-theory (e/d (store-array) (;store-array-recollapse
;;                                                  )))))

;; (defthm store-array-of-store-array-diff
;;   (implies (not (equal ref1 ref2))
;;            (equal (store-array ref1 contents1 (store-array ref2 contents2 heap))
;;                   (store-array ref2 contents2 (store-array ref1 contents1 heap))))
;;   :hints (("Goal" :in-theory (e/d (store-array) (store-array-recollapse)))))

;; (defthm store-array-of-store-array-same
;;   (equal (store-array ref contents1 (store-array ref contents2 heap))
;;          (store-array ref contents1 heap))
;;   :hints (("Goal" :in-theory (e/d (store-array) (store-array-recollapse)))))



;; (defund store-2d-array-row (ref rownum val heap)
;;   (store-array (nth rownum (GET-FIELD ref (array-contents-pair) heap))
;;                val
;;                heap))

;; ;bozo heaps are unlikely to match!
;; (defthm store-2d-array-row-recollapse
;;   (equal (store-array (nth rownum (GET-FIELD ref (array-contents-pair) heap))
;;                       val
;;                       heap)
;;          (store-2d-array-row ref rownum val heap))
;;   :hints (("Goal" :in-theory (enable store-2d-array-row))))

;; ;; (defthm get-length-field-of-store-2d-array-row
;; ;;   (equal (get-field ref '("ARRAY" . "length") (store-2d-array-row ref row val heap))
;; ;;          (len contents))
;; ;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse)))))

;; ;; (defthm get-contents-field-of-store-2d-array-row
;; ;;   (equal (get-field ref (array-contents-pair) (store-2d-array-row ref contents heap))
;; ;;          contents)
;; ;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse)))))

;; (defthm get-field-of-store-2d-array-row-irrel2
;;   (implies (not (memberp pair '(("ARRAY" . "contents") ("ARRAY" . "length"))))
;;            (equal (get-field ref pair (store-2d-array-row ref2 row contents heap))
;;                   (get-field ref pair heap)))
;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse)))))

;; (defthm get-field-of-store-2d-array-row-irrel
;;  (implies (not (equal ref  (nth rownum (GET-FIELD ref2 (array-contents-pair) heap))))
;;           (equal (get-field ref pair (store-2d-array-row ref2 rownum contents-list heap))
;;                  (get-field ref pair heap)))
;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse)))))

;; ;drop?
;; (defthm store-2d-array-row-recollapse2
;;   (implies (equal var (GET-FIELD ref (array-contents-pair) heap))
;;            (equal (store-array (nth rownum var)
;;                                val
;;                                heap)
;;                   (store-2d-array-row ref rownum val heap)))
;;   :hints (("Goal" :in-theory (enable store-2d-array-row))))

;; (defthm store-2d-array-row-recollapse3
;;   (implies (equal (GET-FIELD ref (array-contents-pair) heap2)
;;                   (GET-FIELD ref (array-contents-pair) heap))
;;            (equal (store-array (nth rownum (GET-FIELD ref (array-contents-pair) heap2))
;;                                val
;;                                heap)
;;                   (store-2d-array-row ref rownum val heap)))
;;   :hints (("Goal" :in-theory (enable store-2d-array-row))))

;; (defthm get-field-of-store-2d-array-row-same
;;   (implies (equal (get-field ref (array-contents-pair) heap2)
;;                   (get-field ref (array-contents-pair) heap))
;;            (equal (get-field (nth rownum (get-field ref (array-contents-pair) heap2))
;;                              (array-contents-pair)
;;                              (store-2d-array-row ref rownum contents heap))
;;                   contents))
;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse store-2d-array-row-recollapse2 store-2d-array-row-recollapse3)))))

;; (defthm get-field-of-store-2d-array-row-same---length
;;   (implies (equal (get-field ref (array-contents-pair) heap2)
;;                   (get-field ref (array-contents-pair) heap))
;;            (equal (get-field (nth rownum (get-field ref (array-contents-pair) heap2))
;;                              '("ARRAY" . "length")
;;                              (store-2d-array-row ref rownum contents heap))
;;                   (len contents)))
;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse store-2d-array-row-recollapse2 store-2d-array-row-recollapse3)))))

;; ;BBOZO handle different refs
;; (defthm store-2d-array-row-of-store-2d-array-row-diff
;;   (implies (and (syntaxp (or (smaller-termp ref2 ref1)
;;                              (and (equal ref1 ref2)
;;                                   (smaller-termp row2 row1))))
;;                 (equal ref1 ref2);BBOZO
;;                 (or (not (equal row1 row2))
;;                     (not (equal ref1 ref2)))
;;                 (natp row1)
;;                 (< row1 (len (GET-FIELD REF1 (array-contents-pair) HEAP)))
;;                 (natp row2)
;;                 (< row2 (len (GET-FIELD REF2 (array-contents-pair) HEAP)))
;;                 (not (memberp REF2 (GET-FIELD REF1 (array-contents-pair) HEAP)))
;;  ;               (not (memberp REF1 (GET-FIELD REF2 (array-contents-pair) HEAP)))
;;                 (bag::unique (GET-FIELD REF1 (array-contents-pair) HEAP))
;;                 )
;;            (equal (store-2d-array-row ref1 row1 contents1 (store-2d-array-row ref2 row2 contents2 heap))
;;                   (store-2d-array-row ref2 row2 contents2 (store-2d-array-row ref1 row1 contents1 heap))))
;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse store-2d-array-row-recollapse2 store-2d-array-row-recollapse3)))))

;; ;BBOZO handle different refs
;; (defthm store-2d-array-row-of-store-2d-array-row-diff
;;   (implies (and (syntaxp (smaller-termp row2 row1))
;;                 (not (equal row1 row2))
;;                 (natp row1)
;;                 (< row1 (len (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 (natp row2)
;;                 (< row2 (len (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 (not (memberp REF (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 (bag::unique (GET-FIELD REF (array-contents-pair) HEAP))
;;                 )
;;            (equal (store-2d-array-row ref row1 contents1 (store-2d-array-row ref row2 contents2 heap))
;;                   (store-2d-array-row ref row2 contents2 (store-2d-array-row ref row1 contents1 heap))))
;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse store-2d-array-row-recollapse2 store-2d-array-row-recollapse3)))))

;; (skip -proofs
;;  (defthmd ref-not-in-own-contents ;newly disabled - not true without more hyps!
;;    (implies (and (bag::unique (addresses-of-array-ref ref dims heap))
;;                  (consp dims))
;;             (not (memberp ref (get-field ref (array-contents-pair) heap))))
;;    :otf-flg t
;;    :hints (("Goal" :expand ((ADDRESSES-OF-ARRAY-REF-LIST (GET-FIELD REF (array-contents-pair)
;;                                                                     HEAP)
;;                                                          (CAR DIMS)
;;                                                          (CDR DIMS)
;;                                                          HEAP)
;;                             (addresses-of-array-ref ref dims heap))))))



;; (skip -proofs
;; (defthm ref-not-in-own-contents-hack
;;   (implies (and (bag::unique (addresses-of-array-ref ref '(4 4) heap))
;;                 (equal 4 (len (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 ;(consp dims)
;;                 )
;;            (not (memberp ref (get-field ref (array-contents-pair) heap))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (e/d (JVM::CONS-EQUAL-REWRITE LIST::LEN-OF-CDR) (CAR-OF-GET-FIELD-OF-CONTENTS-HACK
;;                                                             ))
;;                                      :cases ((equal  (GET-FIELD REF (array-contents-pair)
;;                                                  HEAP)
;;                                   (LIST
;;                                  (NTH 0
;;                                       (GET-FIELD REF (array-contents-pair)
;;                                                  HEAP))
;;                                  (NTH 1
;;                                       (GET-FIELD REF (array-contents-pair)
;;                                                  HEAP))
;;                                  (NTH 2
;;                                       (GET-FIELD REF (array-contents-pair)
;;                                                  HEAP))
;;                                  (NTH 3
;;                                       (GET-FIELD REF (array-contents-pair)
;;                                                  HEAP)))))

;;            :expand ((addresses-of-array-ref ref dims heap))))))

;; (skip -proofs
;; (defthm store-2d-array-row-of-store-2d-array-row-diff2
;;   (implies (and (syntaxp (smaller-termp row2 row1))
;;                 (not (equal row1 row2))
;;                 (natp row1)
;;                 (< row1 (len (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 (natp row2)
;;                 (< row2 (len (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 (bag::unique (GET-FIELD REF (array-contents-pair) HEAP))

;; ;                (not (memberp REF (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 (BAG::UNIQUE (ADDRESSES-OF-ARRAY-REF ref
;;                                                      '(4 4)
;;                                                      heap))
;;                 )
;;            (equal (store-2d-array-row ref row1 contents1 (store-2d-array-row ref row2 contents2 heap))
;;                   (store-2d-array-row ref row2 contents2 (store-2d-array-row ref row1 contents1 heap))))
;;   ))

;; (skip -proofs
;; (defthm store-2d-array-row-of-store-2d-array-row-same
;;   (implies (and (natp row)
;;                 (< row (len (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 (bag::unique (GET-FIELD REF (array-contents-pair) HEAP))

;; ;                (not (memberp REF (GET-FIELD REF (array-contents-pair) HEAP)))
;;                 (BAG::UNIQUE (ADDRESSES-OF-ARRAY-REF ref
;;                                                      '(4 4)
;;                                                      heap))
;;                 )
;;            (equal (store-2d-array-row ref row contents1 (store-2d-array-row ref row contents2 heap))
;;                   (store-2d-array-row ref row contents1 heap)))
;;   :hints (("Goal" :in-theory (e/d (store-2d-array-row) (store-2d-array-row-recollapse store-2d-array-row-recollapse2 store-2d-array-row-recollapse3)))))
;; )





;; (defthm recollapse-array-4-hack
;;  (implies (and (equal 4 (len (GET-FIELD ref (array-contents-pair) HEAP)))
;;                (not (memberp REF (GET-FIELD REF (array-contents-pair) HEAP))))
;;           (EQUAL (STORE-2D-ARRAY-ROW
;;                   ref 0 v0
;;                   (STORE-2D-ARRAY-ROW
;;                    ref 1 v1
;;                    (STORE-2D-ARRAY-ROW
;;                     ref 2 v2
;;                     (STORE-2D-ARRAY-ROW
;;                      ref 3 v3
;;                      heap))))
;;                  (STORE-ARRAY-2D ref (LIST v0 v1 v2 v3) heap)))
;;  :hints (("Goal" :expand ((STORE-ARRAY-LIST (CDR (GET-FIELD REF (array-contents-pair)
;;                                                   HEAP))
;;                                   (LIST V1 V2 V3)
;;                                   HEAP)
;; (STORE-ARRAY-LIST (CDDR (GET-FIELD REF (array-contents-pair)
;;                                                   HEAP))
;;                                  (LIST V2 V3)
;;                                  HEAP)
;; (STORE-ARRAY-LIST (NTHCDR 3
;;                                        (GET-FIELD REF (array-contents-pair)
;;                                                   HEAP))
;;                                (LIST V3)
;;                                HEAP)
;; (STORE-ARRAY-LIST (GET-FIELD REF (array-contents-pair)
;;                              HEAP)
;;                   (LIST V0 V1 V2 V3)
;;                   HEAP))
;;  :in-theory (enable store-array-2d list::len-of-cdr STORE-ARRAY-LIST car-becomes-nth-of-0))))

;; (defthm get-field-of-store-array-list-irrel2
;;   (implies (not (memberp pair (list (array-contents-pair) ;("ARRAY" . "length")
;;                                           )))
;;            (equal (get-field ref pair (store-array-list ref-list contents-list len type heap))
;;                   (get-field ref pair heap)))
;;   :hints (("Goal" :in-theory (enable store-array-list))))

;; (defthm get-field-of-store-array-2d-irrel2
;;   (implies (not (memberp pair '(("ARRAY" . "contents") ("ARRAY" . "length"))))
;;            (equal (get-field ref pair (store-array-2d ref2 contents heap))
;;                   (get-field ref pair heap)))
;;   :hints (("Goal" :in-theory (enable store-array-2d))))

;; (defthm get-field-of-store-array-2d-irrel
;;   (implies (not (memberp ref (GET-FIELD ref2 (array-contents-pair) heap)))
;;            (equal (GET-FIELD ref pair (STORE-ARRAY-2D ref2 contents heap))
;;                   (GET-FIELD ref pair heap)))
;;   :hints (("Goal" :in-theory (enable store-array-2d))))

;for now i'm just gonna open up all the array ops...
;(in-theory (disable store-array-recollapse))

;(in-theory (enable STORE-ARRAY-2D))

;; (defthm store-array-list-of-cons
;;   (equal (STORE-ARRAY-LIST REF-LIST (cons item CONTENTS-LIST) len type HEAP)
;;          (IF (ENDP REF-LIST)
;;              HEAP
;;              (STORE-ARRAY (CAR REF-LIST)
;;                           item
;;                           len type
;;                           (STORE-ARRAY-LIST (CDR REF-LIST)
;;                                             CONTENTS-LIST
;;                                             len type
;;                                             HEAP))))
;;   :hints (("Goal" :in-theory (enable store-array-list))))

;; (defthm store-array-list-when-consp
;;   (implies (consp ref-list)
;;            (equal (STORE-ARRAY-LIST REF-LIST CONTENTS-LIST len type HEAP)
;;                   (STORE-ARRAY (CAR REF-LIST)
;;                                (car contents-list)
;;                                len
;;                                type
;;                                (STORE-ARRAY-LIST (CDR REF-LIST)
;;                                                  (cdr CONTENTS-LIST)
;;                                                  len type
;;                                                  HEAP))))
;;   :hints (("Goal" :in-theory (enable store-array-list))))

;(in-theory (disable ARRAY-ELEM-2D-RECOLLAPSE))

;(in-theory (disable STORE-2D-ARRAY-ROW-RECOLLAPSE3))
;(in-theory (enable store-array))
(local (in-theory (enable car-becomes-nth-of-0))) ;todo

;; (defthm store-array-list-of-non-consp
;;   (implies (not (consp ref-list))
;;            (equal (store-array-list ref-list contents-list len type heap)
;;                   heap))
;;   :hints (("Goal" :in-theory (enable store-array-list))))

;(in-theory (disable STORE-2D-ARRAY-ROW-RECOLLAPSE))

;bozo think about whther i need both
(defthm not-equal-nth-when-not-memberp-cheap
  (implies (and (not (memberp a x))
                (natp n)
                (consp x))
           (equal (equal (nth n x) a)
                  (if (< n (len x)) nil (equal a nil))))
  :hints (("Goal" :in-theory (e/d (memberp nth) (nth-of-cdr))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil nil))))

(defthmd not-equal-nth-when-not-memberp-no-limit
  (implies (and (not (memberp a x))
                (natp n)
                (consp x))
           (equal (equal a (nth n x))
                  (if (< n (len x)) nil (equal a nil)))))

;(in-theory (enable array-elem-2d))


;; (defthm store-array-list-open-on-consp
;;   (implies (consp ref-list)
;;            (equal (STORE-ARRAY-LIST REF-LIST CONTENTS-LIST HEAP)
;;                   (STORE-ARRAY (CAR REF-LIST)
;;                                (CAR CONTENTS-LIST)
;;                                (STORE-ARRAY-LIST (CDR REF-LIST)
;;                                                  (CDR CONTENTS-LIST)
;;                                                  HEAP))))
;;   :hints (("Goal" :in-theory (enable store-array-list))))

;(in-theory (enable list::len-of-cdr))

;; (defthm s-of-s-becomes-set-field
;;   (equal (S ad (cons rentry rentries) heap)
;;          (set-field ad pair val (s ad obj heap))))

;(in-theory (disable (:executable-counterpart s))) ;why?

;; (thm
;;  (implies (and (natp m)
;;                (natp n)
;;                (equal n (+ 1 m)))
;;           (equal (set::insert (nth-new-ad m dom) (set::insert (nth-new-ad n dom) set))
;;                  (set::union (new-ads-slice m n dom)
;;                              set)))
;;  :hints (("Goal" :in-theory (enable new-ads-slice))))



;; (skip -proofs
;;  (defthm array-ref-listp-byte-case-when-dims-nil-better
;;    (equal (array-ref-listp ref-list items-left nil ':byte heap)
;;           (and (equal items-left (len ref-list))
;;                (byte-p-list2 ref-list)))
;;    :hints (("Goal" ;:expand (array-ref-listp ref-list items-left nil :byte heap)
;;             :do-not '(generalize eliminate-destructors)

;;             :expand (
;;                      (ARRAY-REF-LISTP REF-LIST ITEMS-LEFT NIL ':BYTE HEAP)
;;                      )
;;             :in-theory (e/d (array-ref-listp) (array-ref-listp-byte-case-when-dims-nil))
;;             ))))


;(in-theory (disable jvm::initialize-one-dim-array)) ;fixme move

;; (defthm integerp-nth-from-byte-p-list
;;   (implies (and (byte-p-list lst)
;;                 (< n (len lst))
;;                 (<= 0 n)
;;                 )
;;            (integerp (nth n lst)))
;;   :hints (("Goal" :in-theory (e/d (byte-p-list ;len
;;                                    nth)
;;                                   (CONSP-WHEN-LEN-EQUAL ;investigate this loop
;;                                    ;why should acl2 simplify the rhs of a hypothesis when there's a free var?
;;                                    nth-of-cdr
;;                                    list::len-of-cdr)))))


;; (defthm get-field-of-store-array-2d
;;   (implies (not (memberp pair '(("ARRAY" . "contents") ;("ARRAY" . "length")
;;                                       )))
;;            (equal (get-field ref pair (store-array-2d ref2 contents numrows rowsize type heap))
;;                   (get-field ref pair heap)))
;;   :hints (("Goal" :in-theory (enable store-array-2d))))

;; ;bozo should store-array-2d len-fix the contents of the outer array?

;; (defthm rkeys-of-store-array-list
;;   (implies (not (zp rowsize)) ;(natp rowsize) ;t;
;;            (equal (rkeys (store-array-list refs contents rowsize type heap))
;;                   (set::union (list::2set refs) (rkeys heap))))
;;   :hints (("Goal" :in-theory (e/d (store-array-list) (set::double-containment)))))

;; (defthm rkeys-of-store-array-2d
;;   (implies (not (zp rowsize))
;;            (equal (rkeys (store-array-2d REF CONTENTS NUMROWS ROWSIZE TYPE HEAP))
;;                   (set::union (list::2set (TAKE NUMROWS (ARRAY-CONTENTS REF HEAP)))
;;                               (rkeys heap))))
;;  :hints (("Goal" :in-theory (enable store-array-2d))))



;; (defthm get-field-of-store-array-2d-irrel
;;   (implies (not (memberp ad2 (take numrows (array-contents ad heap))))
;;            (equal (GET-FIELD ad2 pair (STORE-ARRAY-2D ad CONTENTS NUMROWS ROWSIZE TYPE HEAP))
;;                   (GET-FIELD ad2 pair HEAP)))
;;   :hints (("Goal" :in-theory (enable store-array-2d))))

;(in-theory (disable array-contents))

;; (defthm get-field-contents-of-initialize-2d-array-same
;;   (equal (get-field ad (array-contents-pair) (jvm::initialize-2d-array ad type numrows numcols heap))
;;          (n-new-ads numrows (set::insert ad (rkeys heap))) ;rephrase using new-ads-slice?
;;          )
;;   :hints (("Goal" :in-theory (enable jvm::initialize-2d-array))))

;; (defthm rkeys-of-initialize-2d-array-same
;;   (implies (and (not (zp numrows)) ;drop?
;;                 (member-equal type '(:byte :int))) ;bozo
;;            (equal (rkeys (jvm::initialize-2d-array ad type numrows numcols heap))
;;                   (SET::UNION (LIST::|2SET| (N-NEW-ADS NUMROWS (SET::INSERT AD (RKEYS HEAP))))
;;                               (SET::INSERT AD (RKEYS HEAP)))))
;;   :hints (("Goal" :in-theory (e/d (jvm::initialize-2d-array ;JVM::INITIALIZE-ONE-DIM-ARRAY
;;                                    LIST::2SET
;;                                      ) (SET::DELETE-INSERT-CANCEL
;; ;                                        N-NEW-ADS-BECOMES-N-NEW-ADS2
;; )))))

;; (defthm get-field-of-INITIALIZE-2D-ARRAY-irrel
;;   (implies (and (not (equal ad ad2))
;;                 (not (memberp ad (N-NEW-ADS NUMROWS (SET::INSERT AD2 (RKEYS HEAP))))))
;;            (equal (GET-FIELD ad pair (JVM::INITIALIZE-2D-ARRAY ad2 type numrows cols heap))
;;                   (GET-FIELD ad pair heap)))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-2d-array ;JVM::INITIALIZE-ONE-DIM-ARRAY
;;                                      ))))



;; (defthm ARRAY-REF-LISTP-of-initialize-one-dim-arrays-irrel-single-dim
;;   (implies (and ;(integerp numcols)
;;             (JVM::INTP NUMCOLS) ;yuck?
;;             (no-duplicatesp-equal ads)
;;             (<= 0 numcols)
;;             (memberp type '(:byte :int :boolean)))
;;            (ARRAY-REF-LISTP ads (LIST NUMCOLS) type (JVM::INITIALIZE-ONE-DIM-ARRAYS ads type NUMCOLS heap)))
;;   :hints (("Goal" :in-theory (enable JVM::INITIALIZE-ONE-DIM-ARRAYS))))

;; ;yikes - backchains to a bag fact...
;; (defthmd nth-0-not-memberp-of-cdr
;;   (implies (and (consp ads)
;;                 (no-duplicatesp-equal ads))
;;            (equal (memberp (nth '0 ads) (cdr ads))
;;                   nil))
;;   :hints (("Goal" :in-theory (enable no-duplicatesp-equal))))

;; (defthm g-of-store-array-list-irrel
;;   (implies (not (memberp ad ads))
;;            (equal (g ad (store-array-list ads contents len type heap))
;;                   (g ad heap)))
;;   :hints (("Goal" :in-theory (enable store-array-list))))




;; (defthm array-ref-listp-of-store-array-list
;;   (implies (and (INTEGERP NUMCOLS)
;;                 (no-duplicatesp-equal ads)
;;                 (ARRAY-REF-LISTP ads
;;                                  (LIST NUMCOLS)
;;                                  ':BYTE
;;                                  HEAP))
;;            (ARRAY-REF-LISTP ads
;;                             (LIST NUMCOLS)
;;                             ':BYTE
;;                             (STORE-ARRAY-LIST ads
;;                                               CONTENTS NUMCOLS ':BYTE
;;                                               HEAP)))
;;   :hints (("Goal" :induct (double-cdr-induct ads contents)
;;            :in-theory (enable))))

;; ;bozo allow ads to differ
;; (defthm array-refp-of-store-array-2d
;;   (implies (and (array-refp ad (list numrows numcols) ':byte heap)
;;                 (not (zp numcols))
;;                 (not (memberp ad (array-contents ad heap))))
;;            (array-refp ad (list numrows numcols) ':byte (store-array-2d ad contents numrows numcols ':byte heap)))
;;   :hints (("Goal" :expand ((ARRAY-REFP-AUX AD (LIST NUMROWS NUMCOLS)
;;                                            ':BYTE
;;                                            HEAP NIL)
;;                            (array-refp-aux ad (list numrows numcols)
;;                                            ':byte
;;                                            (store-array-list (take numrows
;;                                                                        (get-field ad (array-contents-pair)
;;                                                                                   heap))
;;                                                              contents numcols ':byte
;;                                                              heap)
;;                                            nil))
;;            :in-theory (e/d (store-array-2d) (SET::PICK-A-POINT-SUBSET-STRATEGY
;;                                              TAKE-WHEN-<=-OF-LEN)))))

(in-theory (disable all-true-listp))

;; (defthm STORE-ARRAY-of-set-field-diff
;;   (implies (not (equal ad ad2))
;;            (equal (STORE-ARRAY ad contents COLS TYPE (SET-FIELD AD2 PAIR VAL heap))
;;                   (SET-FIELD AD2 PAIR VAL (STORE-ARRAY ad contents COLS TYPE heap)))))

;; (defthm STORE-ARRAY-list-of-set-field-diff
;;   (implies (not (memberp ad ads))
;;            (equal (STORE-ARRAY-LIST ads CONTENTS COLS TYPE (SET-FIELD AD PAIR VAL HEAP))
;;                   (SET-FIELD AD PAIR VAL (STORE-ARRAY-LIST ads CONTENTS COLS TYPE HEAP))))
;;   :hints (("Goal" :in-theory (e/d (STORE-ARRAY-LIST) (store-array)))))

;; (defthm STORE-ARRAY-2D-of-set-field
;;  (implies (and (not (equal ad ad2))
;;                (equal rows (len (array-contents ad heap)))
;;                (not (memberp ad2 (array-contents ad heap))))
;;           (equal (STORE-ARRAY-2D ad contents rows cols type (SET-FIELD ad2 pair val heap))
;;                  (SET-FIELD ad2 pair val (STORE-ARRAY-2D ad contents rows cols type heap)))
;;           )
;;  :hints (("Goal" :in-theory (enable STORE-ARRAY-2D))))


;; (defthm g-of-store-array-2d-irrel
;;   (implies (not (memberp ad2 (take rows (array-contents ad heap))))
;;            (equal (G ad2 (STORE-ARRAY-2D ad contents rows cols  ':BYTE heap))
;;                   (G ad2 heap)))
;;   :hints (("Goal" :in-theory (enable STORE-ARRAY-2D))))



;; (defthm g-of-initialize-one-dim-arrays-irrel
;;   (implies (not (memberp ad ads))
;;            (equal (g ad (jvm::initialize-one-dim-arrays ads type contents heap))
;;                   (g ad heap)))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-one-dim-arrays))))

;; (defthm g-of-INITIALIZE-2D-ARRAY
;;   (implies (and (not (equal ad ad2))
;;                 (not (memberp ad (N-NEW-ADS ROWS (SET::INSERT AD2 (RKEYS HEAP))))))
;;            (equal (G ad (JVM::INITIALIZE-2D-ARRAY ad2 type rows cols heap))
;;                   (G ad heap)))
;;   :hints (("Goal" :in-theory (enable JVM::INITIALIZE-2D-ARRAY))))


;bozo add this fact to array-refp?
;; (thm
;;  (implies ..
;;           (not (equal ad (NTH '0 (GET-FIELD ad (array-contents-pair) (JVM::HEAP S0)))))))



;; (thm
;;  (equal (CLEAR-FIELD ref (array-contents-pair) (STORE-ARRAY-LIST ref-lst vals len type heap))
;;         (STORE-ARRAY-LIST ref-lst vals len type heap))
;;  )


;better strategy.  prove lemma about clear-field-contents of store array (it clears out the contents)
;then prove that store array with all nil contents is the same as the clears?
;
;BOZO!
;; (defthm big-hack-4-clear-fields-of-store-array-2d
;;   (implies (equal (GET-FIELD ad (array-contents-pair) heap)
;;                   (GET-FIELD ad (array-contents-pair) heap2))
;;            (equal (CLEAR-FIELD
;;                    (NTH 0
;;                         (GET-FIELD ad
;;                                    (array-contents-pair) heap))
;;                    (array-contents-pair)
;;                    (CLEAR-FIELD
;;                     (NTH 1
;;                          (GET-FIELD ad
;;                                     (array-contents-pair)
;;                                     heap))
;;                     (array-contents-pair)
;;                     (CLEAR-FIELD
;;                      (NTH 2
;;                           (GET-FIELD ad
;;                                      (array-contents-pair)
;;                                      heap))
;;                      (array-contents-pair)
;;                      (CLEAR-FIELD
;;                       (NTH 3
;;                            (GET-FIELD ad
;;                                       (array-contents-pair)
;;                                       heap))
;;                       (array-contents-pair)
;;                       (STORE-ARRAY-2D
;;                        ad
;;                        contents
;;                        4 4 ':BYTE
;;                        heap2)))))
;;                   (CLEAR-FIELD
;;                    (NTH 0
;;                         (GET-FIELD ad
;;                                    (array-contents-pair)
;;                                    heap))
;;                    (array-contents-pair)
;;                    (CLEAR-FIELD
;;                     (NTH 1
;;                          (GET-FIELD ad
;;                                     (array-contents-pair)
;;                                     heap))
;;                     (array-contents-pair)
;;                     (CLEAR-FIELD
;;                      (NTH 2
;;                           (GET-FIELD ad
;;                                      (array-contents-pair)
;;                                      heap))
;;                      (array-contents-pair)
;;                      (CLEAR-FIELD
;;                       (NTH 3
;;                            (GET-FIELD ad
;;                                       (array-contents-pair)
;;                                       heap))
;;                       (array-contents-pair)
;;                       heap2))))))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand ((:free (REF-LIST CONTENTS-LIST LEN TYPE HEAP)
;;                            (STORE-ARRAY-LIST REF-LIST CONTENTS-LIST LEN TYPE HEAP))
;;                     (STORE-ARRAY-2D
;;                             ad
;;                             contents
;;                             4 4 ':BYTE
;;                             heap2)))))



;; (thm
;;  (implies (memberp ad2 (GET-FIELD ad (array-contents-pair) HEAP))
;;           (equal (ARRAY-CONTENTS2 ad (SET-FIELD ad2 (array-contents-pair) val heap2))
;;                  (update-nth (find-index ad2 (GET-FIELD ad (array-contents-pair) HEAP))
;;                              val
;;                              (ARRAY-CONTENTS2 ad heap2))))
;;  :hints (("Goal" :in-theory (enable ARRAY-CONTENTS2))))



;; ;bbozo gen
;; (defthm 2d-array-type-lemma
;;   (implies (and (array-refp ref (list dim1 dim2) ':byte heap)
;;                 (< 0 dim1))
;;            (equal (get-field (nth '0 (get-field ref (array-contents-pair) heap)) (array-type-pair) heap)
;;                   ':byte))
;;   :hints (("Goal" :expand ((array-refp ref (list dim1 dim2) ':byte heap)))))







;; (defthm array-row-of-store-array-2d-same
;;   (implies (and (not (memberp ref (get-field ref (array-contents-pair) heap)))
;;                 (no-duplicatesp-equal (GET-FIELD REF (array-contents-pair) HEAP))
;;                 (equal numrows (len (get-field ref (array-contents-pair) heap)))
;;                 (natp n)
;;                 (natp numrows)
;;                 (< n numrows)
;;                 (natp numcols)
;;                 )
;;            (equal (array-row n ref (store-array-2d ref contents numrows numcols ':byte heap))
;;                   (bvchop-list 8 ;byte-fix-list
;;                                 (take numcols (nth n contents)))))
;;   :hints (("Goal" :in-theory (e/d (array-row) ( store-array-list-when-consp array-row-recollapse))
;; ;          :expand (store-array-2d ref contents numrows '4 ':byte heap)
;;            )))





;; (defthm array-refp-of-store-array-2d-irrel
;;   (implies (and (not (equal ref1 ref2)) ;drop?
;;                 (equal numrows (len (array-contents ref2 heap)))
;;                 (memberp type '(:byte :int :boolean))
;;                 (natp numcols)
;;                 (equal 4 numcols) ;BBOZO
;;                 (not (memberp ref1 (array-contents ref2 heap))))
;;            (equal (array-refp ref1 (cons dim nil) type (store-array-2d ref2 contents numrows numcols type heap))
;;                   (array-refp ref1 (cons dim nil) type heap)))
;;   :hints (("Goal" :in-theory (e/d (;array-refp
;;                               ) (TAKE-WHEN-<=-OF-LEN)))))

;; ;this will match constant dims like '(16)
;; (defthm get-field-type-from-array-refp-better
;;   (implies (and (array-refp ref dims type heap)
;;                 (equal 1 (len dims)) ;gen?
;;                 (true-listp dims)
;;                 )
;;            (equal (GET-FIELD ref (array-type-pair) HEAP)
;;                   type))
;;   :hints (("Goal" :use (:instance get-field-type-from-array-refp (dim (car dims))))))



;; (thm
;;  (implies (and (true-listp lst)
;; ;               (natp n)
;;  ;              (< 0 n)
;;                (natp start)
;;                (natp end)
;;                (<= start end)

;; ;               (equal (len lst) (+ 1 end (- start)))
;;                )
;;           (equal (update-subrange start end vals lst)
;;                  (append (firstn start lst)
;;                          vals
;;                          (nthcdr end lst))
;;                  ))
;;  :hints (("Goal" :in-theory (enable UPDATE-SUBRANGE))))

;; (thm
;;  (implies (and (true-listp lst)
;;                (equal 4 (len lst)))
;;           (equal (UPDATE-SUBRANGE 0 3 vals lst)
;;                  vals)))


;; (defthm sbp32-of-array-elem-2d
;;   (implies (and; (items-have-len free a)
;;                 (intp-list-list a)
;;                 (natp n)
;;                 (< m (len a))
;;                 (natp m)
;;                 (> (LEN (NTH M A)) N)
;;                 )
;;            (signed-byte-p 32 (ARRAY-ELEM-2D m n A)))
;;   :hints (("Goal" :use (:instance intP-NTH-FROM-intP-LIST (lst (NTH M A)))
;;            :in-theory (e/d (ARRAY-ELEM-2D) ( ARRAY-ELEM-2D-RECOLLAPSE SIGNED-BYTE-P-NTH-FROM-BYTE-P-LIST NTH-OF-ARRAY-ROW)))))

;; (defthm sbp32-of-array-elem-2d-gen
;;   (implies (and; (items-have-len free a)
;;             (natp k)
;;             (<= 32 k)
;;                 (intp-list-list a)
;;                 (natp n)
;;                 (< m (len a))
;;                 (natp m)
;;                 (> (LEN (NTH M A)) N)
;;                 )
;;            (signed-byte-p k (ARRAY-ELEM-2D m n A)))
;;   :hints (("Goal" :use (:instance sbp32-of-array-elem-2d)
;;            :in-theory (disable sbp32-of-array-elem-2d))))



;these match the ones in books/arithmetic-3/bind-free/building-blocks.lisp



;; (thm
;;  (or (equal nil (signed-term-size term))
;;      (natp (signed-term-size term))))

;; (defun bind-newsize-to-termsize (x)
;;   (let ((newsize (signed-term-size x)))
;;     (if (natp newsize)
;;         (acons 'newsize (list 'quote newsize) nil)
;;       nil)))

;; (defthm slogxor-tighten
;;   (implies (and (bind-free (bind-newsize-to-termsize x) (newsize))
;;                 (< newsize oldsize)
;;                 (natp newsize)
;;                 (natp oldsize)
;;                 (signed-byte-p newsize x)
;;                 (signed-byte-p newsize y))
;;            (equal (slogxor oldsize x y)
;;                   (slogxor newsize x y)))
;;   :hints (("Goal" :in-theory (enable slogxor))))

;; (defthm slogxor-tighten-alt
;;   (implies (and (bind-free (bind-newsize-to-termsize y) (newsize))
;;                 (< newsize oldsize)
;;                 (natp newsize)
;;                 (natp oldsize)
;;                 (signed-byte-p newsize x)
;;                 (signed-byte-p newsize y))
;;            (equal (slogxor oldsize x y)
;;                   (slogxor newsize x y)))
;;   :hints (("Goal" :in-theory (enable slogxor))))


;; loop:
;; start with (equal 0 (logext 32 (hide x)))
;; try to apply ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1
;; so go show (signed-byte-p 1 (logext 32 (hide x))
;; but this backchains to (unsigned-byte-p 0 (logext 32 (hide x)))
;; which rewrites to (equal 0 (logext 32 (hide x)))




;; (defthm s-bit-equal-0-rewrite
;;   (equal (EQUAL (S-BIT n x) 0)
;;          (equal (getbit n x) 0))
;;   :hints (("Goal" :in-theory (enable getbit slice s-bit))))

;; (defthm s-bit-equal-0-rewrite2
;;   (equal (equal (s-bit n x) -1)
;;          (equal (getbit n x) 1))
;;   :hints (("Goal" :in-theory (enable getbit slice s-bit))))

;; (defthmd slogxor-of-bvchop
;;   (implies (and (integerp x)
;;                 (integerp size)
;;                 (< 0 size))
;;            (equal (slogxor size (bvchop size x) y)
;;                   (slogxor size x y)))
;;   :hints (("Goal" :in-theory (enable slogxor))))

;; (defthmd slogxor-of-bvchop2
;;   (implies (and (integerp x)
;;                 (integerp size)
;;                 (< 0 size))
;;            (equal (slogxor size y (bvchop size x))
;;                   (slogxor size x y)))
;;   :hints (("Goal" :in-theory (enable slogxor))))


;; ;plus? mult?
;; (defun term-needs-to-be-bvchopified (y)
;;   (if (not (consp y))
;;       t ;BBOZO make sure we don't then drop  the bvchop...
;;     (if (quotep y)
;;         (< (unquote y) 0)
;;       (if (and (equal 'logext (car y))
;;                ;test the size param?
;;                )
;;           t
;;         (if (member-equal (car y) '(slogxor))
;;             (or (term-needs-to-be-bvchopified (farg1 y))
;;                 (term-needs-to-be-bvchopified (farg2 y)))
;;           (if (equal 'logapp (car y))
;;               (term-needs-to-be-bvchopified (farg3 y))
;;             nil
;; ;;             (if (equal 'jvm::xshr (car y)) ;;deprecate
;; ;;                 (term-needs-to-be-bvchopified (farg1 y))
;; ;;               nil)
;;             ))))))


;; (skip -proofs
;;  (defthm byte-fix-becomes-logext
;;    (equal (jvm::byte-fix x)
;;           (logext 8 x))
;;    :otf-flg t
;;    :hints (("Goal" :in-theory (enable JVM::BYTE-FIX jvm::s-fix)))))

;; (skip -proofs
;;  (defthm int-fix-becomes-logext
;;    (equal (jvm::int-fix x)
;;           (logext 32 x))))

;; (skip -proofs
;; (defthm logand-minus128-of-logext-8
;;    (equal (LOGAND '-128 (LOGEXT '8 x))
;;           (LOGAND '-128 x))
;;    :hints (("Goal" :in-theory (enable logext logand)))))

;; (skip -proofs
;;  (defthm logand-minus64-of-logext-7
;;    (equal (LOGAND '-64 (LOGEXT 7 x))
;;           (LOGAND '-64 x))))

;; (skip -proofs
;;  (defthm logand-minus64-of-logext-6
;;    (equal (LOGAND '-32 (LOGEXT 6 x))
;;           (LOGAND '-32 x))))

;; (skip -proofs
;;  (defthm logand-minus64-of-logext-5
;;    (equal (LOGAND '-16 (LOGEXT 5 x))
;;           (LOGAND '-16 x))))

;; (skip -proofs
;;  (defthm logand-minus64-of-logext-4
;;    (equal (LOGAND '-8 (LOGEXT 4 x))
;;           (LOGAND '-8 x))))

;; (skip -proofs
;;  (defthm logand-minus64-of-logext-3
;;    (equal (LOGAND '-4 (LOGEXT 3 x))
;;           (LOGAND '-4 x))))

;; (skip -proofs
;;  (defthm logext-shl-1
;;    (implies (and (integerp n)
;;                  (< 1 n) ;gen?
;;                  )
;;             (equal (logext n (jvm::shl x 1))
;;                    (jvm::shl (logext (+ -1 n) x) 1)))
;;    :hints (("Goal" :in-theory (enable bvchop jvm::shl logext)))))

;; (skip -proofs
;;  (defthm logand-even-of-shl-1
;;    (implies (evenp k)
;;             (equal (binary-logand k (jvm::shl x 1))
;;                    (jvm::shl (binary-logand (/ k 2) x) 1)))
;;    :hints (("Goal" :in-theory (enable jvm::shl LOGAND)))))

;; ;trying without these

;; (skip -proofs
;;  (defthm logand-hack
;;    (implies (signed-byte-p 8 a)
;;             (equal (logand -128 a)
;;                    (logapp 7 0 (s-bit 7 a))))
;;    :hints (("Goal" :in-theory (enable
;;                                       logext)))))

;; ;; (skip -proofs
;; ;;  (defthm logand-hack7
;; ;;    (implies (signed-byte-p 7 a)
;; ;;             (equal (logand -64 a)
;; ;;                    (logapp 6 0 (s-bit 6 a))))
;; ;;    :hints (("Goal" :in-theory (enable
;; ;;                                       logext)))))

;; (skip -proofs
;;  (defthm logand-hack6
;;    (implies (signed-byte-p 6 a)
;;             (equal (logand -32 a)
;;                    (logapp 5 0 (s-bit 5 a))))
;;    :hints (("Goal" :in-theory (enable
;;                                logext)))))

;; (skip -proofs
;;  (defthm logand-hack5
;;    (implies (signed-byte-p 5 a)
;;             (equal (logand -16 a)
;;                    (logapp 4 0 (s-bit 4 a))))
;;    :hints (("Goal" :in-theory (enable
;;                                logext)))))

;; (skip -proofs
;;  (defthmd s-shl-becomes-logapp
;;    (implies (integerp x)
;;             (equal (jvm::s-shl x 1)
;;                    (logapp 1 0 (logext 31 x))))
;;    :hints (("Goal" :in-theory (enable logapp jvm::s-shl)))))

;; (skip -proofs
;;  (defthm s-bit-of-logxor
;;    (implies (and (integerp x)
;;                  (integerp y)
;;                  (natp n)
;;                  )
;;             (equal (s-bit n (logxor x y))
;;                    (logxor (s-bit n x) (s-bit n y))))
;;    :hints (("Goal" :in-theory (enable s-bit)))))

;; (skip -proofs
;;  (defthm s-bit-of-logapp
;;    (implies (and (integerp k)
;;                  (< 0 k))
;;             (equal (s-bit k (logapp 1 0 x))
;;                    (s-bit (+ -1 k) x)))
;;    :hints (("Goal" :in-theory (enable logapp s-bit)))))

;; (skip -proofs
;;  (defthm hack
;;    (implies (and (natp n)
;;                  (<= 1 n))
;;             (equal (jvm::xshr (logext n x) 1)
;;                    (logext (+ -1 n) (jvm::xshr x 1))))
;;    :hints (("Goal" :in-theory (enable jvm::xshr logext)))))

;; (skip -proofs
;;  (defthm hack222
;;    (implies (and (natp n)
;;                  (<= 1 n))
;;             (equal (jvm::xshr (bvchop n x) 1)
;;                    (bvchop (+ -1 n) (jvm::xshr x 1))))
;;    :hints (("Goal" :in-theory (enable jvm::xshr bvchop)))))

;; (skip -proofs
;;  (defthm hack3
;;    (implies (and (natp x)
;;                  (< 1 n)
;;                  (natp n))
;;             (equal (LOGEXT n (BINARY-* '2 x))
;;                    (* 2 (logext (+ -1 n) x))))))



;; (defthm sbp-8-logext-7-1
;;  (implies (and (integerp b)
;; ;               (integerp k)
;;  ;              (<= 8 k)
;;                )
;;           (SIGNED-BYTE-P 8 (JVM::SHL (LOGEXT 7 B) 1)))
;;  :hints (("Goal" :in-theory (enable LOGEXT jvm::shl SIGNED-BYTE-P))))

;; ;bozo clean up this series into 1 rule
;; (defthm sbp-8-shl-1
;;   (implies (and (integerp b)
;;                 (signed-byte-p 7 x)
;;                 )
;;            (SIGNED-BYTE-P 8 (JVM::SHL x 1)))
;;   :hints (("Goal" :in-theory (enable LOGEXT jvm::shl SIGNED-BYTE-P))))

;; (defthm sbp-7-shl-1
;;   (implies (and (integerp b)
;;                 (signed-byte-p 6 x)
;;                 )
;;            (SIGNED-BYTE-P 7 (JVM::SHL x 1)))
;;   :hints (("Goal" :in-theory (enable LOGEXT jvm::shl SIGNED-BYTE-P))))

;; (defthm sbp-6-shl-1
;;   (implies (and (integerp b)
;;                 (signed-byte-p 5 x)
;;                 )
;;            (SIGNED-BYTE-P 6 (JVM::SHL x 1)))
;;   :hints (("Goal" :in-theory (enable LOGEXT jvm::shl SIGNED-BYTE-P))))

;; (defthm sbp-5-shl-1
;;   (implies (and (integerp b)
;;                 (signed-byte-p 4 x)
;;                 )
;;            (SIGNED-BYTE-P 5 (JVM::SHL x 1)))
;;   :hints (("Goal" :in-theory (enable LOGEXT jvm::shl SIGNED-BYTE-P))))

;; (defthm sbp-4-shl-1
;;   (implies (and (integerp b)
;;                 (signed-byte-p 3 x)
;;                 )
;;            (SIGNED-BYTE-P 4 (JVM::SHL x 1)))
;;   :hints (("Goal" :in-theory (enable LOGEXT jvm::shl SIGNED-BYTE-P))))

;; (defthm sbp-3-shl-1
;;   (implies (and (integerp b)
;;                 (signed-byte-p 2 x)
;;                 )
;;            (SIGNED-BYTE-P 3 (JVM::SHL x 1)))
;;   :hints (("Goal" :in-theory (enable LOGEXT jvm::shl SIGNED-BYTE-P))))

;; (defthm sbp-2-shl-1
;;   (implies (and (integerp b)
;;                 (signed-byte-p 1 x)
;;                 )
;;            (SIGNED-BYTE-P 2 (JVM::SHL x 1)))
;;   :hints (("Goal" :in-theory (enable LOGEXT jvm::shl SIGNED-BYTE-P))))

;uncomment above


;; (DEFTHM INT-FIX-REWRITE-strong
;;   (IMPLIES t ;(INTEGERP X)
;;            (EQUAL (JVM::INT-FIX X) (LOGEXT 32 X)))
;;   :OTF-FLG T
;;   :HINTS (("Goal" :IN-THEORY (E/D (JVM::BYTE-FIX)
;;                                   (FLOOR-MOD-ELIM EVENP)))))

;; ;bozo redo shl so we can drop hyps?
;; (defthm integerp-shl
;;   (implies (and (integerp x)
;;                 (natp n))
;;            (integerp (jvm::shl x n)))
;;   :hints (("Goal" :in-theory (enable jvm::shl))))

;; logxor with 0

;; logand 255

;; logand with 1

;; byte-fix of shifts

;; (defthm shr-of-0
;;   (equal (logtail 0 x)
;;          (ifix x))
;;   :hints (("Goal" :in-theory (enable logtail floor))))

;; (defthm shr-of-0-forced
;;   (implies (force (integerp x))
;;            (equal (jvm::xshr x 0)
;;                   x))
;;   :hints (("Goal" :in-theory (enable ;jvm::xshr
;;                                      ))))

;; (defthm shr-of-sum
;;   (implies (and (integerp a)
;;                 (integerp b)
;;                 (integerp m)
;;                 (<= 0 m))
;;            (equal (jvm::xshr (+ a b) m)
;;                   (+ (jvm::xshr a m)
;;                      (jvm::xshr b m))))
;;   :hints (("Goal" :in-theory (enable jvm::xshr))))

;; (defthm shr-of-minus
;;   (implies (and (natp n)
;;                 (integerp x))
;;            (equal (jvm::xshr (- x) n)
;;                   (- (jvm::xshr x n))))
;;   :hints (("Goal" :in-theory (enable jvm::xshr))))

;; (defthm hack-7
;;   (IMPLIES (AND (NATP N)
;;                 (< 0 N)
;;                 (< 0 M)
;;                 (NATP M)
;;                 (INTEGERP X)
;;                 )
;;            (EQUAL (JVM::XSHR (- (EXPT 2 (+ -1 M N))) M)
;;                   (- (EXPT 2 (+ -1 N)))))
;;   :hints (("Goal" :in-theory (enable logtail ;jvm::xshr
;;                                      ))))

;; (defthm logapp-equal-0-rewrite
;;   (implies (integerp x)
;;            (equal (EQUAL (LOGAPP 7 0 x) 0)
;;                   (equal x 0)))
;;   :hints (("Goal" :in-theory (enable LOGAPP))))

;; (thm
;;  (equal (LOGEXT 32 (* 2 X))
;;         (* 2 (logext 31 x)))
;;  :hints (("Goal" :in-theory (enable logext logapp))))



;; (defthm shl-becomes-logapp
;;   (implies (integerp x)
;;            (equal (jvm::shl x 1)
;;                   (logapp 1 0 x)))
;;   :hints (("Goal" :in-theory (enable logapp jvm::shl))))



;; (thm
;;  (implies (and (integerp x)
;;                (integerp y))
;;           (equal (jvm::xshr (logxor x y) 5)
;;                  (logxor (jvm::xshr 5 x) (jvm::xshr 5 y))))
;;  :hints (("Goal" :in-theory (enable jvm::xshr))))



;; (defthm s-bit-of-myif
;;   (equal (s-bit n (myif test x1 x2))
;;          (myif test (s-bit n x1) (s-bit n x2)))
;;   :hints (("Goal" :in-theory (enable myif))))

;; ;unsigned...
;; ;drop or gen?
;; (defund nthbyte (n x)
;;   (bvchop 8 (logtail (* 8 n) x)))

;; (defthm nthbyte-0-rw
;;   (implies (integerp x)
;;            (equal (nthbyte 0 x)
;;                   (bvchop 8 x)))
;;   :hints (("Goal" :in-theory (enable nthbyte))))

;; (defthm nthbyte-1-rw
;;   (implies (integerp x)
;;            (equal (nthbyte 1 x)
;;                   (slice 15 8 x)))
;;   :hints (("Goal" :in-theory (enable nthbyte BVCHOP-OF-LOGTAIL-BECOMES-SLICE))))

;; (defthm nthbyte-2-rw
;;   (implies (integerp x)
;;            (equal (nthbyte 2 x)
;;                   (slice 23 16 x)))
;;   :hints (("Goal" :in-theory (enable nthbyte BVCHOP-OF-LOGTAIL-BECOMES-SLICE))))

;; (defthm nthbyte-3-rw
;;   (implies (integerp x)
;;            (equal (nthbyte 3 x)
;;                   (slice 31 24 x)))
;;   :hints (("Goal" :in-theory (enable nthbyte BVCHOP-OF-LOGTAIL-BECOMES-SLICE))))

;; (defthmd signed-byte-p-nth-from-byte-p-list-forced
;;   (implies (and (byte-p-list lst)
;;                 (force (< n (len lst)))
;;                 (<= 0 n))
;;            (signed-byte-p 8 (nth n lst)))
;;   :hints (("Goal" :in-theory (e/d (byte-p-list len nth)
;;                                   (list::len-of-cdr
;;                                    len-of-cdr-better
;;                                    nth-of-cdr)))))

;(in-theory (disable byte-p-list))

(theory-invariant (incompatible (:rewrite logatil-OF-LOGEXT-GEN) (:rewrite LOGEXT-OF-LOGTAIL)))

;(in-theory (disable S-SHL-BECOMES-LOGAPP-GEN))

;; (defthm integerp-of-array-elem-2d-gen
;;   (implies (and (intp-list-list a)
;;                 (natp n)
;;                 (< m (len a))
;;                 (natp m)
;;                 (< n (len (nth m a))))
;;            (integerp (array-elem-2d m n a)))
;;   :hints (("Goal" :use (:instance sbp32-of-array-elem-2d)
;;            :in-theory (disable sbp32-of-array-elem-2d SBP32-OF-ARRAY-ELEM-2D-GEN)))) ;kill one?

;; (defthm bvchop-of-sshr32
;;   (implies (and (natp n)
;;                 (natp shiftamt)
;;                 (<= 0 shiftamt)
;;                 (integerp x)
;;                 (< n 32))
;;            (equal (bvchop n (sshr 32 x shiftamt))
;;                   (slice (+ shiftamt n -1) shiftamt x)))
;;   :hints (("Goal" :in-theory (e/d ( sshr slice) (BVCHOP-OF-LOGTAIL-BECOMES-SLICE
;;                                                            LOGEXT-OF-LOGTAIL ;looped
;;                                                            LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE ;looped
;;                                                            )))))

;(in-theory (disable logtail-bvchop)) ;fixme

;; (defthm logext-of-sshr32
;;   (implies (and (natp n)
;;                 (< 0 n)
;;                 (<= n 32)
;;                 (natp shiftamt)
;;                 )
;;            (equal (logext n (sshr 32 x shiftamt))
;;                   (logext (+ n shiftamt (unary-- shiftamt))
;;                           (slice (binary-+ '-1 (binary-+ n shiftamt))
;;                                  shiftamt x))))
;;   :hints (("Goal" :in-theory (e/d ( sshr slice) (bvchop-of-logtail bvchop-of-logtail-becomes-slice
;;                                                                               LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))

;; ;use to prove the other one?
;; (defthm bvchop-of-sshr
;;   (implies (and (natp n)
;;                 (natp shiftamt)
;;                 (<= 0 shiftamt)
;;                 (integerp x)
;;                 (< n 32))
;;            (equal (bvchop n (sshr 32 x shiftamt))
;;                   (slice (+ shiftamt n -1) shiftamt x)))
;;   :hints (("Goal" :in-theory (e/d ( sshr slice) (bvchop-of-logtail-becomes-slice
;;                                                            LOGEXT-OF-LOGTAIL ;looped
;;                                                            LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE ;looped
;;                                                            )))))

;; (defthm logext-of-sshr
;;   (implies (and (natp n)
;;                 (< 0 n)
;;                 (<= n 32)
;;                 (natp shiftamt)
;;                 )
;;            (equal (logext n (sshr 32 x shiftamt))
;;                   (LOGEXT N
;;                           (SLICE (+ '-1 (+ N SHIFTAMT))
;;                                  SHIFTAMT X))
;;                   ;;(sslice (+ -1 n shiftamt) shiftamt x)
;;                   ))
;;   :hints (("Goal" :in-theory (e/d (slice  sshr) (BVCHOP-OF-LOGTAIL bvchop-of-logtail-becomes-slice
;;                                                                               ;loops:
;;                                                                               LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE)))))



;; ;bozo is this bad because of backchaining?
;; ;should we try to keep array-ref-listp, etc, closed up?
;; (defthm integerp-of-array-elem-2d2
;;   (implies (and (BYTE-P-LIST (ARRAY-ROW row ref heap))
;;                 (natp row)
;;                 (natp col)
;;                 (< col (len (ARRAY-ROW row ref heap)))
;;                 (< row (len (ARRAY-contents ref heap)))
;;                 )
;;            (integerp (ARRAY-ELEM-2D2 row col ref heap)))
;;   :hints (("Goal" :in-theory (e/d (ARRAY-ELEM-2D2 ARRAY-ELEM-2D)
;;                                   (ARRAY-ELEM-2D2-RECOLLAPSE ARRAY-ELEM-2D-recollapse NTH-OF-ARRAY-ROW)))))

;(local (in-theory (disable BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))

;; (encapsulate (((bytepstub *) => *))
;;              (local (defun bytepstub (x) (declare (ignore x)) 0))
;;              (defthm sbp8-of-bytepstub (signed-byte-p 8 (bytepstub x)))
;;              (defthm integerp-of-bytepstub (integerp (bytepstub x))))

;; (BVXOR '1
;;                          '1
;;                          (BVIF '1
;;                                 (EQUAL (GETBIT '7 (LOCALVAR '2 S0)) '0)
;;                                 (GETBIT '2 (LOCALVAR '2 S0))
;;                                 (BVXOR '1
;;                                          '1
;;                                          (GETBIT '2 (LOCALVAR '2 S0)))))

;; (thm
;;  (implies (and (<= (LEN x) 1)
;;                (true-listp x))
;;           (equal (cdr x)
;;                  (list::final-cdr nil))
;;  :hints (("Goal" :expand ((LEN X)
;;                           (LEN (CDR X)))
;;           :in-theory (e/d (len) (LIST::LEN-OF-CDR CONSP-CDR)))))

;; (defthm bvxor-convert-arg2-to-unsigned
;;   (implies (and (syntaxp (member-equal (car y) '(myif logext slogxor ;;slogand
;;                                                       slogior ;smyif ;logapp
;;                                                       )))
;;                 (integerp size)
;;                 (< 0 size)
;;                 (force (integerp x))
;;                 (force (integerp y))
;;                 )
;;            (equal (bvxor size x y)
;;                   (bvxor size x (bvchop size y))))
;;   :hints (("Goal" :in-theory (enable bvxor))))

;; (defthm bvxor-convert-arg1-to-unsigned
;;   (implies (and (syntaxp (member-equal (car x) '(myif logext slogxor ;;slogand
;;                                                       slogior ;smyif ;logapp
;;                                                       )))
;;                 (integerp size)
;;                 (< 0 size)
;;                 (force (integerp x))
;;                 (force (integerp y))
;;                 )
;;            (equal (bvxor size x y)
;;                   (bvxor size (bvchop size x) y)))
;;   :hints (("Goal" :in-theory (enable bvxor))))

;BOZO this may loop with bvchop-identity and other rules which drop the bvchop
;if the operator is anything other than our blessed unsigned functions (e.g., a signed op or a user function), add a bvchop
;i guess this counts variables too, which is good
;; (defthm bvcat-convert-arg2-to-unsigned
;;   (implies (and (syntaxp (member-equal (car highval) *signed-operators*))
;;                 (integerp highsize)
;;                 (< 0 highsize)
;;                 (force (integerp highval))
;; ;                (force (integerp y))
;;                 )
;;            (equal (bvcat highsize highval lowsize lowval)
;;                   (bvcat highsize (bvchop highsize highval) lowsize lowval)))
;;   :hints (("Goal" :in-theory (e/d (bvcat) ()))))

;; (thm
;;  (implies (and (unsigned-byte-p 1 x)
;;                (unsigned-byte-p 1 y))
;;           (equal (BVIF 1 (EQUAL y 0) x (BVNOT 1 x))
;;                  (bvxor 1 x y))))

;bozo BVCAT-COERCE-ARG2-TO-UNSIGNED vs. BVCAT-CONVERT-ARG2-TO-UNSIGNED

;; ;i wonder if this is faster, since the bvxor doesn't get rewritten (but might if we put in n in place of size?)
;; (defthm bvchop-of-bvxor-same
;;   (implies (and (equal n size) ;gen?
;;                 (natp n)
;;                 (integerp size)
;;                 (< 0 size))
;;            (equal (bvchop n (bvxor size a b))
;;                   (bvxor size a b)))
;;   :hints (("Goal" :in-theory (enable slogxor bvxor))))

;; (in-theory (disable bvchop-of-bvxor))
;; (in-theory (enable bvchop-of-bvxor-strict))

;; (defthm bvxor-convert-arg1-to-unsigned-better
;;   (implies (and (syntaxp; (and (not (quotep x)) ;bbbozo make this change everywhere
;;                 ;              (not (member-equal (car x) *blessed-unsigned-operators*)))
;;                  (member-equal (car x) *signed-operators*)
;;                 )
;;                 (integerp size)
;;                 (< 0 size)
;;                 (force (integerp x))
;;                 (force (integerp y))
;;                 )
;;            (equal (bvxor size x y)
;;                   (bvxor size (bvchop size x) y)))
;;   :hints (("Goal" :in-theory (e/d (bvxor
;;                                    ) ()))))

;; (defthm bvxor-convert-arg2-to-unsigned-better
;;   (implies (and (syntaxp; (and (not (quotep y))
;; ;              (not (member-equal (car y) *blessed-unsigned-operators*)))
;;                  (member-equal (car y) *signed-operators*)
;;                 )
;;                 (integerp size)
;;                 (< 0 size)
;;                 (force (integerp x))
;;                 (force (integerp y))
;;                 )
;;            (equal (bvxor size x y)
;;                   (bvxor size x (bvchop size y))))
;;   :hints (("Goal" :in-theory (e/d (bvxor
;;                                    ) ()))))

(local (in-theory (disable ;BVCHOP-LEQ
                   ;LOGTAIL-LEQ
                   )))

;should we break the tie between x and (lognot 1 x) when commuting bvxor's ops?

;; (defun strip-off-mynot-call (term)
;;   (if (and (consp term)
;;            (equal 'mynot (car term)))
;;       (farg1 term)
;;     term))

;; (defun smaller-xor-arg (term1 term2)
;;   (declare (xargs :mode :program))
;;   (smaller-termp (strip-off-mynot-call term1)
;;                 (strip-off-mynot-call term2)))

;; ;fffixme move or combine the xor functions!
;; (defthm xor-commutative
;;   (implies (syntaxp (smaller-xor-arg b a))
;;            (equal (xor a b)
;;                   (xor b a)))
;;   :rule-classes ((:rewrite :loop-stopper nil ;((a b xor))
;;                            ))
;;   :hints (("Goal" :in-theory (enable xor))))

;; ;move
;; (defthm xor-commutative-2
;;   (implies (and (syntaxp (smaller-xor-arg a b)))
;;            (equal (xor b (xor a c))
;;                   (xor a (xor b c))))
;;   :rule-classes ((:rewrite :loop-stopper nil))
;;   :hints (("Goal" :in-theory (enable xor))))

;BOZO replace getbit with logbit?

;(in-theory (disable BVNOT-OF-BVXOR-1))

;bozo looped
;; (defthm reorder-equal-getbit-0
;;   (equal (EQUAL (GETBIT n x) 0)
;;          (EQUAL 0 (GETBIT n x))))

;; ;problem with BVCHOP-1-BECOMES-GETBIT
;; (defthmd coerce-arg-of-getbit-to-unsigned
;;   (implies (and (syntaxp (term-is-signed x))
;;                 (natp size)
;;                 (integerp x))
;;            (equal (getbit size x)
;;                   (getbit size (bvchop (+ 1 size) x))))
;;   :hints (("Goal" :in-theory (e/d (getbit ;s-bit
;;                                    slice) (SLICE-BECOMES-BVCHOP
;;                                    BVCHOP-1-BECOMES-GETBIT
;;                                    slice-becomes-getbit)))))

;; (in-theory (disable BVCHOP-OF-LOGAPP-BIGGER ;BVCHOP-LOGAPP
;;                     ))

;; (in-theory (disable BVCAT-CONVERT-ARG2-TO-UNSIGNED))
;; (in-theory (disable BVXOR-CONVERT-ARG1-TO-UNSIGNED-BETTER))
;; (in-theory (disable BVXOR-CONVERT-ARG2-TO-UNSIGNED-BETTER))


;; (defthm integerp-of-array-elem-2d-gen-byte-version
;;    (implies (and (byte-p-list-list a)
;;                  (natp n)
;;                  (< m (len a))
;;                  (natp m)
;;                  (< n (len (nth m a))))
;;             (integerp (array-elem-2d m n a)))
;;    :hints (("Goal" :use (:instance sbp32-of-array-elem-2d)
;;             :in-theory (disable sbp32-of-array-elem-2d))))

;; (defthm integer-listp-backchain-to-byte-p-list
;;   (implies (and (byte-p-list x)
;;                 (true-listp x) ;bozo yuck, use a better version of integer-listp?
;;                 )
;;            (integer-listp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst (1 1)))
;;   :hints (("Goal" :in-theory (enable integer-listp byte-p-list))))


;; (in-theory (disable bvxor-convert-arg2-to-unsigned-better
;;                     bvxor-convert-arg1-to-unsigned-better
;;                     bvxor-convert-arg1-to-unsigned
;;                     bvxor-convert-arg2-to-unsigned
;;                     bvcat-convert-arg2-to-unsigned
;;                     ))

;; ;bozo gen
;; ;use trim
;; (defthm bvxor-of-bvcat-2
;;   (implies (and (natp size)
;; ;                (integerp x)
;;                 ;(integerp z)
;;                 )
;;            (equal (BVXOR size Z (bvcat SIZE2 Y size X))
;;                   (BVXOR size Z X)))
;;   :hints (("Goal" :cases ((integerp x))
;;            :in-theory (e/d (bvcat bvxor BVCHOP-LOGAPP) (LOGXOR-BVCHOP-BVCHOP)))))

;; (defthmd add-bvchop-to-bvcat-2
;;   (implies (and (syntaxp (and (not (quotep highval))
;;                               (not (member-equal (car highval) (append *blessed-unsigned-operators*
;;                                                                        *signed-operators* ;bozo drop this (here and elsewhere?)
;;                                                                        )))))
;;                 (natp size)
;;                 (natp lowsize)
;;                 (natp highsize)
;;                 )
;;            (equal (bvcat highsize highval lowsize lowval)
;;                   (bvcat highsize (bvchop highsize highval) lowsize lowval)))
;;   :hints (("Goal" :cases ((and (integerp lowval) (integerp highval))
;;                           (and (integerp lowval) (not (integerp highval)))
;;                           (and (not (integerp lowval)) (integerp highval)))
;;            :in-theory (e/d () ()))))

;; (defthmd add-bvchop-to-bvcat-1
;;   (implies (and (syntaxp (and (not (quotep lowval))
;;                               (not (member-equal (car lowval) (append *blessed-unsigned-operators*
;;                                                                       *signed-operators* ;bozo drop this (here and elsewhere?)
;;                                                                       )))))
;;                 (natp size)
;;                 (natp lowsize)
;;                 (natp highsize)
;;                 )
;;            (equal (bvcat highsize highval lowsize lowval)
;;                   (bvcat highsize highval lowsize (bvchop lowsize lowval))))
;;   :hints (("Goal" :cases ((and (integerp lowval) (integerp highval))
;;                           (and (integerp lowval) (not (integerp highval)))
;;                           (and (not (integerp lowval)) (integerp highval)))
;;            :in-theory (e/d () ()))))

;(in-theory (enable bvchop-logapp))

;; (thm
;;  (equal (getbit n (bvnot m x))
;;         (BVNOT 1 (getbit n x)))
;; :hints (("Goal" :in-theory (enable bvnot))))

;(in-theory (disable list::nth-of-cons))

(defthm nth-of-plus-constant
  (implies (and (syntaxp (quotep k))
                (< 0 k)
                (integerp k)
                (natp n))
           (equal (nth (+ k n) (cons a rst))
                  (nth (+ (+ -1 k) n) rst)))
  :hints (("Goal" :in-theory (e/d (nth) (nth-of-cdr)))))

;; (defund keep-every-nth (n lst)
;;   (if (or (endp lst)
;;           (zp n))
;;       nil
;;     (cons (car lst) (keep-every-nth n (nthcdr n lst)))))

;; (local
;;  (defun ind (m n lst)
;;    (if (or (endp lst)
;;            (zp n)
;;            (zp m))
;;        (list m n lst)
;;      (ind (- m 1) n (nthcdr n lst)))))

;; (defthm nth-times
;;   (implies (and (syntaxp (quotep n))
;;                 (natp n)
;;                 (< 0 n)
;;                 (natp m))
;;            (equal (nth (* n m) lst)
;;                   (nth m (keep-every-nth n lst))))
;;   :hints (("Goal" :induct (ind m n lst)
;;            :in-theory (enable keep-every-nth)
;;            :do-not '(generalize eliminate-destructors))))

;; ;BBOZO this is too special purpose!

;; (defthm keep-every-nth-4-lemma
;;   (equal (keep-every-nth 4 (cons a (cons b (cons c (cons d rst)))))
;;          (cons a (keep-every-nth 4 rst)))
;;   :hints (("Goal"
;;            :in-theory (enable ;LIST::NTHCDR-OF-CONS
;;                        )
;;            :expand ((keep-every-nth 4 (cons a (cons b (cons c (cons d rst)))))))))

(defthmd split-list-hack
  (implies (and (consp x)
                (true-listp x))
           (equal (append (take (+ -1 (len x)) x) (list (nth (+ -1 (len x)) x)))
                  x)))

;              (EQUAL (LIST (NTH (+ -1 (LEN X)) X))
;                     (NTHCDR (+ -1 (LEN X)) X))


(defthm perm-cons-last-to-rest
  (implies (and (true-listp x)
                (consp x))
           (perm (cons (nth (+ -1 (len x)) x)
                            (take (+ -1 (len x)) x))
                      x))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance split-list-hack)
           :in-theory (e/d ( ;PERM-OF-CONS PERM-BECOMES-TWO-SUBBAGP-CLAIMS
                            ) (;LIST::EQUAL-APPEND-REDUCTION!
                               ;;LIST::EQUAL-APPEND-REDUCTION!-ALT
                               )))))

;newly disabled:  move up!
;(in-theory (disable BAG::MEMBERP-SUBBAGP)) ;introduces bag reasoning!

(defthm memberp-of-cdr-when-not-memberp
  (implies (not (memberp x lst))
           (not (memberp x (cdr lst)))))

;(in-theory (disable LIST::FIX-OF-NTHCDR))

;; (defthm not-memberp-of-take
;;   (IMPLIES (and (NOT (MEMBERP X LST))
;;                 (<= n (len lst)))
;;            (NOT (MEMBERP X (TAKE n lst))))
;;   :hints (("Goal" :in-theory (enable take MEMBERP))))

;yuck, for this we need more hyps for the new firstn...
(defthm not-memberp-of-subrange
  (implies (and (not (memberp x lst))
                (natp end) ;new
                (< end (len lst)) ;new
;                (natp start)
                )
           (equal (memberp x (subrange start end lst))
                  nil))
  :hints (("Goal" :in-theory (e/d (subrange take)
                                  (;anti-subrange
                                   )))))

;todo: move
;; (defthm insert-nth-2set-subrange-adjacent
;;   (implies (and (natp start)
;;                 (natp end)
;;                 (equal n (+ -1 start))
;;                 (< 0 start)
;;                 (< end (len lst))
;;                 (<= start end)
;;                 )
;;            (equal (set::insert (nth n lst) (list::2set (subrange start end lst)))
;;                   (list::2set (subrange n end lst))))
;;   :hints (("Goal" :expand (TAKE (+ 2 END (- START))
;;                                     (NTHCDR (+ -1 START) LST))
;;            :in-theory (e/d (subrange list::2set) (anti-subrange)))))

;bozo gen
;do we even still need this?
;; (defthm clr-objects-of-store-array-2d-4-4
;;   (implies (and (equal (get-field ref (array-contents-pair) heap)
;;                        (get-field ref (array-contents-pair) heap2))
;;                 (ARRAY-REFP ref
;;                             '(4 4)
;;                             ':BYTE
;;                             heap))
;;            (equal (clr-objects (list::2set (true-list-fix (get-field ref (array-contents-pair) heap))) (store-array-2d ref vals 4 4 ':byte heap2))
;;                   (clr-objects (list::2set (true-list-fix (get-field ref (array-contents-pair) heap))) heap2)))
;;   :hints (("Goal" :in-theory (enable store-array-2d))))


;; ;BOZO gen this!
;; ;cipher proof used to work, this was required to fix it up after more rules were added
;; ;is this used?
;; (defthm copy-objects-of-store-array-2d-hack
;;   (implies (and (equal (GET-FIELD REF (array-contents-pair) HEAP)
;;                        (GET-FIELD REF (array-contents-pair) HEAP2))
;;                 (equal (GET-FIELD REF (array-contents-pair) HEAP)
;;                        (GET-FIELD REF (array-contents-pair) HEAP3))
;;                 (equal 4 (len (GET-FIELD REF (array-contents-pair) HEAP2)))
;;                 ;bozo added
;;                 (TRUE-LISTP (GET-FIELD REF (array-contents-pair) HEAP))
;;                 )
;;            (equal (copy-objects (list::2set (get-field ref (array-contents-pair) heap3))
;;                                 (store-array-2d ref vals 4 4 ':byte heap2)
;;                                 heap)
;;                   (store-array-2d ref vals 4 4 ':byte (copy-objects (list::2set (get-field ref (array-contents-pair) heap2)) heap2 heap))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :cases ((equal (GET-FIELD REF (array-contents-pair) HEAP)
;;                           (list (nth 0 (GET-FIELD REF (array-contents-pair) HEAP))
;;                                 (nth 1 (GET-FIELD REF (array-contents-pair) HEAP))
;;                                 (nth 2 (GET-FIELD REF (array-contents-pair) HEAP))
;;                                 (nth 3 (GET-FIELD REF (array-contents-pair) HEAP)))))
;;            :in-theory (enable store-array-2d CONS-OF-NTH-AND-NTH-PLUS-1))))


;bozo gen
(defthm oddp-9-tighten
  (implies (and (oddp x)
                (integerp x))
           (equal (< x 9)
                  (<= x 7))))

;bozo hope this doesn't loop
(defthm oddp-9-tighten2
  (implies (and (not (equal x 9))
                (oddp x)
                (integerp x))
           (equal (< 9 x)
                  (< 7 x))))

(defthm oddp-9-7-rule
  (implies (and (oddp x)
                (integerp x)
                (<= x 9)
                )
           (equal (< 7 x)
                  (equal x 9))))

;bozo hacky? expensive?
(defthm not-greater-than-255-when-usb8
  (implies (unsigned-byte-p 8 x)
           (not (< 255 x))))

;gen?
;expensive?
(defthm x-less-than-32-when-usb5
  (implies (unsigned-byte-p 5 x)
           (< x 32)))

;; (thm
;;  (implies (not (integerp x))
;;           (equal (LOGEXT 32 X)
;;                  0))
;;  :hints (("Goal" :in-theory (enable logext logbitp logapp))))

;; (thm
;;  (equal (BVOR 32 (LOGEXT 32 x) y)
;;         (BVOR 32 x y))
;;  :hints (("Goal" :cases ((integerp x))
;;           :in-theory (enable bvor))))

;; ;bozo lots more like this!
;; (defthm bvor-non-negative-tp
;;   (<= 0 (bvor size a b))
;;   :rule-classes (:type-prescription)
;;   :hints (("Goal" :in-theory (e/d (bvor)))))

;bozo move up
(in-theory (disable assoc-equal))

;bozo APPEND-TRUE-LISTP-TYPE-PRESCRIPTION vs. list::APPEND-TRUE-LISTP-TYPE-PRESCRIPTION

;i'm not sure match free has any effect here...

;; ;bozo quick and dirty
;; (defun all-vals-less-than-or-equal (k lst)
;;   (if (endp lst)
;;       t
;;     (and (<= (len (car lst)) k)
;;          (all-vals-less-than-or-equal k (cdr lst)))))

;; ;where we currently need this, k and alist are constants but i isn't
;; (defthm len-of-lookup-bound-hack
;;   (implies (and (all-vals-less-than-or-equal k (strip-cdrs alist))
;;                 (<= 0 k) ;(rationalp k)
;;                 )
;;            (not (< k (LEN (LOOKUP-equal i alist)))))
;;   :hints (("Goal" :in-theory (enable lookup-equal
;;                               ASSOC-EQUAL))))

;; (defthm use-old-equal-current-equality
;;   (implies (and (syntaxp (equal s1 's1))
;;                 ;i hope this matches! :
;;                 (hide (equal (localvar n s1) (localvar n s0))) ;s0 is a free variable
;;                 (syntaxp (equal s0 's0))
;;                 )
;;            (equal (localvar n s1)
;;                   (localvar n s0)))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-1-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 1 s0) (localvar 1 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 1 s1) (localvar 1 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-1-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 1 s1) (localvar 1 s0))
;;                   (hide (equal (localvar 1 s1) (localvar 1 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-2-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 2 s0) (localvar 2 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 2 s1) (localvar 2 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-2-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 2 s1) (localvar 2 s0))
;;                   (hide (equal (localvar 2 s1) (localvar 2 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-3-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 3 s0) (localvar 3 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 3 s1) (localvar 3 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-3-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 3 s1) (localvar 3 s0))
;;                   (hide (equal (localvar 3 s1) (localvar 3 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-4-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 4 s0) (localvar 4 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 4 s1) (localvar 4 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-4-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 4 s1) (localvar 4 s0))
;;                   (hide (equal (localvar 4 s1) (localvar 4 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))




;; ;crap.  the lets get expanded out before this is stored as a rule...
;; (defthm hide-of-let-bozo
;;   (equal (HIDE (LET ((X z) (Y w))
;;                     (EQUAL X Y)))
;;          (HIDE (EQUAL z w)))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; ;helps with substitution using an equality of the form (equal (getbit 0 x) blah).
;; (defthmd bvxor-1-add-getbit-arg1
;; ;BOZO the hyp is not likely to fire. get rid of this rule?
;;   (implies t;(not (unsigned-byte-p 1 x)) ;helps prevent loops (if it's just 1 bit, then we can substitute using (equal x blah) just fine without the getbit
;;            (equal (bvxor 1 x y)
;;                   (bvxor 1 (getbit 0 x) y)))
;;   :hints (("Goal" :in-theory (e/d (bvxor-1-of-getbit-arg1) ()))))

;; (theory-invariant (incompatible (:rewrite bvxor-1-of-getbit-arg1) (:rewrite bvxor-1-add-getbit-arg1)))

;drop?
(defthmd cddr-take-becomes-subrange
  (equal (cddr (take 32 x))
         (subrange 2 31 x))
  :hints (("Goal" :in-theory (e/d (subrange cdr-of-cdr-becomes-nthcdr)
                                  (;nthcdr-of-take
;anti-subrange
                                   )))))

;; (defthm hide-old-equal-current-equality-5-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 5 s0) (localvar 5 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 5 s1) (localvar 5 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-5-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 5 s1) (localvar 5 s0))
;;                   (hide (equal (localvar 5 s1) (localvar 5 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))


;; (defthm hide-old-equal-current-equality-6-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 6 s0) (localvar 6 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 6 s1) (localvar 6 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-6-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 6 s1) (localvar 6 s0))
;;                   (hide (equal (localvar 6 s1) (localvar 6 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-7-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 7 s0) (localvar 7 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 7 s1) (localvar 7 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-7-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 7 s1) (localvar 7 s0))
;;                   (hide (equal (localvar 7 s1) (localvar 7 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-8-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 8 s0) (localvar 8 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 8 s1) (localvar 8 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-8-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 8 s1) (localvar 8 s0))
;;                   (hide (equal (localvar 8 s1) (localvar 8 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-9-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 9 s0) (localvar 9 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 9 s1) (localvar 9 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-9-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 9 s1) (localvar 9 s0))
;;                   (hide (equal (localvar 9 s1) (localvar 9 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-0-1
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)
;;                          ))
;;            (equal (equal (localvar 0 s0) (localvar 0 s1))
;;                   ;;note the directionality of this:
;;                   (hide (equal (localvar 0 s1) (localvar 0 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; (defthm hide-old-equal-current-equality-0-2
;;   (implies (syntaxp (and (equal s0 's0)
;;                          (equal s1 's1)))
;;            (equal (equal (localvar 0 s1) (localvar 0 s0))
;;                   (hide (equal (localvar 0 s1) (localvar 0 s0)))))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))


;; ;BOZO why do we need this form (doesn't the s1 term always come first?)?
;; (defthm use-old-equal-current-equality-alt
;;   (implies (and (syntaxp (equal s1 's1))
;;                 ;i hope this matches! :
;;                 (hide (equal (localvar n s0) (localvar n s1))) ;s0 is a free variable
;;                 (syntaxp (equal s0 's0))
;;                 )
;;            (equal (localvar n s1)
;;                   (localvar n s0)))
;;   :hints (("Goal" :expand ((:free (x) (hide x))))))

;; ;bozo move these back?
;; (defmacro current (tag n)
;;   (declare (ignore tag))
;;   `(localvar ,n s1))

;; ;can we get rid of this?
;; (defmacro old (tag n)
;;   (declare (ignore tag))
;;   `(localvar ,n s0))

;; (defthm ARRAY-ELEM-2D-leibniz
;;   (implies (and (equal a1 a2)
;;                 (equal i1 i2)
;;                 (equal j1 j2))
;;            (equal (equal (ARRAY-ELEM-2D i1 j1 a1) (ARRAY-ELEM-2D i2 j2 a2))
;;                   t)))

;(in-theory (disable MEMBERP-OF-CONS)) ;causes case splits

;(in-theory (disable FLOOR-MOD-ELIM))

;FIXME the set package shouldn't import subsetp -- too easy to confuse


;ffixme tweak this now that the contents are being passed in
;; (defthm array-refp-of-initialize-one-dim-array
;;   (implies (and (unsigned-byte-p 31 (len contents))
;;                 (true-listp contents)
;;                 (memberp type '(:byte :int :boolean :short)))
;;            (array-refp ad (cons (len contents) nil) type (jvm::initialize-one-dim-array ad type contents heap)))
;;   :hints (("Goal" :in-theory (enable ;array-refp
;;                               memberp-of-cons))))





;BOZO is this okay? maybe we should just open up INITIALIZE-ONE-DIM-ARRAY?
;or redo it to be an s of a modified object?

;; (defthm clear-out-INITIALIZE-ONE-DIM-ARRAY
;;   (implies (and ;(has-expected-stuff-for-array ct)
;;                 ;(has-expected-stuff-for-object ct)
;;                 )
;;            (equal (CLEAR-FIELD
;;                    ad
;;                    (array-type-pair)
;;                    (CLEAR-FIELD
;;                      ad
;;                      (array-contents-pair)
;;                      (CLEAR-FIELD
;;                       ad
;;                       '(:SPECIAL-DATA . :CLASS)
;;                       (CLEAR-FIELD
;;                        ad
;;                        '("ARRAY" "<array>" . jvm::*ARRAY*)
;;                        (CLEAR-FIELD
;;                         ad
;;                         '("java.lang.Object" . "mcount")
;;                         (CLEAR-FIELD
;;                          ad
;;                          '("java.lang.Object" . "monitor")
;;                          (CLEAR-FIELD
;;                           ad
;;                           '("java.lang.Object" . "wait-set")
;;                           (JVM::INITIALIZE-ONE-DIM-ARRAY
;;                            ad
;;                            type len heap))))))))
;;                   (CLEAR-FIELD
;;                    ad
;;                    (array-type-pair)
;;                    (CLEAR-FIELD
;;                      ad
;;                      (array-contents-pair)
;;                      (CLEAR-FIELD
;;                       ad
;;                       '(:SPECIAL-DATA . :CLASS)
;;                       (CLEAR-FIELD
;;                        ad
;;                        '("ARRAY" "<array>" . jvm::*ARRAY*)
;;                        (CLEAR-FIELD
;;                         ad
;;                         '("java.lang.Object" . "mcount")
;;                         (CLEAR-FIELD
;;                          ad
;;                          '("java.lang.Object" . "monitor")
;;                          (CLEAR-FIELD
;;                           ad
;;                           '("java.lang.Object" . "wait-set")
;;                           heap)))))))))
;;   :hints (("Goal" :in-theory (e/d ((s) ;bozo
;;                                    jvm::INITIALIZE-ONE-DIM-ARRAY) ( s==r)))))

(theory-invariant (incompatible (:rewrite CLEAR-FIELD-OF-S) (:rewrite S-OF-CLR)))

;this may help shrink the term size...
;note that this cuts the mentions of b from 2 to 1.
(defthm myif-of-cons-same-cdrs
  (implies (syntaxp (not (equal a c))) ;otherwise the -same rule should fire?
           (equal (myif test (cons a b) (cons c b))
                  (cons (myif test a c) b)))
  :hints (("Goal" :in-theory (enable myif))))

;we lose one occurrence of x and gain an occurrence of (nth n x) - hope that helps!
(defthm myif-of-update-nth-and-same
  (implies (and (< n (len x))
                (natp n))
           (equal (myif test (update-nth n val x) x)
                  (update-nth n (myif test val (nth n x)) x)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-cons-same-cars
  (implies (syntaxp (not (equal b c))) ;otherwise the -same rule should fire?
           (equal (myif test (cons a b) (cons a c))
                  (cons a (myif test b c))))
  :hints (("Goal" :in-theory (enable myif))))

;gen? -alt?
(defthm myif-of-logext-logior-32-hack
  (implies (signed-byte-p 32 x)
           (equal (myif test x (logext 32 (bvor 32 y x)))
                  (logext 32 (bvor 32 (myif test 0 y) x))))
  :hints (("Goal" :in-theory (enable myif))))

;BOZO think about the extra logext here
(defthm myif-of-logext-logior-32-hack-2
  (implies t;(signed-byte-p 32 x)
           (equal (myif test (logext 32 x) (logext 32 (bvor 32 y x)))
                  (logext 32 (bvor 32 (myif test 0 y) x))))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-of-logior-32-hack
  (implies (and (natp n)
                (unsigned-byte-p n x))
           (equal (myif test x (bvor n y x))
                  (bvor n (myif test 0 y) x)))
  :hints (("Goal" :in-theory (enable myif))))

;; ;wouldn't fire?
;; (defthm myif-of-logior-32-hack-two
;;   (implies (and (natp n)
;;                 (unsigned-byte-p n x))
;;            (equal (myif test (bvor n y x) x)
;;                   (bvor n (myif test 0 y) x)))
;;   :hints (("Goal" :in-theory (enable myif))))

;BOZO think about the extra logext here
(defthm myif-of-logext-logior-32-hack-2
  (implies t;(signed-byte-p 32 x)
           (equal (myif test (logext 32 x) (logext 32 (bvor 32 y x)))
                  (logext 32 (bvor 32 (myif test 0 y) x))))
  :hints (("Goal" :in-theory (enable myif))))

;; (defthm myif-equal-bit-0-64
;;   (implies (unsigned-byte-p 1 bit)
;;            (equal (MYIF (EQUAL bit 0) 0 64)
;;                   (bvcat 1 bit 6 0)))
;;   )

;BOZO think more about stuff like this?
;should ACL2 always do stuff like this?
(defthmd if-backchain-rule
  (implies (not (< tp x))
           (equal (< (IF test tp ep)
                     x)
                  (if test nil
                    (< ep
                       x)))))

;BOZO think more about stuff like this?
;should ACL2 always do stuff like this?
(defthmd if-backchain-rule2
  (implies (< x tp)
           (equal (< x
                     (IF test tp ep))
                  (if test t
                    (< x
                       ep)))))

;; ;bozo drop some hyps?
;; (defthm byte-fix-list-of-update-subrange
;;   (implies (and (equal (len vals) (+ 1 end (- start))) ;(consp vals);(< end (len lst))
;;                 (< end (len lst)))
;;            (equal (byte-fix-list (update-subrange start end vals lst))
;;                   (update-subrange start end (byte-fix-list vals) (byte-fix-list lst))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (nth-0 update-subrange update-nth-of-update-subrange-diff-back
;;                                   if-backchain-rule2 ;why?
;;                                   )
;;                            (update-nth-of-update-subrange-diff car-becomes-nth-of-0)))))

;bozo gen?
(defthm update-nth-equal-update-subrange-special
  (implies (and (<= n end)
                (< end (len lst))
                (natp n)
                (natp end)
                (equal val1 val2)
                (equal lst1 (update-subrange (+ 1 n) end rst lst2))
                )
           (equal (equal (update-nth n val1 lst1)
                         (update-subrange n end (cons val2 rst) lst2))
                  t))
  :hints (("Goal" :in-theory (e/d (;list::update-nth-equal-rewrite
                                   update-subrange) ( update-nth-of-update-subrange-diff)))))

;; (defthm update-nth-equal-update-subrange-special
;;   (implies (and (<= n end)
;;                 (< end (len lst))
;;                 (natp n)
;;                 (natp end)
;;                 )
;;            (equal (equal (update-nth n val1 lst) (update-subrange n end (cons val2 rst) lst))
;;                   (and (equal val1 val2)
;;                        (equal lst (update-subrange (+ 1 n) end rst lst)))))
;;   :hints (("Goal" :in-theory (e/d (list::update-nth-equal-rewrite update-subrange) ( update-nth-of-update-subrange-diff)))))

;; (IMPLIES (AND (INTEGERP K)
;;               (NATP SIZE)
;;               (NOT (EQUAL 1 (GETBIT N X))))
;;          (EQUAL (BVAND SIZE K (REPEATBIT SIZE 0))
;;                 0))

;bozo (MEMBERP (NTH I REF-LIST) (CDR REF-LIST))

;; (defthm unsigned-byte-p-of-nth2
;;   (implies (and (all-unsigned-byte-p size lst)
;; ;                (<= 0 n) ;(integerp n)
;;                 (< n (len lst)))
;;            (unsigned-byte-p size (nth n lst)))
;;   :hints (("Goal" :use (:instance unsigned-byte-p-of-nth)
;;            :in-theory (e/d (NTH-WHEN-N-IS-ZP ALL-UNSIGNED-BYTE-P) (CAR-BECOMES-NTH-OF-0  unsigned-byte-p-of-nth)))))

;(in-theory (disable bvmult-with-usb1))

;do we want this?
(defthm getbit-list-of-myif
  (equal (getbit-list n (myif test x y))
         (myif test (getbit-list n x) (getbit-list n y)))
  :hints (("Goal" :in-theory (enable myif))))


;; ;bozo same for intp-list, etc.
;; (defthm byte-p-list-of-update-subrange
;;   (implies (and (byte-p-list lst)
;;                 (<= start end)
;;                 (< end (len lst))
;;                 (equal (len vals) (+ end 1 (- start)))
;;                 (byte-p-list vals))
;;            (byte-p-list (update-subrange start end vals lst)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (LIST::LEN-OF-CDR-BETTER
;;                             update-subrange update-nth-of-update-subrange-diff-back)
;;                            (update-nth-of-update-subrange-diff
;;                             )))))


;; (defthm bvchop-31-times-cancel
;;    (implies (and (integerp x)
;;                  (integerp y))
;;             (equal (BVCHOP 31 (* x (BVCHOP 31 y)))
;;                    (BVCHOP 31 (* x y)))))

;; (defthm bvchop-31-times-cancelb
;;    (implies (and (integerp x)
;;                  (integerp y))
;;             (equal (BVCHOP 31 (* x (LOGext 31 y)))
;;                    (BVCHOP 31 (* x y))))
;;    :hints (("Goal" :use ((:instance bvchop-31-times-cancel
;;                                    (y (LOGext 31 y)))
;;                          (:instance bvchop-31-times-cancel
;;                                    (y y)))
;;             :in-theory (disable bvchop-31-times-cancel))))


;; (thm
;;  (equal (BVXOR 27 x (+ y (* 2 z (LOGEXT 31 w))))
;;         (BVXOR 27 x (+ y (* 2 z w)))))

(defthmd take-differs-hack
  (implies (and (not (equal (take n lst1) ;binds n
                            (take n lst2)))
                (not (equal (take n x)
                            (take n y))))
           (equal (equal x y)
                  nil)))

(defthmd nthcdr-differs-hack
  (implies (and (not (equal (nthcdr n lst1) ;binds n
                            (nthcdr n lst2)))
                (not (equal (nthcdr n x)
                            (nthcdr n y))))
           (equal (equal x y)
                  nil)))

(defthmd nth-differs-hack
  (implies (and (not (equal (nth n lst1) ;binds n
                            (nth n lst2)))
                (not (equal (nth n x)
                            (nth n y))))
           (equal (equal x y)
                  nil)))

;problems happen when n is a huge constant...
(defthm take-plus-1-hack
  (implies (and (syntaxp (not (quotep n))) ;BOZO
                (equal (take n x)
                       (take n y))
                (equal (len x) (len y))
                (natp n))
           (equal (equal (take (+ 1 n) x)
                         (take (+ 1 n) y))
                  (equal (nth n x)
                         (nth n y))))
  :hints (("Goal" :in-theory (enable take))))

(in-theory (disable update-nth-of-update-nth-becomes-update-subrange))
;(in-theory (disable UPDATE-NTH-WITH-last-VAL))
;(in-theory (disable MEMBERP-NTH-AND-CDR)) ;bozo
;(in-theory (disable LEN-OF-UPDATE-NTH-REWRITE-2)) ;bozo think about this...
;(in-theory (disable FIRSTN-OF-ONE-MORE)) ;think about this more...

(defthm subrange-of-update-subrange-contained
  (implies (and (<= start2 start1)
                (<= end1 end2)
                (<= start1 end1)
                (<= start2 end2)
                (< end2 (len lst))
                (equal (len vals) (+ end2 1 (- start2)))
                (natp start1)
                (natp start2)
                (natp end1)
                (natp end2)
                )
           (equal (SUBRANGE start1 end1 (UPDATE-SUBRANGE start2 end2 vals lst))
                  (SUBRANGE (- start1 start2) (- end1 start2) vals)))
  :hints (("Goal" :in-theory (e/d (SUBRANGE) (;anti-subrange
                                              )))))

;(local (in-theory (disable BVPLUS-RECOLLAPSE)))

(defun indu (n start vals)
  (if (endp vals)
      (list n start vals)
    (indu (+ -1 n) (+ 1 start) (cdr vals))))

;BOZO think about this
(theory-invariant (incompatible (:definition nthcdr ) (:rewrite NTHCDR-OF-CDR-COMBINE)))



;bozo gen
(defthm subrange-of-update-subrange-not-quite-skew
  (implies (and (natp start)
                (<= start end)
                (< end (len lst))
                (natp end)
;;                 (equal (+ end (- start))
;;                        (len vals))
                )
           (equal (subrange start end (update-subrange (+ 1 start) end vals lst))
                  (cons (nth start lst)
                        (subrange 0 (+ end -1 (- start)) vals))))
  :hints (("Goal" :in-theory (e/d (update-subrange-rewrite
                                   ;EQUAL-CONS-CASES2
                                   SUBRANGE-OF-CONS
                                   )
                                  (;anti-subrange; take-of-nthcdr-becomes-subrange
                                   ))
           :cases ((equal end (+ start 1)))
           :do-not '(generalize eliminate-destructors)
           :expand ((subrange start end
                              (update-subrange (+ 1 start)
                                               end vals
                                               lst))))))


(defthmd subrange-differs-hack
  (implies (and (not (equal (subrange start end lst1) ;binds start and end
                            lst2))
                (not (equal (subrange start end x)
                            (subrange start end y))))
           (equal (equal x y)
                  nil)))

;; (defthmd update-subrange-rewrite
;;   (implies (and
;;             (natp start)
;;             (natp end)
;;             (true-listp lst)
;;             (true-listp vals)
;;             (<= start end)
;;             (equal (+ 1 end (- start)) (len vals))
;;             (< end (len lst)))
;;            (equal (update-subrange start end vals lst)
;;                   (append (take start lst)
;;                           vals
;;                           (nthcdr (+ 1 end) lst))))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm update-subrange-equal-rewrite
   (implies (and (equal (len lst1) (len lst2))
                 (natp start)
                 (natp end)
                 (true-listp lst1)
                 (true-listp lst2)
                 (true-listp vals)
                 (<= start end)
                 (equal (+ 1 end (- start)) (len vals))
                 (< end (len lst1))
    ;                (= start 2) (= end 5) (equal vals '(1 2 3 4)) (equal lst1 '(a b c d e f)) (equal lst2 '(aa bb cc dd ee ff))
                 )
            (equal (equal (update-subrange start end vals lst1) lst2)
                   (and (equal vals (subrange start end lst2))
                        (equal (take start lst1)
                               (take start lst2))
                        (equal (nthcdr (+ 1 end) lst1)
                               (nthcdr (+ 1 end) lst2)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable update-subrange-rewrite
                               equal-of-append
                               take-of-nthcdr-becomes-subrange))))

;(in-theory (disable mod-cancel))

;BBOZO see the loop below:
(local (in-theory (disable <-unary-/-positive-right)))
;; 970. Attempting to apply (:REWRITE COLLECT-CONSTANTS-<-/-TWO) to
;;      (< (BINARY-* '32
;;                   (MOD (BINARY-* '1/32 (LOCALVAR '2 S0))
;;                        '1))
;;         '1)
;; 971. Rewriting (to establish) the rhs of the conclusion,
;;      (< X (BINARY-* A (UNARY-/ B))),
;;    under the substitution
;;      A : '1
;;      X : (MOD (BINARY-* '1/32 (LOCALVAR '2 S0))
;;               '1)
;;      B : '32
;; 972. Attempting to apply (:REWRITE <-UNARY-/-POSITIVE-RIGHT) to
;;      (< (MOD (BINARY-* '1/32 (LOCALVAR '2 S0))
;;              '1)
;;         '1/32)
;; 973. Rewriting (to establish) the rhs of the conclusion,
;;      (< (BINARY-* X Y) '1),
;;    under the substitution
;;      X : '32
;;      Y : (MOD (BINARY-* '1/32 (LOCALVAR '2 S0))
;;               '1)
;; 974. Attempting to apply (:REWRITE COLLECT-CONSTANTS-<-/-TWO) to
;;      (< (BINARY-* '32
;;                   (MOD (BINARY-* '1/32 (LOCALVAR '2 S0))
;;                        '1))
;;         '1)

(in-theory (disable UPDATE-SUBRANGE-SPLIT-OFF-LAST-ELEM));bozo move?
(theory-invariant (incompatible (:rewrite UPDATE-SUBRANGE-SPLIT-OFF-LAST-ELEM) (:rewrite UPDATE-NTH-OF-UPDATE-SUBRANGE)))

;; (defthm bvchophack6
;;    (implies (and (integerp x)
;;                  (integerp y)
;;                  (integerp z))
;;             (equal (bvchop 5 (+ (BVCHOP 32 y) z))
;;                    (bvchop 5 (+ y z))))
;;    :hints (("Goal" :in-theory (e/d (bvxor) (LOGXOR-BVCHOP-BVCHOP)))))

;; (defthm bvchophack6b
;;    (implies (and (integerp x)
;;                  (integerp y)
;;                  (integerp z))
;;             (equal (bvchop 5 (+ z (BVCHOP 32 y)))
;;                    (bvchop 5 (+ y z))))
;;    :hints (("Goal" :in-theory (e/d (bvxor) (LOGXOR-BVCHOP-BVCHOP)))))

;bbozo gen
;could do this with linear rule?
;;   (< 59
;;      (SLICE 31 27
;;             (+ (CURRENT 5 "A")
;;                (* 2 (CURRENT 5 "A")
;;                   (CURRENT 5 "A")))))

;;; some of this stuff was needed after we started putting in array-refp hyps automatically for all class members.
;gotta show that calling a set field first doesn't screw that up...
;(in-theory (enable  LEN-OF-UPDATE-NTH-REWRITE-2))

;; (defthm tester2
;;   (implies (and (array-refp ref1 (list dim) ':byte heap) ;bozo
;;                 (equal dim (len newcontents)) ; not going to be true in general
;;                 (true-listp newcontents)
;;                 (byte-p-list newcontents))
;;            (equal (array-refp ref1 (list dim) ':byte (set-field ref2 '("ARRAY" . "contents") newcontents heap))
;;                   t))
;;   :hints (("Goal" :in-theory (enable myif))))

;bozo see TAKE-PLUS-ONE-EQUAL-REWRITE
;maybe which one we want depends on whether we are in the conclusion...
;; (thm
;;  (implies (and (equal (nth n x) (nth n y))
;;                (true-listp x)
;;                (true-listp y)
;;                (< n (len x))
;;                (< n (len y))
;;                (natp n))
;;           (equal (EQUAL (TAKE n x) (TAKE n y))
;;                  (EQUAL (TAKE (+ 1 n) x) (TAKE (+ 1 n) y)))))

;; (thm
;;  (equal (append (take n x) (nthcdr n x))
;;         x))

(defthmd nth-differs-hack2
  (implies (not (equal (nth n x)
                       (nth n y)))
           (equal (equal x y)
                  nil)))

(defthm nthcdrs-differ-when-nths-differ
  (implies (and (NOT (EQUAL (NTH m lst1) (NTH m lst2))) ;binds m
                (<= n m)
                (natp n)
                (natp m)
                )
           (NOT (EQUAL (NTHCDR n lst1) (NTHCDR n lst2))))
  :hints (("Goal" :use (:instance nth-differs-hack2 (n (- m n)) (x (NTHCDR n lst1)) (y (NTHCDR n lst2))))))

(defthmd nthcdr-when-its-just-the-last-elem
  (implies (and (equal n (+ -1 (len x)))
                (natp n))
           (equal (NTHCDR n x)
                  (cons (nth n x) (FINALCDR X))))
  :hints (("Goal" :in-theory (enable ;EQUAL-CONS-CASES2
                              ))))

;update-nth 0 when the list is at most 1 long..

;BOZO more like this?
(defthmd integer-bound-lemma
  (implies (and (< x y)
                (integerp x)
                (integerp y))
           (equal (< (+ 1 x) y)
                  (not (equal x (+ -1 y)))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1 1))))

;(local (in-theory (disable NORMALIZE-EQUAL-0))) ;bozo looped

;; (ARRAY-REFP (OLD 0 "fromarray")
;;                       (LIST (GET-FIELD (OLD 0 "fromarray")
;;                                        '("ARRAY" . "length")
;;                                        (JVM::HEAP S1)))
;;                       ':INT
;;                       (S (OLD 1 "toarray")
;;                          (G (OLD 1 "toarray") (JVM::HEAP S1))
;;                          (JVM::HEAP S0)))


;why I do prefer the latter?  I guess because it makes crystal clear the fact that we don't care about the values of x, only its length
;; (defthm consp-cdr
;;   (equal (consp (cdr x))
;;          (<= 2 (len x))))

;(in-theory (disable LEN-LESS-THAN-2-REWRITE))

;(in-theory (disable LOGEXT-NEGATIVE)) ;i don't think i like this one...


;; (defthm gross1
;;  (implies (ARRAY-REFP ref
;;                       (LIST (LEN (GET-FIELD ref
;;                                             (array-contents-pair)
;;                                             heap)))
;;                       ':INT heap)
;;           (ARRAY-REFP ref
;;                       (LIST (GET-FIELD ref
;;                                        '("ARRAY" . "length")
;;                                        heap))
;;                       ':INT heap))
;;  :hints (("Goal" :in-theory (enable ARRAY-REFP))))

;trying it now..
;(in-theory (enable FIRSTN-OF-ONE-MORE))

;see the file "loops"
;rename
(defthm ineq-hack
  (implies (and (< a b) ;free var
                (<= b c)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                )
           (not (< c a)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 2 nil nil nil))))

;rename
(defthm ineq-hack2
  (implies (and (< a b) ;free var
                (<= b c)
;       (integerp a)
;      (integerp b)
;     (integerp c)
                )
           (not (< c a)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 2))))

(defthm memberp-nth-1-cdr
  (equal (MEMBERP (NTH 1 x) (CDR x))
         (< 1 (len x))))

;move to be next to the other one
(defthm not-less-when->=-max-of-containing-bag
  (implies (and (<= (maxelem bag) k)
                (memberp elem bag))
           (equal (> elem k)
                  nil))
  :hints (("Goal" :in-theory (enable maxelem))))

(defthm memberp-of-maxelem-same
 (implies (consp x)
          (memberp (maxelem x) x))
 :hints (("Goal" :in-theory (enable maxelem))))

(defthm memberp-maxelem-when-subsetp-equal
  (implies (and (subsetp-equal bag1 bag2)
                (consp bag1))
           (memberp (maxelem bag1) bag2))
  :hints (("Goal" :use (:instance memberp-of-maxelem-same (x bag1))
           :in-theory (disable memberp-of-maxelem-same))))

;gen
(defthm subsetp-equal-of-subrange-and-subrange
  (implies (and (<= high high2)
                (natp low)
                (natp high)
                (natp high2))
           (subsetp-equal (SUBRANGE low high X) (SUBRANGE low high2 X)))
  :hints (("Goal" :in-theory (e/d (subrange) (;anti-subrange
                                              )))))

(defthm maxelem-subrange-shorten-hackb
  (implies (and (<= (NTH i x) y)
                (< i (len x))
                (natp i)
                (<= 2 i)
                )
           (equal (< y (MAXELEM (SUBRANGE 2 i x)))
                  (if (< 2 i)
                      (< y (MAXELEM (SUBRANGE 2 (+ -1 i) x)))
                    (< y (nth 2 x)))))
  :hints (("Goal" :use (:instance subrange-split-top (low 2))
           :in-theory (disable subrange-split-top
                               ))))

;; ;gen
;; (defthm length-field-becomes-len-contents
;;   (implies (array-refp ref (cons dim dims) type heap)
;;            (equal (array-length ref heap)
;;                   (LEN (GET-FIELD ref
;;                                   (array-contents-pair)
;;                                   heap))))
;;   :hints (("Goal" :expand ((ARRAY-REFP ref (LIST dim) type heap)))))

(defthmd maxelem-split-hack
  (implies (and (natp i)
                (<= 1 i)
                (< i (len x))
                )
           (equal (subrange 1 i x)
                  (cons (nth 1 x)
                        (subrange 2 i x))))
  :hints (("Goal" :in-theory (enable ;EQUAL-CONS-CASES2
                              ))))

;bozo
(defthm maxelem-of-subrange-lengthen-2-1
  (implies (and (<= (nth 1 x)
                    (maxelem (subrange 2 i x)))
                (< i (len x))
                (natp i)
                (<= 2 i))
           (equal (maxelem (subrange 2 i x))
                  (maxelem (subrange 1 i x))))
  :hints (("Goal" ;:expand ((subrange 1 i x))
           :in-theory (e/d (maxelem-split-hack) (CONS-NTH-ONTO-SUBRANGE)))))

;(in-theory (disable firstn-of-one-more))

;; (defthm <-when-bags-fact2
;;   (implies (and (<= (maxelem bag1) (minelem bag2)) ;binds the free vars
;;                 (memberp x bag1)
;;                 (memberp y bag2))
;;            (not (< y x)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (nil 3 3)))
;;   :hints (("Goal" :use (:instance not-less-when->=-max-of-containing-bag
;;                                   (k y) (elem x) (bag bag1)
;;                                   )
;;            :in-theory (disable not-less-when->=-max-of-containing-bag))))


;; (thm
;;  (implies (and (natp i)
;;                (< 0 i)
;;                (< (+ 1 i) (len x))
;;                )
;;           (equal (<= (MAXELEM (TAKE (+ 1 i) x))
;;                      (NTH (+ 1 i) x))
;;                  (<= (MAXELEM (TAKE i x))
;;                      (NTH (+ 1 i) x))))
;;  :hints (("Goal" :use (:instance take-split (n (+ 1 i)))
;;           :in-theory (disable take-split LIST::EQUAL-APPEND-REDUCTION!))))

;move to seq?
(defthm maxelem-of-first-n+1-when-nth-is-greatest
  (implies (and (<= (maxelem (take n x)) (nth n x))
                (natp n)
                (< (+ 1 n) (len x))
                )
           (equal (maxelem (take (+ 1 n) x))
                  (nth n x)))
  :hints (("Goal" :in-theory (enable take)))
  ;; :hints (("Goal" :use (:instance take-split (n (+ 1 n)))
  ;;          :in-theory (disable take-split
  ;;                              ;cdr-of-take
  ;;                              cdr-of-take-becomes-subrange-better ;new after i added a guard to maxelem...
  ;;                              )))
  )

;; (DEFTHM MAXELEM-OF-UPDATE-NTH-better
;;   (IMPLIES (AND (<= N (LEN LST))
;;                 (TRUE-LISTP LST)
;;                 (<= 0 N)
;;                 (INTEGERP N))
;;            (EQUAL
;;             (MAXELEM (UPDATE-NTH N VAL LST))
;;             (if (equal n (len lst))
;;                 (if (equal 0 n)
;;                     val
;;                   (max val (MAXELEM LST)))
;;               (IF (EQUAL N (+ -1 (LEN LST)))
;;                   (IF (ZP N)
;;                       VAL
;;                       (IF (< VAL (MAXELEM (TAKE (NFIX N) LST)))
;;                           (MAXELEM (TAKE (NFIX N) LST))
;;                           VAL))
;;                   (IF (ZP N)
;;                       (IF (<= VAL
;;                               (MAXELEM (NTHCDR (+ 1 (NFIX N)) LST)))
;;                           (MAXELEM (NTHCDR (+ 1 (NFIX N)) LST))
;;                           VAL)
;;                       (IF (AND (<= VAL
;;                                    (MAXELEM (NTHCDR (+ 1 (NFIX N)) LST)))
;;                                (<= (MAXELEM (TAKE (NFIX N) LST))
;;                                    (MAXELEM (NTHCDR (+ 1 (NFIX N)) LST))))
;;                           (MAXELEM (NTHCDR (+ 1 (NFIX N)) LST))
;;                           (IF (< VAL (MAXELEM (TAKE (NFIX N) LST)))
;;                               (MAXELEM (TAKE (NFIX N) LST))
;;                               VAL)))))))
;;   :OTF-FLG T
;;   :HINTS
;;   (("Goal" :DO-NOT-INDUCT T
;;     :IN-THEORY (E/D (UPDATE-NTH-REWRITE) ((FORCE))))))


(defthm less-than-max-hack
  (implies (< z y)
           (< z (MAX y x))))

(defthm less-than-max-hack-alt
  (implies (< z x)
           (< z (MAX y x))))

;disgusting...
(defthm if-hack
  (implies (integerp x)
           (equal (< z (IF (EQUAL y (+ -1 x))
                           x
                           (+ 1 y)))
                  (< z (+ 1 y)))))

;BOZO try
;(in-theory (disable logext-of-myif))

(defthmd logext-of-myif-back
  (equal (myif test (logext n a) (logext n b))
         (logext n (myif test a b)))
  :hints (("Goal" :in-theory (enable myif))))

(theory-invariant (incompatible (:rewrite LOGEXT-OF-MYIF) (:rewrite LOGEXT-OF-MYIF-back)))

;trying for efficiency...
;(in-theory (disable LIST::NTH-WITH-LARGE-INDEX))


;BOZO gen this series...

; (CDR (TAKE 5 (NTHCDR 26 X)))

;; (defthm subrange-tighten
;;   (implies (and (equal len (len x)) ;binds the free variable len to the result of rewriting (len x)
;;                 (syntaxp (quotep len))
;;                 (natp end)
;;                 (<= len end))
;;            (equal (SUBRANGE start end x)
;;                   (SUBRANGE start (+ -1 len) x)))
;;   :hints (("Goal" :in-theory (e/d (SUBRANGE) (TAKE-OF-NTHCDR-BECOMES-SUBRANGE)))))

(defthm drop-linear-hyps1
  (implies (and (< (+ free x) y)
                (syntaxp (quotep free))
                (<= k free))
           (< (+ k x) y)))

(defthm drop-linear-hyps2
  (implies (and (< (+ free x) y)
                (syntaxp (quotep free))
                (<= 0 free))
           (< x y)))

(defthm drop-linear-hyps3
  (implies (and (< (+ free x) y)
                (syntaxp (quotep free))
                (<= 0 free))
           (not (< y x))))

;; ;whoa. this seems like a bad rule?
;; ;lst was essentially array-contents
;; (defthmd array-ref-not-in-own-contents-helper
;;   (implies (and (bag::unique (cons x (reverse-list (true-list-fix lst))))
;;                 (< n (len lst))
;;                 (natp n))
;;            (not (equal x (nth n lst))))
;;   :hints (("Goal" :in-theory (enable bag::unique-of-cons))))


(in-theory (disable ALISTP))

;; ;use a map (and don't use int-fix)
;; (defthm nth-of-int-fix-list
;;   (implies (and (natp n)
;;                 (< n (len lst)))
;;            (equal (nth n (int-fix-list lst))
;;                   (jvm::int-fix (nth n lst))))
;;   :hints (("Goal" :in-theory (e/d (nth int-fix-list LIST::NTH-OF-CONS) (nth-of-cdr)))))

;; ;use a map (and don't use int-fix)
;; (defthm consp-of-int-fix-list
;;   (equal (consp (int-fix-list x))
;;          (consp x))
;;   :hints (("Goal" :in-theory (enable int-fix-list))))

;; (defthm int-fix-list-of-update-nth
;;   (implies (and (natp n)
;;                 (< n (len lst)))
;;            (equal (int-fix-list (update-nth n val lst))
;;                   (update-nth n (jvm::int-fix val)  (int-fix-list lst))))
;;   :hints (("Goal" :in-theory (enable int-fix-list update-nth))))

;; (defmacro intfix (x)
;;   `(jvm::int-fix ,x))

;; ;strength reduction
;; (defthm irem-by-4-becomes-bvchop
;;   (implies (natp x)
;;            (equal (JVM::IREM x 4)
;;                   (bvchop 2 x)))
;;   :hints (("Goal" :in-theory (e/d (jvm::irem LOGAPP-0) ( TIMES-4-BECOMES-LOGAPp FLOOR-BY-4)))))

;; (defthm idiv-by-4-becomes-slice
;;   (implies (and (signed-byte-p 32 x)
;;                 (<= 0 x))
;;            (equal (JVM::IDIV x 4)
;;                   (slice 30 2 x)))
;;   :hints (("Goal" :in-theory (e/d (jvm::idiv LOGAPP-0) ( TIMES-4-BECOMES-LOGAPp)))))



;(in-theory (enable update-nth-of-update-nth-becomes-update-subrange))

(theory-invariant (incompatible (:rewrite update-subrange) (:rewrite UPDATE-NTH-OF-UPDATE-SUBRANGE)))

;may help during backchaining...
(defthm not-equal-when-less
  (implies (< x y)
           (equal (equal x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(local (in-theory (disable true-listp))) ;bozo

(defthm impossible-value-1
  (implies (and (<= free x)
                (< k free))
           (equal (equal k x)
                  nil)))

(defthm impossible-value-2
  (implies (and (<= free x)
                (< k free))
           (equal (equal x k)
                  nil)))

;bozo this seemed necessary to get rid of some logext32's. - where did they come from?
;trying disabled...
(defthmd usbp8-implies-sbp32
  (implies (unsigned-byte-p 8 x)
           (signed-byte-p 32 x)))

;; (defund iushr32 (r s)
;;   (bvchop 32 (jvm::iushr r s)))

;; (defthm iushr32-recoll
;;   (equal (bvchop 32 (jvm::iushr r s))
;;          (iushr32 r s))
;;   :hints (("Goal" :in-theory (enable iushr32))))

;bozo move
(defthm not-equal-from-bound
  (implies (and (<= free x)
                (< k free)
                )
           (equal (EQUAL x k)
                  nil)))

;the syntaxps are new
(defthm not-equal-constant-when-bound-forbids-it
  (implies (and (syntaxp (quotep k))
                (<= free x)
                (syntaxp (quotep free))
                (< k free))
           (NOT (EQUAL k x))))

;the syntaxps are new
(defthm not-equal-constant-when-bound-forbids-it2
  (implies (and (syntaxp (quotep k))
                (< free x)
                (syntaxp (quotep free))
                (<= k free))
           (NOT (EQUAL k x))))

(defthm use-<=-plus-constant-bound-to-drop-<=-hyp
  (implies (and (<= x (+ k y))
                (syntaxp (quotep k))
                (<= k 0))
           ;; this says x <= y but matches better
           (not (< y x))))

;(in-theory (disable LIST::LEN-EQUAL-1-REWRITE)) ;was looping

;;
;; stuff about arrays of unsigned bytes (BOZO gen to array of arbitrary type elements - we have that notion in ../bvseq/arrays)
;;
(in-theory (disable true-listp)) ;bozo

(in-theory (disable take
                    ;;BV-ARRAYP-LIST
                    ))

(defthm take-when-<-of-len
  (implies (< (len x) n) ;could be expensive?
           (equal (take n x)
                  (if (zp n)
                      nil
                    (append x
                            (repeat (- (nfix n) (len x))
                                    nil)))))
  :hints (("Goal" :in-theory (e/d (take; list::nth-append
                                   ) (take-of-cdr-becomes-subrange)))))

;BOZO really the other should be called -cheap and this one should have no suffix
(defthm memberp-of-cons-irrel-strong
  (implies (not (equal a b))
           (equal (memberp a (cons b x))
                  (memberp a x)))
  :hints (("Goal" :in-theory (enable MEMBERP-OF-CONS))))

;could restrict this to constants k and free
(defthm bound-lemma
  (implies (and (< (+ free y) x)
                (<= k free)
                )
           (< (+ k y) x)))

(defthm signed-byte-p-of-plus-constant
  (implies (and (syntaxp (quotep k))
                (natp k)
                (< x (- 2147483648 k))
                (SIGNED-BYTE-P 32 x))
           (SIGNED-BYTE-P 32 (+ k x)))
  :hints (("Goal" :in-theory (enable SIGNED-BYTE-P))))

(DEFTHM TAKE-OF-UPDATE-SUBRANGE-LEMMA-better
  (IMPLIES
   (AND (<= N (+ 1 END))
        (< END (LEN LST))
;        (EQUAL (+ 1 END (- START)) (LEN VALS))
        (NATP START)
        (NATP END)
        (NATP N)
        (<= START N))
   (EQUAL (TAKE N (UPDATE-SUBRANGE START END VALS LST))
          (APPEND (TAKE START LST)
                  (TAKE (- N START) VALS))))
  :HINTS
  (("Goal" :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
    :IN-THEORY
    (E/D (;LIST::EQUAL-CONS-CASES
          ;LIST::LEN-UPDATE-NTH-BETTER
          ;CONS-CAR-SELF-EQUAL-SELF
          TAKE UPDATE-SUBRANGE
          UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
         (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

;drop?
(defthmd update-subrange-rewrite-better2
  (implies (and (< end (len lst))
                (natp start)
                (natp end)
                (<= start end)
                )
           (equal (update-subrange start end vals lst)
                  (append (take start lst)
                          (take (+ 1 end (- start)) vals)
                          (nthcdr (+ 1 end) lst))))
  :hints (("Goal" :use (:instance update-subrange-rewrite
                                  (lst (true-list-fix lst))
                                  (vals (take (+ 1 end (- start)) vals)))
           :in-theory (e/d (nthcdr-of-true-list-fix equal-of-append)
                           ( take-of-nthcdr-becomes-subrange
                             ;list::fix-of-nthcdr
                             update-subrange-rewrite ;update-subrange-equiv
                             )))))

;; (DEFTHM UPDATE-SUBRANGE-when-extends
;;   (IMPLIES (AND (not (< END (LEN LST)))
;;                 (<= start end)
;;                 (NATP END)
;;                 (NATP START))
;;            (EQUAL (UPDATE-SUBRANGE START END VALS LST)
;;                   (UPDATE-SUBRANGE START END VALS (take (+ 1 end) LST))))
;;   :hints (("Goal" :in-theory (enable update-subrange-rewrite-better take-rewrite))))

;;   :HINTS
;;   (("Goal"
;;     :IN-THEORY
;;     (E/D
;;      (UPDATE-SUBRANGE UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
;;      (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))

;; (DEFTHM LEN-OF-UPDATE-SUBRANGE-better
;;   (IMPLIES (AND (not (< END (LEN LST)))
;;                 (<= start end)
;;             (NATP END)
;;             (NATP START))
;;            (EQUAL (LEN (UPDATE-SUBRANGE START END VALS LST))
;;                   (+ 1 end)))
;;   :HINTS
;;   (("Goal"
;;     :IN-THEORY
;;     (E/D
;;      (UPDATE-SUBRANGE UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF-BACK)
;;      (UPDATE-NTH-OF-UPDATE-SUBRANGE-DIFF)))))




;BOZO why so many cases?
;BOZO gen!
(defthm update-subrange-of-update-subrange-when-outer-is-one-smaller
  (implies (and; (equal (len vals) (- n start))
                (equal m (+ 1 start))
                (<= m n)
       ;         (< n (len lst))
 ;               (true-listp lst)
;                (true-listp vals)
                (natp start)
                (natp n)
                )
           (equal (update-subrange m n vals (update-subrange start n vals2 lst))
                  (update-subrange m n vals (update-nth start (nth 0 vals2) lst))))
  :hints (("Goal" :in-theory (enable update-subrange-rewrite-better))))


;; ;BOZO challenges:
;; (UPDATE-NTH
;;         4
;;         x
;;         (UPDATE-SUBRANGE
;;            3 6 vals
;;            (UPDATE-SUBRANGE
;;                 2 6 vals2 lst)))

;todo: move
(defthm update-nth-of-append
  (equal (update-nth n val (append x y))
         (if (< (nfix n) (len x))
             (append (update-nth n val x) y)
           (append x (update-nth (- n (len x)) val y))))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthm update-nth-of-UPDATE-SUBRANGE-last
  (implies (and (equal (+ 1 n (- m)) (len vals))
                (natp m)
                (< m n)
                (true-listp vals)
                (true-listp lst)
                (natp n)
                (< n (len lst)))
           (equal (UPDATE-NTH n val (UPDATE-SUBRANGE m n vals lst))
                  (UPDATE-NTH n val (UPDATE-SUBRANGE m (- n 1) (take (- n m) vals) lst))))
  :hints (("Goal" :in-theory (enable UPDATE-SUBRANGE-REWRITE CDR-OF-NTHCDR))))

(theory-invariant (incompatible (:rewrite TAKE-EQUAL-LENGHTEN) (:rewrite NTHS-EQUAL-WHEN-TAKES-EQUAL)))

(defthmd nths-equal-when-takes-equal
  (implies (and (equal (take n lst1) (take n lst2))
                (< 0 n)
                (integerp n))
           (EQUAL (NTH 0 lst1)
                  (NTH 0 lst2)))
  :hints (("Goal" :in-theory (enable take))))

;; (defthm nths-equal-when-takes-equal-gen
;;   (implies (and (equal (take n lst1) (take n lst2))
;;                 (< m n)
;;                 (natp m)
;;                 (integerp n))
;;            (EQUAL (NTH m lst1)
;;                   (NTH m lst2))))


;maybe this doesn't loop like the other one does?
(DEFTHM TAKE-EQUAL-LENGHTEN-cheap
  (IMPLIES (AND (EQUAL (NTH N LST1) (NTH N LST2))
                (< N (LEN LST1))
                (< N (LEN LST2))
                (<= 0 N)
                (INTEGERP N))
           (EQUAL (EQUAL (TAKE N LST1)
                         (TAKE N LST2))
                  (EQUAL (TAKE (+ 1 N) LST1)
                         (TAKE (+ 1 N) LST2))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil nil)))
  :HINTS (("Goal" :DO-NOT '(GENERALIZE ELIMINATE-DESTRUCTORS)
           :IN-THEORY (E/d (TAKE NTH) (nth-of-cdr)))))

(defthm UPDATE-NTH-of-UPDATE-subrange-contained
  (implies (and (<= start n)
                (<= n end)
                (natp start)
                (natp end)
                (natp n))
           (equal (UPDATE-NTH n val (UPDATE-SUBRANGE start end vals lst))
                  (UPDATE-SUBRANGE start end (update-nth (- n start) val vals) lst)))
  :hints (("Goal" :in-theory (enable UPDATE-SUBRANGE-rewrite))))

;gen  (LEN (TAKE N L))

;when i need this, lst is the call-stack
(defthm len-pop-push-hack
  (equal
   (EQUAL (LEN lst)
          (BINARY-+ '1
                    (IF (CONSP lst)
                        (BINARY-+ '-1
                                  (LEN lst))
                        '0)))
   (consp lst)))


;; ;slow?
;; (defthm nthcdr-of-byte-fix-list
;;   (implies (and; (<= n (len x))
;;                 (natp n)
;;                 )
;;            (equal (nthcdr n (byte-fix-list x))
;;                   (byte-fix-list (nthcdr n x))))
;;   :hints (("Goal" :in-theory (e/d ((:induction nthcdr)
;;                                    nthcdr
;;                                    byte-fix-list)
;;                                   (NTHCDR-OF-CDR-COMBINE
;;                                    NTHCDR-OF-CDR-COMBINE-strong)))))

;; (defthm subrange-of-byte-fix-list
;;   (implies (and (< end (len lst))
;;                 (natp end)
;;                 (natp start))
;;            (equal (subrange start end (byte-fix-list lst))
;;                   (byte-fix-list (subrange start end lst))))
;;   :hints (("Goal" :in-theory (e/d (subrange) (take-of-nthcdr-becomes-subrange
;;                                               anti-subrange
;;                                               cdr-of-take-becomes-subrange-better)))))


;move
;slow?
(defthm UPDATE-SUBRANGE-of-UPDATE-SUBRANGE-reorder
  (implies (and (< end2 start1)
                (natp start1)
                (natp start2)
                (natp end1)
                (natp end2))
           (equal (UPDATE-SUBRANGE start1 end1 vals1 (UPDATE-SUBRANGE start2 end2 vals2 lst))
                  (UPDATE-SUBRANGE start2 end2 vals2 (UPDATE-SUBRANGE start1 end1 vals1 lst))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (UPDATE-SUBRANGE-rewrite-better TAKE-OF-NTHCDR-BECOMES-SUBRANGE)
                                  (<-OF-IF-ARG1 IF-BACKCHAIN-RULE2 IF-BACKCHAIN-RULE TAKE-WHEN-<-OF-LEN)))))

(defthm equal-if-<-hack
  (implies (and (rationalp x)
                (rationalp y))
           (equal (EQUAL x (IF (< y x) x y))
                  (<= y x))))

;;== new stuff

;; (defthm nth-of-push
;;   (equal (nth n (jvm::push x y))
;;          (if (zp n) x (nth (+ -1 n) y)))
;;   :hints (("Goal" :in-theory (enable jvm::push list::nth-of-cons))))

;;
;; bvchop-list
;;

;; ;BOZO do i really not have this?
;; ;dup from jvm
;; ;move to an earlier book?
;; (defund bvchop-list (size lst)
;;   (declare (type (integer 0 *) size)
;;            (xargs :guard (ALL-INTEGERP lst)))
;;   (if (atom lst)
;;       nil
;;     (cons (bvchop size (car lst))
;;           (bvchop-list size (cdr lst)))))

(defthm all-signed-byte-p-implies-all-integerp
  (implies (all-signed-byte-p free x)
           (all-integerp x))
  :hints (("Goal" :in-theory (enable all-signed-byte-p all-integerp))))

;(in-theory (disable bvxor-1-becomes-bitxor)) ;trying without

;new stuff:


;; ;this is when we know what the entire class is
;; (defthm open-execute-INVOKEspecial-another
;;   (implies (and (equal class-name (jvm::arg1 inst)) ;i hope this binds to the result of rewriting (farg1 inst)
;;                 (equal (g class-name
;;                           class-table)
;;                        method) ;binds the free variables method and class-table
;;                 (equal (g class-name class-table)
;;                        (g class-name (jvm::class-table s)))
;;                 (syntaxp (quotep-for-tracing method)))
;;            (equal (jvm::execute-INVOKEspecial inst th s)
;;                   (jvm::execute-INVOKEspecial2 inst th s)))
;;   :hints (("Goal" :in-theory (enable jvm::execute-INVOKEspecial2 jvm::execute-invokespecial jvm::popn))))

;; (in-theory (disable LIST::LEN-POS-REWRITE
;;                     LIST::LEN-OF-NON-CONSP
;;                     LIST::NTH-WITH-LARGE-INDEX
;;                     CAR-BECOMES-NTH-OF-0
;;                     )))

;; ;this one is probably better:
;; (defun bitlist-to-bv2 (bitlist)
;;   (declare (xargs :guard (all-integerp bitlist)))
;;   (if (atom bitlist)
;;       0
;;     (bvcat 1
;;            (car bitlist)
;;            (+ -1 (len bitlist))
;;            (bitlist-to-bv2 (cdr bitlist)))))

;; (defthmd bitlist-to-bv2-opener
;;   (implies (not (endp bitlist))
;;            (equal (bitlist-to-bv2 bitlist)
;;                   (bvcat 1
;;                          (car bitlist)
;;                          (+ -1 (len bitlist))
;;                          (bitlist-to-bv2 (cdr bitlist))))))

;; (defthm bitlist-to-bv2-nil
;;   (equal (bitlist-to-bv2 nil)
;;          0))

;; (defthmd mv-nth-opener
;;   (implies (and (not (zp n))
;;                 (not (endp l)))
;;            (equal (mv-nth n l)
;;                   (MV-NTH (- N 1) (CDR L))))
;;   :hints (("Goal" :in-theory (enable mv-nth))))

;; (defthmd mv-nth-opener-zp
;;   (implies (not (endp l))
;;            (equal (mv-nth 0 l)
;;                   (car l)))
;;   :hints (("Goal" :in-theory (e/d (mv-nth) ()))))

;stuff from rc6  - file this stuff!

; kill this stuff?

;; ;bozo eventually just go to bvneg
;; (defthm bvminus-of-bvplus-tighten
;;   (implies (and (< n m)
;;                 (natp m)
;;                 (natp n)
;;                 (integerp x)
;;                 (integerp y)
;;                 (integerp z)
;;                 )
;;            (equal (bvminus n x (bvplus m y z))
;;                   (bvminus n x (bvplus n y z))))
;;   :hints (("Goal" :in-theory (e/d (bvminus bvplus) (anti-bvplus)))))

;; ;bozo handle this better
;; (defthm bvplus-of-bvminus
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (equal (bvplus 5 x (bvminus 5 y x))
;;                   (bvchop 5 y)))
;;   :hints (("Goal" :in-theory (e/d (bvminus bvplus) (anti-bvplus))))
;;   )

;; (defthm iushr-constant-opener
;;   (implies (and (syntaxp (quotep JVM::VAL2)))
;;            (equal (JVM::IUSHR JVM::VAL1 JVM::VAL2)
;;                   (logext 32 (SLICE 31 (BVCHOP 5 JVM::VAL2) JVM::VAL1))))
;;   :hints (("Goal" :in-theory (enable JVM::IUSHR))))


;; ;use trim?
;; (defthm bvminus-of-bvor-tighten
;;   (implies (and (< n m)
;;                 (natp m)
;;                 (natp n)
;;                 (integerp x)
;;                 (integerp y)
;;                 (integerp z)
;;                 )
;;            (equal (bvminus n x (bvor m y z))
;;                   (bvminus n x (bvor n y z))))
;;   :hints (("Goal" :use ((:instance BVMINUS-OF-BVCHOP-GEN-ARG2
;;                                    (size1 n)
;;                                    (size2 n)
;;                                    (y x)
;;                                    (x (bvor m y z)))
;;                         (:instance BVMINUS-OF-BVCHOP-GEN-ARG2
;;                                    (size1 n)
;;                                    (size2 n)
;;                                    (y x)
;;                                    (x (bvor n y z))))
;;            :in-theory (disable BVMINUS-OF-BVCHOP-GEN-ARG2))))

;; (defthm get-field-contents-of-initialize-2d-array-sub-array
;;   (implies (memberp ad (n-new-ads jvm::outercount (set::insert jvm::addr (rkeys jvm::heap)))) ;rephrase?
;;            (equal (get-field ad (array-contents-pair) (jvm::initialize-2d-array jvm::addr type jvm::outercount jvm::innercount jvm::heap))
;;                   (jvm::initial-array-contents type jvm::innercount))))

;; (defun count-elements->= (item set)
;;   (if (set::empty set)
;;       0
;;     (if (equal item (set::head set))
;;         (+ 1 (count-elements->= (item (set::tail set))))
;;       (count-elements->= (item (set::tail set))))))



;this isn't true - should it be?
;; (thm
;;  (implies (and (< (LEN DATA) INDEX)
;;                (equal len (len data))
;;                (integerp index))
;;           (equal (BV-ARRAY-READ ELEMENT-SIZE LEN INDEX DATA)
;;                  boo))
;;  :hints (("Goal" :in-theory (enable bv-array-read LIST::NTH-WITH-LARGE-INDEX))))

;; (defthm getbit-of-bv-array-read-gen
;;   (implies (and (syntaxp (quotep n))
;;                 (syntaxp (quotep data))
;;                 (natp n)
;;                 (natp index)
;;                 (< n element-size)
;; ;                (< index (len data))
;;                 (equal len (len data))
;;                 (natp element-size))
;;            (equal (getbit n (bv-array-read element-size len index data))
;;                   (bv-array-read 1 len index (getbit-list n data))))
;;   :hints (("Goal" :cases ((< index (len data)))))
;;  )


;; (skip- proofs
;;  (defun print-array (array-name array n)
;;    (if (< n 0)
;;        nil
;;      (print-array array-name
;;                   array
;;                   (prog2$ (cw " ~x0~%" (cons n (aref1 array-name array n)))
;;                           (+ -1 n))))))

;; (skip- proofs (verify-guards print-array))

;; ;bozo copy how we do print-list in terms of the cw command and spaces
;; ;could call a more general print array function?
;; ;n should usually be (+ -1 dag-len)?
;; (defun print-dag (n dag-array)
;;   (prog2$ (cw "(")
;;           (prog2$ (print-array 'dag-array dag-array n)
;;                   (cw ")~%"))))

;; (skip- proofs (verify-guards print-dag))

;;; new stuff to support branches when simulating using the dag rewriter:

;; ;drop?
;; (defthm bitxor-of-bv-array-read-arg1
;;   (implies (and (< 1 element-size)
;;                 (natp index)
;;                 (< index (len data)) ;drop? or change to (< index len)
;;                 (equal len (len data))
;;                 (natp element-size)

;;                 )
;;            (equal (bitxor (bv-array-read ELEMENT-SIZE LEN INDEX DATA)
;;                           y)
;;                   (bitxor (bv-array-read 1 LEN index (getbit-list 0 data))
;;                           y)))
;;   :hints (("Goal"
;;            :use (:instance BITXOR-OF-BVCHOP-ARG2
;;                            (X (BV-ARRAY-READ ELEMENT-SIZE LEN INDEX DATA))
;;                            (N 1)
;;                            (Y Y)
;;                            )
;;            :in-theory (disable bv-array-read BITXOR-OF-BVCHOP-ARG2 BITXOR-OF-GETBIT-ARG2))))

;; (defthm bitxor-of-bv-array-read-arg2
;;   (implies (and (< 1 element-size)
;;                 (natp index)
;;                 (< index (len data)) ;drop?
;;                 (equal len (len data))
;;                 (natp element-size)
;;                 )
;;            (equal (bitxor y
;;                           (bv-array-read ELEMENT-SIZE LEN INDEX DATA))
;;                   (bitxor y
;;                           (bv-array-read 1 LEN index (getbit-list 0 data)))))
;;   :hints (("Goal"
;;            :use (:instance BITXOR-OF-BVCHOP-ARG2
;;                            (X (BV-ARRAY-READ ELEMENT-SIZE LEN INDEX DATA))
;;                            (N 1)
;;                            (Y Y)
;;                            )
;;            :in-theory (disable bv-array-read BITXOR-OF-BVCHOP-ARG2 BITXOR-OF-GETBIT-ARG2))))

(defthm lookup-of-bvif
  (equal (lookup (bvif size test a b) program)
         (myif test (lookup (bvchop size a) program)
               (lookup (bvchop size b) program)))
  :hints (("Goal" :in-theory (enable bvif myif))))

;; ;turns a bvif into a myif...
;; (defthm INDEX-INTO-PROGRAM-of-bvif
;;   (equal (JVM::INDEX-INTO-PROGRAM (bvif size test a b) program)
;;          (myif test (JVM::INDEX-INTO-PROGRAM (bvchop size a) program)
;;                (JVM::INDEX-INTO-PROGRAM (bvchop size b) program)))
;;   :hints (("Goal" :in-theory (enable bvif myif))))

;; ;move
;; ;is this ever used?
;; (defun print-dag-expr (arg dag-array)
;;   (declare (xargs :guard (and (ARRAY1P 'dag-array dag-array)
;;                               (or (quotep arg)
;;                                   (and (integerp arg)
;;                                        (<= 0 arg)
;;                                        (< arg (CAR (DIMENSIONS 'dag-array dag-array))))))
;;                   :guard-hints (("Goal" :in-theory (enable array1p)))))
;;   (let ((expr (if (integerp arg)
;;                   (aref1 'dag-array dag-array arg)
;;                 arg)))
;;     (prog2$ (cw "~x0~%" expr)
;;             t)))

;; ;switch this to be hung off of step?
;; (defthm do-inst-becomes-do-inst-3-with-print
;;   (implies (axe-syntaxp (print-dag-expr inst dag-array)) ;always true, causes printing
;;            (equal (jvm::do-inst inst th s)
;;                   (do-inst3 (car inst) inst th s)))
;;   :hints (("Goal" :use (:instance do-inst-becomes-do-inst-3)
;;            :in-theory (disable do-inst-becomes-do-inst-3))))

;;
;; rules to normalize nests of bitxors
;;

 ;bozo if we're keeping bvnots, prove rules about x and not(x) adjacent in a bitxor nest


;; (BVXOR (+ 15 (- N))
;;                              1 (SLICE 14 N X))



;; (skip -proofs
;;  (DEFTHM BVCHOP-OF-LOGXOR-better2
;;    (IMPLIES (AND (NATP N) (integerp A) (integerp B))
;;             (EQUAL (BVCHOP N (LOGXOR A B))
;;                    (LOGXOR (BVCHOP N A) (BVCHOP N B))))))


;; (skip -proofs
;;  (defthm logbitp-of-logand
;;    (implies (and (natp n)
;;                  (integerp x)
;;                  (integerp y))
;;             (equal (logbitp n (logand x y))
;;                    (and (logbitp n x)
;;                         (logbitp n y))))
;;    :hints (("Goal" :in-theory (enable logand logbitp*)))))

;; (skip -proofs
;;  (defthm logbitp-of-logxor
;;    (implies (and (natp n)
;;                  (integerp x)
;;                  (integerp y))
;;             (equal (LOGBITP N (LOGXOR X y))
;;                    (xor (logbitp n x)
;;                               (logbitp n y))))
;;    :hints (("Goal" :in-theory (enable logand LOGEQV logxor xor logbitp*)))))

;; ;drop?
;; (skip -proofs
;;  (defthm getbit-ash-1
;;    (implies (and (<= c n)
;;                  (natp n)
;;                  (natp c)
;;                  (integerp i))
;;             (equal (getbit N (ASH i c))
;;                    (getbit (- n c) i)))
;;  :hints (("Goal" :in-theory (e/d (ash logbitp LOGAPP ) ())))))




;; ;bozo what about associativity?
;; ;this assumes it has already fired
;; ;bozo probably we only want to handle nests where the size is the same?
;; (defun unsorted-bvxor-nestp (term)
;;   (declare (xargs :guard (pseudo-termp term)))
;;   (if (consp term)
;;       (let* ((fun (car term)))
;;         (if (equal 'bvxor fun)
;;             (if (and (consp (caddr term))
;;                      (equal (car (caddr term)) 'bvxor))
;;                 ..
;;               ;bvxor nest with exactly two elems:
;;               (smaller-bvxor-arg (caddr term) (cadddr term)

;;                 nil)))
;;     nil))







;; (defthm true-listp-of-get-field-contents-of-initialize-2d-array-same-2
;;   (implies (and (natp numrows)
;;                 (memberp ad (n-new-ads numrows (set::insert ad2 (rkeys heap)))))
;;            (equal (true-listp (GET-FIELD AD (array-contents-pair)
;;                                          (JVM::INITIALIZE-2D-ARRAY AD2 type NUMROWS NUMCOLS HEAP)))
;;                   t))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-2d-array))))

;; (defthm get-class-of-initialize-one-dim-arrays-when-member
;;   (implies (memberp ad ads)
;;            (equal (get-field ad '(:special-data . :class) (jvm::initialize-one-dim-arrays ads type vals heap))
;;                   (jvm::make-one-dim-array-type type)))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-one-dim-arrays
;;                                      jvm::initialize-one-dim-array ;yuck
;;                                      ))))

;; (defthm get-class-of-initialize-2d-array-sub-array
;;   (implies (memberp ad (n-new-ads2 outercount (set::insert addr (rkeys heap))))
;;            (equal (get-field ad (class-pair) (jvm::initialize-2d-array addr type outercount innercount heap))
;;                   (jvm::make-one-dim-array-type type)))
;;   :hints (("Goal" :in-theory (e/d (JVM::INITIALIZE-ONE-DIM-ARRAYS) (EQUAL-CONS-CASES2-ALT-BETTER)))))

;; (defthm g-of-g-contents-of-initialize-2d-array-same
;;   (equal (g (array-contents-pair) (g ad (jvm::initialize-2d-array ad type numrows numcols heap)))
;;          (n-new-ads numrows (set::insert ad (rkeys heap))))
;;   :hints (("Goal" :in-theory (enable jvm::initialize-2d-array))))


;; (DEFTHM G-of-g-CONTENTS-OF-INITIALIZE-2D-ARRAY-SUB-ARRAY
;;   (IMPLIES (MEMBERP AD (N-NEW-ADS JVM::OUTERCOUNT (SET::INSERT JVM::ADDR (RKEYS JVM::HEAP))))
;;            (EQUAL (G (array-contents-pair)
;;                      (G AD
;;                         (JVM::INITIALIZE-2D-ARRAY JVM::ADDR
;;                                                  TYPE JVM::OUTERCOUNT JVM::INNERCOUNT
;;                                                  JVM::HEAP)))
;;                   (JVM::INITIAL-ARRAY-CONTENTS TYPE JVM::INNERCOUNT)))
;;   :hints (("Goal" :use (:instance GET-FIELD-CONTENTS-OF-INITIALIZE-2D-ARRAY-SUB-ARRAY)
;;            :in-theory (e/d (get-field)( GET-FIELD-CONTENTS-OF-INITIALIZE-2D-ARRAY-SUB-ARRAY)))))



;These rules add bvchop around the argument of a bit-vector function when that argument is not a bit-vector operator.
;This is needed for things to type-check for STP.
;Example, if X is a usb16, then (bvxor 8 x y) doesn't type check, so we make it (bvxor 8 (bvchop 8 x) y).
;should this be stp-theory?
;; (deftheory add-bvchops '(;add-bvchop-to-bvxor-1
;;                           ;add-bvchop-to-bvxor-2
;;                           ;add-bvchop-to-bvand-1
;;                           ;add-bvchop-to-bvand-2
;;                           add-bvchop-to-bvcat-1
;;                           add-bvchop-to-bvcat-2))

;; (deftheory remove-bvchops '(bvxor-of-bvchop-1
;;                              bvxor-of-bvchop-2
;;                              bvcat-of-bvchop-low
;;                              bvcat-of-bvchop-high
;;                              bvxor-1-of-getbit-arg1
;;                              bvxor-1-of-getbit-arg2
;;                              bvand-1-of-getbit-arg1
;;                              bvand-1-of-getbit-arg2
;;                              bvif-of-getbit-arg1
;;                              bvif-of-getbit-arg2
;;                              ))

;; ;BOZO
;; (deftheory remove-bvchops2 '(bvxor-of-bvchop-1
;;                              bvxor-of-bvchop-2
;;                              bvcat-of-bvchop-low
;;                              bvcat-of-bvchop-high
;;                              bvxor-1-of-getbit-arg1
;;                              bvxor-1-of-getbit-arg2
;;                              bvand-1-of-getbit-arg1
;;                              bvand-1-of-getbit-arg2
;;                              bvif-of-getbit-arg1
;;                              bvif-of-getbit-arg2
;;                              trim-to-n-bits-meta-rule
;;                              trim-to-n-bits-meta-rule-for-logops
;;                              trim-to-n-bits-meta-rule-for-slice
;;                              ))

;BOZO or should we handle this in our translation to STP?
;we could also handle the adding of bvchops when we translate to stp?
;; (deftheory add-padding '(bvcat-pad-low
;;                          bvcat-pad-high
;;                          bvmult-pad-arg1
;;                          bvmult-pad-arg2
;;                          bvxor-pad-arg1
;;                          bvxor-pad-arg2))

;; (defthm val-of-myif
;;   (equal (val n (myif test x y))
;;          (myif test (val n x)
;;                (val n y)))
;;   :hints (("Goal" :in-theory (enable myif))))
