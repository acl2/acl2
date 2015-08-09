#|
  Book:    make-theorems
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

;; --------------------------------------------------------
;; INCLUDE BOOKS

;; Dave Greeve's symbol manipulation functions
(include-book "symbol-manip")

;; general rewrites needed for compiled vectors
(include-book "vector-comp-canon")

;; to reason about firstn
(include-book "list-defthms-help")

;; primitive definitions
(include-book "source_shallow")

;; extra ihs theorems
(include-book "ihs-defthms-help")

;; more helper theorems for appending
(include-book "append-defthms-help")

(include-book "data-structures/list-defthms" :dir :system)

(include-book "arithmetic/top-with-meta" :dir :system)

;; computed hints
(include-book "computed-hints")

; Edited by Matt K.:
; (include-book "super-ihs" :dir :super-ihs)
(include-book "coi/super-ihs/super-ihs" :dir :system)
;; --------------------------------------------------------


;; --------------------------------------------------------
;; THEOREM TYPES
(defmacro comp-thm (name itr-term ind-term)
`(encapsulate ()
  (defthm ,name
     (equal  ,itr-term ,ind-term)
     :hints (("Goal"
              :induct t)
             (stable-simp-enable-hint1 stable-under-simplificationp pspv)
             (stable-simp-enable-hint2 stable-under-simplificationp pspv)
             (disable-hint '(nats-list-nth ,(car itr-term) ,(car ind-term)) nil))))
)
(defmacro type-thm (name itr-term ind-term labels)
`(encapsulate ()
  (defthm ,name
     (equal ,ind-term ,itr-term)
     :hints ((stable-simp-enable-hint1 stable-under-simplificationp pspv)
             (stable-simp-enable-hint2 stable-under-simplificationp pspv)
             (disable-hint ',labels nil))))
)
(defmacro fn-thm (name itr-term ind-term)
`(encapsulate ()
  (defthm ,name
     (equal  ,ind-term ,itr-term)
     :hints ((stable-simp-enable-hint1 stable-under-simplificationp pspv)
             (stable-simp-enable-hint2 stable-under-simplificationp pspv)
             (disable-hint ',(list (car itr-term) (car ind-term)) nil))))
)
;; inst-thm helper function.
(defun make-instantiations (instantiations)
  (if (endp instantiations) nil
    (cons `(:instance ,(caar instantiations) ,@(cdar instantiations))
          (make-instantiations (cdr instantiations)))))

;; inst-thm helper function.
(defun make-inst-thms (instantiations)
  (if (endp instantiations) nil
    (cons (caar instantiations)
          (make-inst-thms (cdr instantiations)))))


;;  ------------------------------------------------------
;; STREAM CLIQUE INVARIANT STUFF

;; makes statement of equivalence for an arbitrary family of recursive streams.
  (defun multi-nthpred (inv-name arg-lst ind-name n index-name)
    (declare (xargs :mode :program))
    (let ((nthpred (join-symbols1 inv-name inv-name '|-nthpred-| index-name))
          (hist-inv-hlp (join-symbols1 inv-name inv-name '|-hist-inv-hlp-| index-name)))

      (list
       `(defun ,nthpred (hist ,@arg-lst j)
          (equal (nth (loghead ,n j) hist)
                 (,ind-name ,@arg-lst j ',index-name)))

       `(defun ,hist-inv-hlp (hist ,@arg-lst i j)
          (if (not (and (natp j)
                        (< j i)
                        (<= (- i (expt2 ,n)) j))) T
            (,nthpred hist ,@arg-lst j))))))

(defun make-multi-nthpred (inv-name arg-lst ind-name n-lst index-names)
  (declare (xargs :mode :program))
  (if (endp index-names) nil
    `(,@(multi-nthpred inv-name arg-lst ind-name
                       (car n-lst) (car index-names))
      ,@(make-multi-nthpred inv-name arg-lst ind-name (cdr n-lst)
                            (cdr index-names)))))

(defun this-stream-hist (one-stream? branches)
  (if one-stream? 'hist `(nth ,branches hist)))

(defun make-inv-hlp (inv-name index-names arg-lst branches one-stream?)
  (declare (xargs :mode :program))
  (let ((hist-inv-hlp (join-symbols1 inv-name inv-name '|-hist-inv-hlp-| (car index-names))))
    (if (endp index-names) nil ;;`(,hist-inv-hlp (nth ,branches hist) ,@arg-lst i j)
      (cons `(,hist-inv-hlp ,(this-stream-hist one-stream? branches)
                            ,@arg-lst i j)
            (make-inv-hlp inv-name (cdr index-names) arg-lst (- branches 1) one-stream?)))))

(defun make-invs (arg-lst inv-name index-names branches one-stream?)
  (declare (xargs :mode :program))
  (let ((hist-inv-hlps (join-symbols1 inv-name inv-name '|-hist-inv-hlp|)))
    (list `(defun ,hist-inv-hlps (hist ,@arg-lst i j)
             (if (zp j)
                 (and ,@(make-inv-hlp inv-name index-names arg-lst branches one-stream?))
               (and ,@(make-inv-hlp inv-name index-names arg-lst branches one-stream?)
                    (,hist-inv-hlps hist ,@arg-lst i (- j 1))))))))

;; three lemmas about each branch in a clique of streams.
(defun inv-defun-events (ind-name inv-name arg-lst n index-name branches one-stream?)
  (declare (xargs :mode :program))
  (let ((hist-inv-hlps (join-symbols1 inv-name inv-name '|-hist-inv-hlp|))
        (hist-inv-j (join-symbols1 inv-name inv-name '|-hist-inv-j-| index-name))
        (hist-inv-l (join-symbols1 inv-name inv-name '|-hist-inv-l-| index-name))
        (ihs-help (join-symbols1 inv-name inv-name '|-ihs-help-| index-name)))

    (list

     ;; first, we want to do the boiler-plate in a clean rule environment
     `(local (set-default-hints nil))

     `(defthmd ,hist-inv-j
        (implies (and (<= l j)
                      (natp j)
                      (< j i)
                      (natp l)
                      (<= (- i (expt2 ,n)) l)
                      (,hist-inv-hlps hist ,@arg-lst i j))
                 (equal (,ind-name ,@arg-lst l ',index-name)
                        (nth (loghead ,n l)
                             ,(this-stream-hist one-stream? branches))
                        ))
        :hints (("Goal"
                 :induct t
                 )))


     `(defthm ,hist-inv-l
        (implies (and (natp l)
                      (natp i)
                      (< l i)
                      (<= (- i (expt2 ,n)) l)
                      (,hist-inv-hlps hist ,@arg-lst i (- i 1)))
                 (equal
                        (,ind-name ,@arg-lst l ',index-name)
                        (nth (loghead ,n l)
                             ,(this-stream-hist one-stream? branches))))
        :hints (("Goal"
                 :use (:instance ,hist-inv-j (j (- i 1)))
                 :in-theory (disable ,hist-inv-hlps
                                     (:executable-counterpart expt)
                                     unsigned-byte-p-forward-to-expt-bound
                                     unsigned-byte-p-loghead-forward-chaining
                                     unsigned-byte-p-forward-to-nonnegative-integerp)))
        :rule-classes
        ,(if (equal n 0)
             `(:rewrite
               (:rewrite
                :corollary (implies (and (natp l)
                                         (natp i)
                                         (< l i)
                                         (<= (- i (expt2 ,n)) l)
                                         (,hist-inv-hlps hist ,@arg-lst i (- i 1)))
                                    (equal (,ind-name ,@arg-lst l ',index-name)
                                           (nth 0 ,(this-stream-hist one-stream? branches))))
                :hints (("Goal"
                        :in-theory (disable ,hist-inv-hlps
                                            (:executable-counterpart expt)
                                            unsigned-byte-p-forward-to-expt-bound
                                            unsigned-byte-p-loghead-forward-chaining
                                            unsigned-byte-p-forward-to-nonnegative-integerp)))))
           ':rewrite))

     ;; specific ihs-helper theorem for the "nthred-most theorem" below
     `(defthmd ,ihs-help
        (implies (and (integerp i)
                      (integerp j)
                      (<= 0 j)
                      (<= 0 i)
                      (< j i)
                      (equal (loghead ,n j)
                             (loghead ,n i))
                      (<= (+ ,(- (- (expt2 n) 1)) i) j))
                 (>= j i))
        :hints (("Goal" :in-theory (enable loghead)))
        :rule-classes ((:forward-chaining :trigger-terms ((equal (loghead ,n j)
                                                                 (loghead ,n i)))))))))

(defun make-inv-equivs-rec (ind-name arg-lst index-names n-lst itr-name branches)
  (if (endp index-names) nil
    (cons `(equal (,ind-name ,@arg-lst lim ',(car index-names))
                  (nth (loghead ,(car n-lst) lim)
                       (nth ,branches (,itr-name ,@arg-lst i lim hist))))
          (make-inv-equivs-rec ind-name arg-lst (cdr index-names)
                               (cdr n-lst) itr-name (- branches 1)))))

(defun make-inv-equivs (ind-name arg-lst index-names n-lst itr-name branches)
  ;; first case is for when hist is a flat list (not a buffer of buffers)
  (if (equal branches 0)
      `((equal (,ind-name ,@arg-lst lim ',(car index-names))
               (nth (loghead ,(car n-lst) lim)
                    (,itr-name ,@arg-lst i lim hist))))
    (make-inv-equivs-rec ind-name arg-lst index-names
                         n-lst itr-name branches)))

       (defun inst-mk-cases (n size)
          (if (zp size) `((equal (loghead ,n lim) ,size))
            (cons `(equal (loghead ,n lim) ,size)
                  (inst-mk-cases n (- size 1)))))

       (defun inst-hint (susp size)
         (if susp `(:cases ,(inst-mk-cases size (- (expt2 size) 1)))
           nil))


(defun make-inv-inst-thms (arg-lst inv-name index-names n-lst itr-inst
                                   init-hist single-hist branches)
  (declare (xargs :mode :program))
  (if (endp index-names) nil
    (let ((inv-inst (join-symbols1 inv-name inv-name (car index-names) '|-inst-thm|))
          (inv-inst-alt (join-symbols1 inv-name inv-name (car index-names) '|-inst--alt-thm|))
          (ind-inst (join-symbols1 inv-name '|ind_| (car index-names))))
      (cons
       `(defthm ,inv-inst
          (equal (,ind-inst ,@arg-lst lim)
                 (nth (loghead ,(car n-lst) lim)
                      ,(if single-hist
                           `(,itr-inst ,@arg-lst lim)
                         `(nth ,branches (,itr-inst ,@arg-lst lim)))))
          :hints (("Goal"
                   :in-theory (enable ,ind-inst ,itr-inst loghead-0)
                   :use (:instance ,inv-name (lim lim) (i 0) (hist ',init-hist)))
                  (inst-hint stable-under-simplificationp ',(car n-lst))))
       (cons
        `(defthmd ,inv-inst-alt
           (equal
            (nth (loghead ,(car n-lst) lim)
                 ,(if single-hist
                      `(,itr-inst ,@arg-lst lim)
                    `(nth ,branches (,itr-inst ,@arg-lst lim))))
            (,ind-inst ,@arg-lst lim)))
        (make-inv-inst-thms arg-lst inv-name (cdr index-names) (cdr n-lst) itr-inst
                            init-hist single-hist (- branches 1)))))))

(defmacro defthmd+ (&rest args)
  `(progn (in-theory (current-theory :here))
          (defthmd ,@args)))

(defun make-update-hists (index-names n-lst branches one-stream?)
  (declare (xargs :mode :program))
  (let ((up (join-symbols1 '|up| '|up| (car index-names))))
    (if (endp index-names) nil
      (cons `(update-nth
              (loghead ,(car n-lst) i) ,up
              ,(this-stream-hist one-stream? branches))
            (make-update-hists (cdr index-names) (cdr n-lst) (- branches 1) one-stream?)))))

(defun make-ihs-names (inv-name index-names)
    (if (endp index-names) nil
      (cons (join-symbols1 inv-name inv-name '|-ihs-help-| (car index-names))
            (make-ihs-names inv-name (cdr index-names)))))

(defun ind-inst-names (inv-name index-names)
  (if (endp index-names) nil
    (cons (join-symbols1 inv-name '|ind_| (car index-names))
          (ind-inst-names inv-name (cdr index-names)))))

(defun main-inv-expand (inv-name arg-lst arg-preds ind-name itr-name
                                 n-lst index-names branches one-stream? init-hist)
  (declare (xargs :mode :program))
  (let ((hist-inv-hlps (join-symbols1 inv-name inv-name '|-hist-inv-hlp|))
        (hist-inv-most (join-symbols1 inv-name inv-name '|-hist-inv-most|))
        (itr-loop-name (join-symbols1 itr-name '|$itr_loop_| itr-name))
        (itr-inst (join-symbols1 itr-name '|itr_| itr-name)))

    (append (list

     `(defthm ,hist-inv-most
       (implies (and (< j i)
                     (natp j)
                     (natp i)
                     (equal l (loghead ,(car n-lst) i))
                     (consp hist)
                     (,hist-inv-hlps hist ,@arg-lst i j))
                (,hist-inv-hlps ,(if one-stream?
                                     `(update-nth l
                                                  up
                                                  ,(this-stream-hist one-stream? branches))
                                   `(list ,@(reverse (make-update-hists
                                                      index-names n-lst branches one-stream?))))
                                ,@arg-lst (+ 1 i) j))
       :hints (("Goal" :induct t
                :in-theory (e/d (,@(make-ihs-names inv-name index-names)
                                 update-nth update-nth-update-nth)
                                (loghead-1))
                :expand ((:free ,`(index-name)
                                (,ind-name ,@arg-lst 1 index-name))
                         (:free ,`(index-name)
                                (,ind-name ,@arg-lst 0 index-name))
                         (:free ,`(up) (,hist-inv-hlps up ,@arg-lst (+ 1 i) j))))))

     ;; -----------------------------------------------
     ;; rules we don't want for the invariant proof
     `(local (in-theory (disable update-nth-update-nth)))

     `(local (in-theory (disable LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT)))
     `(local (in-theory (disable LOGHEAD-SUM-CHOP-FIRST-ARG-WHEN-CONSTANT-ALT)))

     ;; this rule in super-ihs should be disabled, for our purposes
     `(local (in-theory (disable loghead-1)))
     `(local (in-theory (disable loghead-identity)))

     `(local (in-theory (disable loghead-equal-rewrite-constant-case)))
     `(local (in-theory (disable loghead-plus-constant-equal-constant)))
     `(local (in-theory (disable loghead-when-size-is-not-positive)))

     `(local (in-theory (disable UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING)))
     `(local (in-theory (disable unsigned-byte-p-forward-to-expt-bound)))
     `(local (in-theory (disable unsigned-byte-p-forward-to-nonnegative-integerp)))

     ;;         ;; now we add back all of our rules
     `(local (set-default-hints (list *priority-phased-simplification*)))
     `(local (add-priority 1 disable-hint))
     `(local (add-priority 2 hint-expand))
     `(local (add-priority 3 stable-simp-enable-hint3))
     `(local (add-priority 4 stable-simp-enable-hint1))
     `(local (add-priority 5 hint-loghead-0))
     ;; -----------------------------------------------

     `(defthmd+ ,inv-name
        (implies (and (true-listp hist)
                      (consp hist)
                      (natp lim)
                      (natp i)
                      (<= i (+ lim 1))
                      ,@arg-preds
                      (,hist-inv-hlps hist ,@arg-lst i (- i 1)))
                 (and ,@(make-inv-equivs ind-name arg-lst index-names
                                         n-lst itr-loop-name branches)))
        :hints (("Goal" :induct t)
                (hint-expand id ',arg-lst ',itr-loop-name ',ind-name ',inv-name)
                (hint-loghead-0 id)
                (stable-simp-enable-hint1 stable-under-simplificationp pspv)
                (stable-simp-enable-hint3 stable-under-simplificationp pspv)
                (disable-hint nil '(,hist-inv-hlps ,ind-name)))))

     (make-inv-inst-thms  arg-lst inv-name index-names n-lst itr-inst
                          init-hist one-stream? branches))))

(defun inv-expand (ind-name inv-name arg-lst n-lst index-names one-stream?)
  (declare (xargs :mode :program))
  (if (endp index-names) nil
    `(,@(inv-defun-events ind-name inv-name arg-lst
                          (car n-lst) (car index-names)
                          (- (len index-names) 1) one-stream?)
      ,@(inv-expand ind-name inv-name arg-lst
                    (cdr n-lst) (cdr index-names) one-stream?))))

(defmacro inv-encap (inv-name arg-lst arg-preds i-name itr-name n-lst index-names init-hist)
  (let* ((ind-name (join-symbols1 i-name '|$ind_block_| i-name))
         (rev-n-lst (reverse n-lst))
         (rev-index-names (reverse index-names))
         (streams (- (len rev-index-names) 1))
         (one-stream? (equal streams 0)))

    `(encapsulate ()
                  ,@(make-multi-nthpred inv-name arg-lst ind-name
                                        rev-n-lst rev-index-names)
                  ,@(make-invs arg-lst inv-name rev-index-names streams one-stream?)
                  ,@(inv-expand ind-name inv-name arg-lst
                                rev-n-lst rev-index-names one-stream?)
                  ,@(main-inv-expand inv-name arg-lst arg-preds ind-name itr-name rev-n-lst
                                     rev-index-names streams one-stream? init-hist))))

(defun inv-inst-alts (name index-names)
  (if (endp index-names) nil
    (cons (join-symbols1 name name (car index-names) '|-inst--alt-thm|)
          (inv-inst-alts name (cdr index-names)))))

(defun inv-insts (name index-names)
  (if (endp index-names) nil
    (cons (join-symbols1 name name (car index-names) '|-inst-thm|)
          (inv-insts name (cdr index-names)))))

(defun ind-block-calls (name index-names)
  (if (endp index-names) nil
    (cons (join-symbols1 name '|ind_| (car index-names))
          (ind-block-calls name (cdr index-names)))))

(defmacro takes-thm (name depth hist-size inv-name itr-name arg-lst
                           arg-preds ind-takes i-name index-names init-hist)
  (let ((hist-inv-hlps (join-symbols1 inv-name inv-name '|-hist-inv-hlp|))
        (ind-name (join-symbols1 i-name '|$ind_block_| i-name))
        (itr-loop-name (join-symbols1 itr-name '|$itr_loop_| itr-name))
        (itr-inst (join-symbols1 itr-name '|itr_| itr-name))
        (name2 (join-symbols1 name name '|inst|)))


  `(encapsulate ()

(local (in-theory (disable loghead-ash-pos-rewrite)))
(local (in-theory (disable loghead-+-logior)))
(local (in-theory (disable logior-=-0)))
(local (in-theory (disable logxor-rewrite)))
(local (in-theory (disable loghead-logior)))

(local (add-priority 1 disable-hint))
(local (add-priority 2 stable-simp-enable-hint1))
(local (add-priority 3 stable-simp-enable-hint2))
(local (disable-prioritized-runes))


  (defthm ,name
     (implies (and (natp i)
                   (<= i ,depth)
                   (true-listp hist)
                   (consp hist)
                   (equal (len hist) ,hist-size)
                   ,@arg-preds
                   (,hist-inv-hlps hist ,@arg-lst i (- i 1)))
              (equal (firstn ,depth (,itr-loop-name ,@arg-lst i ,(- depth 1) hist))
                     (append (firstn i hist) (,ind-takes ,@arg-lst i))))
     :hints (("Goal" :induct t)
                (hint-expand id ',arg-lst ',itr-loop-name ',ind-name ',inv-name)
             (stable-simp-enable-hint1 stable-under-simplificationp pspv)
             (stable-simp-enable-hint2 stable-under-simplificationp pspv)
             (disable-hint '(,@(inv-inst-alts inv-name index-names)
                             ,@(ind-block-calls i-name index-names))
                           '(,@(inv-insts inv-name index-names)
                             ,hist-inv-hlps))))

  (defthm ,name2
    (implies (and ,@arg-preds)
             (equal (firstn ,depth (,itr-inst ,@arg-lst ,(- depth 1)))
                    (,ind-takes ,@arg-lst 0)))
             :hints (("Goal"
                      :in-theory (enable ,itr-inst ,hist-inv-hlps)
                      :use (:instance ,name (i 0) (hist ',init-hist))))))))
;; END STREAM CLIQUE INVARIANT STUFF
;; -----------------------------------------------------------------


;; -----------------------------------------------------------------
;; VECTOR SPLIT STUFF
(defun make-c-vec-split-expand (size length)
  (if (not (and (< 0 size) (natp size) (<= size length))) nil
    (if (zp length) nil
      (cons `(c-vec-split ,size (nthcdr ,length x))
            (make-c-vec-split-expand size (- length size))))))

(defun hint-c-vec-split (susp size length)
  (if susp `(:expand ((c-vec-split ,size x)
                      ,@(make-c-vec-split-expand size length)))
    nil))

(defun make-cases (i size)
  (if (zp size) `((equal ,i ,size))
    (cons `(equal ,i ,size)
          (make-cases i (- size 1)))))

(defun hint-split (susp i size)
  (if susp `(:cases ,(make-cases i (- size 1)))
    nil))

(defmacro vec-split-true-listp-thm (name type size length)
  `(defthm ,name
     (implies (and (,type x)
                    (natp |i|)
                    (<= |i| ,size))
               (true-listp (nth |i| (c-vec-split ,size x))))
     :hints (("Goal" :in-theory (enable ,type))
             (hint-split stable-under-simplificationp '|i| ,size)
             (hint-c-vec-split stable-under-simplificationp ,size ,length))))

(defmacro vec-split-eq-thm (name type size length)
  `(defthm ,name
     (implies (and (,type x)
                   (natp |i|) (natp |j|) (< |j| ,size) (< |i| ,size))
              (equal (nth |j| (nth |i| (c-vec-split ,size x)))
                     (nth (+ (* |i| ,size) |j|) x)))
     :hints (("Goal" :in-theory (enable ,type))
             (hint-split stable-under-simplificationp '|i| ,size)
             (hint-c-vec-split stable-under-simplificationp ,size ,length))))

(defmacro make-vec-thm (name type1 type2 vec-size vec-length)
  `(encapsulate ()
                (vec-split-true-listp-thm ,(join-symbols1 name name '|-true-listp-thm|)
                                           ,type1 ,vec-size ,vec-length)
                (vec-split-eq-thm ,(join-symbols1 name name '|-split-eq-thm|)
                                  ,type1 ,vec-size ,vec-length)
                (defthm ,name
                   (implies (,type1 x)
                            (,type2 (c-vec-split ,vec-size x)))
                   :hints (("Goal" :in-theory (disable nth))
                           (stable-simp-enable-hint1 stable-under-simplificationp pspv)
                           (stable-simp-enable-hint2 stable-under-simplificationp pspv)
                           (disable-hint '(,type1 ,type2) nil)))))

;; END VECTOR SPLIT STUFF
;; -----------------------------------------------------------------


(defmacro make-thm (&key
               (name 'name)
               (thm-type 'fn)
               (itr-term 'nil)
               (ind-term 'nil)
               (enables 'nil)
               (itr-name 'nil)
               (ind-name 'nil)
               (arg-types 'nil)
               (arg-list 'nil)
               (hist-widths 'nil)
               (branches 'nil)
               (take-depth 'nil)
               (init-hist 'nil)
               (hist-width 'nil)
               (invar-thm 'nil)
               (ind-loop 'nil)
               (type1 'nil)
               (type2 'nil)
               (vector-length 'nil)
               (vector-size 'nil))
  (cond ((equal thm-type 'fn) `(fn-thm ,name ,itr-term ,ind-term))
        ((equal thm-type 'type) `(type-thm ,name ,itr-term ,ind-term ,enables))
        ((equal thm-type 'comp) `(comp-thm ,name ,itr-term ,ind-term))
        ((equal thm-type 'invariant)
         `(inv-encap ,name ,arg-list ,arg-types ,ind-name ,itr-name
                     ,hist-widths ,branches ,init-hist))
        ((equal thm-type 'takes)
         `(takes-thm ,name ,take-depth ,hist-width ,invar-thm ,itr-name
                     ,arg-list ,arg-types ,ind-name ,ind-loop ,branches ,init-hist))
        ((equal thm-type 'vector-split)
         `(make-vec-thm ,name ,type1 ,type2 ,vector-size ,vector-length))))

