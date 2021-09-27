; Even more utilities supporting the lifter(s)
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

;; This book contains lifter utilities that involve the rewriter (and thus
;; depends on skip-proofs).

(include-book "../rewriter")
(include-book "rule-lists-jvm")
(include-book "lifter-utilities") ;for standard-hyps-basic0
(include-book "kestrel/utilities/unify" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

(local (in-theory (disable acl2-count
                           consp-from-len-cheap)))

(local (in-theory (enable member-equal-becomes-memberp))) ;todo

;move
;todo: use this more!  may help when setting a field other than the class inside of the set of the class
;we could even name the class pair in such a way that it always comes first...
(defthm insert-of-rkeys-of-set-field-same
  (equal (set::insert ad (rkeys (set-field ad pair val heap)))
         (set::insert ad (rkeys heap))))

(defthm >=-len-of-len-same
  (>=-len x (len x)))

(defthm >=-len-rewrite
  (implies (natp n)
           (equal (>=-len x n)
                  (>= (len x) n))))

(defthm all->=-len-when-items-have-len
  (implies (and (items-have-len m items)
                (true-listp items) ;drop?
                (natp n)
                (integerp m)
                (<= n m)
                )
           (all->=-len items n) ;todo: this should not check the final cdr
           )
  :hints (("Goal" :in-theory (enable >=-LEN))))

(defthm alistp-when-items-have-len
  (implies (and (true-listp heap-triples)
                (items-have-len n heap-triples) ;n is a free var
                (posp n))
           (alistp heap-triples))
  :hints (("Goal" :in-theory (enable items-have-len alistp))))

(defun missing-classes (dag-lst)
  (if (endp dag-lst)
      nil
    (let* ((entry (first dag-lst))
           (expr (cdr entry)))
      (if (and (consp expr)
               (eq 'g (ffn-symb expr))
               (quotep (farg1 expr))
               (stringp (unquote (farg1 expr)))
               (natp (farg2 expr))
               (call-of 'JVM::CLASS-TABLE (lookup (farg2 expr) dag-lst)))
          (cons (unquote (farg1 expr)) (missing-classes (rest dag-lst)))
        (missing-classes (rest dag-lst))))))


;;do we need hyps about the class table?
;; Returns (mv erp result state)
(defund run-static-initializer-for-next-class (class-name th s-dag hyps ;class-table-map
                                                         extra-rules monitored-rules
                                                         state)
  (declare (xargs :mode :program :stobjs (state))
           (ignore th) ;todo!
           )
  (b* ((- (cw "(Running initializer for ~x0.~%" class-name))
       ((mv erp term-to-run) (dagify-term2 `(run-until-return-from-stack-height
                                             (binary-+ '1 (stack-height s0))
                                             ;; The dag-to-term here might be slow:
                                             (jvm::invoke-static-initializer-for-next-class ',class-name (th) ,(dag-to-term s-dag))
                                             )))
       ((when erp) (mv erp nil state))
       (- (cw "Term to run: ~x0" term-to-run))
       (- (cw "Assumptions: ~x0" hyps))
       ((mv erp result state)
        (simp-dag term-to-run
                  :rules (append extra-rules
                                 (run-until-return-from-stack-height-rules-smart)
                                 (rule-list-1001))
                  :monitor monitored-rules
                  :interpreted-function-alist (make-interpreted-function-alist '(get-SUPERCLASSES) (w state))
                  :assumptions hyps
                  ;; :print t
                  ;; :print-interval 100000
                  :simplify-xorsp nil
                  :check-inputs nil))
       ((when erp) (mv erp nil state))
       (- (cw "Result: ~X01)" result nil))
       (missing-classes (missing-classes result))
       (- (and missing-classes (cw "~%NOTE: The following classes seem to be missing (consider including their books in your session): ~x0~%" missing-classes)))
       ((when (member-eq 'run-until-return-from-stack-height (dag-fns result))) ;perhaps the result must actually be a make-state??
        (mv :failed-to-initialize-class
            (er hard 'run-static-initializer-for-next-class "Failed to initialize ~s0 (see above)." class-name)
            state)))
    ;;i've seen this fail to resolve a lookup (call to 'g') of a class name in the class table, because i failed to include the class table hyp for that class
    (mv (erp-nil) result state)))

;may have to initialize super classes first..
;; Returns (mv erp result state)
(defund initialize-class (class-name th s-dag hyps ;class-table-map
                                    extra-rules monitored-rules
                                    state)
  (declare (xargs :mode :program
                  :stobjs (state)
                  :guard (and (jvm::class-namep class-name)
                              (symbol-listp extra-rules))))
  (b* (((mv erp dag)
        (compose-term-and-dag `(memberp ',class-name (jvm::initialized-classes replace-me))
                              'replace-me
                              s-dag))
       ((when erp) (mv erp nil state))
       ((mv erp result state)
        (simp-dag
         dag
         :rules (append '( ;bool-fix ;looped?
                          ;;BOOL-FIX-WHEN-BOOLEANP
                          ;;jvm::in-of-rkeys-when-g
                          ;;jvm::in-of-rkeys-when-g-rev
                          )
                        extra-rules
                        '(jvm::initialized-classes-of-make-state
                          memberp-constant-opener)
                        ;;(rule-list-1001)
                        )
         :monitor (append monitored-rules
                          '( ;JVM::LOOKUP-FIELD-BASE-3
                            ;;jvm::in-of-rkeys-when-g
                            ;;jvm::in-of-rkeys-when-g-rev
                            ))
         ;; :print t
         :simplify-xorsp nil
         :assumptions hyps
         :check-inputs nil))
       ((when erp) (mv erp nil state))
       ;; TODO: Better error message if the run didn't finish!
       ;; (- (cw "~X01" hyps nil))
       ((when (not (quotep result)))
        (let ((missing-classes (missing-classes result)))
          (progn$ (print-list result)
                  (and missing-classes (cw " Note: The following classes seem to be missing (consider including their books in your session): ~x0" missing-classes))
                  (mv (erp-t)
                      (er hard? 'initialize-class "Could not determine whether class ~x0 is initialized (see result just above)" class-name)
                      state))))
       (result (safe-unquote result)))
    (if result
        (mv (erp-nil) s-dag state)
      (mv-let (erp result state)
        (run-static-initializer-for-next-class class-name th s-dag hyps ;class-table-map
                                               extra-rules monitored-rules
                                               state)
        (if erp
            (mv erp nil state)
          (initialize-class class-name th
                            result
                            hyps
                            ;;class-table-map
                            extra-rules monitored-rules
                            state))))))

;; Returns (mv erp dag state)
(defund initialize-classes (class-names th s-dag hyps ;class-table-map
                                       extra-rules monitored-rules
                                       state)
  (declare (xargs :mode :program
                  :stobjs (state)
                  :guard (and (symbol-listp extra-rules)
                              (jvm::all-class-namesp class-names)
                              ;; what about th?
                              (weak-dag-or-quotep s-dag)
                              (pseudo-term-listp hyps)
                              (symbol-listp extra-rules)
                              (symbol-listp monitored-rules))))
  (if (endp class-names)
      (mv (erp-nil) s-dag state)
    (let ((class-name (car class-names)))
      (prog2$ (cw "(Initializing class ~x0 (and perhaps its super classes).~%" class-name)
              (mv-let (erp s-dag state)
                (initialize-class class-name th s-dag hyps ;class-table-map
                                  extra-rules monitored-rules
                                  state)
                (if erp
                    (mv erp nil state)
                  (prog2$ (cw ")~%")
                          (initialize-classes (cdr class-names)
                                              th
                                              s-dag
                                              hyps
                                              ;;class-table-map
                                              extra-rules monitored-rules
                                              state))))))))

;; TODO: build a tool to abstract the result of this, making claims about
;; get-static-field and get-field of get-static-field for the initialized
;; stuff...  perhaps restrict is to state where all the values written to heap
;; addresses are constant.  Perhaps also do a proof that the assumptions
;; generated are not contradictory (e.g.,confirm that those claims all hold of
;; the initialized state)
;; Once made, such a tool could be used for many examples
;; TODO: the order of the calls to set-static-field may depend on DAG node number if we use the current rules...
;; Returns (mv erp term state).
(defun initialize-classes-in-arbitrary-state-fn (class-names assumptions extra-rules monitored-rules state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (b* ((state-var 's0)
       (assumptions (translate-terms assumptions 'initialize-classes-in-arbitrary-state-fn (w state)))
       ((mv erp state-var-dag) (dagify-term2 state-var)) ;todo: could call a dagify-var
       ((when erp) (mv erp nil state))
       ((mv erp result-dag state)
        (initialize-classes class-names
                            (th)
                            state-var-dag
                            (append `((equal (jvm::initialized-classes ,state-var) 'nil))
                                    (standard-hyps-basic0 state-var)
                                    (translate-terms (class-table-hyps2 state-var (global-class-alist state)) 'fake (w state))
                                    assumptions
                                    )
                            (append '(set-static-field-of-set-static-field-diff-class-axe
                                      set-static-field-of-set-static-field-diff-field-axe
                                      set-static-field-of-set-static-field-same ;always include?!
                                      )
                                    extra-rules)
                            (append monitored-rules
                                    nil ;'(jvm::invoke-static-initializer-for-next-class-base)
                                    )
                            state))
       ((when erp) (mv erp nil state)))
    (mv (erp-nil) (dag-to-term result-dag) state)))

;; Returns (mv erp term state).
(defmacro initialize-classes-in-arbitrary-state (class-names
                                                 &key
                                                 (assumptions 'nil)
                                                 (extra-rules 'nil)
                                                 (monitor 'nil)
                                                 )
  `(initialize-classes-in-arbitrary-state-fn ,class-names ,assumptions ,extra-rules ,monitor state))

;; Example call: (initialize-classes-in-arbitrary-state '("org.kethereum.hashes.Sha256"))


;; Check whether TERM is a suitable call to NEW-AD or NTH-NEW-AD on HEAP-TERM.
(defund symbolic-new-address-in-heapp (term heap-term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp heap-term))))
  (or (and (call-of 'new-ad term)
           (equal (farg1 term) `(rkeys ,heap-term)))
      (and (call-of 'nth-new-ad term)
           (myquotep (farg1 term))
           (natp (unquote (farg1 term)))
           (equal (farg2 term) `(rkeys ,heap-term)))))

(defund all-symbolic-new-address-in-heapp (terms heap-term)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-termp heap-term))))
  (if (endp terms)
      t
    (and (symbolic-new-address-in-heapp (first terms) heap-term)
         (all-symbolic-new-address-in-heapp (rest terms) heap-term))))

;; Check whether HEAP-TERM is a nest of set-fields wrapped around BASE-TERM.
(defund symbolic-set-field-nestp (heap-term base-heap-term)
  (declare (xargs :guard (and (pseudo-termp heap-term)
                              (pseudo-termp base-heap-term))))
  (if (equal heap-term base-heap-term)
      t
    (and (call-of 'set-field heap-term) ;; (set-field ad class-field-pair value heap)
         (= 4 (len (fargs heap-term)))
         (quotep (farg2 heap-term)) ;the class-name-field-name pair must be constant
         (symbolic-set-field-nestp (farg4 heap-term) base-heap-term))))

(defund get-heap-triples-from-symbolic-set-field-nest (heap-term base-heap-term)
  (declare (xargs :guard (and (pseudo-termp heap-term)
                              (pseudo-termp base-heap-term)
                              (symbolic-set-field-nestp heap-term base-heap-term))
                  :guard-hints (("Goal" :in-theory (enable symbolic-set-field-nestp)))))
  (if (equal heap-term base-heap-term)
      nil
    (if (not (mbt (consp heap-term))) ;to make the termination proof easier
        nil
      (let ((address-term (farg1 heap-term))
            (class-field-pair (farg2 heap-term)) ;quoted
            (value-term (farg3 heap-term)))
        (cons (list address-term class-field-pair value-term)
              (get-heap-triples-from-symbolic-set-field-nest (farg4 heap-term) base-heap-term))))))

(defund symbolic-set-static-field-nestp (static-field-map-term base-static-field-map-term)
  (declare (xargs :guard (and (pseudo-termp static-field-map-term)
                              (pseudo-termp base-static-field-map-term))))
  (if (equal static-field-map-term base-static-field-map-term)
      t
    (and (call-of 'jvm::set-static-field static-field-map-term)
         (= 4 (len (fargs static-field-map-term)))
         (quotep (farg1 static-field-map-term)) ;the class-name
         (quotep (farg2 static-field-map-term)) ;the field-id (name and type)
         (symbolic-set-static-field-nestp (farg4 static-field-map-term) base-static-field-map-term))))

(defund get-static-field-triples-from-symbolic-set-static-field-nest (static-field-map-term base-static-field-map-term)
  (declare (xargs :guard (and (pseudo-termp static-field-map-term)
                              (pseudo-termp base-static-field-map-term)
                              (symbolic-set-static-field-nestp static-field-map-term base-static-field-map-term))
                  :guard-hints (("Goal" :in-theory (enable symbolic-set-static-field-nestp)))))
  (if (equal static-field-map-term base-static-field-map-term)
      nil
    (if (not (mbt (consp static-field-map-term))) ;to make the termination proof easier
        nil
        (let ((class-name (farg1 static-field-map-term)) ;quoted
              (field-id (farg2 static-field-map-term))   ;quoted
              (value-term (farg3 static-field-map-term)))
          (cons (list class-name field-id value-term)
                (get-static-field-triples-from-symbolic-set-static-field-nest (farg4 static-field-map-term) base-static-field-map-term))))))

;also includes quoteps, since they have no vars
(defun symbolic-constantp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (null (all-vars term))  ;essentially a constant (covers constant arrays too)
  )

;; recognize a nest of conses ending in *nil*
(defun symbolic-listp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      nil
    (if (equal term *nil*)
        t
      (and (call-of 'cons term)
           (= 2 (len (fargs term)))
           (symbolic-listp (farg2 term))))))

;; (defforall-simple symbolic-listp :guard (pseudo-term-listp x))
;; (verify-guards all-symbolic-listp)

(defun symbolic-list-elements (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolic-listp term))))
  (if (not (mbt (consp term))) ;for termination
      nil
    (if (equal term *nil*)
        nil
      (cons (farg1 term)
            (symbolic-list-elements (farg2 term))))))

(defthm <-of-acl2-count-of-symbolic-list-elements
  (implies (symbolic-listp term)
           (< (acl2-count (symbolic-list-elements term))
              (acl2-count term))))

(defthm pseudo-term-listp-of-symbolic-list-elements
  (implies (and (pseudo-termp term)
                (symbolic-listp term))
           (pseudo-term-listp (symbolic-list-elements term))))

;; Recognize a constant or a new-address
(defun supported-scalar-termp (term heap-term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp heap-term))))
  (or (symbolic-constantp term)
      (symbolic-new-address-in-heapp term heap-term)))

;; Recognize a list of constants / new-addresses
(defun all-supported-scalar-termp (terms heap-term)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-termp heap-term))))
  (if (endp terms)
      t
    (and (supported-scalar-termp (first terms) heap-term)
         (all-supported-scalar-termp (rest terms) heap-term))))

;; Recognize a constant, a new-address, or an array where the values are constants / new-addresses
;; TODO: Can a non-constant bv-array arise?   Maybe not...
(defund supported-heap-value-termp (term heap-term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp heap-term))))
  (or (supported-scalar-termp term heap-term)
      ;; otherwise, must be a cons nest (this represents an array whose elements
      ;; are new addresses (or perhaps constants) -- note: the representation
      ;; of arrays of pointers may change in the future)
      (and (symbolic-listp term)
           (all-supported-scalar-termp (symbolic-list-elements term) heap-term))))

(defund all-supported-heap-value-term-in-heapp (terms base-heap-term)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-termp base-heap-term))))
  (if (endp terms)
      t
    (and (supported-heap-value-termp (first terms) base-heap-term)
         (all-supported-heap-value-term-in-heapp (rest terms) base-heap-term))))

(defun filter-non-supported-heap-value-terms-in-heapp (terms base-heap-term)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-termp base-heap-term))))
  (if (endp terms)
      nil
    (if (supported-heap-value-termp (first terms) base-heap-term)
        (filter-non-supported-heap-value-terms-in-heapp (rest terms) base-heap-term)
      (cons (first terms)
            (filter-non-supported-heap-value-terms-in-heapp (rest terms) base-heap-term)))))

(defun filter-non-quoteps (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (if (endp terms)
      nil
    (if (not (quotep (first terms)))
        (cons (first terms)
              (filter-non-quoteps (rest terms)))
      (filter-non-quoteps (rest terms)))))

(defthm pseudo-term-listp-of-filter-non-quoteps
  (implies (pseudo-term-listp items)
           (pseudo-term-listp (filter-non-quoteps items))))

(in-theory (disable STRIP-CADDRS-of-cdr)) ;looped

(defun all-bound-in-heap (ads heap)
  (declare (xargs :guard (true-listp ads)))
  (if (endp ads)
      t
    (and (set::in (first ads) (rkeys heap))
         (all-bound-in-heap (rest ads) heap))))

(defthm all-bound-in-heap-of-cons
  (equal (all-bound-in-heap (cons ad ads) heap)
         (and (set::in ad (rkeys heap))
              (all-bound-in-heap ads heap))))

(defthm all-bound-in-heap-of-nil
  (all-bound-in-heap nil heap))

(add-known-boolean all-bound-in-heap)

(defthm not-in-of-minus1
  (implies (all-addressp (set::2list dom))
           (not (set::in -1 dom)))
  :hints (("Goal" :in-theory (enable all-addressp))))

(defthm not-null-refp-of-nth-when-all-bound-in-heap
  (implies (and (all-bound-in-heap ads heap)
                (jvm::heapp heap)
                (< n (len ads))
                (natp n))
           (not (null-refp (nth n ads))))
  :hints (("Goal" :in-theory (e/d (JVM::HEAPP nth KEY-LIST)
                                  (;NTH-OF-CDR
                                   )))))

(defthm in-of-nth-new-ad-and-2set-of-n-new-ads
  (implies (and (<= m n)
                (posp m)
                (integerp n))
           (set::in (nth-new-ad m dom) (list::2set (n-new-ads n dom))))
  :hints (("Goal" :in-theory (disable n-new-ads-becomes-n-new-ads2))))

;; assumes that we can tell all the addresses apart syntactically
(defun heap-triple-fields-for-ad (heap-triples address)
  (declare (xargs :guard (and (true-listp heap-triples)
                              (items-have-len 3 heap-triples))))
  (if (endp heap-triples)
      nil
    (let* ((triple (first heap-triples))
           (triple-address (first triple)))
      (if (not (equal triple-address address))
          (heap-triple-fields-for-ad (rest heap-triples) address)
        (let ((triple-field (second triple)))
          (cons triple-field
                (heap-triple-fields-for-ad (rest heap-triples) address)))))))

;; ;; Check whether all the ADS have value VAL for the given class-name-field-name
;; ;; pair.
;; (defun all-have-field-val (ads pair val heap)
;;   (declare (xargs :guard (and (true-listp ads)
;;                               (jvm::heapp heap))))
;;   (if (endp ads)
;;       t
;;     (let ((ad (first ads)))
;;       (and (equal val (get-field ad pair heap))
;;            (all-have-field-val (rest ads) pair val heap)))))

;; (defthm all-have-field-val-of-cons
;;   (equal (all-have-field-val (cons ad ads) pair val heap)
;;          (and (equal val (get-field ad pair heap))
;;               (all-have-field-val ads pair val heap))))

;; (defthm all-have-field-val-of-nil
;;   (all-have-field-val nil pair val heap))

;; (add-known-boolean all-have-field-val)

;; returns :fail if none is found, or a quoted constant
(defun constant-value-of-field (heap-triples address field)
  (declare (xargs :guard (and (true-listp heap-triples)
                              (items-have-len 3 heap-triples))))
  (if (endp heap-triples)
      :fail
    (let* ((triple (first heap-triples))
           (triple-address (first triple))
           (triple-pair (second triple))
           (triple-value (third triple)))
      (if (and (equal triple-address address)
               (equal triple-pair field)
               (myquotep triple-value))
          triple-value
        (constant-value-of-field (rest heap-triples) address field)))))

;; returns :fail if the ADDRESSES don't all have constants written to
;; FIELD. Otherwise, returns a list of the constant values (unquoted).
(defun field-vals-if-all-addresses-have-them (addresses field heap-triples)
  (declare (xargs :guard (and (true-listp addresses)
                              (true-listp heap-triples)
                              (items-have-len 3 heap-triples))))
  (if (endp addresses)
      nil
    (let* ((address (first addresses))
           (maybe-constant-value-of-field (constant-value-of-field heap-triples address field)))
      (if (eq :fail maybe-constant-value-of-field)
          :fail
        (cons (unquote maybe-constant-value-of-field)
              (field-vals-if-all-addresses-have-them (rest addresses) field heap-triples))))))

;;;
;;; get-field-of-addresses
;;;

;; This machinery handles the following situation: Say you have an array, A, of
;; references to objects, all of which have a field F.  Then you encounter a
;; term representing A[i].F but i is not a constant.  It may be the case that
;; all of the objects have F fields that are constant (maybe all the same,
;; maybe different).  In such a case, one can simplify the above expression to
;; L[i], where L is the constant list of the F fields of the items in the
;; array, in order.  Essentially, this swaps the field extraction and the array
;; indexing (meaning that the field extraction must be done on every element).

;; Get the value of a single field from multiple objects, returning a list of
;; the values.
(defund get-field-of-addresses (addresses field heap)
  (if (endp addresses)
      nil
    (cons (get-field (first addresses) field heap)
          (get-field-of-addresses (rest addresses) field heap))))

(defthm get-field-of-addresses-of-cons
  (equal (get-field-of-addresses (cons ad ads) field heap)
         (cons (get-field ad field heap)
               (get-field-of-addresses ads field heap)))
  :hints (("Goal" :in-theory (enable get-field-of-addresses))))

(defthm get-field-of-addresses-of-nil
  (equal (get-field-of-addresses nil field heap)
         nil)
  :hints (("Goal" :in-theory (enable get-field-of-addresses))))

(defthmd get-field-of-nth
  (implies (and (natp n)
                (< n (len ads)))
           (equal (get-field (nth n ads) field heap)
                  (nth n (get-field-of-addresses ads field heap))))
  :hints (("Goal" :in-theory (e/d (nth get-field-of-addresses)
                                  (;nth-of-cdr
                                   )))))

(defthmd get-field-of-nth-when-equal-of-get-field-of-addresses
  (implies (and (equal (get-field-of-addresses ads field heap)
                       val)
                (syntaxp (quotep val))
                (natp n)
                (< n (len ads)))
           (equal (get-field (nth n ads) field heap)
                  (nth n val)))
  :hints (("Goal" :in-theory (enable get-field-of-nth))))

(defthmd get-field-of-nth-when-equal-of-get-field-of-addresses-alt
  (implies (and (equal val
                       (get-field-of-addresses ads field heap))
                (syntaxp (quotep val))
                (natp n)
                (< n (len ads)))
           (equal (get-field (nth n ads) field heap)
                  (nth n val)))
  :hints (("Goal" :in-theory (enable get-field-of-nth))))

;; See comment on field-claims-for-array-items.  Returns a list of claims
(defun field-claim-for-array-items (field addresses heap-triples ads-term heap-term)
  (declare (xargs :guard (and (true-listp addresses)
                              (true-listp heap-triples)
                              (items-have-len 3 heap-triples))))
  (let* ((maybe-value-list (field-vals-if-all-addresses-have-them addresses field heap-triples)))
    (if (not (eq :fail maybe-value-list))
        `((equal (get-field-of-addresses ,ads-term ,field ,heap-term)
                 ',maybe-value-list))
      nil)))

;; For each field in FIELDS, if all of the ADDRESSES are given a constant value
;; (not necessarily the same constant) for that field by the TRIPLES, make an
;; assumption about the result of projecting out that field from all of the
;; ADDRESSES. TODO: Consider then removing the individual claims about the
;; field vals of all the individual addresses -- but we'd need to do some
;; analysis that the addresses involved are not referred to outside their use
;; in populating the array pointed to by the static field we are handling.
(defun field-claims-for-array-items (fields addresses heap-triples ads-term heap-term)
  (declare (xargs :guard (and (true-listp fields) ;all quoted
                              (true-listp addresses)
                              (true-listp heap-triples)
                              (items-have-len 3 heap-triples))))
  (if (endp fields)
      nil
    (append (field-claim-for-array-items (first fields) addresses heap-triples ads-term heap-term)
            (field-claims-for-array-items (rest fields) addresses heap-triples ads-term heap-term))))

(mutual-recursion
 ;; Make assumptions corresponding to elements of HEAP-TRIPLES representing
 ;; writes to ADDRESS-TERM, except use TERM-FOR-ASSUMPTIONS, which is equal to
 ;; ADDRESS-TERM, when making the assumptions.
 (defun initialized-field-assumptions-for-heap-address (count
                                                        heap-triples
                                                        address-term
                                                        term-for-assumptions ;a path into the heap starting from a static field
                                                        base-heap-term
                                                        all-heap-triples)
   (declare (xargs :guard (and (natp count)
                               (true-listp heap-triples)
                               (items-have-len 3 heap-triples)
                               (pseudo-term-listp (strip-cadrs heap-triples))
                               (pseudo-term-listp (strip-caddrs heap-triples))
                               (pseudo-termp base-heap-term)
                               (all-supported-heap-value-term-in-heapp (strip-caddrs heap-triples) base-heap-term)
                               (true-listp all-heap-triples)
                               (items-have-len 3 all-heap-triples)
                               (pseudo-term-listp (strip-caddrs all-heap-triples))
                               (pseudo-term-listp (strip-cadrs all-heap-triples))
                               (all-supported-heap-value-term-in-heapp (strip-caddrs all-heap-triples) base-heap-term)
                               (pseudo-termp term-for-assumptions))
                   :verify-guards nil ;done below
                   ))
   (if (zp count)
       (er hard? 'initialized-field-assumptions-for-heap-address "Limit reached.  Possible circularity in heap.")
     (if (endp heap-triples)
         nil
       (let* ((triple (first heap-triples))
              (address-term-of-triple (first triple)))
         (if (not (equal address-term address-term-of-triple))
             ;; This triple is irrelevant:
             (initialized-field-assumptions-for-heap-address (+ -1 count) (rest heap-triples) address-term term-for-assumptions base-heap-term all-heap-triples)
           ;; This triple represents a heap write to a field of the address we
           ;; are interested in:
           (let ((quoted-class-field-pair (second triple))
                 (value-term (third triple)))
             (append
              (if (symbolic-constantp value-term)
                  ;;if the value is a constant, we make a direct claim about it
                  ;;(if not, the value term must mention a new address, so we
                  ;;can't make a direct claim):
                  `((equal (get-field ,term-for-assumptions ,quoted-class-field-pair ,base-heap-term)
                           ,value-term))
                (if (symbolic-new-address-in-heapp value-term base-heap-term)
                    ;; The value written is a symbolic new address (can't
                    ;; mention such an address in these assumptions), so
                    ;; generate assumptions for its fields:
                    (initialized-field-assumptions-for-heap-address (+ -1 count)
                                                                    all-heap-triples
                                                                    value-term
                                                                    `(get-field ,term-for-assumptions ,quoted-class-field-pair ,base-heap-term)
                                                                    base-heap-term
                                                                    all-heap-triples)
                  ;; The value must be a symbolic list (cons nest) of
                  ;; new-addresses and constants, so generate assumptions for
                  ;; the individual addresses and for the length.  TODO: Check
                  ;; that this is a "contents" field of an array.
                  (if (not (symbolic-listp value-term))
                      (er hard 'initialized-field-assumptions-for-heap-address "Unexpected case.")
                    ;; guard proof should exclude this case:
                    (if (not (equal quoted-class-field-pair
                                    `',(array-contents-pair)))
                        (er hard? 'initialized-field-assumptions-for-heap-address "Unexpected case (value is a list but we don't seem to be setting the contents field of an array.")
                      ;; It's a symbolic list (and we can assume it's non-empty since it's not a constant):
                      (let* ((symbolic-array-elements (symbolic-list-elements value-term))
                             (symbolic-new-addresses (filter-non-quoteps symbolic-array-elements))
                             (field-term `(get-field ,term-for-assumptions ,quoted-class-field-pair ,base-heap-term))
                             (fields-for-first-ad (heap-triple-fields-for-ad all-heap-triples (first symbolic-array-elements))) ;these are quoted
                             )
                        (append `((equal (len ,field-term) ',(len symbolic-array-elements)))
                                (field-claims-for-array-items fields-for-first-ad
                                                              symbolic-array-elements
                                                              all-heap-triples
                                                              field-term
                                                              base-heap-term)
                                (if (and (equal symbolic-new-addresses
                                                symbolic-array-elements)
                                         (subsetp-equal symbolic-array-elements (strip-cars all-heap-triples)))
                                    ;; If all the array elements are new
                                    ;; addresses (and all such addresses have
                                    ;; some field written -- which they will,
                                    ;; at least to set their classes), then
                                    ;; generate an assumption about all the
                                    ;; addresses being bound:
                                    `((all-bound-in-heap (get-field ,term-for-assumptions ,quoted-class-field-pair ,base-heap-term)
                                                         ,base-heap-term))
                                  nil)
                                (initialized-field-assumptions-for-heap-addresses (+ -1 count)
                                                                                  symbolic-new-addresses
                                                                                  0 ;element number
                                                                                  field-term
                                                                                  base-heap-term
                                                                                  all-heap-triples)))))))
              ;; Process the rest of the heap-triples, since they may set other fields of this object:
              (initialized-field-assumptions-for-heap-address (+ -1 count) (rest heap-triples) address-term term-for-assumptions base-heap-term all-heap-triples))))))))

 (defun initialized-field-assumptions-for-heap-addresses (count
                                                          address-terms
                                                          element-number
                                                          term-for-assumptions ;a path into the heap starting from a static field
                                                          base-heap-term
                                                          all-heap-triples)
   (declare (xargs :guard (and (natp count)
                               (pseudo-term-listp address-terms)
                               (natp element-number)
                               (pseudo-termp term-for-assumptions)
                               (true-listp all-heap-triples)
                               (items-have-len 3 all-heap-triples)
                               (pseudo-term-listp (strip-cadrs all-heap-triples))
                               (pseudo-term-listp (strip-caddrs all-heap-triples))
                               (pseudo-termp base-heap-term)
                               (all-supported-heap-value-term-in-heapp (strip-caddrs all-heap-triples) base-heap-term))))
   (if (zp count)
       (er hard? 'initialized-field-assumptions-for-heap-address "Limit reached.  Possible circularity in heap.")
     (if (endp address-terms)
         nil
       (append (initialized-field-assumptions-for-heap-address (+ -1 count)
                                                               all-heap-triples
                                                               (first address-terms)
                                                               `(nth ',element-number ,term-for-assumptions)
                                                               base-heap-term
                                                               all-heap-triples)
               (initialized-field-assumptions-for-heap-addresses (+ -1 count)
                                                                 (rest address-terms)
                                                                 (+ 1 element-number)
                                                                 term-for-assumptions ;a path into the heap starting from a static field
                                                                 base-heap-term
                                                                 all-heap-triples))))))

(make-flag initialized-field-assumptions-for-heap-address)

(defthm-flag-initialized-field-assumptions-for-heap-address
  (defthm theorem-for-initialized-field-assumptions-for-heap-address
    (true-listp (initialized-field-assumptions-for-heap-address count heap-triples address-term term-for-assumptions base-heap-term all-heap-triples))
    :flag initialized-field-assumptions-for-heap-address)
  (defthm theorem-for-initialized-field-assumptions-for-heap-addresses
    (true-listp (initialized-field-assumptions-for-heap-addresses count address-terms element-number term-for-assumptions base-heap-term all-heap-triples))
    :flag initialized-field-assumptions-for-heap-addresses))

(verify-guards initialized-field-assumptions-for-heap-address
  :hints (("Goal" :in-theory (enable all-supported-heap-value-term-in-heapp
                                     supported-heap-value-termp))))

(defun initialized-class-assumptions-for-static-fields (static-field-triples heap-triples base-static-field-map-term base-heap-term)
  (declare (xargs :guard (and (true-listp heap-triples)
                              (items-have-len 3 heap-triples)
                              (pseudo-termp base-heap-term)
                              (pseudo-term-listp (strip-cars heap-triples))
                              (pseudo-term-listp (strip-cadrs heap-triples))
                              (pseudo-term-listp (strip-caddrs heap-triples))
                              (all-supported-heap-value-term-in-heapp (strip-caddrs heap-triples)
                                             base-heap-term)
                              (true-listp static-field-triples)
                              (pseudo-termp base-static-field-map-term)
                              (items-have-len 3 static-field-triples)
                              (pseudo-term-listp (strip-cars static-field-triples))
                              (pseudo-term-listp (strip-cadrs static-field-triples)))
                  :guard-hints (("Goal" :in-theory (enable strip-cars)))))
  (if (endp static-field-triples)
      nil
    (let* ((triple (first static-field-triples))
           (quoted-class-name (first triple))
           (quoted-field-id (second triple))
           (value-term (third triple)) ;known to be a new address or a quotep
           )
      (if (quotep value-term)
          (cons `(equal (jvm::get-static-field ,quoted-class-name ,quoted-field-id ,base-static-field-map-term) ,value-term)
                (initialized-class-assumptions-for-static-fields (rest static-field-triples) heap-triples base-static-field-map-term base-heap-term))
        ;; the value is a new address, so get info about its fields from the heap-term:
        (append (initialized-field-assumptions-for-heap-address 1000000
                                                                heap-triples
                                                                value-term
                                                                `(jvm::get-static-field ,quoted-class-name ,quoted-field-id ,base-static-field-map-term)
                                                                base-heap-term
                                                                heap-triples)
                (initialized-class-assumptions-for-static-fields (rest static-field-triples) heap-triples base-static-field-map-term base-heap-term))))))

(defun assumption-checking-rules ()
  (set-difference-eq (append '(jvm::static-field-map-of-make-state
                               jvm::heap-of-make-state
                               get-field-of-set-field-diff-1
                               get-field-of-set-field-diff-2
                               get-field-of-set-field-same
                               get-static-field-of-set-static-field-same
                               get-static-field-of-set-static-field-diff
                               list::nth-of-cons
;                               equal-of-cons-and-cons
                               insert-of-rkeys-of-set-field-same
                               list::len-cons
                               all-bound-in-heap-of-cons
                               all-bound-in-heap-of-nil
                               get-field-of-addresses-of-nil
                               get-field-of-addresses-of-cons
                               in-of-nth-new-ad-and-2set-of-n-new-ads)
                             (base-rules)
                             ;; (jvm-semantics-rules)
                             (jvm-simplification-rules)
                             (new-ad-rules)  ;include less of these?
                             ;extra-rules
                             )
                     '(rkeys-of-set-field-both)))

;; ;; Returns (mv erp :ok-or-nil state).
;; (defun sanity-check-assumptions (generated-assumptions state-var initialized-state-dag state)
;;   (declare (xargs :mode :program
;;                   :stobjs (state)
;;                   :guard (pseudo-term-listp generated-assumptions)))
;;   (if (endp generated-assumptions)
;;       (mv (erp-nil) :ok state)
;;     (b* ((assumption (first generated-assumptions))
;;          (dag-to-prove (compose-term-and-dag assumption state-var initialized-state-dag))
;;          ((mv erp sanity-check-result state)
;;           (simp-dag dag-to-prove :rules (assumption-checking-rules) :check-inputs nil))
;;          ((when erp) (mv erp nil state))
;;          ((when (not (equal sanity-check-result *t*)))
;;           (cw "(Failure dag:~% ~x0)~%" sanity-check-result)
;;           (mv (erp-t)
;;               (er hard 'initialized-class-assumptions-fn "Sanity check failed to prove assumption ~X01.  See rewritten DAG above." assumption nil)
;;               state)))
;;       (sanity-check-assumptions (rest generated-assumptions) state-var initialized-state-dag state))))

;; Create a list of assumptions about S0 that correspond to what the
;; initializers of the given classes do (todo: what about superclasses?).  Note
;; that the particular heap addresses will not be relevant, so we must
;; abstract.
;; Returns (mv erp assumptions state).
(defun initialized-class-assumptions-fn (class-names
                                         assumptions
                                         extra-rules
                                         monitored-rules
                                         state)
  (declare (xargs :mode :program
                  :stobjs (state)
                  :guard (and (true-listp class-names)
                              (jvm::all-class-namesp class-names))))
  (b* ((- (cw "(Generating assumptions established by the static initializers of ~x0:~%" class-names))
       (state-var 's0)
       ((mv erp initialized-state-term state)
        (initialize-classes-in-arbitrary-state class-names :assumptions assumptions :extra-rules extra-rules :monitor monitored-rules))
       ((when erp)
        (mv erp nil state))
       ((mv matchp alist)
        (unify-term initialized-state-term '(jvm::make-state :tt :heap :ct :hrt :mt :static-field-map :initialized-classes :intern-table)))
       ((when (not matchp))
        (mv :bad-for-for-state (er hard 'initialized-class-assumptions "Bad form for a state: ~x0" initialized-state-term) state))
       (heap-term (lookup-eq-safe :heap alist))
       (static-field-map-term (lookup-eq-safe :static-field-map alist))
       ;; Check the heap:
       (base-heap-term `(jvm::heap ,state-var))
       ((when (not (symbolic-set-field-nestp heap-term base-heap-term)))
        (mv :unsupported-heap-term (er hard 'initialized-class-assumptions "Unsupported heap term: ~X01" heap-term nil) state))
       (heap-triples (get-heap-triples-from-symbolic-set-field-nest heap-term base-heap-term)) ;each is (list address class-field-pair value)
       (addresses-written-in-heap (strip-cars heap-triples))
       (class-field-pairs-written-in-heap (strip-cadrs heap-triples)) ;each is a quoted constant?
       (values-written-to-heap (strip-caddrs heap-triples))
       (ad-field-pairs (pairlis$ addresses-written-in-heap class-field-pairs-written-in-heap))
       ((when (not (all-supported-heap-value-term-in-heapp values-written-to-heap base-heap-term)))
        (mv :unsupported-heap-term
            (er hard 'initialized-class-assumptions
                "Unsupported heap term (not all writes are constants or new addresses or symbolic lists of supported terms): ~x0.  Offending values: ~X12"
                heap-term
                (filter-non-supported-heap-value-terms-in-heapp values-written-to-heap base-heap-term)
                nil)
            state))
       ((when (not (all-symbolic-new-address-in-heapp addresses-written-in-heap base-heap-term)))
        (mv :unsupported-written-ads
            (er hard 'initialized-class-assumptions "Unsupported written ads in heap: ~x0" heap-term) state))
       ((when (not (no-duplicatesp ad-field-pairs)))
        (mv :unsupported-heap-term
            (er hard 'initialized-class-assumptions "Unsupported heap term (duplicate writes): ~x0" heap-term) state))
       ;; Check the static-field-map:
       (base-static-field-map-term `(jvm::static-field-map ,state-var))
       ((when (not (symbolic-set-static-field-nestp static-field-map-term base-static-field-map-term)))
        (mv :unsupported-static-field-map
            (er hard 'initialized-class-assumptions "Unsupported static-field-map term: ~X01" static-field-map-term nil) state))
       (static-field-triples (get-static-field-triples-from-symbolic-set-static-field-nest static-field-map-term base-static-field-map-term))
       (class-names-of-static-field-writes (strip-cars static-field-triples))
       (field-ids-of-static-field-writes (strip-cadrs static-field-triples))
       (values-of-static-field-writes (strip-caddrs static-field-triples))
       (class-name-field-id-pairs (pairlis$ class-names-of-static-field-writes field-ids-of-static-field-writes))
       ((when (not (no-duplicatesp class-name-field-id-pairs)))
        (mv :unsupported-static-field-map
            (er hard 'initialized-class-assumptions "Unsupported static-field-map term (duplicate writes): ~x0" static-field-map-term) state))
       ((when (not (all-supported-scalar-termp values-of-static-field-writes base-heap-term)))
        (mv :unsupported-static-field-map
            (er hard 'initialized-class-assumptions "Unsupported static-field-map term (bad value): ~x0" static-field-map-term) state))
       (generated-assumptions (initialized-class-assumptions-for-static-fields static-field-triples heap-triples base-static-field-map-term base-heap-term))
       (- (cw "(Generated ~x0 assumptions established by the static initializers of ~x1:~%~X23.)~%" (len generated-assumptions) class-names generated-assumptions nil))
       ;; ;; Sanity check
       ((mv erp initialized-state-dag) (dagify-term2 initialized-state-term))
       ((when erp) (mv erp nil state))
       ((mv erp dag-to-prove) (compose-term-and-dag (make-conjunction-from-list generated-assumptions) state-var initialized-state-dag))
       ((when erp) (mv erp nil state))
       ((mv erp sanity-check-result state)
        (simp-dag dag-to-prove
                  :rules (assumption-checking-rules)
                  :check-inputs nil))
       ((when erp) (mv erp nil state))
       ((when (not (equal sanity-check-result *t*)))
        (cw "(Failure dag:~% ~x0)~%" sanity-check-result)
        (mv :sanity-check-failed
            (er hard 'initialized-class-assumptions-fn "Sanity check failed.  See rewritten DAG above.")
            state
           ))
       (- (cw "(Sanity check passed.)~%"))
       ;; ((mv & state)
       ;;  (sanity-check-assumptions generated-assumptions state-var initialized-state-dag state))
       )
    (mv (erp-nil) generated-assumptions state)))

;; Returns (mv erp assumptions state).
(defmacro initialized-class-assumptions (class-names
                                         &key
                                         (assumptions 'nil)
                                         (extra-rules 'nil)
                                         (monitor 'nil)
                                         )
  `(initialized-class-assumptions-fn ,class-names ,assumptions ,extra-rules ,monitor state))

;; TODO: Add sanity check to prove the assumptions on the intialized class

(defthm in-of-nth-of-rkeys
  (implies (and (all-bound-in-heap ads heap)
                (< n (len ads))
                (natp n))
           (set::in (nth n ads) (rkeys heap)))
  :hints (("Goal" :in-theory (e/d (nth key-list)
                                  (;nth-of-cdr
                                   )))))

;; (defthm get-field-of-nth-when-all-have-field-val
;;   (implies (and (all-have-field-val ads pair val heap)
;;                 (< n (len ads))
;;                 (natp n))
;;            (equal (get-field (nth n ads) pair heap)
;;                   val))
;;   :hints (("Goal" :in-theory (e/d (nth key-list)
;;                                   (nth-of-cdr)))))
