; A transformation to annotate local vars with declar or assign, for ATC
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Karthik Nukala (nukala@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Generalize to take the wrapper names (declar and assign) as options
;; (maybe also at that point remove "c" from the name of this transformation).
;; TODO: Generalize to take predicates that recognize when to use c::assign
;; and when to put in nothing.

;; TODO: Add some tests to ensure no wrappers are added to struct writers, etc.

;; Note the 3 cases in :doc atc-let-designations.

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/apt/utilities/def-equality-transformation" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/fresh-names" :dir :system)
(include-book "kestrel/utilities/pack-lists" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/bound-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/restore-mv-in-branches" :dir :system)
(include-book "kestrel/terms-light/reconstruct-lets-in-term" :dir :system)
(include-book "kestrel/terms-light/non-trivial-formals" :dir :system)
(include-book "kestrel/terms-light/replace-corresponding-arg" :dir :system)
(include-book "kestrel/typed-lists-light/symbol-listp" :dir :system)
(include-book "kestrel/strings-light/split-string-repeatedly" :dir :system)
(include-book "kestrel/c/atc/let-designations" :dir :system)
(include-book "std/system/check-mbt-call" :dir :system)
(include-book "std/system/check-mbt-dollar-call" :dir :system)
(include-book "std/system/number-of-results" :dir :system)
(include-book "std/system/formals-plus" :dir :system)
(include-book "std/system/uguard-plus" :dir :system)
(include-book "std/system/ubody-plus" :dir :system)
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/flatten-ands-in-lit" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable symbol-listp mv-nth true-listp plist-worldp member-equal)))

;; Check whether TERM is the macro expansion of mbt or mbt-dollar.
(defund call-of-mbt-or-mbt-dollarp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (b* (((mv mbtp &) (check-mbt-call term))
       ((mv mbt$p &) (check-mbt$-call term)))
    (or mbtp mbt$p)))

;; Find the member of ITEMS2 that is in the corresponding position as TARGET-ITEM is in ITEMS.
;; TARGET-ITEM should be a member of ITEMS.
;; TODO: does this function exist?
(defund corresponding-item (items items2 target-item)
  (declare (xargs :guard (and (true-listp items)
                              (true-listp items2))))
  (if (endp items)
      (er hard? 'corresponding-item "Did not find ~x0." target-item)
    (if (equal target-item (first items))
        (first items2)
      (corresponding-item (rest items) (rest items2) target-item))))

(defthm pseudo-termp-of-corresponding-item
  (implies (pseudo-term-listp items2)
           (pseudo-termp (corresponding-item items items2 target-item)))
  :hints (("Goal" :in-theory (enable corresponding-item))))

(defconst *modern-array-write-ops*
  (let ((types '(schar uchar sshort ushort sint uint slong ulong sllong ullong)))
    (pack-symbols-with-symbols types '(-array-write) "" "" "" "C")))

(defconst *deprecated-array-write-ops*
  (let ((types '(schar uchar sshort ushort sint uint slong ulong sllong ullong)))
    (pack-symbols-with-symbols types types "" "-ARRAY-WRITE-" "" "C")))

(defconst *array-write-ops*
  (append *modern-array-write-ops* *deprecated-array-write-ops*))

(defconst *scalar-write-ops*
  (let ((types '(schar uchar sshort ushort sint uint slong ulong sllong ullong)))
    (pack-symbol-with-symbols '|| types "" "" "-WRITE" "C")))

;; Recognizes symbols of the form:
;; struct-<tag>-write-<member>, or
;; struct-<tag>-write-<member>-<type>.
;; Doesn't take the world.  Since these names contain dashes, they can't be the
;; names of user functions passed to ATC (which must be portable ASCII C
;; identifiers).
;; TODO: Better check?
(defun struct-write-op-namep (name)
  (declare (xargs :guard (symbolp name)))
  (let ((parts (split-string-repeatedly (symbol-name name) #\-)))
    (and (or (= 4 (len parts))
             (= 5 (len parts)))
         (equal "STRUCT" (first parts))
         (equal "WRITE" (third parts)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Utilities for reasoning about translated mv-let terms

(defund mv-nth-call (term n)
  (declare (xargs :guard (and (pseudo-termp term)
                              (natp n))))
  (and (consp term)
       (let ((term (if (eql 'hide (ffn-symb term))
                       (farg1 term)
                     term)))
         (equal `(mv-nth ',n mv) term))))

(defund ascending-mv-nth-list-p (terms n)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (natp n))))
  (or (endp terms)
      (and (mv-nth-call (first terms) n)
           (ascending-mv-nth-list-p (rest terms) (+ n 1)))))

(defund trans-mv-let-p (term)
  (declare (xargs :guard (pseudo-termp term)))
  (b* (((unless (lambda-applicationp term)) nil)
       (outer-lambda (ffn-symb term))
       ((unless (equal (lambda-formals outer-lambda) '(mv))) nil)
       (outer-lambda-body (lambda-body outer-lambda))
       ((unless (lambda-applicationp outer-lambda-body)) nil)
       (mv-nth-list (fargs outer-lambda-body)))
    (and (consp mv-nth-list)
         (ascending-mv-nth-list-p mv-nth-list 0))))

(defund trans-mv-let-formals (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (trans-mv-let-p term))
                  :guard-hints (("Goal" :in-theory (enable trans-mv-let-p)))))
  (lambda-formals (ffn-symb (lambda-body (ffn-symb term)))))

(defthm symbol-listp-of-trans-mv-let-formals
  (implies (and (pseudo-termp term)
                (trans-mv-let-p term))
           (symbol-listp (trans-mv-let-formals term)))
  :hints (("Goal" :in-theory (enable trans-mv-let-p trans-mv-let-formals))))

(defthm consp-of-trans-mv-let-formals
  (implies (and (pseudo-termp term)
                (trans-mv-let-p term))
           (consp (trans-mv-let-formals term)))
  :hints (("Goal" :in-theory (enable trans-mv-let-formals
                                     trans-mv-let-p))))

(defund trans-mv-let-arg (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (trans-mv-let-p term))
                  :guard-hints (("Goal" :in-theory (enable trans-mv-let-p)))))
  (farg1 term))

(defthm pseudo-termp-of-trans-mv-let-arg
  (implies (and (pseudo-termp term)
                (trans-mv-let-p term))
           (pseudo-termp (trans-mv-let-arg term)))
  :hints (("Goal" :in-theory (enable trans-mv-let-p trans-mv-let-arg))))

(defthm acl2-count-of-trans-mv-let-arg-linear
  (implies (trans-mv-let-p term)
           (< (acl2-count (trans-mv-let-arg term))
              (acl2-count term)))
  :hints (("Goal" :in-theory (enable trans-mv-let-arg
                                     trans-mv-let-p)))
  :rule-classes ((:linear :trigger-terms ((acl2-count (trans-mv-let-arg term))))))

(defund trans-mv-let-body (term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (trans-mv-let-p term))
                  :guard-hints (("Goal" :in-theory (enable trans-mv-let-p)))))
  (lambda-body (ffn-symb (lambda-body (ffn-symb term)))))

(defthm pseudo-termp-of-trans-mv-let-body
  (implies (pseudo-termp term)
           (pseudo-termp (trans-mv-let-body term)))
  :hints (("Goal" :in-theory (enable trans-mv-let-body))))

(defthm acl2-count-of-trans-mv-let-body-linear
  (implies (trans-mv-let-p term)
           (< (acl2-count (trans-mv-let-body term))
              (acl2-count term)))
  :hints (("Goal" :in-theory (enable trans-mv-let-body
                                     trans-mv-let-p)))
  :rule-classes ((:linear :trigger-terms ((acl2-count (trans-mv-let-body term))))))

(defund make-mv-nth-list-aux (n acc)
  (declare (xargs :guard (natp n)))
  (let ((acc (cons `(mv-nth ',n mv) acc)))
    (if (zp n)
        acc
      (make-mv-nth-list-aux (- n 1) acc))))

(defthm pseudo-term-listp-of-make-mv-nth-list-aux
  (implies (pseudo-term-listp acc)
           (pseudo-term-listp (make-mv-nth-list-aux n acc)))
  :hints (("Goal" :in-theory (enable make-mv-nth-list-aux))))

(defthm len-of-make-mv-nth-list-aux
  (equal (len (make-mv-nth-list-aux n acc))
         (+ (nfix n) (len acc) 1))
  :hints (("Goal" :in-theory (enable make-mv-nth-list-aux))))

(defund make-mv-nth-list (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (make-mv-nth-list-aux (- n 1) nil)))

(defthm pseudo-term-listp-of-make-mv-nth-list
  (pseudo-term-listp (make-mv-nth-list n))
  :hints (("Goal" :in-theory (enable make-mv-nth-list))))

(defthm len-of-make-mv-nth-list
  (equal (len (make-mv-nth-list n))
         (nfix n))
  :hints (("Goal" :in-theory (enable make-mv-nth-list))))

(defund make-trans-mv-let (formals arg body)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-termp arg)
                              (pseudo-termp body))))
  `((lambda (mv)
      ((lambda ,formals
        ,body)
      ,@(make-mv-nth-list (len formals))))
    ,arg))

(defthmd pseudo-term-p-of-make-trans-mv-let
  (implies (and (symbol-listp formals)
                (pseudo-termp arg)
                (pseudo-termp body))
           (pseudo-termp (make-trans-mv-let formals arg body)))
  :hints (("Goal" :in-theory (enable make-trans-mv-let))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Light type-checking to determine whether a C-like function is void

(defund c-like-returns-aux (fn-name terms acc)
  (declare (xargs :guard (and (symbolp fn-name)
                              (pseudo-term-listp terms)
                              (pseudo-term-listp acc))))
  (and (mbt (pseudo-term-listp terms))
       (b* (((when (endp terms)) acc)
            (term (first terms))
            ((when (variablep term))
             (c-like-returns-aux fn-name (rest terms) (cons term acc)))
            (fn (ffn-symb term)))
         (cond ((consp fn)
                (c-like-returns-aux fn-name (cons (lambda-body fn) (rest terms)) acc))
               ((and (eq 'if fn)
                     (consp (cddr term)))
                ;; if the test is an mbt, we only consider the then branch
                (if (call-of-mbt-or-mbt-dollarp (farg1 term))
                    (c-like-returns-aux fn-name
                                        (cons (farg2 term) (rest terms))
                                        acc)
                  (c-like-returns-aux fn-name
                                      (list* (farg2 term) (farg3 term) (rest terms))
                                      acc)))
               ((eq fn-name fn)
                ;; term is a recursive call
                (c-like-returns-aux fn-name (rest terms) acc))
               (t (c-like-returns-aux fn-name (rest terms) (cons term acc)))))))

(defthm pseudo-term-listp-of-c-like-returns-aux
  (implies (and (pseudo-term-listp terms)
                (pseudo-term-listp acc))
           (pseudo-term-listp (c-like-returns-aux fn-name terms acc)))
  :hints (("Goal" :in-theory (e/d (c-like-returns-aux)
                                  (pseudo-term-listp-of-cons)))))

(defund c-like-returns (fn-name term)
  (declare (xargs :guard (and (symbolp fn-name)
                              (pseudo-termp term))))
  (c-like-returns-aux fn-name (list term) nil))

(defthm pseudo-term-listp-of-c-like-returns
  (implies (pseudo-termp term)
           (pseudo-term-listp (c-like-returns fn-name term)))
  :hints (("Goal" :in-theory (enable c-like-returns))))

(defund c-like-return-var (ret)
  (declare (xargs :guard (and (pseudo-termp ret))))
  (if (variablep ret)
      ret
    (and (consp ret)
         (eq 'cons (ffn-symb ret))
         (let ((farg1 (farg1 ret)))
           (and (variablep farg1)
                farg1)))))

(defthm symbolp-of-c-like-return-var
  (implies (pseudo-termp ret)
           (symbolp (c-like-return-var ret)))
  :hints (("Goal" :in-theory (enable c-like-return-var))))

(defund c-like-returns-all-var (var returns)
  (declare (xargs :guard (and (variablep var)
                              (pseudo-term-listp returns))))
  (or (endp returns)
      (and (eq var (c-like-return-var (first returns)))
           (c-like-returns-all-var var (rest returns)))))

(defund c-like-returns-var (returns)
  (declare (xargs :guard (pseudo-term-listp returns)))
  (if (endp returns)
      nil
    (let ((ret-var (c-like-return-var (first returns))))
      (and (c-like-returns-all-var ret-var (rest returns))
           ret-var))))

(defthm symbolp-of-c-like-returns-var
  (implies (pseudo-term-listp returns)
           (symbolp (c-like-returns-var returns)))
  :hints (("Goal" :in-theory (enable c-like-returns-var))))

(defconst *c-array-types*
  '(c::uchar-arrayp
    c::ushort-arrayp
    c::uint-arrayp
    c::ulong-arrayp
    c::ullong-arrayp
    c::schar-arrayp
    c::sshort-arrayp
    c::sint-arrayp
    c::slong-arrayp
    c::sllong-arrayp))

;; The following functions are based on `atc-typed-formals` and
;; `atc-check-guard-conjunct` in
;; books/kestrel/c/atc/function-and-loop-generation

(defund conjunct-is-mutable-type-of-c-var-p (var conjunct)
  (declare (xargs :guard (and (symbolp var)
                              (pseudo-termp conjunct))
                  :guard-hints (("Goal" :in-theory (enable check-mbt-call)))))
  (b* ((conjunct (mv-let (mbtp arg)
                   (check-mbt-call conjunct)
                   (if mbtp arg conjunct)))
       ((when (or (variablep conjunct)
                  (fquotep conjunct)
                  (flambda-applicationp conjunct)))
        nil)
       (fn (ffn-symb conjunct))
       (arg (farg1 conjunct)))
    (cond ((eq 'c::star fn)
           (and (not (variablep arg))
                (not (fquotep arg))
                (not (flambda-applicationp arg))
                (consp (cdr arg))
                (eq var (farg1 arg))))
          ((member-eq fn *c-array-types*)
           (eq var arg)))))

(defund any-conjunct-is-mutable-type-of-c-var-p (var conjuncts)
  (declare (xargs :guard (and (symbolp var)
                              (pseudo-term-listp conjuncts))))
  (and (not (endp conjuncts))
       (or (conjunct-is-mutable-type-of-c-var-p var (first conjuncts))
           (any-conjunct-is-mutable-type-of-c-var-p var (rest conjuncts)))))

(defund c-var-mutable-type-p (var guard)
  (declare (xargs :guard (and (symbolp var)
                              (pseudo-termp guard))))
  (any-conjunct-is-mutable-type-of-c-var-p var (flatten-ands-in-lit guard)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund c-like-fn-is-void-p-aux (fn-name formals guard body)
  (declare (xargs :guard (and (symbolp fn-name)
                              (symbol-listp formals)
                              (pseudo-termp guard)
                              ;; assume body is translated
                              (pseudo-termp body))))
  (b* ((return-terms (c-like-returns fn-name body))
       (ret-var (c-like-returns-var return-terms)))
    (and ret-var
         (member-eq ret-var formals)
         (c-var-mutable-type-p ret-var guard))))

(defund c-like-fn-is-void-p (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (c-like-fn-is-void-p-aux
   fn
   (formals+ fn wrld)
   (uguard+ fn wrld)
   (ubody+ fn wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund wrap-in-declar (term wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))))
  (if (variablep term)
      `(c::declar ,term)
    (if (quotep term)
        (prog2$ (er hard? 'wrap-in-declar "WARNING: Naked constant: ~x0." term)
                `(c::declar ,term))
      (let ((fn (ffn-symb term)))
        (if (or (not (symbolp fn))
                (member-eq fn *stobjs-out-invalid*))
            (er hard? 'wrap-in-declar "Unexpected term: ~x0." term)
          (let ((number-of-results (number-of-results fn wrld)))
            (case number-of-results
              (1 `(c::declar ,term))
              (2 `(c::declar1 ,term))
              (3 `(c::declar2 ,term))
              (4 `(c::declar3 ,term))
              (5 `(c::declar4 ,term))
              (6 `(c::declar5 ,term))
              (7 `(c::declar6 ,term))
              (8 `(c::declar7 ,term))
              (9 `(c::declar8 ,term))
              (10 `(c::declar9 ,term))
              (otherwise
               (prog2$ (er hard? 'wrap-in-declar
                           "Unsupported number of results: ~x0." number-of-results)
                       `(c::declar ,term))))))))))

(defthm pseudo-termp-of-wrap-in-declar
  (implies (pseudo-termp term)
           (pseudo-termp (wrap-in-declar term wrld)))
  :hints (("Goal" :in-theory (enable wrap-in-declar))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund wrap-in-assign (term wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))))
  (if (variablep term)
      `(c::assign ,term)
    (if (quotep term)
        (prog2$ (er hard? 'wrap-in-assign "WARNING: Naked constant: ~x0." term)
                `(c::assign ,term))
      (let ((fn (ffn-symb term)))
        (if (or (not (symbolp fn))
                (member-eq fn *stobjs-out-invalid*))
            (er hard? 'wrap-in-assign "Unexpected term: ~x0." term)
          (let ((number-of-results (number-of-results fn wrld)))
            (case number-of-results
              (1 `(c::assign ,term))
              (2 `(c::assign1 ,term))
              (3 `(c::assign2 ,term))
              (4 `(c::assign3 ,term))
              (5 `(c::assign4 ,term))
              (6 `(c::assign5 ,term))
              (7 `(c::assign6 ,term))
              (8 `(c::assign7 ,term))
              (9 `(c::assign8 ,term))
              (10 `(c::assign9 ,term))
              (otherwise
               (prog2$ (er hard? 'wrap-in-assign
                           "Unsupported number of results: ~x0." number-of-results)
                       `(c::assign ,term))))))))))

(defthm pseudo-termp-of-wrap-in-assign
  (implies (pseudo-termp term)
           (pseudo-termp (wrap-in-assign term wrld)))
  :hints (("Goal" :in-theory (enable wrap-in-assign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 ;; For each let-bound var, wrap 'c::declare around the first let-binding and,
 ;; for subsequent let-bindings, either wrap in 'c::assign (if the value is
 ;; non-statement), recurse (if the value is an if statement), or do nothing
 ;; (if the value is another type of statement).
 (defund annotate-c-locals-in-term (term seen-vars wrld)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-listp seen-vars)
                               (plist-worldp wrld))
                   :verify-guards nil ;; verified below
                   ))
   (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           term ; can this happen?
         (if (eq 'if fn)
             (let* ((test (farg1 term))
                    (test-is-mbtp (call-of-mbt-or-mbt-dollarp test)))
               `(if ,test
                    ;; always process the then-branch:
                    ,(annotate-c-locals-in-term (farg2 term) seen-vars wrld)
                  ,(if test-is-mbtp
                       ;; else branch irrelevant, so make no changes to it:
                       (farg3 term)
                     ;; else branch needs to be processed:
                     (annotate-c-locals-in-term (farg3 term) seen-vars wrld))))
           (if (consp fn)
               ;; Term is a lambda/let:
               (if (trans-mv-let-p term)
                   ;; Term is a translated mv-let:
                   (b* ((mv-let-body (trans-mv-let-body term))
                        (mv-let-formals (trans-mv-let-formals term))
                        (mv-let-arg (trans-mv-let-arg term))
                        ((mv new-arg new-seen-vars)
                         (annotate-c-locals-in-arg (first mv-let-formals)
                                                   mv-let-arg
                                                   seen-vars
                                                   wrld))
                        (new-body (annotate-c-locals-in-term mv-let-body new-seen-vars wrld)))
                     (make-trans-mv-let mv-let-formals new-arg new-body))
                 ;; not an mv-let:
                 (b* ((lambda-body (lambda-body fn))
                      (lambda-formals (lambda-formals fn))
                      (args (fargs term))
                      ((mv new-args new-seen-vars)
                       (annotate-c-locals-in-lambda lambda-formals args seen-vars wrld))
                      (new-body (annotate-c-locals-in-term lambda-body new-seen-vars wrld)))
                   `((lambda ,lambda-formals ,new-body) ,@new-args)))
             ;; The pattern 'mv-nth of mv-list' represents a un-reconstructed mv-let, so we allow both kinds of things here:
             (if (member-eq fn '(mv-nth mv-list)) ; both happen to be binary and have arg2 as the main one
                 `(,fn ,(farg1 term) ,(annotate-c-locals-in-term (farg2 term) seen-vars wrld))
               ;; May be a recursive call (allow only that?):
               term ;; (er hard? 'annotate-c-locals-in-term "Unexpected term: ~X01" term nil)
               )))))))

 (defund annotate-c-locals-in-lambda (formals args seen-vars wrld)
   (declare (xargs :guard (and (symbol-listp formals)
                               (pseudo-term-listp args)
                               (= (len formals) (len args))
                               (symbol-listp seen-vars)
                               (plist-worldp wrld))
                   :measure (acl2-count args)))
   (if (not (mbt (= (len formals) (len args))))
       (mv args seen-vars)
     (if (endp formals)
         (mv nil seen-vars)
       (b* (((mv new-arg new-seen-vars)
             (annotate-c-locals-in-arg (first formals) (first args) seen-vars wrld))
            ((mv new-args new-seen-vars)
             (annotate-c-locals-in-lambda (rest formals) (rest args) new-seen-vars wrld)))
         (mv (cons new-arg new-args) new-seen-vars)))))

 (defund annotate-c-locals-in-arg (formal arg seen-vars wrld)
   (declare (xargs :guard (and (symbolp formal)
                               (pseudo-termp arg)
                               (symbol-listp seen-vars)
                               (plist-worldp wrld))
                   :measure (acl2-count arg)
                   :ruler-extenders :all
                   ))
   (if (eql formal arg) ; skip trivial arguments
       (mv arg seen-vars)
     (b* ((formal-seenp (member-eq formal seen-vars))
          (new-seen-vars (if formal-seenp seen-vars (cons formal seen-vars)))
          (arg-fn (and (consp arg)
                       (let ((arg-fn (ffn-symb arg)))
                         (and (symbolp arg-fn)
                              arg-fn))))
          (arg-is-ifp (eq 'if arg-fn))
          (arg-is-statementp (and (not arg-is-ifp)
                                  (or (member-eq arg-fn *array-write-ops*)
                                      (member-eq arg-fn *scalar-write-ops*)
                                      ;; todo: pointer write ops?
                                      (struct-write-op-namep arg-fn)
                                      (and (function-symbolp arg-fn wrld)
                                           (logicp arg-fn wrld)
                                           (recursivep arg-fn nil wrld)))))
          (new-arg (cond (arg-is-ifp
                          `(if ,(farg1 arg)
                               ,(annotate-c-locals-in-term (farg2 arg) seen-vars wrld)
                             ,(annotate-c-locals-in-term (farg3 arg) seen-vars wrld)))
                         ((or arg-is-statementp
                              (and (not (variablep arg))
                                   (not (fquotep arg))
                                   (not (flambda-applicationp arg))
                                   (c-like-fn-is-void-p (ffn-symb arg) wrld)))
                          arg)
                         ((not formal-seenp) (wrap-in-declar arg wrld))
                         (t (wrap-in-assign arg wrld)))))
       (mv new-arg new-seen-vars)))))

(make-flag
 flag-annotate-c-locals-in-term
 annotate-c-locals-in-term
 :defthm-macro-name defthm-annotate-c-locals-in-term
 :ruler-extenders :all)

(defthm-annotate-c-locals-in-term
  (defthm pseudo-term-of-annotate-c-locals-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (annotate-c-locals-in-term term seen-vars wrld)))
    :flag annotate-c-locals-in-term)
  (defthm len-of-mv-nth-0-of-annotate-c-locals-in-lambda
    (equal (len (mv-nth 0 (annotate-c-locals-in-lambda formals args seen-vars wrld)))
           (len args))
    :flag annotate-c-locals-in-lambda)
  (defthm pseudo-term-listp-of-mv-nth-0-of-annotate-c-locals-in-lambda
    (implies (pseudo-term-listp args)
             (pseudo-term-listp (mv-nth 0 (annotate-c-locals-in-lambda formals args seen-vars wrld))))
    :flag annotate-c-locals-in-lambda)
  (defthm symbol-listp-of-mv-nth-1-of-annotate-c-locals-in-lambda
    (implies (and (symbol-listp formals)
                  (symbol-listp seen-vars))
             (symbol-listp (mv-nth 1 (annotate-c-locals-in-lambda formals args seen-vars wrld))))
    :flag annotate-c-locals-in-lambda)
  (defthm pseudo-termp-of-mv-nth-0-of-annotate-c-locals-in-arg
    (implies (pseudo-termp arg)
             (pseudo-termp (mv-nth 0 (annotate-c-locals-in-arg formal arg seen-vars wrld))))
    :flag annotate-c-locals-in-arg)
  (defthm symbol-listp-of-mv-nth-1-of-annotate-c-locals-in-arg
    (implies (and (symbolp formal)
                  (symbol-listp seen-vars))
             (symbol-listp (mv-nth 1 (annotate-c-locals-in-arg formal arg seen-vars wrld))))
    :flag annotate-c-locals-in-arg)
  :hints (("Goal"
           :in-theory (e/d (annotate-c-locals-in-term
                            annotate-c-locals-in-lambda
                            annotate-c-locals-in-arg)
                           (struct-write-op-namep))
           :expand ((annotate-c-locals-in-arg formal arg seen-vars wrld))
           :induct (flag-annotate-c-locals-in-term
                    flag term formals args formal arg seen-vars wrld))))

(verify-guards annotate-c-locals-in-term)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun annotate-c-locals-core-function-aux (fn
                                            body ;translated
                                            wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (not (member-eq fn *stobjs-out-invalid*))
                              (pseudo-termp body)
                              (plist-worldp wrld))))
  (let* ((new-body (annotate-c-locals-in-term body (fn-formals fn wrld) wrld))
         ;; TODO: Have def-equality-transformation always do this after getting back the transformed body?
         ;; TODO: What about mvs not in top-level ifs?
         (num-values (num-return-values-of-fn fn wrld))
         (new-body (if (<= 2 num-values)
                       (restore-mv-in-branches new-body num-values
                                               (list fn) ; do we need this?
                                               wrld)
                     new-body))
         (new-body (reconstruct-lets-in-term new-body)) ; the MV won't interfere with this
         )
    new-body))

;; Transforms a function body.  Returns the new body.
;; We call translate-term here and then do the rest of the work in the :logic-mode helper function.
(defun annotate-c-locals-core-function (fn untranslated-body state)
  (declare (xargs :mode :program ;because this calls translate-term
                  :guard (symbolp fn)
                  :stobjs state))
  (let* ((wrld (w state))
         (translated-body (translate-term untranslated-body 'annotate-c-locals-core-function wrld)) ;todo: can we avoid translating?
         )
    (annotate-c-locals-core-function-aux fn translated-body wrld)))

;; Make the full transformation:
(def-equality-transformation
  annotate-c-locals ; name of the transformation to create
  annotate-c-locals-core-function ; core function to transform a function body
  nil ; transform-specific required args
  nil                ; transform-specific keyword args and defaults
  :enables '(c::assign c::declar)
  :measure-enables '(c::assign c::declar)
  :guard-enables '(c::assign c::declar))
