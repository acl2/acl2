; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")

; Prove that various ACL2 primitives satisfy acl2p.

(defun prove-acl2p-lst (names)
  (declare (xargs :guard (symbol-listp names)))
  (cond ((endp names) nil)
        (t (cons `(make-event
                   (let* ((name ',(car names))
                          (acl2p-name (prefix-symbol "ACL2P-" name))
                          (formals (formals name (w state)))
                          (name-formals (cons name formals))
                          (acl2p-formals (pairlis-x1
                                          'acl2p
                                          (pairlis-x2 formals nil)))
                          (hints `(:hints
                                   (("Goal" :in-theory (enable ,name))))))
                     `(defthm ,acl2p-name
                        (implies ,(conjoin-untranslated-terms acl2p-formals)
                                 (acl2p ,name-formals))
                        ,@hints)))
                 (prove-acl2p-lst (cdr names))))))

(defmacro prove-acl2p (&rest name-or-names)
  (declare (xargs :guard (or (symbolp name-or-names)
                             (symbol-listp name-or-names))))
  (cond ((null name-or-names)
         '(value-triple :prove-acl2p-empty))
        ((null (cdr name-or-names))
         `(with-output :off :all :on (error)
            ,(car (prove-acl2p-lst name-or-names))))
        (t
         `(with-output :off :all :on (error)
            (progn ,@(prove-acl2p-lst name-or-names))))))

(defthm character-listp-implies-acl2p
  (implies (character-listp l)
           (acl2p l)))

(defthm acl2p-coerce
  (implies (and (acl2p x)
                (acl2p y))
           (acl2p (coerce x y)))
  :hints (("Goal" :use (:instance completion-of-coerce
                                  (acl2::x x)
                                  (acl2::y y)))))

(defthm symbol-listp-implies-acl2p ; for acl2p-pkg-imports
  (implies (symbol-listp lst)
           (acl2p lst))
  :hints (("Goal" :in-theory (disable (force)))))

(defthm acl2p-cons-rewrite
  (equal (acl2p (cons x y))
         (and (acl2p x)
              (acl2p y))))

(in-theory (e/d (bad-atom) ((:i acl2p))))

(defthm acl2p-hide
  (implies (acl2p x)
           (acl2p (hide x)))
  :hints (("Goal" :expand ((hide x)))))

; I don't know why the rule acl2p-return-last can cause a lot of slowdown in
; proving acl2p-pairlis$-tailrec, but it does, so we prove it first and disable
; it.  That should be fine since return-last is typically enabled.
; Similarly for disabling acl2p-the-check for acl2p-assoc2 and others.

(prove-acl2p return-last)
(prove-acl2p the-check)
(in-theory #!acl2(disable acl2p-return-last acl2p-the-check))

; And here are some more such, from proving acl2p-ancestors-check1.
(prove-acl2p if)
(prove-acl2p from-df)
(prove-acl2p mv-list)
(in-theory (disable acl2::acl2p-mv-list (:type-prescription acl2p)
                    acl2::acl2p-from-df acl2::acl2p-if))

; Modification of events in axioms.lisp.

(prove-acl2p add-to-set-eq-exec)
(prove-acl2p symbol-listp)

(local
 (encapsulate
  ()
  (local
   (defun all-vars1/all-vars1-lst (flg lst ans)
     (if (eq flg 'all-vars1)
         (cond ((variablep lst) (add-to-set-eq lst ans))
               ((fquotep lst) ans)
               (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst) ans)))
         (cond ((endp lst) ans)
               (t (all-vars1/all-vars1-lst 'all-vars-lst1 (cdr lst)
                                           (all-vars1/all-vars1-lst 'all-vars1 (car lst) ans)))))))

  (local
   (defthm step-1-lemma
     (equal (all-vars1/all-vars1-lst flg lst ans)
            (if (equal flg 'all-vars1) (all-vars1 lst ans) (all-vars1-lst lst ans)))))

  (local
   (defthm step-2-lemma
     (implies (and (acl2p ans)
                   (acl2p term))
              (acl2p (all-vars1/all-vars1-lst flg term ans)))))

; (prove-acl2p all-vars1)
  (defthm acl2::acl2p-all-vars1
    (implies (and (acl2p term)
                  (acl2p ans))
             (acl2p (all-vars1 term ans)))
    :hints (("Goal"
             :use (:instance step-2-lemma (flg 'all-vars1)))))))

(defun all-vars1-lst-induction (lst ans)
  (cond ((endp lst) ans)
        (t (all-vars1-lst-induction (cdr lst)
                                    (all-vars1 (car lst) ans)))))

; (prove-acl2p all-vars1-lst)
(defthm acl2::acl2p-all-vars1-lst
  (implies (and (acl2p lst) (acl2p ans))
           (acl2p (all-vars1-lst lst ans)))
  :hints (("Goal" :induct (all-vars1-lst-induction lst ans))))

(defthm acl2p-suff
  (implies (or (acl2-numberp x)
               (symbolp x)
               (characterp x)
               (stringp x))
           (acl2p x)))

(in-theory (disable acl2p))

(defun sort-by-increasing-absolute-event-number (fns wrld)
  (declare (xargs :mode :program))

; It would be easy enough to write this from scratch, but I'll take advantage
; of an existing utility defined in the ACL2 sources.

  (reverse
   (strip-cadrs (acl2::sort->-absolute-event-number (pairlis-x2 fns nil)
                                                    wrld))))

(defun restrict-to-defined-callees-2 (callees fal ok-fns)
  (declare (xargs :guard (and (symbol-listp callees)
                              (true-listp ok-fns))))
  (cond ((endp callees) t)
        (t (let ((g (car callees)))
             (and (or (member-eq g ok-fns)
                      (hons-get g fal))
                  (restrict-to-defined-callees-2 (cdr callees) fal ok-fns))))))

(defun restrict-to-defined-callees-1 (fns wrld fal ok-fns)
  (declare (xargs :mode :program))
  (cond
   ((endp fns) fal)
   ((member-eq (car fns) ok-fns)
    (restrict-to-defined-callees-1 (cdr fns) wrld fal ok-fns))
   (t
    (let* ((fn (car fns))
           (body (acl2::body fn nil wrld))
           (callees (acl2::all-ffn-symbs body nil))
           (okp (restrict-to-defined-callees-2 callees fal (cons fn ok-fns))))
      (restrict-to-defined-callees-1 (cdr fns)
                                     wrld
                                     (if okp
                                         (hons-acons fn nil fal)
                                       fal)
                                     ok-fns)))))

(defun restrict-to-defined-callees (fns wrld ok-fns)

; Fns is a list of function symbols sorted by increasing absolute-event-number.
; Ok-fns is a list of function symbols.  We restrict by accumulating into
; fast-alist acc, those members of fns not in ok-fns such that all callees in
; the definition are in acc (as keys)d or in ok-fns.  Note that this rules out
; collecting functions defined by mutual-recursion.

  (declare (xargs :mode :program))
  (let ((fal (restrict-to-defined-callees-1 fns wrld nil ok-fns)))
    (progn$ (fast-alist-free fal)
            (acl2::reverse-strip-cars fal nil))))

#!acl2
(encapsulate
  ()

  (local
   (in-theory
    (union-theories
     (union-theories '((:e tau-system))
                     (theory 'minimal-theory))
     (set-difference-theories
      (set-difference-theories (current-theory :here)
                               (function-theory 'ground-zero))
      '(member-eq-exec-is-member-equal
        member-eql-exec-is-member-equal
        assoc-eql-exec-is-assoc-equal
        rassoc-eq-exec-is-rassoc-equal
        rassoc-eql-exec-is-rassoc-equal
        remove-eq-exec-is-remove-equal
        remove-eql-exec-is-remove-equal
        remove1-eq-exec-is-remove1-equal
        remove1-eql-exec-is-remove1-equal
        remove-duplicates-eq-exec-is-remove-duplicates-equal
        remove-duplicates-eql-exec-is-remove-duplicates-equal
        set-difference-eq-exec-is-set-difference-equal
        set-difference-eql-exec-is-set-difference-equal
        add-to-set-eq-exec-is-add-to-set-equal
        add-to-set-eql-exec-is-add-to-set-equal
        union-eq-exec-is-union-equal
        union-eql-exec-is-union-equal
        remove1-assoc-eq-exec-is-remove1-assoc-equal
        remove1-assoc-eql-exec-is-remove1-assoc-equal
        remove-assoc-eq-exec-is-remove-assoc-equal
        remove-assoc-eql-exec-is-remove-assoc-equal
        put-assoc-eq-exec-is-put-assoc-equal
        put-assoc-eql-exec-is-put-assoc-equal
        intersection-eq-exec-is-intersection-equal
        intersection-eql-exec-is-intersection-equal
        )))))

  (make-event (let* ((wrld (w state))
                     (untouchables (global-val 'untouchable-fns wrld))
                     (fns
                      (zf::restrict-to-defined-callees
                       (zf::sort-by-increasing-absolute-event-number
                        (append (strip-cars *badge-prim-falist*)
                                (loop$ for x in *blacklisted-apply$-fns*
                                       when (and (logicp x wrld)
                                                 (not (member-eq x untouchables))
                                                 (not (assoc-eq x *ttag-fns*)))
                                       collect x))
                        wrld)
                       wrld
                       '(coerce cons-rewrite hide return-last the-check if
                                from-df mv-list add-to-set-eq-exec symbol-listp
                                all-vars1 all-vars1-lst))))
                `(zf::prove-acl2p ,@fns))))
