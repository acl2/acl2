(in-package "ACL2")

#|
Hi, Sarah (and Warren) --

Here's the email I promised, guiding you in how to use make-event to
write a new mut-rec macro, so that for example:

(mut-rec (defun f1 ...) (defun f2 ...))

produces the event

(progn (defun f1 ...) (defun f2 ...))

if f1 and f2 are not truly mutually recursive.

:Doc note-4-2 points to the book I mentioned, that gives a sense of
how to use make-event:

| The documentation for make-event now points to a new book,
| books/make-event/defrule.lisp, that shows how make-event can be used to
| do macroexpansion before generating events.  Thanks to Carl Eastlund for
| useful interaction on the acl2-help mailing list that led us to add this
| example.

Actually, this book has been updated (recently -- maybe with you,
Sarah), and I'm attaching the revised version.

That example is particularly useful in this case, because it shows how
to call translate to get the internal forms of the bodies of the
defuns.

So, I think I'd proceed as follows.
|#

(set-state-ok t)

(defun dcls-has-measurep (dcls)
  (if (atom dcls)
      nil
    (if (eq (caar dcls) 'xargs)
        (assoc-keyword :MEASURE (cdar dcls))
      (dcls-has-measurep (cdr dcls)))))

(defun def-has-measurep (def)
  (let ((dcl (fourth def)))
    (and (consp dcl)
         (eq (car dcl) 'declare)
         (dcls-has-measurep (cdr dcl)))))

(defun add-bogus-measure (def)
  (if (not (def-has-measurep def))
      (case-match def
        (('defun name formals . rest)
         `(defun ,name ,formals
            (declare (xargs :measure (acl2-count ,(car formals))))
            ,@rest))
        (& (er hard 'add-bogus-measure
               "Bad def, ~x0")))
    def))


(defun add-bogus-measure-lst (defs)
 (cond ((endp defs) nil)
       (t (cons (add-bogus-measure (car defs))
                (add-bogus-measure-lst (cdr defs))))))

(defun fn-names-from-defs (defs)
  (if (atom defs)
      nil
    (cons (cadar defs)
          (fn-names-from-defs (cdr defs)))))

;(cw "~x0~%" (all-fnnames ',defs)) ; nil (w state)))
(defun build-call-tree (fn-names state)
  (declare (xargs :mode :program))
  (if (atom fn-names)
      nil
    (acons (car fn-names)
           (all-fnnames (body (car fn-names) nil (w state)))
           (build-call-tree (cdr fn-names) state))))


(defun all-fnnames-list (fn-names state)
  (declare (xargs :mode :program))
  (if (atom fn-names)
      nil
    (union-equal (all-fnnames (body (car fn-names) nil (w state)))
            (all-fnnames-list (cdr fn-names) state))))


(include-book "ordinals/lexicographic-ordering" :dir :system)
(encapsulate
 ()
 (set-well-founded-relation l<)
 (mutual-recursion
  (defun free-node-list (ns call-tree unseen-nodes)
    (declare (xargs :measure (list (acl2-count unseen-nodes) (acl2-count ns) )))
    (if (atom ns)
        t
      (and (free-node (car ns) call-tree unseen-nodes)
           (free-node-list (cdr ns) call-tree unseen-nodes))))

  (defun free-node (n call-tree unseen-nodes)
    (declare (xargs :measure (list (acl2-count unseen-nodes) 0)))
    (and (member n unseen-nodes)
         (free-node-list (cdr (assoc n call-tree))
                         call-tree
                         (set-difference-eq unseen-nodes (list n)))))
  )
)

(defun separate-fns (df-fns call-tree all-fns mr-fns-acc rst-fns-acc)
  (if (atom df-fns)
      (mv mr-fns-acc rst-fns-acc)
    (if (free-node (car df-fns) call-tree all-fns)
        (separate-fns (cdr df-fns)
                      call-tree all-fns
                      mr-fns-acc
                      (cons (car df-fns) rst-fns-acc))
      (separate-fns (cdr df-fns)
                    call-tree all-fns
                    (cons (car df-fns) mr-fns-acc)
                    rst-fns-acc))))

(defun find-fn-def (fn-name defs)
  (if (atom defs)
      nil
    (if (equal (cadar defs) fn-name)
        (car defs)
      (find-fn-def fn-name (cdr defs)))))

(defun find-fn-defs (fn-names defs)
  (if (atom fn-names)
      nil
    (cons (find-fn-def (car fn-names) defs)
          (find-fn-defs (cdr fn-names) defs))))

(defun mut-rec-fn (defs state)
  (declare (xargs :mode :program))
  (let* ((dfnames (fn-names-from-defs defs))
         (fnnames (union-equal dfnames (all-fnnames-list dfnames state)))
         (call-tree (build-call-tree dfnames
                                     state)))
     (mv-let (mr-fns fr-fns)
             (separate-fns dfnames call-tree fnnames nil nil)
             (cons 'progn
                   (append
                    (find-fn-defs fr-fns defs)
                    (if mr-fns
                        (list (cons 'mutual-recursion
                                    (find-fn-defs mr-fns defs)))
                      nil))))))


(defmacro mut-rec (&rest defs)
 `(make-event (er-progn (set-ld-skip-proofsp t state)
                        (encapsulate
                         ()
                         (set-ignore-ok t)
                         (set-irrelevant-formals-ok t)
                         (set-bogus-mutual-recursion-ok t)
                         (mutual-recursion ,@(add-bogus-measure-lst defs)))
;                         (mutual-recursion ,@defs))
                         (value (mut-rec-fn ',defs state)))))



#|
(mut-rec
     (DEFUN WP-SUM-SIMPLE-MOD-2-L_280 (X Z A NSAVE)
            (WP-SUM-SIMPLE-MOD-2-L_282 X Z (COPY 0)
                                       NSAVE))
     (DEFUN WP-SUM-SIMPLE-MOD-2-L_282 (X Z A NSAVE)
            (WP-SUM-SIMPLE-MOD-2-L_283 X Z A NSAVE))
     (DEFUN WP-SUM-SIMPLE-MOD-2-L_283 (X Z A NSAVE)
            (AND (AND (NATP X) (NOT (= X 0)))
                 (WP-SUM-SIMPLE-MOD-2-L_286 X Z (INT_ADD A X 32)
                                            NSAVE)))
     (DEFUN WP-SUM-SIMPLE-MOD-2-L_286 (X Z A NSAVE)
            (AND (AND (NATP X) (NOT (= X 0)))
                 (WP-SUM-SIMPLE-MOD-2-L_287 (INT_SUB X 1 32)
                                            Z A NSAVE)))
     (DEFUN WP-SUM-SIMPLE-MOD-2-L_287 (X Z A NSAVE)
            (OR (AND (NATP X)
                     (AND (= X 0)
                          (WP-SUM-SIMPLE-MOD-2-L_291 X (= X 0)
                                                     A NSAVE)))
                (AND (NATP X)
                     (AND (NOT (= X 0))
                          (WP-SUM-SIMPLE-MOD-2-L_283 X (= X 0)
                                                     A NSAVE)))))
     (DEFUN WP-SUM-SIMPLE-MOD-2-L_291 (X Z A NSAVE)
            (= (* 2 A) (* NSAVE (+ 1 NSAVE)))))

(defun mut-rec-fn (defs state)
|#
; Return a suitable event, perhaps a progn or mutual-recursion or a combination
; of them, for introducing defs.

; The idea is to call (all-fnnames (body fn nil (w state))) for each function
; symbol defined in defs, to get a list of all function symbols in the
; translated body.  From that, one can build an alist associating each such
; fn with that list.  Then one can iterate, so that at each iteration one
; gathers up all function symbols whose bodies don't depend on any others bound
; in the alist.  Something like that.

;...)

;Please feel free to ask for help!



#|
(defmacro mut-rec (&rest defs)
 `(make-event (er-progn (set-ld-skip-proofsp t state)
                        (encapsulate
                         ()
                         (set-ignore-ok t)
                         (set-irrelevant-formals-ok t)
                         (set-bogus-mutual-recursion-ok t)
                         (mutual-recursion ,@(add-bogus-measure-lst defs)))
;                        (mut-rec-fn ',defs state))))
                        (prog2$
                         (cw "names ~x0~%" (all-fnnames-list
                                            (fn-names-from-defs ',defs) state))
                         (prog2$
                          (or
                           (cw "final-defs ~x0~%"
                               (mut-rec-fn ',defs state))
                           (cw "free? ~x0~%"
                               (free-node 'WP-SUM-SIMPLE-MOD-2-L_291
                                          (build-call-tree
                                           (fn-names-from-defs
                                            ',defs) state)
                                          (all-fnnames-list
                                           (fn-names-from-defs ',defs) state)))
                          (cw "free? ~x0~%"
                              (free-node 'WP-SUM-SIMPLE-MOD-2-L_280
                                         (build-call-tree
                                          (fn-names-from-defs
                                           ',defs) state)
                                         (all-fnnames-list
                                          (fn-names-from-defs ',defs) state))))
                           (value (list 'defun 'foo '(x) 'x)))))))
|#
