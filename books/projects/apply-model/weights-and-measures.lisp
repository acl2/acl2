; Weights and Measures for the Doppelganger Construction

; The doppelganger construction requires analysis of the user-defined
; functions, for example, to identify them, partition them into G1 and G2,
; determine the weight of each, determine their internals, etc.  This book
; provides a utility, implemented as a new make-event event named
; weights-and-measures, for doing that analysis.

; Suppose you want to create a file containing the defuns of the doppelgangers
; of the badged functions in a book named "some-user-defs.lisp".  Your
; doppelgangers book should begin by including this book.  Then locally include
; the book you want to analyze, "some-user-defs", but use the idiom:

; (local (include-book "some-user-defs")) ; no_port

; so that cert.pl doesn't load that book's portcullis.

; Then invoke the event:

; (weights-and-measures)

; Invoking (weights-and-measures) will define the following constants by
; analyzing the world created by the local inclusion of "some-user-defs".

;   *user-fns*
;   *g2-fns*
;   *g1-fns*
;   *tameness-conditions*
;   *weight-alist*
;   *max-internal-weight-alist*
;   *original-measures-alist*

; and it will introduce macro forms:
;   (tameness-bit fn)
;   (max-internal-weight fn)
;   (chronological-position fn)
;   (original-measure fn)

; These new macro forms can be used in the definitions of the measures for the
; G2 doppelgangers.  In fact, they SHOULD ONLY BE USED in that context since
; they TAMEP! and use formal variables like FN and ARGS that only make sense in
; the context of those measures.

(in-package "MODAPP")

(include-book "apply-prim")

(defun generate-g2-fns (chron-fns wrld g2-fns)
  (declare (xargs :mode :program))
  (cond
   ((endp chron-fns) (reverse g2-fns))
   (t (generate-g2-fns (cdr chron-fns)
                       wrld
                       (if (intersectp-eq g2-fns (all-fnnames (body (car chron-fns) nil wrld)))
                           (cons (car chron-fns) g2-fns)
                           g2-fns)))))

(defun generate-g2-tameness-conditions1 (vars ilks)
  (declare (xargs :mode :program))
  (cond
   ((eq ilks t) nil)
   ((endp ilks) nil)
   ((eq (car ilks) :FN)
    (cons `(TAMEP-FUNCTIONP! ,(car vars))
          (generate-g2-tameness-conditions1 (cdr vars) (cdr ilks))))
   ((eq (car ilks) :EXPR)
    (cons `(TAMEP! ,(car vars))
          (generate-g2-tameness-conditions1 (cdr vars) (cdr ilks))))
   (t (generate-g2-tameness-conditions1 (cdr vars) (cdr ilks)))))

(defun executable-badge (fn wrld)
  (declare (xargs :mode :program))
  (cond
   ((symbolp fn)
    (let ((temp (hons-get fn *badge-prim-falist*)))
      (cond
       (temp (cdr temp))
       ((eq fn 'BADGE) *generic-tame-badge-1*)
       ((eq fn 'TAMEP) *generic-tame-badge-1*)
       ((eq fn 'TAMEP-FUNCTIONP) *generic-tame-badge-1*)
       ((eq fn 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*)
       ((eq fn 'APPLY$) *apply$-badge*)
       ((eq fn 'EV$) *ev$-badge*)
       (t (cdr
           (assoc-eq
            fn
            (cdr
             (assoc-eq :badge-userfn-structure
                       (table-alist 'badge-table wrld)))))))))
   (t nil)))

(defun generate-g2-tameness-conditions (fns wrld)
  (declare (xargs :mode :program))
  (cond
   ((endp fns) nil)
   (t (cons (cons (car fns)
                  (generate-g2-tameness-conditions1
                   (formals (car fns) wrld)
                   (access apply$-badge
                           (executable-badge (car fns) wrld)
                           :ilks)))
            (generate-g2-tameness-conditions (cdr fns) wrld)))))

(defun weight1 (x weight-alist)
  (if (consp x)
      (+ 1
         (weight1 (car x) weight-alist)
         (weight1 (cdr X) weight-alist))
      (if (symbolp x)
          (let ((temp (assoc-eq x weight-alist)))
            (cond
             ((null temp) 0)
             (t (cdr temp))))
          (acl2-count x))))

(defun symbolp-to-natp-alistp (x)
  (cond
   ((atom x) (equal x nil))
   ((and (consp (car x))
         (symbolp (caar x))
         (natp (cdar x)))
    (symbolp-to-natp-alistp (cdr x)))))

(defthm symbolp-to-natp-alistp-implies-natp-cdr-assoc-equal
  (implies (and (assoc-equal x a)
                (symbolp-to-natp-alistp a))
           (natp (cdr (assoc-equal x a)))))

(defthm natp-weight1
  (implies (symbolp-to-natp-alistp a)
           (natp (weight1 x a)))
  :rule-classes :type-prescription)

(mutual-recursion

 (defun expand-all-lambdas (term)
   (declare (xargs :mode :program))
   (cond
    ((variablep term) term)
    ((fquotep term) term)
    ((flambdap (ffn-symb term))
     (expand-all-lambdas
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))))
    (t (fcons-term (ffn-symb term)
                   (expand-all-lambdas-list (fargs term))))))

 (defun expand-all-lambdas-list (terms)
   (declare (xargs :mode :program))
   (cond
    ((endp terms) nil)
    (t (cons (expand-all-lambdas (car terms))
             (expand-all-lambdas-list (cdr terms))))))
 )

(defun generate-weight-alist (fns weight-alist wrld)
  (declare (xargs :mode :program))
  (cond
   ((endp fns) weight-alist)
   (t (generate-weight-alist (cdr fns)
                             (cons (cons (car fns)
                                         (weight1 (expand-all-lambdas (body (car fns) nil wrld))
                                                  weight-alist))
                                   weight-alist)
                             wrld))))

(defun chronological-position1 (x lst next-available-chronological-position)
  (cond ((endp lst) (+ 1 next-available-chronological-position))
        ((eq x (car lst)) next-available-chronological-position)
        (t (chronological-position1 x (cdr lst) (+ 1 next-available-chronological-position)))))

(defun quoted-fn/expr-actuals (terms ilks)
  (declare (xargs :mode :program))
  (cond ((endp terms) nil)
        ((and (or (eq (car ilks) :fn)
                  (eq (car ilks) :expr))
              (quotep (car terms)))
         (cons (car terms)
               (quoted-fn/expr-actuals (cdr terms) (cdr ilks))))
        (t (quoted-fn/expr-actuals (cdr terms) (cdr ilks)))))

(defun fn/expr-formals (vars ilks)
  (declare (xargs :mode :program))
  (cond ((endp vars) nil)
        ((or (eq (car ilks) :fn)
             (eq (car ilks) :expr))
         (cons (car vars)
               (fn/expr-formals (cdr vars) (cdr ilks))))
        (t (fn/expr-formals (cdr vars) (cdr ilks)))))

(defun make-max-weight1 (lst)
  (declare (xargs :mode :program))
  (cond
   ((endp lst) 0)
   ((endp (cdr lst))
    `(weight ,(car lst)))
   (t `(max (weight ,(car lst))
            ,(make-max-weight1 (cdr lst))))))

(mutual-recursion
 (defun collect-internals (fn term g2-fns wrld ans)
   (declare (xargs :mode :program))
   (cond
    ((variablep term) ans)
    ((fquotep term) ans)
    ((flambdap (ffn-symb term))
     (er hard 'collect-internals
         "We thought all LAMBDAs were expanded before calling this function!"))
    ((null (executable-badge (ffn-symb term) wrld))
     (er hard 'collect-internals
         "Unbadged function ~x0!"
         (ffn-symb term)))
    ((and (not (eq fn (ffn-symb term)))
          (not (eq fn 'apply$))
          (not (eq fn 'ev$))
          (member-eq (ffn-symb term) g2-fns))
     (let* ((ilks (access apply$-badge
                          (executable-badge (ffn-symb term) wrld)
                          :ilks))
            (qlst (quoted-fn/expr-actuals (fargs term)
                                          (if (eq ilks t) nil ilks))))
       (collect-internals-lst
        fn
        (fargs term)
        g2-fns
        wrld
        (union-equal (cons (kwote (ffn-symb term)) qlst) ans))))
    (t (collect-internals-lst fn (fargs term) g2-fns wrld ans))))

 (defun collect-internals-lst (fn terms g2-fns wrld ans)
   (declare (xargs :mode :program))
   (cond
    ((endp terms) ans)
    (t (collect-internals-lst
        fn (cdr terms) g2-fns wrld
        (collect-internals fn (car terms) g2-fns wrld ans))))))

(defun make-max-internal-weight (fn g2-fns wrld)

; We return a list containing all 
; * :fn and :expr formals of fn
; * quoted evgs in :fn and :expr slots of the (beta-reduced) body of fn, and
; * quoted names of all all partially instantiated *g2-fns* called in that body

  (declare (xargs :mode :program))

  (make-max-weight1
   (union-equal
    (fn/expr-formals (formals fn wrld)
                     (if (and (executable-badge fn wrld)
                              (not (eq (access apply$-badge (executable-badge fn wrld) :ilks) t)))
                         (access apply$-badge (executable-badge fn wrld) :ilks)
                         nil))
    (collect-internals
     fn
     (expand-all-lambdas (body fn nil wrld))
     g2-fns
     wrld
     nil))))

(defun max-internal-weight-alist (fns g2-fns wrld alist)
  (declare (xargs :mode :program))
  (cond
   ((endp fns) alist)
   (t (max-internal-weight-alist
       (cdr fns)
       g2-fns
       wrld
       (cons (cons (car fns)
                   (make-max-internal-weight (car fns) g2-fns wrld))
             alist)))))

(defun generate-original-measures-alist (fns wrld)
  (declare (xargs :mode :program))
  (cond
   ((endp fns) nil)
   ((getpropc (car fns) 'justification nil wrld)
    (cons (cons (car fns)
                (access justification
                        (getpropc (car fns) 'justification nil wrld)
                        :measure))
          (generate-original-measures-alist (cdr fns) wrld)))
   (t (cons (cons (car fns) 0)
            (generate-original-measures-alist (cdr fns) wrld)))))

(defmacro weights-and-measures ()
  `(encapsulate
     nil
     (make-event
      `(defconst *user-fns*
; chronological listing of all badged fns in def-warrant order
         ',(reverse
            (strip-cars
             (cdr
              (assoc-eq :badge-userfn-structure
                        (table-alist 'badge-table (w state))))))))

     (make-event
      `(defconst *g2-fns* ; chronological listing of all fns ancestrally dependent
; on APPLY$, starting with APPLY$ and EV$; def-warrant order
         ',(generate-g2-fns *user-fns*
                            (w state)
                            '(apply$ ev$))))

     (defconst *g1-fns* ; chronological listing of all defun$ fns not ancestrally
; dependent on APPLY$; def-warrant order
       (set-difference-eq *user-fns* *g2-fns*))

     (make-event
      `(defconst *tameness-conditions*
         ',(generate-g2-tameness-conditions (cddr *g2-fns*) (w state))))

     (defmacro tameness-bit (fn)
       (let ((clst (cdr (assoc-eq fn *tameness-conditions*))))
         (cond
          ((null clst) 0)
          ((null (cdr clst)) `(IF ,(car clst) 0 1))
          (t `(IF ,(cons 'AND clst) 0 1)))))

     (make-event
      `(defconst *weight-alist*
         ',(generate-weight-alist (cddr *g2-fns*) nil (w state))))

     (defun weight (x) (weight1 x *weight-alist*))

     (defthm natp-weight
       (natp (weight x))
       :rule-classes :type-prescription)

     (defmacro chronological-position (x)
; Because *user-fns* is in def-warrant order, so are our positions.
       (cond
        ((or (eq x 'apply$)
             (eq x 'apply$-userfn))
         0)
        ((or (eq x 'ev$)
             (eq x 'ev$-list)) 1)
        ((member x *user-fns*)
         (chronological-position1 x *user-fns* 2))
        (t 0)))

     (make-event
      `(defconst *max-internal-weight-alist*
         ',(max-internal-weight-alist (cddr *g2-fns*) *g2-fns* (w state) nil)))


     (defmacro max-internal-weight (fn)
       (or (cdr (assoc-eq fn *max-internal-weight-alist*))
           0))

     (make-event
      `(defconst *original-measures-alist*
         ',(generate-original-measures-alist *g2-fns* (w state))))

     (defmacro original-measure (fn)
       (cdr (assoc-eq fn *original-measures-alist*)))

     ))


