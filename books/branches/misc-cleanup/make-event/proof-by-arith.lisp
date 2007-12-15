; This book shows how one can use make-event to try different proof strategies
; for a given theorem until one works.  Specifically, the strategies employed
; in this example are the use of different built-in arithmetic books.

; (proof-by-arith event) expands into:

; (encapsulate ()
;              (local (include-book <book>))
;              extra-event-1
;              ...
;              extra-event-k
;              event)

; for an appropriate <book> and extra-event-i (1<=i<=k).  By default, book and
; associated events extra-event-i are taken from *default-arith-book-alist*,
; where each is tried in sequence until the encapsulate is admitted.

; The general form is

; (proof-by-arith event &optional quietp arith-book-alist)

; where quietp suppresses output during the search, and arith-book-alist can be
; used in place of *default-arith-book-alist*.

; Sandip Ray points out that it would be really cool to do this sort of thing
; in parallel!  That may happen some day....

(in-package "ACL2")

(comp '(union-theories-fn1
        set-difference-theories-fn1
        augment-runic-theory1
        runic-theoryp1
        theoryp1
        current-theory1
        theoryp!1
        current-theory-fn))

(defconst *default-arith-book-alist*

; Here is the default list of books to try including, each of which is
; associated with a list of events to execute after including the book.

  '(("arithmetic-3/bind-free/top")
    ("arithmetic-3/floor-mod/floor-mod")
    ("arithmetic/top-with-meta")
    ("rtl/rel5/arithmetic/top")
    ("arithmetic-3/bind-free/top"
     (set-default-hints
      '((nonlinearp-default-hint
         stable-under-simplificationp
         hist
         pspv))))
    ("arithmetic-3/floor-mod/floor-mod"
     (set-default-hints
      '((nonlinearp-default-hint
         stable-under-simplificationp
         hist
         pspv))))))

(defun proof-by-arith-1 (event book-alist ctx state)
  (declare (xargs :mode :program :stobjs state))
  (cond
   ((endp book-alist)
    (silent-error state)) ; (mv t nil state), a soft error
   (t (let* ((pair (car book-alist))
             (book (car pair))
             (extra-events (cdr pair))
             (encap-event
              `(encapsulate
                ()
                (local (include-book ,book :dir :system))
                ,@extra-events
                ,event)))
        (mv-let (erp trans-ans state) ; trans-ans is (cons stobjs-out values)
                (trans-eval encap-event ctx state)
                (cond ((or erp
                           (car (cdr trans-ans))) ; erp from trans-ans
                       (proof-by-arith-1 event (cdr book-alist) ctx state))
                      (t (value encap-event))))))))

(defmacro proof-by-arith (&whole whole-form
                                 event &optional quietp arith-book-alist)

; See comment at top of file.

; Note that all of the arguments are taken literally, i.e., none should be
; quoted.

  (let ((body `(proof-by-arith-1 ',event
                                 ,(if arith-book-alist
                                      (list 'quote arith-book-alist)
                                    '*default-arith-book-alist*)
                                 'proof-by-arith
                                 state)))
    `(make-event
      ,(if quietp
           `(er-progn (set-inhibit-output-lst '(prove proof-tree warning
                                                      observation event
                                                      expansion summary))
                      ,body)
         body)
      :on-behalf-of ,whole-form)))

; From John Erickson's email to acl2-help, 4/19/06.
(proof-by-arith
 (defthm nnid
   (implies (and (integerp n)
                 (< 0 n))
            (equal (denominator (+ 1 (* 1/2 n)))
                   (denominator (* 1/2 n))))
   :rule-classes nil))

; Use the quiet flag to avoid output during expansion.  If you run this event
; (after the others above except perhaps the immediately preceding) after
; executing (assign make-event-debug t), you can see that the expansion is
; quiet.
(proof-by-arith
 (defthm nnid2
   (implies (and (integerp n)
                 (< 0 n))
            (equal (denominator (+ 1 (* 1/2 n)))
                   (denominator (* 1/2 n))))
   :rule-classes nil)
 t)

; Using rtl arithmetic:
(proof-by-arith
 (defthm nnid3
   (implies (and (integerp n)
                 (< 0 n))
            (equal (denominator (+ 1 (* 1/2 n)))
                   (denominator (* 1/2 n))))
   :rule-classes nil)
 nil
 (("arithmetic-3/floor-mod/floor-mod"
   (set-default-hints
    '((nonlinearp-default-hint
       stable-under-simplificationp
       hist
       pspv))))
  ("rtl/rel5/arithmetic/top")
  ("arithmetic-3/bind-free/top"
   (set-default-hints
    '((nonlinearp-default-hint
       stable-under-simplificationp
       hist
       pspv))))))

; Test of non-trivial alist entry:
(proof-by-arith
 (defthm easy
   (equal (+ x y (- x))
          (fix y))
   :rule-classes nil)
 nil
 (("arithmetic-3/floor-mod/floor-mod"
   (set-default-hints
    '((nonlinearp-default-hint
       stable-under-simplificationp
       hist
       pspv))))))
