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


;; This comment fools the dependency scanner into thinking that this book
;; depends on lots of arithmetic books.
#||
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "arithmetic-3/top" :dir :system)
(include-book "rtl/rel8/arithmetic/top" :dir :system)

;; [Jared] trying to remove rtl/rel5
;; (include-book "rtl/rel5/arithmetic/top" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
||#

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

  '(("arithmetic/top-with-meta")
    ("arithmetic-3/top")
    ("rtl/rel8/arithmetic/top")
    ("arithmetic-3/top"
     (set-default-hints
      '((nonlinearp-default-hint
         stable-under-simplificationp
         hist
         pspv))))
    ("arithmetic-5/top")
    ("arithmetic-5/top"
     (set-default-hints
     '((nonlinearp-default-hint++ 
        id
        stable-under-simplificationp
        hist
        nil))))))

(defun proof-by-arith-1 (event book-alist ctx state)
  (declare (xargs :mode :program :stobjs state))
  (cond
   ((endp book-alist)
    (silent-error state)) ; (mv t nil state), a soft error
   (t (let* ((pair (car book-alist))
             (book (car pair))
             (extra-events (cdr pair))
             (in-certify-book (f-get-global 'certify-book-info state))
             (encap-event
              `(encapsulate
                ()
                (local (include-book ,book :dir :system))
                ,@extra-events
                ,event))
             (final-encap-event
              (cond (in-certify-book encap-event)
                    (t `(encapsulate
                         ()
                         (local (include-book ,book :dir :system))
                         (set-inhibit-warnings "Skip-proofs")
                         (skip-proofs
                          (encapsulate
                           ()
                           ,@extra-events
                           ,event)))))))
        (mv-let (erp trans-ans state) ; trans-ans is (cons stobjs-out values)
                (trans-eval encap-event ctx state t)
                (cond ((or erp
                           (car (cdr trans-ans))) ; erp from trans-ans
                       (proof-by-arith-1 event (cdr book-alist) ctx state))
                      (t (value final-encap-event))))))))

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
      (state-global-let*
       ((ld-skip-proofsp (if (eq (cert-op state) :write-acl2xu)

; We are doing provisional certification, so we need to save the correct
; expansion in the .acl2x file.  Normally we do a successful proof twice using
; proof-by-arith, and that will still hold in this case: once when generating
; the .acl2x file, and once when generating the .pcert file.

                             nil
                           (f-get-global 'ld-skip-proofsp state))))
       ,(if quietp
            `(er-progn (set-inhibit-output-lst '(prove proof-tree warning
                                                       observation event
                                                       expansion summary))
                       ,body)
          body))
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
  ;; [Jared]: trying to remove rtl/rel5
  ("rtl/rel8/arithmetic/top")
  ("arithmetic-3/bind-free/top"
   (set-default-hints
    '((nonlinearp-default-hint
       stable-under-simplificationp
       hist
       pspv))))))

; Test of non-trivial alist entry:
(proof-by-arith
 (defthm |proof-by-arith.lisp easy|
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

; Requires a few tries:
(proof-by-arith
 (defthm |proof-by-arith.lisp harder|
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (< a b))
            (< (* a a) (* b b)))))
