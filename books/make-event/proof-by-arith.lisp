
; Sandip Ray points out that it would be really cool to do this sort of thing
; in parallel!  That may happen some day....


;; This comment fools the dependency scanner into thinking that this book
;; depends on lots of arithmetic books.
#||
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "arithmetic-3/top" :dir :system)
(include-book "rtl/rel9/arithmetic/top" :dir :system)

;; [Jared] trying to remove rtl/rel5
;; (include-book "rtl/rel5/arithmetic/top" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
||#

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc proof-by-arith
  :parents (arithmetic)
  :short "Attempt to prove a theorem using various arithmetic libraries"
  :long "<p>This book shows how one can use make-event to try different proof
  strategies for a given theorem, or more generally a given event, until one
  works.  Specifically, the strategies employed in this example are the use of
  different built-in arithmetic books.</p>

 <p>@('(proof-by-arith event)') expands into:</p>

 @({
 (encapsulate ()
              (local (include-book <book>))
              extra-event-1
              ...
              extra-event-k
              event)
 })

 <p>for an appropriate @('<book>') and @('extra-event-i') (@('1 <= i <= k')).
 By default, @('<book>') and associated events @('extra-event-i') are taken
 from @('*default-arith-book-alist*'), where each is tried in sequence until
 the encapsulate is admitted.</p>

 <p>The general form is:</p>

 @({(proof-by-arith event &optional quietp arith-book-alist)})

 <p>where @('quietp') suppresses output during the search, and
 @('arith-book-alist') can be used in place of
 @('*default-arith-book-alist*').</p>")

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
    ("rtl/rel9/arithmetic/top")
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

(defun proof-by-arith-1 (event book-alist inh)
  (declare (xargs :guard (true-list-listp book-alist)))
  (cond
   ((endp book-alist)
    nil)
   (t (cons (let* ((pair (car book-alist))
                   (book (car pair))
                   (extra-events (cdr pair))
                   (encap `(encapsulate
                            ()
                            (local (include-book ,book :dir :system))
                            ,@extra-events
                            ,event)))
              (if inh
                  `(with-output
                    :off ,inh
                    ,encap)
                encap))
            (proof-by-arith-1 event (cdr book-alist) inh)))))

(defmacro proof-by-arith (&whole whole-form
                                 event &optional quietp arith-book-alist)

; See comment at top of file.

; Note that all of the arguments are taken literally, i.e., none should be
; quoted.

  `(make-event
    (cons :or (proof-by-arith-1 ',event
                                ,(if arith-book-alist
                                     (list 'quote arith-book-alist)
                                   '*default-arith-book-alist*)
                                ',(and quietp
                                       '(prove proof-tree warning
                                               observation event
                                               history summary))))
    :on-behalf-of ,whole-form))

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
  ;; [Matt K.]: changed rel8 to rel9
  ("rtl/rel9/arithmetic/top")
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
